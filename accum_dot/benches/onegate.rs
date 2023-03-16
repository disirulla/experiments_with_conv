#[warn(unused_must_use)]
#[warn(unused_imports)]
use accum_dot::RandomInputGenerator;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rand::rngs::OsRng;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Circuit, ConstraintSystem, Error, Column, Advice, Selector}, dev::MockProver, poly::kzg::commitment::ParamsKZG,
};
use halo2curves::{FieldExt, bn256::{Bn256, G1Affine}};
use std::{marker::PhantomData, time::Instant};
use std::io::Write;
use halo2_proofs::poly::Rotation;
use halo2_proofs::{
    plonk::*,
    poly::commitment::ParamsProver,
    transcript::{Blake2bRead, Blake2bWrite, Challenge255},
    poly::kzg::{
        commitment::KZGCommitmentScheme,
        multiopen::{ProverSHPLONK, VerifierSHPLONK},
        strategy::SingleStrategy,
    },
    transcript::{TranscriptReadBuffer, TranscriptWriterBuffer},
};


static  IMLEN:usize = 512;
static mut KERLEN:usize = 4;

#[derive(Debug,Clone)]
struct NormalConv<F: FieldExt>{
    image: Column<Advice>,
    kernel: Column<Advice>,
    conv: Column<Advice>,
    seldot: Selector,
    _marker: PhantomData<F>
}

#[derive(Debug,Clone)]
struct NormalConvChip<F: FieldExt>{
    config: NormalConv<F>,
    _marker: PhantomData<F>
}

impl<F: FieldExt> NormalConvChip<F>{
    pub fn configure(meta: &mut ConstraintSystem<F>)->NormalConv<F>{
        let image = meta.advice_column();
        let kernel = meta.advice_column();
        let conv = meta.advice_column();
        let seldot = meta.selector();

        meta.create_gate("normalconv", |meta|{
            let s = meta.query_selector(seldot);
            
            let mut diff  = vec![];
            let conlen;
            let klen;
            unsafe{
                conlen = IMLEN - KERLEN + 1;
                klen = KERLEN;
            }
            

            let mut imgexpvec = vec![];
            for i in 0..IMLEN{
                let imgbuf = meta.query_advice(image, Rotation((i as i32)));
                imgexpvec.push(imgbuf);
            }

            for i in 0..conlen{
                let exp_conv_val = meta.query_advice(conv, Rotation((i as i32)));
                let mut conv_val = Expression::Constant(F::zero());
                for j in 0..klen{
                    let ker = meta.query_advice(kernel, Rotation((j as i32)));
                    conv_val = conv_val + imgexpvec[i+j].clone()*ker;
                }
                let buf = conv_val - exp_conv_val;
                diff.push(buf);
            }
            Constraints::with_selector(s, diff)   
        });

        NormalConv { image: image,
             kernel: kernel,
              conv: conv,
              seldot: seldot,
            _marker: PhantomData }
    }
}

#[derive(Debug,Clone)]
struct NormalConvCircuit<F: FieldExt>{
    image: Vec<F>,
    kernel: Vec<F>,
}

impl<F:FieldExt> Circuit<F> for NormalConvCircuit<F>
{   
    type Config = NormalConv<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        return self.clone();
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        NormalConvChip::configure(meta)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_region(||"NormalConv", |mut region|{
            
            let mut imgcells = vec![];
            for i in 0..self.image.len(){
                let i_cell = region.assign_advice(||"image".to_owned()+&i.to_string(),
                 config.image, 
                 i, 
                 || Value::known(self.image[i]))?;
                imgcells.push(i_cell);   
            };

            let mut kercells = vec![];
            for i in 0..self.kernel.len(){
                let k_cell = region.assign_advice(||"kernel".to_owned()+&i.to_string(),
                 config.kernel, 
                 i, 
                 || Value::known(self.kernel[i]))?;
                kercells.push(k_cell);   
            };

            config.seldot.enable(&mut region, 0)?;

            let convlen = self.image.len() - self.kernel.len() + 1;
            for i in 0..convlen{
                let mut convcells = vec![];
                let mut conval = Value::known(F::zero());
                for j in 0..self.kernel.len(){
                    conval = conval + imgcells[i+j].value().copied()*kercells[j].value();
                }
                let conv_cell = region.assign_advice(||"conv_val".to_owned()+&i.to_string(),
                 config.conv, 
                 i, 
                 || conval)?;
                convcells.push(conv_cell);
            }
            Ok(())
        })
    
    }

}


fn run(c: &mut Criterion){
    let k = 10;
    let mut rng = OsRng;
    let mut group = c.benchmark_group("conv");
    let params = ParamsKZG::<Bn256>::setup(k, &mut rng);
    for &len in [4, 8, 16, 32, 64, 128, 256, 512].iter() {

        let gen;
        unsafe{
            KERLEN = len;
            gen = RandomInputGenerator::new(IMLEN, len);
        }
        let img = gen.one_dimage;
        let ker = gen.one_dkernel;
        let onegatecircuit =  NormalConvCircuit{
        image: img,
        kernel: ker
        };

        group.sample_size(10);
        group.throughput(Throughput::Elements(len as u64));
        group.bench_with_input(BenchmarkId::new("KeyGenForOneGate", len), &len, |b, &_| {
            b.iter(|| {
                let vk = keygen_vk(&params, &onegatecircuit).unwrap();
                let pk = keygen_pk(&params, vk, &onegatecircuit).unwrap();
            });
        });

        let vk = keygen_vk(&params, &onegatecircuit).unwrap();
        let pk = keygen_pk(&params, vk, &onegatecircuit).unwrap();

        group.sample_size(20);
        group.throughput(Throughput::Elements(len as u64));
        group.bench_with_input(BenchmarkId::new("ProofForOneGate", len), &len, |b, &_| {
            b.iter(|| {
                let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
                create_proof::<
                KZGCommitmentScheme<Bn256>,
                ProverSHPLONK<'_, Bn256>,
                Challenge255<G1Affine>,
                _,
                Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
                _,
            >(&params, &pk, &[onegatecircuit.clone()], &[&[]], rng, &mut transcript);
            let proof = transcript.finalize();
        
            });
        });
    }

    } 
    


criterion_group! {
    name = benches;
    config = Criterion::default().with_plots();
    targets = run
  }
  criterion_main!(benches);