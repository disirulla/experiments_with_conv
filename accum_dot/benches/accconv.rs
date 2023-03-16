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


static mut IMLEN:usize = 512;
static mut KERLEN:usize = 4;

#[derive(Debug,Clone)]
struct AccumConv<F: FieldExt>{
    image: Column<Advice>,
    kernel: Vec<Column<Advice>>,
    accumconv: Vec<Column<Advice>>,
    seldot: Vec<Selector>,
    _marker: PhantomData<F>
}

#[derive(Debug,Clone)]
struct AccumConvChip<F: FieldExt>{
    config: AccumConv<F>,
    _marker: PhantomData<F>
}

impl<F: FieldExt> AccumConvChip<F>{
    pub fn configure(meta: &mut ConstraintSystem<F>)->AccumConv<F>{
        let image = meta.advice_column();
        let mut kernel = vec![];
        let mut accumconv = vec![];
        let mut seldot = vec![];
        let conlen;
        unsafe{
             conlen = IMLEN - KERLEN + 1;
        }

        for i in 0..conlen{
            kernel.push(meta.advice_column());
            accumconv.push(meta.advice_column());
            seldot.push(meta.selector());

        meta.create_gate("accumconv", |meta|{
            let s = meta.query_selector(seldot[i]);
            let a_prev = meta.query_advice(accumconv[i], Rotation::prev());
            let a = meta.query_advice(accumconv[i], Rotation::cur());
            let im = meta.query_advice(image, Rotation::cur());
            let ke = meta.query_advice(kernel[i], Rotation::cur());           
            
            vec![s*((a_prev+(im*ke))-a)]

        });

        }

        AccumConv { image: image,
             kernel: kernel,
              accumconv,
              seldot: seldot,
            _marker: PhantomData }
    }
}

#[derive(Debug,Clone)]
struct AccConvcircuit<F: FieldExt>{
    image: Vec<F>,
    kernel: Vec<F>,
}

impl<F:FieldExt> Circuit<F> for AccConvcircuit<F>
{   
    type Config = AccumConv<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        return self.clone();
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        AccumConvChip::configure(meta)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_region(||"AccumConv", |mut region|{
            
            let mut imgcells = vec![];
            for i in 1..=self.image.len(){
                let i_cell = region.assign_advice(||"image".to_owned()+&i.to_string(),
                 config.image, 
                 i, 
                 || Value::known(self.image[i-1]))?;
                imgcells.push(i_cell);   
            };

            let conlen = self.image.len() - self.kernel.len() + 1;
            let mut offset_dotp = 0;
            for k in 0..conlen{
                let mut accumval = Value::known(F::zero());
                let acc_cell = region.assign_advice(||"accum".to_owned()+&k.to_string()+&0.to_string(),
                     config.accumconv[k], 
                     0+offset_dotp, 
                     || accumval)?;

                for i in 1..=self.kernel.len(){
                    config.seldot[k].enable(&mut region, i+offset_dotp)?;
                    let k_cell = region.assign_advice(||"kernel".to_owned()+&k.to_string()+&i.to_string(),
                     config.kernel[k], 
                     i+offset_dotp, 
                     || Value::known(self.kernel[i-1]))?;

                     accumval = accumval + (imgcells[i+offset_dotp-1].value().copied()*k_cell.value().copied());

                     let acc_cell = region.assign_advice(||"accum".to_owned()+&k.to_string()+&i.to_string(),
                     config.accumconv[k], 
                     i+offset_dotp, 
                     || accumval)?;

                };
                offset_dotp+=1 //stride
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
            gen = RandomInputGenerator::new(IMLEN, KERLEN);
        }
        let img = gen.one_dimage;
        let ker = gen.one_dkernel;
        let accumconvcircuit =  AccConvcircuit{
        image: img,
        kernel: ker
        };

        group.sample_size(10);
        group.throughput(Throughput::Elements(len as u64));
        group.bench_with_input(BenchmarkId::new("KeyGenForAccumConv", len), &len, |b, &_| {
            b.iter(|| {
                let vk = keygen_vk(&params, &accumconvcircuit).unwrap();
                let pk = keygen_pk(&params, vk, &accumconvcircuit).unwrap();
            });
        });

        let vk = keygen_vk(&params, &accumconvcircuit).unwrap();
        let pk = keygen_pk(&params, vk, &accumconvcircuit).unwrap();

        group.sample_size(20);
        group.throughput(Throughput::Elements(len as u64));
        group.bench_with_input(BenchmarkId::new("ProofForAccumConv", len), &len, |b, &_| {
            b.iter(|| {
                let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
                create_proof::<
                KZGCommitmentScheme<Bn256>,
                ProverSHPLONK<'_, Bn256>,
                Challenge255<G1Affine>,
                _,
                Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
                _,
            >(&params, &pk, &[accumconvcircuit.clone()], &[&[]], rng, &mut transcript);
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