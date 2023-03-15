#[warn(unused_must_use)]
use accum_dot::RandomInputGenerator;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Circuit, ConstraintSystem, Error, Column, Advice, Selector}, dev::MockProver, poly::kzg::commitment::ParamsKZG,
};
use halo2curves::{FieldExt, bn256::{Bn256, G1Affine}};
use rand::rngs::OsRng;
use std::{marker::PhantomData, time::Instant};
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


#[derive(Debug,Clone)]
struct AccumDot<F: FieldExt>{
    image: Column<Advice>,
    kernel: Column<Advice>,
    accumulator: Column<Advice>,
    seldot: Selector,
    _marker: PhantomData<F>
}

#[derive(Debug,Clone)]
struct AccumDotChip<F: FieldExt>{
    config: AccumDot<F>,
    _marker: PhantomData<F>
}

impl<F: FieldExt> AccumDotChip<F>{
    pub fn configure(meta: &mut ConstraintSystem<F>)->AccumDot<F>{
        let image = meta.advice_column();
        let kernel = meta.advice_column();
        let accum = meta.advice_column();
        let seldot = meta.selector();

        meta.create_gate("accumdot", |meta|{
            let s = meta.query_selector(seldot);
            let a_prev = meta.query_advice(accum, Rotation::prev());
            let a = meta.query_advice(accum, Rotation::cur());
            let i = meta.query_advice(image, Rotation::cur());
            let k = meta.query_advice(kernel, Rotation::cur());

            vec![s*((a_prev+(i*k))-a)]

        });

        AccumDot { image: image,
             kernel: kernel,
              accumulator: accum,
              seldot: seldot,
            _marker: PhantomData }
    }
}

#[derive(Debug,Clone)]
struct Accdotcircuit<F: FieldExt>{
    image: Vec<F>,
    kernel: Vec<F>,
}

impl<F:FieldExt> Circuit<F> for Accdotcircuit<F>
{   
    type Config = AccumDot<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        return self.clone();
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        AccumDotChip::configure(meta)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_region(||"accumdot", |mut region|{
            
            let mut imgcells = vec![];
            for i in 1..=self.image.len(){
                config.seldot.enable(&mut region, i)?;
                let i_cell = region.assign_advice(||"image".to_owned()+&i.to_string(),
                 config.image, 
                 i, 
                 || Value::known(self.image[i-1]))?;
                imgcells.push(i_cell);   
            };

            let mut kercells = vec![];
            for i in 1..=self.kernel.len(){
                let k_cell = region.assign_advice(||"kernel".to_owned()+&i.to_string(),
                 config.kernel, 
                 i, 
                 || Value::known(self.kernel[i-1]))?;
                kercells.push(k_cell);   
            };

            let mut accumcells = vec![];
            let mut accumval = Value::known(F::zero());
            for i in 1..=self.image.len(){
                let acc_cell = region.assign_advice(||"accum".to_owned()+&i.to_string(),
                config.accumulator, 
                i-1, 
                || accumval)?;
                accumcells.push(acc_cell);
                accumval = accumval + (imgcells[i-1].value().copied()*kercells[i-1].value().copied());
            };
            let acc_cell = region.assign_advice(||"accum".to_owned()+&self.image.len().to_string(),
                config.accumulator, 
                self.image.len(), 
                || accumval)?;
                accumcells.push(acc_cell);

            Ok(())
        })
    
    }

}

fn run(c: &mut Criterion){
    let k = 10;
    let mut rng = OsRng;
    let mut group = c.benchmark_group("dot");
    let params = ParamsKZG::<Bn256>::setup(k, &mut rng);
    for &len in [4, 8, 16, 32, 64, 128, 256, 512].iter() {

        let gen = RandomInputGenerator::new(len, len);
        let img = gen.one_dimage;
        let ker = gen.one_dkernel;
        let circuit = Accdotcircuit {
        image: img,
        kernel: ker
        };

        group.sample_size(20);
        group.throughput(Throughput::Elements(len as u64));
        group.bench_with_input(BenchmarkId::new("KeyGen", len), &len, |b, &_| {
            b.iter(|| {
                let vk = keygen_vk(&params, &circuit).unwrap();
                let pk = keygen_pk(&params, vk, &circuit).unwrap();
            });
        });

        let vk = keygen_vk(&params, &circuit).unwrap();
        let pk = keygen_pk(&params, vk, &circuit).unwrap();

        group.sample_size(20);
        group.throughput(Throughput::Elements(len as u64));
        group.bench_with_input(BenchmarkId::new("Prove", len), &len, |b, &_| {
            b.iter(|| {
                let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
                create_proof::<
                KZGCommitmentScheme<Bn256>,
                ProverSHPLONK<'_, Bn256>,
                Challenge255<G1Affine>,
                _,
                Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
                _,
            >(&params, &pk, &[circuit.clone()], &[&[]], rng, &mut transcript);
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


