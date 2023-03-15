#[warn(unused_must_use)]
#[warn(unused_imports)]
use ark_std::{end_timer, start_timer};
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
mod lib;


static IMLEN:usize = 512;
static KERLEN:usize = 512;


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
            for i in 1..=IMLEN{
                config.seldot.enable(&mut region, i)?;
                let i_cell = region.assign_advice(||"image".to_owned()+&i.to_string(),
                 config.image, 
                 i, 
                 || Value::known(self.image[i-1]))?;
                imgcells.push(i_cell);   
            };

            let mut kercells = vec![];
            for i in 1..=KERLEN{
                let k_cell = region.assign_advice(||"kernel".to_owned()+&i.to_string(),
                 config.kernel, 
                 i, 
                 || Value::known(self.kernel[i-1]))?;
                kercells.push(k_cell);   
            };

            let mut accumcells = vec![];
            let mut accumval = Value::known(F::zero());
            for i in 1..=IMLEN{
                let acc_cell = region.assign_advice(||"accum".to_owned()+&i.to_string(),
                config.accumulator, 
                i-1, 
                || accumval)?;
                accumcells.push(acc_cell);
                accumval = accumval + (imgcells[i-1].value().copied()*kercells[i-1].value().copied());
            };
            let acc_cell = region.assign_advice(||"accum".to_owned()+&IMLEN.to_string(),
                config.accumulator, 
                IMLEN, 
                || accumval)?;
                accumcells.push(acc_cell);

            Ok(())
        })
    
    }

}

fn main() {
    let k = 10;
    let mut rng = OsRng;
    use lib::RandomInputGenerator;
    let gen = RandomInputGenerator::new(IMLEN, KERLEN);
    let img = gen.one_dimage;
    let ker = gen.one_dkernel;
    let circuit = Accdotcircuit {
        image: img,
        kernel: ker
    };

    let params = ParamsKZG::<Bn256>::setup(k, &mut rng);

    let vk_time_start = Instant::now();
    let vk = keygen_vk(&params, &circuit).unwrap();
    let vk_time = vk_time_start.elapsed();

    let pk_time_start = Instant::now();
    let pk = keygen_pk(&params, vk, &circuit).unwrap();
    let pk_time = pk_time_start.elapsed();;

    let proof_time_start = Instant::now();
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        _,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
        _,
    >(&params, &pk, &[circuit], &[&[]], rng, &mut transcript);
    let proof = transcript.finalize();
    let proof_time = proof_time_start.elapsed();


    let verify_time_start = Instant::now();
    let verifier_params = params.verifier_params();
    let strategy = SingleStrategy::new(&params);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    assert!(verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<'_, Bn256>,
    >(verifier_params, pk.get_vk(), strategy, &[&[]], &mut transcript)
    .is_ok());
    let verify_time = verify_time_start.elapsed();

    println!("Time to generate vk {:?}", vk_time);
    println!("Time to generate pk {:?}", pk_time);
    println!("Prover Time {:?}", proof_time);
    println!("Verifier Time {:?}", verify_time);

}
