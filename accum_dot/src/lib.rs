use rand::{self, Rng};
use halo2curves::bn256::Fr;


pub struct RandomInputGenerator{
    pub one_dimage: Vec<Fr>,
    pub one_dkernel: Vec<Fr>,
}

impl RandomInputGenerator{
    pub fn new( imlen: usize,kerlen: usize)->Self{
        
        let mut rng = rand::thread_rng();
        
        let mut imagevec = vec![];
        for _i in 0..imlen{
            let x = rng.gen_range(0..=255);
            let buf = Fr::from(x);
            imagevec.push(buf);
        }

        let mut kernels = vec![];
        for _j in 0..kerlen{
            let random_value:f32 = rng.gen_range(-5.0..=5.0);
            let x = random_value.round() as i32;
            let mut buf = Fr::from(x as u64);
            if x < 0
            { buf = -Fr::from(x as u64);} 
            kernels.push(buf);    
        }

        Self { 
        one_dimage: imagevec, 
        one_dkernel: kernels 
        }

    }
}