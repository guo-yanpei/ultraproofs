use ark_ff::{FftField, Field, One};
use ark_serialize::CanonicalSerialize;

#[derive(Debug, Clone)]
pub struct MlPoly<F: Field>(pub Vec<F>);

impl<F: Field> MlPoly<F> {
    pub fn eval(self, point: &[F]) -> F {
        let mut scratch = self.0;
        let mut cur_len = scratch.len() >> 1;
        assert_eq!(1 << point.len(), scratch.len());
        for r in point.iter() {
            for i in 0..cur_len {
                scratch[i] = scratch[i * 2] + (scratch[i * 2 + 1] - scratch[i * 2]) * (*r);
            }
            cur_len >>= 1;
        }
        scratch[0]
    }

    pub fn split(self, n: usize) -> Vec<MlPoly<F>> {
        assert_eq!(n & (n - 1), 0);
        let mut polies = (0..n).map(|_| vec![]).collect::<Vec<_>>();
        let len = self.0.len();
        for i in (0..len).step_by(n) {
            for j in 0..n {
                polies[j].push(self.0[i + j]);
            }
        }
        polies.into_iter().map(|x| MlPoly(x)).collect()
    }

    pub fn fold(&mut self, point: &[F]) {
        let mut cur_len = self.0.len();
        for r in point.iter() {
            cur_len >>= 1;
            for i in 0..cur_len {
                self.0[i] = self.0[i * 2] + (self.0[i * 2 + 1] - self.0[i * 2]) * (*r);
            }
        }
        self.0.truncate(cur_len);
    }
}

#[derive(Debug, Clone)]
pub struct UniVarPoly<F: Field>(Vec<F>);

impl<F: Field> UniVarPoly<F> {
    pub fn new(coeff: Vec<F>) -> Self {
        UniVarPoly(coeff)
    }

    pub fn serialize(&self) -> Vec<u8> {
        let mut bytes = vec![];
        self.0
            .iter()
            .for_each(|x| <F as CanonicalSerialize>::serialize_compressed(&x, &mut bytes).unwrap());
        bytes
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn eval(&self, point: &F) -> F {
        let mut res = self.0.last().unwrap().clone();
        for i in self.0.iter().rev().skip(1) {
            res *= point;
            res += i;
        }
        res
    }
}

#[derive(Debug, Clone)]
pub struct UniPolyEvals<F: Field> {
    evals: Vec<F>,
    offset_inv: F,
}

impl<F: FftField> UniPolyEvals<F> {
    pub fn new(evals: Vec<F>, offset_inv: F) -> UniPolyEvals<F> {
        UniPolyEvals { evals, offset_inv }
    }

    pub fn len(&self) -> usize {
        self.evals.len()
    }

    pub fn serialize(&self) -> Vec<u8> {
        let mut bytes = vec![];
        self.evals
            .iter()
            .for_each(|x| <F as CanonicalSerialize>::serialize_compressed(&x, &mut bytes).unwrap());
        bytes
    }

    pub fn n_th_eval(&self, n: usize) -> F {
        self.evals[n & (self.evals.len() - 1)]
    }

    pub fn eval(self, mut point: F, mut root_inv: F, inv_2: F) -> F {
        let UniPolyEvals {
            mut evals,
            mut offset_inv,
        } = self;
        let mut len = evals.len();
        let mut inv = <F as One>::one();
        for _ in 0..evals.len().ilog2() {
            len >>= 1;
            let mut w = offset_inv;
            for j in 0..len {
                let t = (evals[j] - evals[j + len]) * point * w;
                evals[j] = evals[j] + evals[j + len] + t;
                w *= root_inv;
            }
            offset_inv *= offset_inv;
            inv *= inv_2;
            point *= point;
            root_inv *= root_inv;
        }
        evals[0] * inv
    }
}
