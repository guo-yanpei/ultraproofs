use ark_ec::{CurveGroup, VariableBaseMSM, pairing::Pairing};
use ark_ff::{Field, One, UniformRand};
use rand::Rng;
use std::marker::PhantomData;

use crate::poly::MlPoly;

const LOG_CHUNK_NUM: usize = 4;
pub struct Mkzg<E: Pairing>(PhantomData<E>);
#[derive(Debug, Clone)]
pub struct MkzgCommit<E: Pairing>([E::G1; 1 << LOG_CHUNK_NUM]);
#[derive(Debug, Clone)]
pub struct MkzgProof<E: Pairing>(Vec<E::G1>);
#[derive(Debug, Clone)]
pub struct MkzgVerParams<E: Pairing> {
    pub g: E::G1,
    pub h: E::G2,
    params: Vec<E::G2>,
}

impl<E: Pairing> MkzgVerParams<E> {
    pub fn trim(&self, log_len: usize) -> Self {
        let mut params = self.params.clone();
        params.truncate(log_len);
        MkzgVerParams {
            g: self.g,
            h: self.h,
            params,
        }
    }
}

#[derive(Debug, Clone)]
pub struct MkzgProveParams<E: Pairing>(Vec<E::G1Affine>);
impl<E: Pairing> MkzgProveParams<E> {
    pub fn trim(&self, log_len: usize) -> Self {
        let mut params = self.0.clone();
        params.truncate(1 << log_len);
        MkzgProveParams(params)
    }
}

impl<E: Pairing> Mkzg<E> {
    pub fn gen_srs(len: usize, rng: &mut impl Rng) -> (MkzgProveParams<E>, MkzgVerParams<E>) {
        let g = <E::G1 as UniformRand>::rand(rng);
        let h = <E::G2 as UniformRand>::rand(rng);
        let tau = (0..len)
            .map(|_| E::ScalarField::rand(rng))
            .collect::<Vec<_>>();
        let vp = MkzgVerParams {
            g,
            h,
            params: (0..len).map(|x| h * tau[x]).collect(),
        };
        let mut power_of_g = vec![E::ScalarField::one()];
        for i in 0..len {
            let cur_len = power_of_g.len();
            for j in 0..cur_len {
                power_of_g.push(power_of_g[j] * tau[i]);
            }
        }
        (
            MkzgProveParams(<E::G1 as CurveGroup>::normalize_batch(
                &power_of_g.iter().map(|x| g * x).collect::<Vec<_>>(),
            )),
            vp,
        )
    }

    pub fn commit(srs: &MkzgProveParams<E>, poly: MlPoly<E::ScalarField>) -> MkzgCommit<E> {
        if srs.0.len() != poly.0.len() >> LOG_CHUNK_NUM {
            panic!("{} {}", file!(), line!());
        }
        let polies = poly.split(1 << LOG_CHUNK_NUM);
        let mut commits = vec![];
        for p in polies {
            commits.push(E::G1::msm_unchecked(&srs.0, &p.0));
        }
        MkzgCommit(commits.try_into().unwrap())
    }

    pub fn open(
        srs: &MkzgProveParams<E>,
        mut poly: MlPoly<E::ScalarField>,
        mut point: Vec<E::ScalarField>,
    ) -> (MkzgProof<E>, E::ScalarField) {
        assert_eq!(srs.0.len() << LOG_CHUNK_NUM, 1 << point.len());
        poly.fold(&point[0..LOG_CHUNK_NUM]);
        point = point[LOG_CHUNK_NUM..].to_vec();

        let one = E::ScalarField::one();
        let mul = point
            .iter()
            .fold(E::ScalarField::from(1), |acc, x| acc * (one - x));
        let point = point
            .iter()
            .map(|&x| x * Field::inverse(&(one - x)).unwrap())
            .collect::<Vec<_>>();
        let mut proofs = vec![];
        let mut cur_len = poly.0.len() >> 1;
        let mut poly = poly.0;
        assert_eq!(poly.len(), srs.0.len());
        let mut bases = srs.0.clone();
        for p in point.iter() {
            let mut scalars = vec![];
            for i in 0..cur_len {
                bases[i] = bases[i * 2];
                scalars.push(poly[i * 2 + 1]);
            }
            bases.truncate(cur_len);
            proofs.push(E::G1::msm_unchecked(&bases, &scalars));
            for i in 0..cur_len {
                poly[i] = poly[i * 2] + poly[i * 2 + 1] * p;
            }
            poly.truncate(cur_len);
            cur_len >>= 1;
        }
        (MkzgProof(proofs), poly[0] * mul)
    }

    pub fn verify(
        vp: &MkzgVerParams<E>,
        mut point: Vec<E::ScalarField>,
        comm: &MkzgCommit<E>,
        value: E::ScalarField,
        proof: MkzgProof<E>,
    ) -> bool {
        let point2 = point.split_off(LOG_CHUNK_NUM);
        let one = E::ScalarField::one();
        let mul = point2
            .iter()
            .fold(E::ScalarField::from(1), |acc, x| acc * (one - x));
        let point2 = point2
            .iter()
            .map(|&x| x * Field::inverse(&(one - x)).unwrap())
            .collect::<Vec<_>>();
        let value = value * mul.inverse().unwrap();
        let MkzgVerParams { g, h, mut params } = vp.clone();
        for i in 0..point2.len() {
            params[i] -= h * point2[i];
        }
        let mut proof = proof.0;
        proof.push(g);
        params.push(h * value);

        let mut commits = comm.0;
        let mut cur_len = commits.len() >> 1;
        for r in point.iter() {
            for i in 0..cur_len {
                commits[i] = commits[i * 2] + (commits[i * 2 + 1] - commits[i * 2]) * (*r);
            }
            cur_len >>= 1;
        }

        E::multi_pairing(proof, params) == E::pairing(commits[0], h)
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Bn254, Fr};
    use ark_ff::UniformRand;
    use rand::thread_rng;

    use crate::{kzg::{LOG_CHUNK_NUM, Mkzg}, poly::MlPoly};

    #[test]
    fn it_works() {
        let log_len = 8;
        let mut rng = thread_rng();
        let poly = MlPoly(
            (0..1 << log_len)
                .map(|_| <Fr as UniformRand>::rand(&mut rng))
                .collect(),
        );
        let (pp, vp) = Mkzg::<Bn254>::gen_srs(10, &mut rng);
        let pp = pp.trim(log_len - LOG_CHUNK_NUM);
        let vp = vp.trim(log_len - LOG_CHUNK_NUM);
        let commit = Mkzg::commit(&pp, poly.clone());
        let point = (0..log_len)
            .map(|_| <Fr as UniformRand>::rand(&mut rng))
            .collect::<Vec<_>>();
        let (proof, value) = Mkzg::open(&pp, poly.clone(), point.clone());
        assert_eq!(value, poly.eval(&point));
        assert!(Mkzg::verify(&vp, point, &commit, value, proof));
    }
}
