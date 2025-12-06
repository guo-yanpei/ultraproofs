use std::{collections::HashMap, marker::PhantomData};

use ark_ec::pairing::Pairing;
use ark_ff::{Field, Zero};
use ark_serialize::CanonicalSerialize;
use util::{
    kzg::{Mkzg, MkzgProof, MkzgProveParams, SumcheckProof},
    merkle_tree::MerkleTreeProver,
    oracle::RandomOracle,
    poly::MlPoly,
    radix2group::Radix2Group,
};

pub struct LightLigero<E: Pairing> {
    _data: PhantomData<E>,
}

pub struct LightLigeroProverState<F: Field> {
    codes: Vec<Vec<F>>,
    omega: F,
    mt_prover: MerkleTreeProver,
}

pub struct LightLigeroCommit([u8; 32]);

pub struct LightLigeroProof<E: Pairing> {
    columns: Vec<Vec<E::ScalarField>>,
    merkle_paths: Vec<u8>,
    kzg_proof: (MkzgProof<E>, SumcheckProof<E::ScalarField>),
}

impl<E: Pairing> LightLigero<E> {
    pub fn commit(
        poly: MlPoly<E::ScalarField>,
        code_rate: usize,
    ) -> (LightLigeroProverState<E::ScalarField>, LightLigeroCommit) {
        let polies = poly.split(16);
        let code_length = polies[0].0.len() << code_rate;
        let fft_group = Radix2Group::new(code_length);
        let codes = polies
            .iter()
            .map(|x| fft_group.fft(&x.0))
            .collect::<Vec<_>>();

        let codes = (0..code_length)
            .map(|i| (0..16).map(|j| codes[j][i]).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        let mt_prover = MerkleTreeProver::new(
            &codes
                .iter()
                .map(|v| {
                    let mut bytes = vec![];
                    v.iter().for_each(|x| {
                        <E::ScalarField as CanonicalSerialize>::serialize_compressed(x, &mut bytes)
                            .unwrap()
                    });
                    bytes
                })
                .collect(),
        );
        let commit = mt_prover.commit();
        (
            LightLigeroProverState {
                codes,
                omega: fft_group.element_at(1),
                mt_prover,
            },
            LightLigeroCommit(commit),
        )
    }

    pub fn prove(
        srs: &MkzgProveParams<E>,
        poly: MlPoly<E::ScalarField>,
        state: LightLigeroProverState<E::ScalarField>,
        point: &Vec<E::ScalarField>,
        oracle: &mut RandomOracle<E::ScalarField>,
    ) -> LightLigeroProof<E> {
        let polies = poly.split(16);
        let point1 = point[0..4].to_vec();
        let point2 = point[4..].to_vec();
        let coeff = MlPoly::new_eq(&point1).0;
        let poly_width = polies[0].0.len();
        let mut compressed_poly = vec![<E::ScalarField as Zero>::zero(); poly_width];
        for i in 0..polies.len() {
            for j in 0..poly_width {
                compressed_poly[j] += polies[i].0[j] * coeff[i];
            }
        }
        let width = state.codes[0].len();
        let compress_poly = MlPoly(compressed_poly);
        let kzg_commit = Mkzg::commit(srs, &compress_poly);
        let mut samples = oracle
            .next_n_ints(50)
            .into_iter()
            .map(|x| x % width)
            .collect::<Vec<_>>();
        samples.sort();
        samples.dedup();
        let points = {
            let log_poly_width = poly_width.ilog2() as usize;
            samples
                .iter()
                .map(|&x| {
                    let mut v = vec![state.omega.pow(&[x as u64])];
                    for i in 1..log_poly_width {
                        v.push(v[i] * v[i]);
                    }
                    v
                })
                .collect::<Vec<_>>()
        };
        let proof = Mkzg::batch_open(srs, poly, points, oracle);
        LightLigeroProof {
            columns: samples
                .iter()
                .map(|&x| state.codes.iter().map(|y| y[x].clone()).collect())
                .collect(),
            merkle_paths: state.mt_prover.open(&samples),
            kzg_proof: proof,
        }
    }
}
