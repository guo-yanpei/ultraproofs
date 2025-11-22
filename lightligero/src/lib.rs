use std::marker::PhantomData;

use ark_ec::pairing::Pairing;
use ark_ff::Field;
use ark_serialize::CanonicalSerialize;
use util::{merkle_tree::MerkleTreeProver, poly::MlPoly, radix2group::Radix2Group};

pub struct LightLigero<E: Pairing> {
    _data: PhantomData<E>,
}

pub struct LightLigeroProverState<F: Field> {
    codes: Vec<Vec<F>>,
    mt_prover: MerkleTreeProver,
}

pub struct LightLigeroCommit([u8; 32]);

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
            LightLigeroProverState { codes, mt_prover },
            LightLigeroCommit(commit),
        )
    }


    pub fn prove(poly: MlPoly<E::ScalarField>) {

    }
}
