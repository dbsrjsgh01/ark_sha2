use crate::ConstraintF;

use ark_ec::CurveGroup;
use ark_ff::{
    biginteger::{BigInteger as _, BigInteger64 as B},
    One, PrimeField,
};
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::{fields::fp::FpVar, prelude::*, uint32::UInt32};
use ark_relations::{
    ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, SynthesisMode},
};
use std::{
    marker::PhantomData,
    ops::{AddAssign, Mul, MulAssign},
};

pub const H: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

pub const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

pub struct SHA256Circuit<F: PrimeField> {
    pub digest: Option<[u32; 8]>,
    pub msg: Option<[u32; 8]>,
    _field: PhantomData<F>,
}

impl<F: PrimeField> SHA256Circuit<F> {
    pub fn new(digest: [u32; 8], msg: [u32; 8]) -> Self {
        Self {
            digest: Some(digest),
            msg: Some(msg),
            _field: PhantomData,
        }
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for SHA256Circuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        // input
        let digest = Vec::<UInt32<F>>::new_input(cs.clone(), || {
            self.digest.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let msg = Vec::<UInt32<F>>::new_input(cs.clone(), || {
            self.msg.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let mut input = msg.clone();

        // hash
        let mut const_k = Vec::new();

        for k_i in K {
            const_k.push(UInt32::<F>::constant(k_i));
        }

        let mut const_h = Vec::new();

        for h_i in H {
            const_h.push(UInt32::<F>::constant(h_i));
        }

        // Ch(E, F, G) = (E and F) ^ (not E and G)
        // Maj(A, B, C) = (A and B) ^ (B and C) ^ (C and A)
        // s_0(A) = (A >> 2) ^ (A >> 13) ^ (A >> 22)
        // s_1(E) = (E >> 6) ^ (E >> 11) ^ (E >> 25)
        // H' = H + Ch + s_1 + const_K
        // E_new = H' + D
        // A_new = H' + Maj + s_0

        fn and<F: PrimeField>(left: UInt32<F>, right: UInt32<F>) -> UInt32<F> {
            let left_bits = left.clone().to_bits_le();
            let right_bits = right.clone().to_bits_le();

            let mut res_bits: Vec<Boolean<F>> = Vec::new();

            for (l_i, r_i) in left_bits.clone().iter().zip(right_bits.clone().into_iter()) {
                res_bits.push(r_i.and(l_i).unwrap());
            }

            for _ in res_bits.len()..32 {
                res_bits.push(Boolean::FALSE);
            }

            let res = UInt32::<F>::from_bits_le(&res_bits);

            res
        }

        fn not<F: PrimeField>(input: UInt32<F>) -> UInt32<F> {
            let input_bits = input.clone().to_bits_le();

            let mut res_bits: Vec<Boolean<F>> = Vec::new();

            for i in input_bits.clone().iter() {
                res_bits.push(i.not());
            }

            for _ in res_bits.len()..32 {
                res_bits.push(Boolean::TRUE);
            }

            let res = UInt32::<F>::from_bits_le(&res_bits);

            res
        }

        fn s_0<F: PrimeField>(a: UInt32<F>) -> UInt32<F> {
            let tmp_0 = a.clone().rotr(2);
            let tmp_1 = a.clone().rotr(13);
            let tmp_2 = a.clone().rotr(22);

            tmp_0.xor(&tmp_1.xor(&tmp_2).unwrap()).unwrap()
        }

        fn s_1<F: PrimeField>(e: UInt32<F>) -> UInt32<F> {
            let tmp_0 = e.clone().rotr(6);
            let tmp_1 = e.clone().rotr(11);
            let tmp_2 = e.clone().rotr(25);

            tmp_0.xor(&tmp_1.xor(&tmp_2).unwrap()).unwrap()
        }

        fn maj<F: PrimeField>(a: UInt32<F>, b: UInt32<F>, c: UInt32<F>) -> UInt32<F> {
            let tmp_0 = and(a.clone(), b.clone());
            let tmp_1 = and(c.clone(), b.clone());
            let tmp_2 = and(a.clone(), c.clone());

            tmp_0.xor(&tmp_1.xor(&tmp_2).unwrap()).unwrap()
        }

        fn ch<F: PrimeField>(e: UInt32<F>, f: UInt32<F>, g: UInt32<F>) -> UInt32<F> {
            let tmp_0 = and(e.clone(), f.clone());
            let tmp_1 = and(g.clone(), not(e.clone()));

            tmp_0.xor(&tmp_1).unwrap()
        }

        for i in 0..64 {
            let ch_out = ch::<F>(input[4].clone(), input[5].clone(), input[6].clone());
            let maj_out = maj::<F>(input[0].clone(), input[1].clone(), input[2].clone());

            let s_0_out = s_0::<F>(input[0].clone());
            let s_1_out = s_1::<F>(input[4].clone());

            let h_prime =
                UInt32::<F>::addmany(&[input[7].clone(), ch_out, s_1_out, const_k[i].clone()])
                    .unwrap();

            input[7] = input[6].clone();
            input[6] = input[5].clone();
            input[5] = input[4].clone();
            input[4] = UInt32::<F>::addmany(&[h_prime.clone(), input[3].clone()]).unwrap();
            input[3] = input[2].clone();
            input[2] = input[1].clone();
            input[1] = input[0].clone();
            input[0] = UInt32::<F>::addmany(&[h_prime, maj_out, s_0_out]).unwrap();
        }

        for i in 0..8 {
            input[i].enforce_equal(&digest[i])?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod sha2 {
    use super::SHA256Circuit;
    use ark_bn254::Fr;
    use ark_crypto_primitives::snark::SNARK;
    use ark_std::{
        rand::{Rng, RngCore, SeedableRng},
        test_rng,
    };

    #[test]
    fn test_sha256() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
    }
}
