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

// Simple Implementation for padding message lower than 512-bit length
pub fn pad(input: Vec<u32>) -> [u32; 16] {
    let mut res_vec = input.clone();
    let len = 32 * res_vec.len();

    res_vec.push(0x80000000);

    for _ in res_vec.len()..15 {
        res_vec.push(0x00000000);
    }
    res_vec.push(len.try_into().unwrap());

    let res_slice = res_vec.into_boxed_slice();

    let res: Box<[u32; 16]> = match res_slice.try_into() {
        Ok(elem) => elem,
        Err(o) => panic!("Expected a Vec of length 16 but it was {}", o.len()),
    };

    *res
}

#[derive(Clone, Copy, Debug)]
pub struct SHA256Circuit<F: PrimeField> {
    pub digest: Option<[u32; 8]>,
    pub msg: Option<[u32; 16]>,
    _field: PhantomData<F>,
}

impl<F: PrimeField> SHA256Circuit<F> {
    pub fn new(digest: [u32; 8], msg: [u32; 16]) -> Self {
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
        let digest = Vec::<UInt32<F>>::new_witness(cs.clone(), || {
            self.digest.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let msg = Vec::<UInt32<F>>::new_witness(cs.clone(), || {
            self.msg.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // hash
        let mut const_k = Vec::new();

        for k_i in K {
            const_k.push(UInt32::<F>::constant(k_i));
        }

        let mut const_h = Vec::new();

        for h_i in H {
            const_h.push(UInt32::<F>::constant(h_i));
        }

        let mut input = const_h.clone();

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

        fn shr<F: PrimeField>(input: UInt32<F>, by: usize) -> UInt32<F> {
            let input_bits = input.clone().to_bits_le();

            let mut res_bits: Vec<Boolean<F>> = Vec::new();

            for i in &input_bits.clone()[by..] {
                res_bits.push(i.clone());
            }

            for _ in res_bits.len()..32 {
                res_bits.push(Boolean::FALSE);
            }

            let res = UInt32::<F>::from_bits_le(&res_bits);

            res
        }

        fn sig_0<F: PrimeField>(a: UInt32<F>) -> UInt32<F> {
            let tmp_0 = a.clone().rotr(7);
            let tmp_1 = a.clone().rotr(18);
            let tmp_2 = shr(a.clone(), 3);

            tmp_0.xor(&tmp_1.xor(&tmp_2).unwrap()).unwrap()
        }

        fn sig_1<F: PrimeField>(a: UInt32<F>) -> UInt32<F> {
            let tmp_0 = a.clone().rotr(17);
            let tmp_1 = a.clone().rotr(19);
            let tmp_2 = shr(a.clone(), 10);

            tmp_0.xor(&tmp_1.xor(&tmp_2).unwrap()).unwrap()
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

        let mut w = msg.clone();

        for _ in w.clone().len()..64 {
            w.push(UInt32::<F>::constant(0));
        }

        for i in 0..48 {
            let sig_0_out = sig_0::<F>(w[i + 1].clone());
            let sig_1_out = sig_1::<F>(w[i + 14].clone());

            w[i + 16] =
                UInt32::<F>::addmany(&[sig_0_out, sig_1_out, w[i].clone(), w[i + 9].clone()])
                    .unwrap();
        }

        for i in 0..64 {
            let ch_out = ch::<F>(input[4].clone(), input[5].clone(), input[6].clone());
            let maj_out = maj::<F>(input[0].clone(), input[1].clone(), input[2].clone());

            let s_0_out = s_0::<F>(input[0].clone());
            let s_1_out = s_1::<F>(input[4].clone());

            let h_prime = UInt32::<F>::addmany(&[
                input[7].clone(),
                ch_out,
                s_1_out,
                const_k[i].clone(),
                w[i].clone(),
            ])
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
            digest[i].enforce_equal(&UInt32::<F>::addmany(&[
                input[i].clone(),
                const_h[i].clone(),
            ])?)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod sha2 {
    use super::{pad, SHA256Circuit, H, K};
    use ark_bn254::{Bn254 as E, Fr as F};
    use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
    use ark_groth16::{prepare_verifying_key, Groth16};
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
    use ark_std::{
        rand::{Rng, RngCore, SeedableRng},
        test_rng,
    };

    use hex;
    use openssl::sha::sha256;

    fn sha2(msg: [u32; 16]) -> [u32; 8] {
        let mut w: Vec<u32> = msg.to_vec();
        let mut input: [u32; 8] = H.clone();

        fn sig_0(a: u32) -> u32 {
            let tmp_0 = a.clone().rotate_right(7);
            let tmp_1 = a.clone().rotate_right(18);
            let tmp_2 = a.clone() >> 3;

            tmp_0 ^ tmp_1 ^ tmp_2
        }

        fn sig_1(a: u32) -> u32 {
            let tmp_0 = a.clone().rotate_right(17);
            let tmp_1 = a.clone().rotate_right(19);
            let tmp_2 = a.clone() >> 10;

            tmp_0 ^ tmp_1 ^ tmp_2
        }

        fn s_0(a: u32) -> u32 {
            let tmp_0 = a.clone().rotate_right(2);
            let tmp_1 = a.clone().rotate_right(13);
            let tmp_2 = a.clone().rotate_right(22);

            tmp_0 ^ tmp_1 ^ tmp_2
        }

        fn s_1(e: u32) -> u32 {
            let tmp_0 = e.clone().rotate_right(6);
            let tmp_1 = e.clone().rotate_right(11);
            let tmp_2 = e.clone().rotate_right(25);

            tmp_0 ^ tmp_1 ^ tmp_2
        }

        fn maj(a: u32, b: u32, c: u32) -> u32 {
            let tmp_0 = a & b;
            let tmp_1 = b & c;
            let tmp_2 = a & c;

            tmp_0 ^ tmp_1 ^ tmp_2
        }

        fn ch(e: u32, f: u32, g: u32) -> u32 {
            let tmp_0 = e & f;
            let tmp_1 = !e & g;

            tmp_0 ^ tmp_1
        }

        for i in 0..48 {
            let sig_0 = sig_0(w[i + 1].clone());
            let sig_1 = sig_1(w[i + 14].clone());
            w.push(
                w[i].clone()
                    .wrapping_add(w[i + 9].clone())
                    .wrapping_add(sig_0)
                    .wrapping_add(sig_1),
            );
        }

        let mut test = input.clone().to_vec();

        for i in 0..64 {
            let ch_out = ch(input[4].clone(), input[5].clone(), input[6].clone());
            let maj_out = maj(input[0].clone(), input[1].clone(), input[2].clone());

            let s_0_out = s_0(input[0].clone());
            let s_1_out = s_1(input[4].clone());

            let h_prime = input[7]
                .clone()
                .wrapping_add(ch_out)
                .wrapping_add(s_1_out)
                .wrapping_add(K[i].clone())
                .wrapping_add(w[i]);

            input[7] = input[6].clone();
            input[6] = input[5].clone();
            input[5] = input[4].clone();
            input[4] = input[3].clone().wrapping_add(h_prime.clone());
            input[3] = input[2].clone();
            input[2] = input[1].clone();
            input[1] = input[0].clone();
            input[0] = h_prime.wrapping_add(maj_out).wrapping_add(s_0_out);
        }

        for ((i, input_i), h_i) in input.clone().iter().enumerate().zip(H.clone().into_iter()) {
            input[i] = input_i + h_i;
        }

        input
    }

    #[test]
    fn test_sha256() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());

        let digest: [u32; 8] = [
            0x9c56cc51, 0xb374c3ba, 0x189210d5, 0xb6d4bf57, 0x790d351c, 0x96c47c02, 0x190ecf1e,
            0x430635ab,
        ];

        let msg: [u32; 16] = [
            0x61626364, 0x65666768, 0x80000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
            0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
            0x00000000, 0x00000040,
        ]; // "abcdefgh"

        println!("{:x?}", sha2(msg.clone()));

        let circuit = SHA256Circuit::<F>::new(digest, msg);

        let cs = ark_relations::r1cs::ConstraintSystem::new_ref();

        circuit.clone().generate_constraints(cs.clone()).unwrap();

        println!("# of constraints: {:?}", cs.num_constraints());

        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_sha256_with_groth16() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());

        let digest: [u32; 8] = [
            0x9c56cc51, 0xb374c3ba, 0x189210d5, 0xb6d4bf57, 0x790d351c, 0x96c47c02, 0x190ecf1e,
            0x430635ab,
        ];

        let msg: [u32; 16] = [
            0x61626364, 0x65666768, 0x80000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
            0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
            0x00000000, 0x00000040,
        ];

        let circuit = SHA256Circuit::<F>::new(digest, msg);

        let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();

        let pvk = prepare_verifying_key::<E>(&vk);

        let proof = Groth16::<E>::prove(&pk, circuit, &mut rng).unwrap();

        assert!(Groth16::<E>::verify_with_processed_vk(&pvk, &[], &proof).unwrap());
    }

    #[test]
    fn test_pad() {
        let msg = vec![0x61626364, 0x65666768];

        let padded_msg = pad(msg.clone());

        let test_res: [u32; 16] = [
            0x61626364, 0x65666768, 0x80000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
            0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
            0x00000000, 0x00000040,
        ];

        assert_eq!(padded_msg, test_res);
    }
}
