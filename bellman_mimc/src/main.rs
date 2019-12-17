use rand::thread_rng;
use std::time::{Instant};
use bellman_ce::pairing::Engine;
use bellman_ce::pairing::bn256::{Bn256}; // use BN256 curve
use bellman_ce::pairing::ff::{Field, ScalarEngine};
use bellman_ce::{Circuit, ConstraintSystem, SynthesisError};
use bellman_ce::groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof, Proof,
};

use rand::{self, Rand};

const MIMC_ROUNDS: usize = 91;
const MIMC_STEP: usize = 200;

/// This is an implementation of the MiMC block cipher,
/// for the BN256 curve. Uses x^7 powering sequence
/// See http://eprint.iacr.org/2016/492 for more
/// information about this construction.
/// Code was originally written for the LongSight hash function,
/// and has been adapted to evaluate the MiMC block cipher 
///
/// ```
/// function MiMC(x ⦂ Fp, k ⦂ Fp) {
///     for i from 0 up to 92 {
///         x := (x + k + Ci)^7
///     }
///     return x
/// }
/// ```
fn mimc<E: Engine>(mut x: E::Fr, k: E::Fr, constants: &[E::Fr]) -> E::Fr {
    assert_eq!(constants.len(), MIMC_ROUNDS);

    for i in 0..MIMC_ROUNDS {
        // tmp1 = x + k + c[i]
        let mut tmp1 = x;
        tmp1.add_assign(&constants[i]);
        tmp1.add_assign(&k);
        // tmp2 = (x + k + c[i])^2
        let mut tmp2 = tmp1;
        tmp2.square();
        // tmp3 = (x + k + c[i])^4
        let mut tmp3 = tmp2;
        tmp3.square();
        // tmp4 = (x + k + c[i])^6
        let mut tmp4 = tmp3;
        tmp4.mul_assign(&tmp2);
        // tmp5 = (x + k + c[i])^7
        let mut tmp5 = tmp4;
        tmp5.mul_assign(&tmp1);
        x = tmp5;
    }

    x
}

struct MiMCDemo<'a, E: Engine> {
    repetitions: usize,
    x: Option<E::Fr>,
    k: Option<E::Fr>,
    constants: &'a [E::Fr],
}

impl<'a, E: Engine> Circuit<E> for MiMCDemo<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        assert_eq!(self.constants.len(), MIMC_ROUNDS);

        for _ in 0..(self.repetitions) {

        let mut x_value = self.x;
        let mut x = cs.alloc(
            || "preimage x",
            || x_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        // Allocate the key.
        let k_value = self.k;
        let k = cs.alloc(
            || "preimage key",
            || k_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        for i in 0..MIMC_ROUNDS {
            // x := (x + k + Ci)^7
            let cs = &mut cs.namespace(|| format!("round {}", i));

            let tmp_value = x_value.map(|mut e| {
                e.add_assign(&k_value.unwrap());
                e.add_assign(&self.constants[i]);
                e.square();
                e
            });
            let tmp = cs.alloc(
                || "tmp",
                || tmp_value.ok_or(SynthesisError::AssignmentMissing),
            )?;

            cs.enforce(
                || "tmp = (x + k + Ci)^2",
                |lc| lc + x + k + (self.constants[i], CS::one()),
                |lc| lc + x + k + (self.constants[i], CS::one()),
                |lc| lc + tmp,
            );

            // tmp_2 = (x + k + ci)^4 
            // tmp_2 = tmp^2
            let tmp_2_value = tmp_value.map(|mut e| {
                e.mul_assign(&tmp_value.unwrap());
                e
            });
            let tmp_2 = cs.alloc(
                || "tmp2",
                || tmp_2_value.ok_or(SynthesisError::AssignmentMissing),
            )?;
            cs.enforce(
                || "tmp2 = (xL + Ci)^4",
                |lc| lc + tmp,
                |lc| lc + tmp,
                |lc| lc + tmp_2,
            );

            // tmp_3 = (x + k + ci)^6
            // tmp_3 = (tmp_2)(tmp)
            let tmp_3_value = tmp_2_value.map(|mut e| {
                e.mul_assign(&tmp_value.unwrap());
                e
            });
            let tmp_3 = cs.alloc(
                || "tmp3",
                || tmp_3_value.ok_or(SynthesisError::AssignmentMissing),
            )?;
            cs.enforce(
                || "tmp3 = (xL + Ci)^6",
                |lc| lc + tmp_2,
                |lc| lc + tmp,
                |lc| lc + tmp_3,
            );

            // new_x = (x + k + ci)^7
            // new_x = (x + k + ci).(tmp_3)
            let rhs_value = x_value.map(|mut e| {
                e.add_assign(&k_value.unwrap());
                e.add_assign(&self.constants[i]);
                e
            });
            let new_x_value = tmp_3_value.map(|mut e| {
                e.mul_assign(&rhs_value.unwrap());
                e
            });
            let new_x = if i == (MIMC_ROUNDS - 1) {
                cs.alloc_input(
                    || "image",
                    || new_x_value.ok_or(SynthesisError::AssignmentMissing),
                )?
            } else {
                cs.alloc(
                    || "new_x",
                    || new_x_value.ok_or(SynthesisError::AssignmentMissing),
                )?
            };

            cs.enforce(
                || "new_x = (x + k + Ci)^7",
                |lc| lc + x + k + (self.constants[i], CS::one()),
                |lc| lc + tmp_3,
                |lc| lc + new_x,
            );

            x = new_x;
            x_value = new_x_value;
        }
    }
        Ok(())
    }
}

// #[test]
fn main() {
    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    let rng = &mut thread_rng();

    // Generate the MiMC round constants
    let constants = (0..MIMC_ROUNDS)
        .map(|_| <Bn256 as ScalarEngine>::Fr::rand(rng))
        .collect::<Vec<_>>();


    // Let's benchmark stuff!
    const SAMPLES: u32 = 12;
    // Just a place to put the proof data, so we can
    // benchmark deserialization.
    let mut proof_vec = vec![];

    for sample_idx in 0..SAMPLES {

        println!("Creating parameters...");
        let num_repetitions = ((sample_idx as usize) + 1) * MIMC_STEP;

        // Create parameters for our circuit
        let params = {
            let c = MiMCDemo::<Bn256> {
                repetitions: num_repetitions,
                x: None,
                k: None,
                constants: &constants,
            };
    
            generate_random_parameters(c, rng).unwrap()
        };
    
        // Prepare the verification key (for proof verification)
        let pvk = prepare_verifying_key(&params.vk);
    
        println!("Creating proofs...");
    
        // Generate a random preimage and compute the image
        let x = <Bn256 as ScalarEngine>::Fr::rand(rng);
        let k = <Bn256 as ScalarEngine>::Fr::rand(rng);

        let mut input_vec = vec![];

        for _ in 0..num_repetitions {
            input_vec.push(mimc::<Bn256>(x, k, &constants));
        }
        proof_vec.truncate(0);
    
        let c = MiMCDemo {
            repetitions: num_repetitions,
            x: Some(x),
            k: Some(k),
            constants: &constants,
        };
    
        let start = Instant::now();
        {
            // Create a groth16 proof with our parameters.
            let proof = create_random_proof(c, &params, rng).unwrap();

            proof.write(&mut proof_vec).unwrap();
        }

        let total_proving = start.elapsed();

        let start = Instant::now();
        let proof = Proof::read(&proof_vec[..]).unwrap();
        // Check the proof
        assert!(verify_proof(&pvk, &proof, &input_vec).unwrap());
        let total_verifying = start.elapsed();

        let proving_avg = total_proving;
        let proving_avg =
            proving_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (proving_avg.as_secs() as f64);
    
        let verifying_avg = total_verifying;
        let verifying_avg =
            verifying_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (verifying_avg.as_secs() as f64);

        println!("applying MiMC cipher: {:?} times", num_repetitions);
        println!("proving time: {:?} seconds", proving_avg);
        println!("verifying time: {:?} seconds", verifying_avg);    
    }
}

/*
Creating parameters...
Has generated 74001 points
Creating proofs...
applying MiMC cipher: 200 times
proving time: 2.2159106 seconds
verifying time: 0.0408817 seconds
Creating parameters...
Has generated 148001 points
Creating proofs...
applying MiMC cipher: 400 times
proving time: 4.130553 seconds
verifying time: 0.0709889 seconds
Creating parameters...
Has generated 222001 points
Creating proofs...
applying MiMC cipher: 600 times
proving time: 5.1992319 seconds
verifying time: 0.1179327 seconds
Creating parameters...
Has generated 296001 points
Creating proofs...
applying MiMC cipher: 800 times
proving time: 8.2689414 seconds
verifying time: 0.1259838 seconds
Creating parameters...
Has generated 370001 points
Creating proofs...
applying MiMC cipher: 1000 times
proving time: 9.3462021 seconds
verifying time: 0.1612466 seconds
Creating parameters...
Has generated 444001 points
Creating proofs...
applying MiMC cipher: 1200 times
proving time: 10.552889799999999 seconds
verifying time: 0.1793965 seconds
Creating parameters...
Has generated 518001 points
Creating proofs...
applying MiMC cipher: 1400 times
proving time: 15.1779458 seconds
verifying time: 0.2295376 seconds
Creating parameters...
Has generated 592001 points
Creating proofs...
applying MiMC cipher: 1600 times
proving time: 18.3351802 seconds
verifying time: 0.25943 seconds
Creating parameters...
Has generated 666001 points
Creating proofs...
applying MiMC cipher: 1800 times
proving time: 21.2403677 seconds
verifying time: 0.2853507 seconds
Creating parameters...
Has generated 740001 points
Creating proofs...
applying MiMC cipher: 2000 times
proving time: 22.731332899999998 seconds
verifying time: 0.3332196 seconds
*/