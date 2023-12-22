#![no_main]
// If you want to try std support, also update the guest Cargo.toml file
#![no_std]  // std support is experimental

// use ark_ff::QuadExtField;
use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
// For randomness (during paramgen and proof generation)
use ark_std::rand::{Rng, RngCore, SeedableRng};

// Bring in some tools for using pairing-friendly curves
// We're going to use the BLS12-377 pairing-friendly elliptic curve.
use ark_bls12_377::{Bls12_377, Fr};
use ark_ff::Field;
use ark_std::test_rng;

// We'll use these interfaces to construct our circuit.
use ark_relations::{
    lc, ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable},
};

use risc0_zkvm::guest::env;



risc0_zkvm::guest::entry!(main);

const MIMC_ROUNDS: usize = 1;


fn mimc<F: Field>(mut xl: F, mut xr: F, constants: &[F]) -> F {
    assert_eq!(constants.len(), MIMC_ROUNDS);

    for i in 0..MIMC_ROUNDS {
        let mut tmp1 = xl;
        tmp1.add_assign(&constants[i]);
        let mut tmp2 = tmp1;
        tmp2.square_in_place();
        tmp2.mul_assign(&tmp1);
        tmp2.add_assign(&xr);
        xr = xl;
        xl = tmp2;
    }

    xl
}

struct AddDemo<F: Field> {
    x: Option<F>,
    y: Option<F>,
}

impl< F: Field> ConstraintSynthesizer<F> for AddDemo<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let x_value = self.x;
        let x = cs.new_witness_variable(|| x_value.ok_or(SynthesisError::AssignmentMissing))?;

        let y_value = self.y;
        let y = cs.new_witness_variable(|| y_value.ok_or(SynthesisError::AssignmentMissing))?;

        let z_value = x_value.map(|mut e| {
            e.add_assign(&y_value.unwrap());
            e
        });
        let z = cs.new_witness_variable(|| z_value.ok_or(SynthesisError::AssignmentMissing))?;

        cs.enforce_constraint(lc!() + x, lc!() + y, lc!() + z)?;

        Ok(())
    }
}


/// This is our demo circuit for proving knowledge of the
/// preimage of a MiMC hash invocation.
struct MiMCDemo<'a, F: Field> {
    xl: Option<F>,
    xr: Option<F>,
    constants: &'a [F],
}

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<'a, F: Field> ConstraintSynthesizer<F> for MiMCDemo<'a, F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        assert_eq!(self.constants.len(), MIMC_ROUNDS);

        // Allocate the first component of the preimage.
        let mut xl_value = self.xl;
        let mut xl =
            cs.new_witness_variable(|| xl_value.ok_or(SynthesisError::AssignmentMissing))?;

        // Allocate the second component of the preimage.
        let mut xr_value = self.xr;
        let mut xr =
            cs.new_witness_variable(|| xr_value.ok_or(SynthesisError::AssignmentMissing))?;

        for i in 0..MIMC_ROUNDS {
            // xL, xR := xR + (xL + Ci)^3, xL
            let ns = ns!(cs, "round");
            let cs = ns.cs();

            // tmp = (xL + Ci)^2
            let tmp_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.square_in_place();
                e
            });
            let tmp =
                cs.new_witness_variable(|| tmp_value.ok_or(SynthesisError::AssignmentMissing))?;

            cs.enforce_constraint(
                lc!() + xl + (self.constants[i], Variable::One),
                lc!() + xl + (self.constants[i], Variable::One),
                lc!() + tmp,
            )?;

            // new_xL = xR + (xL + Ci)^3
            // new_xL = xR + tmp * (xL + Ci)
            // new_xL - xR = tmp * (xL + Ci)
            let new_xl_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.mul_assign(&tmp_value.unwrap());
                e.add_assign(&xr_value.unwrap());
                e
            });

            let new_xl = if i == (MIMC_ROUNDS - 1) {
                // This is the last round, xL is our image and so
                // we allocate a public input.
                cs.new_input_variable(|| new_xl_value.ok_or(SynthesisError::AssignmentMissing))?
            } else {
                cs.new_witness_variable(|| new_xl_value.ok_or(SynthesisError::AssignmentMissing))?
            };

            cs.enforce_constraint(
                lc!() + tmp,
                lc!() + xl + (self.constants[i], Variable::One),
                lc!() + new_xl - xr,
            )?;

            // xR = xL
            xr = xl;
            xr_value = xl_value;

            // xL = new_xL
            xl = new_xl;
            xl_value = new_xl_value;
        }

        Ok(())
    }
}

// struct AddDemo<'a, F: Field> {
//     x: Option<F>,
//     y: Option<F>,
// }




pub fn main() {
    // TODO: Implement your guest code here

    // read the input
    let input: u32 = env::read();

     // We're going to use the Groth16 proving system.
     use ark_groth16::Groth16;

     // This may not be cryptographically safe, use
     // `OsRng` (for example) in production software.
     let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
 
     // Generate the MiMC round constants
    //  let constants = (0..MIMC_ROUNDS).map(|_| );
 
    //  println!("Creating parameters...");
 
     // Create parameters for our circuit
     let (pk, vk) = {
        //  let c = MiMCDemo::<Fr> {
        //      xl: None,
        //      xr: None,
        //      constants: &constants,
        //  };
        let c = AddDemo::<Fr> {
            x: None,
            y: None,
        };
 
         Groth16::<Bls12_377>::setup(c, &mut rng).unwrap()
     };
 
     // Prepare the verification key (for proof verification)
    //  let pvk = Groth16::<Bls12_377>::process_vk(&vk).unwrap();
 
 
    //  // Let's benchmark stuff!
     const SAMPLES: u32 = 1;
    //  let mut total_proving = Duration::new(0, 0);
    //  let mut total_verifying = Duration::new(0, 0);
 
    //  // Just a place to put the proof data, so we can
    //  // benchmark deserialization.
    //  // let mut proof_vec = vec![];
 
     for _ in 0..SAMPLES {
    //      // Generate a random preimage and compute the image
        //  let x = rng.gen();
        //  let y = rng.gen();
    //      let image = mimc(xl, xr, &constants);
 
    //      // proof_vec.truncate(0);
 
    //      {
    //          // Create an instance of our circuit (with the
    //          // witness)
    //          let c = MiMCDemo {
    //              xl: Some(xl),
    //              xr: Some(xr),
    //              constants: &constants,
    //          };
 
    //          // Create a groth16 proof with our parameters.
    //          let proof = Groth16::<Bls12_377>::prove(&pk, c, &mut rng).unwrap();
    //          print!("proof: {:?}", &proof);
    //          // print!("image: {:?}", &image);
    //          // print!("verification key: {:?}", &pvk);
 
    //          assert!(
    //              Groth16::<Bls12_377>::verify_with_processed_vk(&pvk, &[image], &proof).unwrap()
    //          );
 
    //          // proof.write(&mut proof_vec).unwrap();
    //      }
 
 
    //      // let proof = Proof::read(&proof_vec[..]).unwrap();
    //      // Check the proof
 
     }
    

    // TODO: do something with the input

    // write public output to the journal
    env::commit(&input);
}
