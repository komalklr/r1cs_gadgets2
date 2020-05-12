
#![allow(non_snake_case)]

extern crate bulletproofs;



use bulletproofs::r1cs::{LinearCombination,ConstraintSystem,Verifier,R1CSError,R1CSProof,Prover};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand::thread_rng;
use std::str::FromStr;
// fn example_gadget<CS: ConstraintSystem>(
//     cs: &mut CS,
//     a1: LinearCombination,
//     a2: LinearCombination,
//     b1: LinearCombination,
//     b2: LinearCombination,
//     c1: LinearCombination,
//     c2: LinearCombination,
// ) {
//     let (_, _, c_var) = cs.multiply(a1 + a2, b1 + b2);
//     cs.constrain(c1 + c2 - c_var);
// }

// // Prover's scope
// fn example_gadget_proof(
//     pc_gens: &PedersenGens,
//     bp_gens: &BulletproofGens,
//     a1: u64,
//     a2: u64,
//     b1: u64,
//     b2: u64,
//     c1: u64,
//     c2: u64,
// ) -> Result<(R1CSProof, Vec<CompressedRistretto>), R1CSError> {
//     let mut transcript = Transcript::new(b"R1CSExampleGadget");

//     // 1. Create a prover
//     let mut prover = Prover::new(pc_gens, &mut transcript);

//     // 2. Commit high-level variables
//     let (commitments, vars): (Vec<_>, Vec<_>) = [a1, a2, b1, b2, c1]
//         .into_iter()
//         .map(|x| prover.commit(Scalar::from(*x), Scalar::random(&mut thread_rng())))
//         .unzip();

//     // 3. Build a CS
//     example_gadget(
//         &mut prover,
//         vars[0].into(),
//         vars[1].into(),
//         vars[2].into(),
//         vars[3].into(),
//         vars[4].into(),
//         Scalar::from(c2).into(),
//     );

//     // 4. Make a proof
//     let proof = prover.prove(bp_gens)?;

//     Ok((proof, commitments))
// }


// // Verifier logic
// fn example_gadget_verify(
//     pc_gens: &PedersenGens,
//     bp_gens: &BulletproofGens,
//     c2: u64,
//     proof: R1CSProof,
//     commitments: Vec<CompressedRistretto>,
// ) -> Result<(), R1CSError> {
//     let mut transcript = Transcript::new(b"R1CSExampleGadget");

//     // 1. Create a verifier
//     let mut verifier = Verifier::new(&mut transcript);

//     // 2. Commit high-level variables
//     let vars: Vec<_> = commitments.iter().map(|V| verifier.commit(*V)).collect();

//     // 3. Build a CS
//     example_gadget(
//         &mut verifier,
//         vars[0].into(),
//         vars[1].into(),
//         vars[2].into(),
//         vars[3].into(),
//         vars[4].into(),
//         Scalar::from(c2).into(),
//     );

//     // 4. Verify the proof
//     verifier
//         .verify(&proof, &pc_gens, &bp_gens)
//         .map_err(|_| R1CSError::VerificationError)
// }


// fn example_gadget_roundtrip_helper(
//     a1: u64,
//     a2: u64,
//     b1: u64,
//     b2: u64,
//     c1: u64,
//     c2: u64,
// ) -> Result<(), R1CSError> {
//     // Common
//     let pc_gens = PedersenGens::default();
//     let bp_gens = BulletproofGens::new(128, 1);

//     let (proof, commitments) = example_gadget_proof(&pc_gens, &bp_gens, a1, a2, b1, b2, c1, c2)?;

//     example_gadget_verify(&pc_gens, &bp_gens, c2, proof, commitments)
// }

// fn example_gadget_roundtrip_serialization_helper(
//     a1: u64,
//     a2: u64,
//     b1: u64,
//     b2: u64,
//     c1: u64,
//     c2: u64,
// ) -> Result<(), R1CSError> {
//     // Common
//     let pc_gens = PedersenGens::default();
//     let bp_gens = BulletproofGens::new(128, 1);

//     let (proof, commitments) = example_gadget_proof(&pc_gens, &bp_gens, a1, a2, b1, b2, c1, c2)?;

//     let proof = proof.to_bytes();

//     let proof = R1CSProof::from_bytes(&proof)?;

//     example_gadget_verify(&pc_gens, &bp_gens, c2, proof, commitments)
// }


// #[test]
// fn example_gadget_test() {
//     // (3 + 4) * (6 + 1) = (40 + 9)
//     assert!(example_gadget_roundtrip_helper(3, 4, 6, 1, 40, 9).is_ok());
//     // (3 + 4) * (6 + 1) != (40 + 10)
//     assert!(example_gadget_roundtrip_helper(3, 4, 6, 1, 40, 10).is_err());
// }

// #[test]
// fn example_gadget_serialization_test() {
//     // (3 + 4) * (6 + 1) = (40 + 9)
//     assert!(example_gadget_roundtrip_serialization_helper(3, 4, 6, 1, 40, 9).is_ok());
//     // (3 + 4) * (6 + 1) != (40 + 10)
//     assert!(example_gadget_roundtrip_serialization_helper(3, 4, 6, 1, 40, 10).is_err());
// }
fn example_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    a: LinearCombination,
    b: LinearCombination,
    c: LinearCombination,
) {
    let (_, _, c_var) = cs.multiply(a, b);
    cs.constrain(c - c_var);
}

// Prover's scope
fn example_gadget_proof(
    pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    a: u64,
    b: u64,
    c: u64,
) -> Result<(R1CSProof, Vec<CompressedRistretto>), R1CSError> {
    let mut transcript = Transcript::new(b"R1CSExampleGadget");

    // 1. Create a prover
    let mut prover = Prover::new(pc_gens, &mut transcript);

    // 2. Commit high-level variables
    let (commitments, vars): (Vec<_>, Vec<_>) = [a, b, c]
        .into_iter()
        .map(|x| prover.commit(Scalar::from(*x), Scalar::random(&mut thread_rng())))
        .unzip();

    // 3. Build a CS
    println!("Prover : {:?}",vars[2]);
    example_gadget(
        &mut prover,
        vars[0].into(),
        vars[1].into(),
        Scalar::from(c).into(),
    );

    // 4. Make a proof
    let proof = prover.prove(bp_gens)?;

    Ok((proof, commitments))
}


// Verifier logic
fn example_gadget_verify(
    pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    c: u64,
    proof: R1CSProof,
    commitments: Vec<CompressedRistretto>,
) -> Result<(), R1CSError> {
    let mut transcript = Transcript::new(b"R1CSExampleGadget");
     let proof="008a1c2cf6735918aa7f8597caefb4a803613e05ba36f9f806468d5d0c7df916192ea88c0d3344ca696f3fda50bcb1ca13f08ecffcfa5e9025e3e86e5a32dbd20f1430a9a66fcb99cbc37f8faa47ebbd611de6f7e0c113c08e4e39133432e80539a64587c21b44569e4cbb55e3c5884657a35a90681baa212851fdde761a33d504e6b276b1d54ab06f7f1fa78763741f702a02c94390b61c66c748322e6e3b7870524db675654c28a8bfb0f73fc221ed1639b6905b4d9733b943294b8b4109b874ca8c61793073ac1ca4903097ac7b265794618370e19fd716cba747f19a183c515ec90b29db343b7676dd4778e45db44cbfd1ba68130337a637e266cbd56f6459bcfb202d5c580289ec4d3497750a71c8bd2cce67b28cdb465574fe42091a620d0b1fd6430c44339fa6d2ced4b9b426be8325a30f6d6d8c3b3e14fa5b5b01c20de45865a20fc683738416b220593cf0c0a2e7052aadcca56c2bd5add14181310467a46d2a976a1d98d78fce7a1138be076c89cb39b6c973d8c0340196f5548e0f793b433dec5885aefc6b58e5c35b1ac7b007709f3156175185908188a266cc01".to_string();
//     // 1. Create a verifier
//     let com1="96411dd2da68d581ae853b78609c4709b03fe85d422258f580a7b5e18c5a0a6f".to_string();
//     let com2="3ac11fa169f49ca36264b975a66031b33e5966340f05b7ce1f9843f7fbd3f46a".to_string();
//     let com3="3054fbc9aee22fbfd4a0056696b294c715be83fb8e75ec4a0b40dfd8e90a4b32".to_string();
     let proof=R1CSProof::from_bytes(&hex::decode(proof).unwrap())
                 .expect("Rangeproof deserialization failed");

               
//         let mut commitments=Vec::new();
//         commitments.push(CompressedRistretto::from_slice(
//                     &hex::decode(com1)
//                         .unwrap()));
//         commitments.push(CompressedRistretto::from_slice(
//             &hex::decode(com2)
//                 .unwrap()));
//         commitments.push(CompressedRistretto::from_slice(
//             &hex::decode(com3)
//                 .unwrap()));
//     let c="35";
//     let c = i64::from_str(&c).unwrap() as u64;
//     // println!("..proof: {:?}",proof);
//     // println!("....com1:{:?}",commitments[0]);
//     // println!("...com2:{:?}",commitments[1]);
//     // println!("...com2:{:?}",commitments[2]);
//     // println!(".....c:{}",c);
    let mut verifier = Verifier::new(&mut transcript);

//     // 2. Commit high-level variables
//     let vars: Vec<_> = commitments.iter().map(|V| verifier.commit(*V)).collect();
//    // println!("Verifier : {:?}",vars[2]);
//     // 3. Build a CS
//     example_gadget(
//         &mut verifier,
//         vars[0].into(),
//         vars[1].into(),
//         Scalar::from(c).into(),
//     );

    // 4. Verify the proof
    verifier
        .verify(&proof, &pc_gens, &bp_gens)
        .map_err(|_| R1CSError::VerificationError)
}


fn example_gadget_roundtrip_helper(
    a: u64,
    b: u64,
    c: u64,
) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 1);

     let (proof, commitments) = example_gadget_proof(&pc_gens, &bp_gens, a, b, c)?;
//      println!("PROOF: {:?}",proof);
//     println!("...........commitments 1:");
//    println!("proof = \"{}\"", hex::encode(proof.to_bytes()));
//    print!("vc = \"");
//    for com in &commitments {
//        println!("commit = {:?}\n", com);
//        print!("{} ", hex::encode(com.as_bytes()));
//    }
//    println!("\"\n");

    example_gadget_verify(&pc_gens, &bp_gens, c, proof, commitments)
}

fn example_gadget_roundtrip_serialization_helper(
    a: u64,
    b: u64,
    c: u64,
) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 1);

    let (proof, commitments) = example_gadget_proof(&pc_gens, &bp_gens, a, b, c)?;

   // let proof = proof.to_bytes();
   // println!("Proof: ",proof);
   
   let proof = proof.to_bytes();
    let proof = R1CSProof::from_bytes(&proof)?;

    example_gadget_verify(&pc_gens, &bp_gens, c, proof, commitments)
}


#[test]
fn example_gadget_test() {
    // (3 + 4) * (6 + 1) = (40 + 9)
    assert!(example_gadget_roundtrip_helper(5, 7, 35).is_ok());
    // (3 + 4) * (6 + 1) != (40 + 10)
    //assert!(example_gadget_roundtrip_helper(3, 4, 10).is_err());
}

// #[test]
// fn example_gadget_serialization_test() {
//     // (3 + 4) * (6 + 1) = (40 + 9)
//     assert!(example_gadget_roundtrip_serialization_helper(3, 4, 6, 1, 40, 9).is_ok());
//     // (3 + 4) * (6 + 1) != (40 + 10)
//     assert!(example_gadget_roundtrip_serialization_helper(3, 4, 6, 1, 40, 10).is_err());
// }

 
