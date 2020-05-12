
#![allow(non_snake_case)]

extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;
extern crate rand;

use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand::thread_rng;
use practice::r1cs_utils::{AllocatedQuantity, positive_no_gadget, constrain_lc_with_scalar};
pub fn bound_check_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    v: AllocatedQuantity,
    a: AllocatedQuantity,
    b: AllocatedQuantity,
    max: u64,
    min: u64,
    bit_size: usize,
) -> Result<(), R1CSError> {

    cs.constrain(v.variable - LinearCombination::from(min) - a.variable);

    cs.constrain(LinearCombination::from(max) - v.variable - b.variable);

    // Constrain a + b to be same as max - min.
    constrain_lc_with_scalar::<CS>(cs, a.variable + b.variable, &Scalar::from(max - min));

    // Constrain a in [0, 2^n)
    assert!(positive_no_gadget(cs, a, bit_size).is_ok());
    // Constrain b in [0, 2^n)
    assert!(positive_no_gadget(cs, b, bit_size).is_ok());

    Ok(())
}


fn risk_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    lc_array:&mut [LinearCombination],
    quantity_v:AllocatedQuantity,
    quantity_a:AllocatedQuantity,
    quantity_b:AllocatedQuantity,
    upper:u64,
    lower:u64,
    bit_sz:usize,
) {
    let risk_factor_array = vec![0.61, 0.14, 0.71, 0.23, 0.42, 0.8, 0.13, 0.2];
    let mut lc:LinearCombination=LinearCombination::from(Scalar::zero());
    let mut l:LinearCombination=LinearCombination::from(Scalar::zero());

    let x1:LinearCombination=LinearCombination::from(Scalar::from(1000u64));//Scaling to 1000
    // x1=x1*(Scalar::from(1000));
    for it in risk_factor_array.iter().zip(lc_array.iter()) {
        let (a, b) = it;
        let (_, _, c1) = cs.multiply(LinearCombination::from((a*f64::from(1000)) as u64), b.clone());
        lc=lc.clone()+c1;
        l=l.clone()+b.clone();
    }
   // cs.constrain(l-x1);
    // let (_, _, c1) = cs.multiply(LinearCombination::from(1u64), x1);
    // let (_, _, c2) = cs.multiply(LinearCombination::from(4u64), x2);
    // let (_, _, c3) = cs.multiply(LinearCombination::from((0.5*f64::from(1000)) as u64), x3);
    let lc1:LinearCombination=quantity_v.variable.into();
    cs.constrain(lc - lc1);
    assert!(bound_check_gadget(cs, quantity_v, quantity_a, quantity_b, upper, lower, bit_sz).is_ok());
}

fn risk_gadget_proof(
    pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    wt_array:&mut [f64],
    upper: u64,
    lower: u64,
    bit_sz:usize,
) -> Result<(R1CSProof, Vec<CompressedRistretto>), R1CSError> {
    let mut transcript = Transcript::new(b"R1CSExampleGadget");

    // 1. Create a prover
    let mut prover = Prover::new(pc_gens, &mut transcript);

    // 2. Commit high-level variables
    let (mut commitments, vars): (Vec<_>, Vec<_>) = wt_array
        .into_iter()
        .map(|x| prover.commit(Scalar::from(((*x)*(f64::from(1000))) as u64), Scalar::random(&mut thread_rng())))//Values are scaled
        .unzip();
    
    // 3. Build a CS
    let mut lc_array:Vec<LinearCombination> = Vec::new();
    
    for _y in vars{
        lc_array.push(_y.into());
    }
    let mut num:u64=0;
    let mut temp;
    let mut x;
    let mut y;
    let risk_factor_array = vec![0.61, 0.14, 0.71, 0.23, 0.42, 0.8, 0.13, 0.2];

    for it in risk_factor_array.iter().zip(wt_array.iter()) {
        let (a, b) = it;
        x=(a*f64::from(1000)) as u64;
        y=(b*f64::from(1000)) as u64;
        temp=x*y;
        num=num+(temp as u64);
    }
    println!("num is : {}",num);
    let a = num - lower;
    let b = upper - num;
    let (com_v, var_v) = prover.commit(num.into(),Scalar::random(&mut thread_rng()));
    let (com_a, var_a) = prover.commit(a.into(), Scalar::random(&mut thread_rng()));
    let (com_b, var_b) = prover.commit(b.into(), Scalar::random(&mut thread_rng()));
    let quantity_v = AllocatedQuantity {
        variable: var_v,
        assignment: Some(num),
    };
    let quantity_a = AllocatedQuantity {
        variable: var_a,
        assignment: Some(a),
    };
    let quantity_b = AllocatedQuantity {
        variable: var_b,
        assignment: Some(b),
    };
    risk_gadget(
        &mut prover,
        &mut lc_array,
        quantity_v,
        quantity_a,
        quantity_b,
        upper,
        lower,
        bit_sz
    );
    commitments.push(com_v);
    commitments.push(com_a);
    commitments.push(com_b);
    // 4. Make a proof
    let proof = prover.prove(bp_gens)?;

    Ok((proof, commitments))
}


// Verifier logic
fn risk_gadget_verify(
    pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    upper:u64,
    lower:u64,
    bit_sz:usize,
    proof: R1CSProof,
    commitments: Vec<CompressedRistretto>,
) -> Result<(), R1CSError> {
    let mut transcript = Transcript::new(b"R1CSExampleGadget");

    // 1. Create a verifier
    let mut verifier = Verifier::new(&mut transcript);

    // 2. Commit high-level variables
    let vars: Vec<_> = commitments.iter().map(|V| verifier.commit(*V)).collect();
    let mut lc_array:Vec<LinearCombination> = Vec::new();
    // let mut ctr=0;
    let len=vars.len();

    for ctr in 0..len-3{
        lc_array.push(vars[ctr].into());
       // ctr=ctr+1;
    }
    
    let quantity_v = AllocatedQuantity {
        variable: vars[len-3],
        assignment: None,
    };
    let quantity_a = AllocatedQuantity {
        variable: vars[len-2],
        assignment: None,
    };
    let quantity_b = AllocatedQuantity {
        variable: vars[len-1],
        assignment: None,
    };
    // 3. Build a CS
    risk_gadget(
        &mut verifier,
        &mut lc_array,
        quantity_v,
        quantity_a,
        quantity_b,
        upper,
        lower,
        bit_sz
    );

    // 4. Verify the proof
    verifier
        .verify(&proof, &pc_gens, &bp_gens)
        .map_err(|_| R1CSError::VerificationError)
}
fn range_gadget_proof(
    pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    wt_array:&mut [f64],
    b:u64,
    bit_sz:usize,
) -> Result<(R1CSProof, Vec<CompressedRistretto>), R1CSError> {
    let mut transcript = Transcript::new(b"R1CSExampleGadget");

    // 1. Create a prover
    let mut prover = Prover::new(pc_gens, &mut transcript);
    
    // 3. Build a CS
    let mut commitments=Vec::with_capacity(50);
    for f in wt_array{
    let y=((*f)*f64::from(1000)) as u64;
    let x=b-y;
    let (com_v, var_v) = prover.commit(y.into(),Scalar::random(&mut thread_rng()));
    let (com_a, var_a) = prover.commit(y.into(), Scalar::random(&mut thread_rng()));
    let (com_b, var_b) = prover.commit(x.into(), Scalar::random(&mut thread_rng()));
    let quantity_v = AllocatedQuantity {
        variable: var_v,
        assignment: Some(y),
    };
    let quantity_a = AllocatedQuantity {
        variable: var_a,
        assignment: Some(y),
    };
    let quantity_b = AllocatedQuantity {
        variable: var_b,
        assignment: Some(x),
    };
    bound_check_gadget(
        &mut prover,
        quantity_v,
        quantity_a,
        quantity_b,
        b,
        0,
        bit_sz
    );
   
    commitments.push(com_v);
    commitments.push(com_a);
    commitments.push(com_b);
    }
    // 4. Make a proof
    let proof = prover.prove(bp_gens)?;

    Ok((proof, commitments))
}
fn range_gadget_verify(
    pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    b:u64,
    bit_sz:usize,
    proof: R1CSProof,
    commitments: Vec<CompressedRistretto>,
)-> Result<(), R1CSError> {
    let mut transcript = Transcript::new(b"R1CSExampleGadget");

    // 1. Create a verifier
    let mut verifier = Verifier::new(&mut transcript);

    // 2. Commit high-level variables
    let vars: Vec<_> = commitments.iter().map(|V| verifier.commit(*V)).collect();
    let mut ctr=0;
    let len=vars.len();
    while ctr < len {
    let quantity_v = AllocatedQuantity {
        variable: vars[ctr],
        assignment: None,
    };
    let quantity_a = AllocatedQuantity {
        variable: vars[ctr+1],
        assignment: None,
    };
    let quantity_b = AllocatedQuantity {
        variable: vars[ctr+2],
        assignment: None,
    };
    ctr = ctr + 3;
    // 3. Build a CS
    bound_check_gadget(
        &mut verifier,
        quantity_v,
        quantity_a,
        quantity_b,
        b,
        0,
        bit_sz
    );
    }
    // 4. Verify the proof
    verifier
        .verify(&proof, &pc_gens, &bp_gens)
        .map_err(|_| R1CSError::VerificationError)

}
fn count_bits(number: u64) -> usize {
    let used_bits = 64 - number.leading_zeros();
    return used_bits as usize
}
fn risk_gadget_roundtrip_helper(
    mut wt_array:&mut [f64],
) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 1);
    let upper:u64=1000000;
    let bit_sz=count_bits(upper);
    let lower:u64=20;
    //Proof for 
   // 1. w1f1 + w2f2 + ...... = f,  fi are risk factor array(low level variables) 
   //and wi is weight array (high level variables)
   // 2. f lies in bounds i.e (lower <= f <= upper)
   // 3. w1 + w2 + w3 +...... = 1
    let (proof, commitments) = risk_gadget_proof(&pc_gens, &bp_gens, &mut wt_array, upper,lower,bit_sz)?;
    println!("proof = {:?}\n", proof);
    println!("...........commitments 1:");
    println!("proof = \"{}\"", hex::encode(proof.to_bytes()));
    print!("vc = \"");
    for com in &commitments {
        println!("commit = {:?}\n", com);
        print!("{} ", hex::encode(com.as_bytes()));
    }
    println!("\"\n");
    risk_gadget_verify(&pc_gens, &bp_gens, upper,lower,bit_sz, proof, commitments)
}
fn range_gadget_roundtrip_helper(
    mut wt_array:&mut [f64],
) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(1024, 1);
    let b=(0.81*f64::from(1000)) as u64;
    let bit_sz=count_bits(b);
     //Proof for
     // for all i (0 <= wi <= b)
    let (proof, commitments) = range_gadget_proof(&pc_gens, &bp_gens, &mut wt_array,b,bit_sz)?;

    range_gadget_verify(&pc_gens, &bp_gens,b,bit_sz, proof, commitments)
}
fn risk_gadget_roundtrip_helper2(
    proof:String,
    commitments:String,
) -> Result<(), R1CSError> {
    // Common
    let proof = "00dcd0fb093c9d5d6b4a5a6aa8ab3808be3ee5b7ddd2820335b2ffdce377b5fb4272e6d7a717fcda17b7487cb03934453f6129df6c202b1f49fa9dea38170dc45b5a18da500f39608e387a0af14c2741cc17eede826a61d6a103abcb278dc78f31c24bb6f73640f53a5e6fa603348f766682f192c1af43d12554774f35ed5ac72c5acf4cb05de98acda6bb3bf7747d4d45d0e0ffad68e6cb42bdfe118bea2f8b1a04d4429cefd18d87975c8b51bd2c67734593bc8f224fa3ca1b0fc1136608216d28145be38daed86bf3d92c11492c77625456eb1d5711895b456ccf6c204a5d0c804ee2cad6c12760656a3260acdcedf196db29d75d4961c4348417f7a326bd5272adb178927b4f6513e4f251302b1a4a823a43e01caa1b463762a826fa7167023ebe44a34742c771b5511e9a1a72270e7253f5879b1ed7e64b93b44d63aeee0cf88f15d9c2f88f589b91f1423824f0f5d9cb6afaa302f8e8c9c7bda1f2870202666211978fb1570246588f985f4904b53fa673065c3d5fe70429f7a574c9064d0c42da4dc4da58f1d462d2a46d867a8804f9f95791af4407f153a9d1cf10eb7bcc319c94461839932720d55665483cf6ec935392b658a3f3ce6cf211fa720361cae2bfb83bc5c47963cb3fee79b25a3b2230468fb6160a16783ae58eff11b720b2535de14669100681831e0aacf83ad63eb78e106e860e8337821e73c49a9566f4dfc7b86bfc782b8c486136140c2fba516958c52cd460a393105946c65a2b69c65419a2b1feb34e3a0ec9070f62136b79e0def435a4295ee9646a77efb766757e1f256dfe365fd9e159c245d8c3a0c424be787f28e465c5d825e9a40189757762ecce36aa97e43828cac3cc6965f72b841bb3322c3ac3d13cb9e454551d003b7abaf40bf1da7f751138db353c033c9c94cf08a11b58581bea7b074043004419deb8e46333b6403a7f38a60f08644557ef3eaee5212bd5bb828ebfaeeaf1b7340a6bbf73de0bf06f22fcdd3015c84bdaa649470ca9ea03c9dad0f77035c2a55c5207596e983fa5eb5c2ab66ad3777c7cec2e05ed9155da7bd8c58e7d46201d01d9ee3ff11de56de710f2ca28d3f05059aabfa931e59c0528b8a288aa5bb3300b".to_string();
   // let commitments = "baf63cbc50ea094e2c7581db325a34b2190b9aefcb0f70650bafabcd43598b6c 604baa56a06798322408c562531a6a430a861672398168547be92f9c38e0a704 3014fffd6d9631e72b23dd7362f8292e7940a85055b7ee80be074bd1c12c546d 2cea327a3820cd8eebac153c76478f0d515f60cb06ef1c2418b48c1eab5adf4b 204f2dafa6105655e2228ee3eaae3b571f0497cc44965a39594ac549cbf8e879 e4c0237e0ea0e3a426ef37ed0b5406e8af6ecd3778e20a1ea158d510fd7ac306 7c03b0ce0d052cd5d2aa96549e0727389c80e52338f186850a96327f26f5f27e 34b2946e9dae6e40ea78a3668b95f4cb73f17e4ca6ffe18993ea02c9bb7e4449 9043064beef053b0f814a7a9476e31bcec9351865e119cfb0cf805bd74c7337d 76f5d3e9b00eaca52a4c874c645c55769db0e98f9fee1177d58643461d68e608 c403ae113afca7876ea1d30872b5a979726562d8bb50049526d614c7d2f7964c ".to_string();
    println!("dsfdfdfd");
    let  commitments="fe50bf461ffdb0a28f0fa64381e33e243fa03708d34a4125779de1805dcced4a b6293a339880318a011f1ef54426772e1411649d3a1153a71f5e6c0e8fae5d01 707e938cac258642076214aee95958aff823a3766cca8d7ef016af93c57dbb39 feb0a8be39bc4e7acdd7d8a0bb1d8134c814358fd45fb0ab19cef8866d88b85d ea2ebc0dcbf87de742aa6511532017d15f3551435ec323c7bcec49c3aaf52a47 5edb6a1c06e357e95dcc721ce3e671880674b7b8cbcf57c750043397b4f58a4b dc1687df35e595daf5c4efb77c31a04af3ac3b6d75df2c7739057bf6b2c8e14f 14b09f09f402b9c8872dd0fd8f0ac5c0e6a9c27b1919801af54b40892c616b23 a27d05aa253f427011d94f8f83ec61e5ccfa15483556eadaaa321e168b136142 021276b19b5cf9b3e649e5729f8be297601950b1ad462556f23d7372872a1862 347804ba35879436f1f2315a11e63c34a43050f13501fd436bf9cc33cbeb9221".to_string();
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(1024, 1);
    let upper:u64=1000000;
    let bit_sz=count_bits(upper);
    let lower:u64=20;
    let proof=R1CSProof::from_bytes(&hex::decode(proof).unwrap())
                .expect("Rangeproof deserialization failed");
    println!("proof: {:?}",proof);
    // let proof = proof.into_bytes();    //pub fn into_bytes(self) -> Vec<u8>
    // let b = &proof; // b: &Vec<u8>
    // let proof: &[u8] = &b; // proof: &[u8]
    // let proof = R1CSProof::from_bytes(&proof)?;
    let mut split_commitments = commitments.split(" ");
    let mut v: Vec<&str> = split_commitments.collect();
    println!("....length: {} ",v.len());
  //  v.remove(v.len()-1);
    let mut commitments=Vec::new();
    for k in v{
        println!("{:?}",k);
     commitments.push(CompressedRistretto::from_slice(
        &hex::decode(k)
            .unwrap())

    );            println!("{:?}",commitments[commitments.len()-1]);

    }     
    println!("....length: {} ",commitments.len());
    //pub fn from_slice(bytes: &[u8]) -> CompressedRistretto
    //Proof for 
   // 1. w1f1 + w2f2 + ...... = f,  fi are risk factor array(low level variables) 
   //and wi is weight array (high level variables)
   // 2. f lies in bounds i.e (lower <= f <= upper)
   // 3. w1 + w2 + w3 +...... = 1
   
   //let proof = RangeProof::from_bytes(&hex::decode(&proofs[i][j]).unwrap())
           //     .expect("Proof deserialization failed");

    //let (proof, commitments) = risk_gadget_proof(&pc_gens, &bp_gens, &mut wt_array, upper,lower,bit_sz)?;
    // let result = risk_gadget_verify(&pc_gens, &bp_gens, upper,lower,bit_sz, proof, commitments);
    // match result {
    // 	Ok(_) => println!(" verified correctly "),
    // 	Err(_) => println!(" Not verified correctly: "),
    // }
    risk_gadget_verify(&pc_gens, &bp_gens, upper,lower,bit_sz, proof, commitments)
    //return result
}

#[test]
fn risk_gadget_test2() {
  
   // let mut wt_array=vec![0.0, 0.0, 0.0, 0.0, 0.4, 0.0, 0.0, 0.6];
    assert!(risk_gadget_roundtrip_helper2("ff".to_string(),"gf".to_string()).is_ok());
}
// #[test]
// fn risk_gadget_test() {
  
//     let mut wt_array=vec![0.0, 0.0, 0.0, 0.0, 0.4, 0.0, 0.0, 0.6];
//     assert!(risk_gadget_roundtrip_helper(&mut wt_array).is_ok());
// }
// #[test]
// fn range_gadget_test() {
//    // let mut wt_array=vec![0.6,0.5,0.8,0.0,0.3,0.08,0.43];//,0.76];
//     let mut wt_array=vec![0.0, 0.0, 0.0, 0.8, 0.0, 0.0, 0.0, 0.6];
//     assert!(range_gadget_roundtrip_helper(&mut wt_array).is_ok());
// }

// #[test]
// fn example_gadget_serialization_test() {
//     // (3 + 4) * (6 + 1) = (40 + 9)
//     assert!(example_gadget_roundtrip_serialization_helper(3, 4, 6, 1, 40, 9).is_ok());
//     // (3 + 4) * (6 + 1) != (40 + 10)
//     assert!(example_gadget_roundtrip_serialization_helper(3, 4, 6, 1, 40, 10).is_err());
// }

