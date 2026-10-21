module

import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Verified
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombContract
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombGenerator
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts

/-! Signing through the shared pipeline with the checked fixed-base comb. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm.TComb

theorem combSign_ok (hC : Law Spec.Secp256k1.curve) {s₀ : State} (hp : combSignPre s₀) :
    WP isa signSecp256k1Comb s₀ fun t => SignKeep secp256k1 s₀ t ∧ SignPost secp256k1 s₀ t := by
  have member : (secp256k1Comb.tsym,secp256k1CombWords)∈secp256k1CombConsts := List.mem_singleton_self _
  have ht := tableMem_of_consts hp.2 member
  have hd := table_disjoint_of_consts hp.2 member
    (show scR s₀∈s₀.wr by rw [hp.1.wr]; simp)
  exact signWith_ok secp256k1_ok hC hp.1 fun _ S sy => comb_generator_stage hC S sy ht rfl hd

end VG.Proof.Ecdsa.Arm.Secp256k1
