module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
public import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
import VerifiedGarbage.Proof.Ecdsa.AArch64.Tables

/-! The Jacobian verifier's relational proof uses only the bytes already
exposed as public by the shared ECDSA verification specification. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

theorem jacPublic_of_spec {s₁ s₂ : State}
    (pub : (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)).pub s₁ s₂) :
    JacPublic p256 s₁ s₂ := by
  sig_pub [Spec.Ecdsa.P256.inst,Spec.Ecdsa.Instance.verifyContract,Spec.Ecdsa.Instance.verifySig,
    Spec.P256.curve,Spec.Ecdsa.scratchWords,AArch64.abi,AArch64.argRegs,p256_combConsts,
    Abi.withConsts] at pub
  obtain ⟨hsp,hsy,inputs,h0,h1,h2,h3⟩ := pub
  refine ⟨⟨hsp,fun r hr => ?_⟩,hsy,?_,?_,?_⟩
  · simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  all_goals
    have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
    have parts := List.append_inj eqBytes (by simp only [List.length_append,Weierstrass.length_bytesAt])
    have front := List.append_inj parts.1 (by simp only [Weierstrass.length_bytesAt])
  · exact front.1
  · exact front.2
  · exact parts.2

end VG.Proof.Ecdsa.Verify.AArch64
