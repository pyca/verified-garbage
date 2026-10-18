module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.PackedMain
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.PackedMain
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Checks
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Checks
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import Mathlib.Data.Finset.Card
meta import Mathlib.Data.Nat.Find
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym

/-!
# ECDSA verification over P-521 on AArch64: `Verified`

P-521 is a curve the proof supports (`p521_ok`, given the inversions' soundness `InvSounds`, and `Law` for its group
law, which the registration file supplies: `Proof.P521.law` and `invSound_of_toM`), so `packedNafVerify_ok` gives
the contract's postcondition; `x19`–`x25` are restored, and no instruction
writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time relative to the contract's public inputs
(`packedNafVerify_public_ct`): the comb reads the entries of the digits of
`u = e s⁻¹`, from the digest and the signature, directly; the public NAF
branches on the digits of `v = r s⁻¹` and on the coordinates of the key, and
reads the entries of those digits; around them, by taint tracking
(`verify_checks`), the only branches are on loop counters and every other
address is an argument plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P521

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P521

theorem pre_of {s : State} (h : verifyAArch64.pre s) : VPre p521 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, held, fit, hdw⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, ⟨by rw [h1]; simp, held, fit, hdw _ (by simp)⟩⟩

theorem verify_callsKeep : CallsKeep verifyP521 := by lit_decide

theorem verify_untouched : KeepsUntouched verifyP521 := by lit_decide

theorem verify_keepsV : verifyP521.allInstrs keepsV = true := by lit_decide

theorem verify_a64 (hL : Weierstrass.Law Spec.P521.curve) (hO : Weierstrass.PrimeOrder Spec.P521.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (s : State)
    (hs : verifyAArch64.pre s) :
    ∃ t s', Exec isa verifyP521 s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := packedNafVerify_ok (p521_ok hI) (by decide) hL hO (by decide) hT
    (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he verify_callsKeep verify_untouched verify_keepsV hsv, hpost⟩

/-- The contract's public inputs: the pointers, the table, and the key, digest and signature. -/
theorem jacPublic_of_spec {s₁ s₂ : State}
    (pub : (Spec.Ecdsa.P521.inst.verifyContract (AArch64.abi.withConsts p521.combConsts)).pub s₁ s₂) :
    JacPublic p521 s₁ s₂ := by
  sig_pub [Spec.Ecdsa.P521.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P521.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p521_combConsts,
    Abi.withConsts] at pub
  obtain ⟨hsp, hsy, inputs, h0, h1, h2, h3⟩ := pub
  refine ⟨⟨hsp, fun r hr => ?_⟩, hsy, ?_, ?_, ?_⟩
  · simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  all_goals
    have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
    have parts := List.append_inj eqBytes (by simp only [List.length_append, Weierstrass.length_bytesAt])
    have front := List.append_inj parts.1 (by simp only [Weierstrass.length_bytesAt])
  · exact front.1
  · exact front.2
  · exact parts.2

theorem verify_ct (hL : Weierstrass.Law Spec.P521.curve) (hO : Weierstrass.PrimeOrder Spec.P521.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) :
    ConstantTime isa
      (Spec.Ecdsa.P521.inst.verifyContract (AArch64.abi.withConsts p521.combConsts)).pre
      (Spec.Ecdsa.P521.inst.verifyContract (AArch64.abi.withConsts p521.combConsts)).pub verifyP521 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact packedNafVerify_public_ct (p521_ok hI) (by decide) hL hO (by decide) hT packed_verify_checks _ _ _ _ _ _
    (pre_of (implies.pre _ pre₁)) (pre_of (implies.pre _ pre₂)) (jacPublic_of_spec pub) e₁ e₂

theorem verify_verified (hL : Weierstrass.Law Spec.P521.curve) (hO : Weierstrass.PrimeOrder Spec.P521.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) :
    Verified AArch64.target verifyP521
      (Spec.Ecdsa.P521.inst.verifyContract (AArch64.abi.withConsts p521.combConsts)) := by
  refine ⟨fun s hs => ?_, verify_ct hL hO hI hT, implies.sat⟩
  obtain ⟨t, s', he, ha, hp⟩ := verify_a64 hL hO hI hT s (implies.pre _ hs)
  exact ⟨t, s', he, ha, implies.post s s' hs hp⟩

end VG.Proof.Ecdsa.Verify.AArch64.P521
