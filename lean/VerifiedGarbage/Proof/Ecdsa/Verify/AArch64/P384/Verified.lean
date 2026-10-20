module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMain
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Checks
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
import VerifiedGarbage.Proof.P384.EcdhDouble.Verified
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.StepDTiming
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.AArch64
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Batteries.Data.List.Lemmas
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot

/-!
# ECDSA verification over P-384 on AArch64: `Verified`

P-384 is a curve the proof supports (`p384_ok`, given the inversions' soundness `InvSounds`, and `Law` for its group
law, which the registration file supplies: `Proof.P384.law` and `invSound_of_toM`), so `pubNafVerify_ok` gives
the contract's postcondition, its doublings the register-allocated ones of
ECDH (`P384.EcdhDouble.dblsOk`, `ctRD`); `x19`–`x25` are restored, and no instruction
writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time relative to the contract's public inputs
(`pubNafVerify_public_ct`): the comb reads the entries of the digits of
`u = e s⁻¹`, from the digest and the signature, directly; the public NAF
branches on the digits of `v = r s⁻¹` and on the coordinates of the key, and
reads the entries of those digits; around them, by taint tracking
(`verify_checks`), the only branches are on loop counters and every other
address is an argument plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P384

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P384

theorem pre_of {s : State} (h : verifyAArch64.pre s) : VPre p384 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, held, fit, hdw⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, ⟨by rw [h1]; simp, held, fit, hdw _ (by simp)⟩⟩

/-- The allocated doubling does what the window's must. -/
theorem dbl_ok (hI : Weierstrass.AArch64.InvSounds) (base : Addr) :
    Weierstrass.AArch64.PubNaf.NafDblOk (Ecdh.AArch64.winQ p384) p384.C base 8192
      (some (.block Impl.P384.EcdhAllocatedCode.doubleRD)) := fun _ h => by
  cases h
  exact (P384.EcdhDouble.dblsOk P384.EcdhDouble.p384_C_p (Ecdh.AArch64.winLayQ (p384_ok hI))
    (Ecdh.AArch64.winAQ (p384_ok hI)) (Weierstrass.unitMod_pow_two (p384_ok hI).p_odd _) base _ rfl).1

/-- The allocated doubling is constant-time given `x0`. -/
theorem dbl_ct : Weierstrass.AArch64.PubNaf.NafDblCT (some (.block Impl.P384.EcdhAllocatedCode.doubleRD)) :=
  fun _ h => by cases h; exact P384.EcdhDouble.Certificate.ctRD

theorem verify_callsKeep : CallsKeep verifyP384 := by lit_decide

theorem verify_untouched : KeepsUntouched verifyP384 := by lit_decide

theorem verify_keepsV : verifyP384.allInstrs keepsV = true := by lit_decide

theorem verify_a64 (hL : Weierstrass.Law Spec.P384.curve) (hO : Weierstrass.PrimeOrder Spec.P384.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (s : State)
    (hs : verifyAArch64.pre s) :
    ∃ t s', Exec isa verifyP384 s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := pubNafVerify_ok (p384_ok hI) (by decide) (by decide) hL hO (by decide) hT
    (dbl_ok hI) (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he verify_callsKeep verify_untouched verify_keepsV hsv, hpost⟩

/-- The contract's public inputs: the pointers, the table, and the key, digest and signature. -/
theorem jacPublic_of_spec {s₁ s₂ : State}
    (pub : (Spec.Ecdsa.P384.inst.verifyContract (AArch64.abi.withConsts p384.combConsts)).pub s₁ s₂) :
    JacPublic p384 s₁ s₂ := by
  sig_pub [Spec.Ecdsa.P384.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P384.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p384_combConsts,
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

theorem verify_ct (hL : Weierstrass.Law Spec.P384.curve) (hO : Weierstrass.PrimeOrder Spec.P384.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) :
    ConstantTime isa
      (Spec.Ecdsa.P384.inst.verifyContract (AArch64.abi.withConsts p384.combConsts)).pre
      (Spec.Ecdsa.P384.inst.verifyContract (AArch64.abi.withConsts p384.combConsts)).pub verifyP384 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact pubNafVerify_public_ct (p384_ok hI) (by decide) (by decide) hL hO (by decide) hT verify_checks
    (dbl_ok hI) dbl_ct _ _ _ _ _ _
    (pre_of (implies.pre _ pre₁)) (pre_of (implies.pre _ pre₂)) (jacPublic_of_spec pub) e₁ e₂

theorem verify_verified (hL : Weierstrass.Law Spec.P384.curve) (hO : Weierstrass.PrimeOrder Spec.P384.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) :
    Verified AArch64.target verifyP384
      (Spec.Ecdsa.P384.inst.verifyContract (AArch64.abi.withConsts p384.combConsts)) := by
  refine ⟨fun s hs => ?_, verify_ct hL hO hI hT, implies.sat⟩
  obtain ⟨t, s', he, ha, hp⟩ := verify_a64 hL hO hI hT s (implies.pre _ hs)
  exact ⟨t, s', he, ha, implies.post s s' hs hp⟩

end VG.Proof.Ecdsa.Verify.AArch64.P384
