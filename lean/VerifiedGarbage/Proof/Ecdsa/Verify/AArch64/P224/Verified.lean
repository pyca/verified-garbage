module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P224.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Verified
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P224.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.P224.AArch64
import Batteries.Data.List.Lemmas
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P224.Contract
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P224.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P224.AArch64
meta import Batteries.Data.List.Lemmas

/-!
# ECDSA verification over P-224 on AArch64: `Verified`

P-224 is a curve the proof supports (`p224_ok`, given the inversions' soundness `InvSounds`, and `Law` for its group
law, which the registration file supplies: `Proof.P224.law` and `invSound_of_toM`), so `verify_ok` gives
the contract's postcondition; `x19`–`x25` are restored, and no instruction
writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time relative to the contract's public inputs
(`verify_public_ct`): the comb reads the entries of the digits of
`u = e s⁻¹`, from the digest and the signature, directly; around it, by taint
tracking, the only branches are on loop counters and every other address is
an argument plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P224

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P224

theorem pre_of {s : State} (h : verifyAArch64.pre s) : VPre p224 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, held, fit, hdw⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, ⟨by rw [h1]; simp, held, fit, hdw _ (by simp)⟩⟩

theorem verify_callsKeep : CallsKeep verifyP224 := by lit_decide

theorem verify_untouched : KeepsUntouched verifyP224 := by lit_decide

theorem verify_keepsV : verifyP224.allInstrs keepsV = true := by lit_decide

theorem verify_a64 (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (s : State)
    (hs : verifyAArch64.pre s) :
    ∃ t s', Exec isa verifyP224 s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := verify_ok (p224_ok hI) hL hT (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he verify_callsKeep verify_untouched verify_keepsV hsv, hpost⟩

open VG.Proof.Weierstrass.AArch64 in
/-- The public comb's iterations, and the code before and after it, by taint tracking. -/
theorem verify_checks : VerifyChecks p224 where
  comb := {
    init := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0]) (fun _ _ _ _ h => h) (by taint_decide)
    head := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x19]) (fun _ _ _ _ h => h) (by taint_decide)
    tail := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x19, .x16]) (fun _ _ _ _ h => h)
      (by taint_decide) }
  before := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) (fun _ _ _ _ h => h)
    (by taint_decide)
  after := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0]) (fun _ _ _ _ h => h) (by taint_decide)

/-- The contract's public inputs: the pointers, the table, and the key, digest and signature. -/
theorem verifyPublic_of_spec {s₁ s₂ : State}
    (pub : (Spec.Ecdsa.P224.inst.verifyContract (AArch64.abi.withConsts p224.combConsts)).pub s₁ s₂) :
    VerifyPublic p224 s₁ s₂ := by
  sig_pub [Spec.Ecdsa.P224.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P224.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p224_combConsts,
    Abi.withConsts] at pub
  obtain ⟨hsp, hsy, inputs, h0, h1, h2, h3⟩ := pub
  have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
  have parts := List.append_inj eqBytes (by simp only [List.length_append, Weierstrass.length_bytesAt])
  have front := List.append_inj parts.1 (by simp only [Weierstrass.length_bytesAt])
  refine ⟨⟨hsp, fun r hr => ?_⟩, hsy, publicU_congr front.2 parts.2⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem verify_ct (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start) :
    ConstantTime isa
      (Spec.Ecdsa.P224.inst.verifyContract (AArch64.abi.withConsts p224.combConsts)).pre
      (Spec.Ecdsa.P224.inst.verifyContract (AArch64.abi.withConsts p224.combConsts)).pub verifyP224 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact verify_public_ct (p224_ok hI) hL hT verify_checks _ _ _ _ _ _
    (pre_of (implies.pre _ pre₁)) (pre_of (implies.pre _ pre₂)) (verifyPublic_of_spec pub) e₁ e₂

theorem verify_verified (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start) :
    Verified AArch64.target verifyP224
      (Spec.Ecdsa.P224.inst.verifyContract (AArch64.abi.withConsts p224.combConsts)) := by
  refine ⟨fun s hs => ?_, verify_ct hL hI hT, implies.sat⟩
  obtain ⟨t, s', he, ha, hp⟩ := verify_a64 hL hI hT s (implies.pre _ hs)
  exact ⟨t, s', he, ha, implies.post s s' hs hp⟩

end VG.Proof.Ecdsa.Verify.AArch64.P224
