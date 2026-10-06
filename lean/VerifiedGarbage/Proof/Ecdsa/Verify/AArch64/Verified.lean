import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Timing
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified

/-!
# ECDSA verification over P-256 on AArch64: `Verified`

P-256 is a curve the proof supports (`p256_ok`, given the inversions' soundness `InvSounds`, and `Law` for its group
law, which the registration file supplies: `Proof.P256.law` and `invSound_of_toM`), so `verify_ok` gives
the contract's postcondition; `x19`–`x25` are restored, and no instruction
writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). The public fixed-base lookup uses the scalar determined
by the digest and signature, which the shared contract declares public.
`verify_public_ct` relates these lookups; taint tracking checks the rest.
-/

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

theorem pre_of {s : State} (h : verifyAArch64.pre s) : VPre p256 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, held, fit, hdw⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, ⟨by rw [h1]; simp, held, fit, hdw _ (by simp)⟩⟩

theorem verify_noCalls : verifyP256.noCalls = true := by lit_decide

theorem verify_untouched : KeepsUntouched verifyP256 := by lit_decide

theorem verify_keepsV : verifyP256.allInstrs keepsV = true := by lit_decide

theorem verify_a64 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (s : State)
    (hs : verifyAArch64.pre s) :
    ∃ t s', Exec isa verifyP256 s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := verify_ok (p256_ok hI) hL hT (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he verify_noCalls verify_untouched verify_keepsV hsv, hpost⟩

theorem verify_checks : VerifyChecks p256 where
  comb := {
    init := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
      (fun _ _ _ _ h => h) (by taint_decide)
    head := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x19])
      (fun _ _ _ _ h => h) (by taint_decide)
    tail := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x19, .x16])
      (fun _ _ _ _ h => h) (by taint_decide) }
  before := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ h => h) (by taint_decide)
  after := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

/-- The shared specification exposes the scalar's inputs. -/
theorem verify_public_of_spec {s₁ s₂ : State}
    (pub : (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)).pub s₁ s₂) :
    VerifyPublic p256 s₁ s₂ := by
  sig_pub [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P256.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p256_combConsts,
    Abi.withConsts] at pub
  obtain ⟨hsp, hsy, inputs, h0, h1, h2, h3⟩ := pub
  refine ⟨⟨hsp, fun r hr => ?_⟩, hsy, ?_⟩
  · simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
    have parts := List.append_inj eqBytes (by simp only [List.length_append,
      Weierstrass.length_bytesAt])
    have digest := (List.append_inj parts.1 (by simp only [Weierstrass.length_bytesAt])).2
    exact publicU_congr digest parts.2

/-- Use the public inputs declared by the shared specification directly. -/
theorem verify_ct (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    ConstantTime isa
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)).pre
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)).pub verifyP256 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  apply verify_public_ct (p256_ok hI) hL hT (by decide) verify_checks
    _ _ _ _ _ _ (pre_of (implies.pre _ pre₁)) (pre_of (implies.pre _ pre₂)) (verify_public_of_spec pub) e₁ e₂

theorem verify_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    Verified AArch64.target verifyP256
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)) := by
  refine ⟨fun s hs => ?_, verify_ct hL hI hT, implies.sat⟩
  obtain ⟨t, s', he, ha, hp⟩ := verify_a64 hL hI hT s (implies.pre _ hs)
  exact ⟨t, s', he, ha, implies.post s s' hs hp⟩

end VG.Proof.Ecdsa.Verify.AArch64
