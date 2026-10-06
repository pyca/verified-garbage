import VerifiedGarbage.Proof.Rsa.AArch64.CvCTCode
import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_crt_values` on AArch64: verified against the shared contract

`cvA` states the shared contract on the registers and the stack
(`cv_implies`); with correctness (`cvCode_correct`) and constant time
(`cvCode_constantTime`), `CrtValues.code` is verified (`cv_verified`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.Keys

/-- A state meeting `cvA.pre`: a 512-bit modulus, one-byte factors and
exponent, and the stack arguments at `0x6000`. -/
def cvSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1 | .x2 => 0x1100 | .x3 => 1 | .x4 => 0x1200 | .x5 => 1 | .x6 => 0x2000
    | .x7 => 64 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6001 then 0x30 else if a = 0x6008 then 1 else if a = 0x6011 then 0x31
    else if a = 0x6018 then 1 else if a = 0x6021 then 0x32 else if a = 0x6028 then 1
    else if a = 0x6031 then 0x80 else if a = 0x6039 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x6000, 64⟩]
  wr := [⟨0x1000, 1⟩, ⟨0x1100, 1⟩, ⟨0x1200, 1⟩, ⟨0x8000, 8192⟩]

theorem stackArgs_eight (s : State) :
    List.map (stackArg s) (List.range 8) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7] := rfl

theorem cv_implies : cvA.Implies (Spec.Rsa.crtValuesContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvA, stackArgs_eight, List.append_eq] at h
    sig_pre [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvA, stackArgs_eight, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvA, stackArgs_eight, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvA, stackArgs_eight, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvA, stackArgs_eight, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
    refine ⟨?_, hsp, by rw [stackArgs_eight, stackArgs_eight, a0, a1, a2, a3, a4, a5, a6, a7],
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  sat := by sig_implies_sat [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvA, stackArgs_eight,
    List.append_eq] [cvSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using cvSatState

/-- `vg_rsa_crt_values`. -/
theorem cv_verified : Verified target CrtValues.code (Spec.Rsa.crtValuesContract abi) :=
  Verified.of_correct cvCode_correct cvCode_constantTime cv_implies

end VG.Proof.Rsa.AArch64
