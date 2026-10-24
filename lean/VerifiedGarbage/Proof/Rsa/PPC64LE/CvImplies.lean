module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvContract
public import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_crt_values` on PPC64LE: the shared contract implies `cvP`

As on AArch64 (`Proof/Rsa/AArch64/CvVerified.lean`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE

/-- A state meeting `cvP.pre`: a 512-bit modulus, one-byte factors and
exponent, and the stack arguments at `sp + 96 = 0x6060`. -/
def cvSatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 1 | .r5 => 0x1100 | .r6 => 1 | .r7 => 0x1200 | .r8 => 1 | .r9 => 0x2000
    | .r10 => 64 | _ => 0
  lr := 0
  sp := 0x6000
  mem a := if a = 0x6061 then 0x30 else if a = 0x6068 then 1 else if a = 0x6071 then 0x31
    else if a = 0x6078 then 1 else if a = 0x6081 then 0x32 else if a = 0x6088 then 1
    else if a = 0x6091 then 0x80 else if a = 0x6098 then 0x20 else if a = 0x6099 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x6060, 64⟩]
  wr := [⟨0x1000, 1⟩, ⟨0x1100, 1⟩, ⟨0x1200, 1⟩, ⟨0x8000, 8448⟩]

theorem stackArgs_eight (s : State) :
    List.map (stackArg s) (List.range 8) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7] := rfl

theorem cv_implies : cvP.Implies (Spec.Rsa.crtValuesContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvP, stackArgs_eight,
      List.append_eq] at h
    sig_pre [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvP, stackArgs_eight,
      List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvP, stackArgs_eight,
      List.append_eq]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | omega
  post := by
    sig_implies_post [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvP, stackArgs_eight,
      List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvP, stackArgs_eight,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
    refine ⟨?_, hsp, by rw [stackArgs_eight, stackArgs_eight, a0, a1, a2, a3, a4, a5, a6, a7],
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  sat := by
    sig_implies_sat [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvP, stackArgs_eight,
      List.append_eq] [cvSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using cvSatState

end VG.Proof.Rsa.PPC64LE.CrtValues
