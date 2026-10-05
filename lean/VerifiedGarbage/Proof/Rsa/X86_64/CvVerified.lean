import VerifiedGarbage.Proof.Rsa.X86_64.CvCTCode
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_crt_values` on x86-64: verified against the shared contract

`cvContract` states the shared contract on the registers and the stack
(`cv_implies`); with correctness (`cvCode_correct`) and constant time
(`cvCode_constantTime`), `CrtValues.code` is verified (`cv_verified`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64.Keys

theorem stackArgs_ten (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

/-- A state meeting `cvContract.pre`: a 512-bit modulus, one-byte factors
and exponent, and the stack arguments at `0x6008`. -/
def cvSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 0x1100 | .rcx => 1 | .r8 => 0x1200 | .r9 => 1
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x20 else if a = 0x6010 then 0x40 else if a = 0x6019 then 0x30
    else if a = 0x6020 then 1 else if a = 0x6029 then 0x31 else if a = 0x6030 then 1
    else if a = 0x6039 then 0x32 else if a = 0x6040 then 1 else if a = 0x6049 then 0x80
    else if a = 0x6051 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x6008, 80⟩]
  wr := [⟨0x1000, 1⟩, ⟨0x1100, 1⟩, ⟨0x1200, 1⟩, ⟨0x8000, 8192⟩]

theorem cv_implies : cvContract.Implies (Spec.Rsa.crtValuesContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvContract, stackArgs_ten, List.append_eq] at h
    sig_pre [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvContract, stackArgs_ten, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvContract, stackArgs_ten, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvContract, stackArgs_ten, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvContract, stackArgs_ten, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    refine ⟨?_, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, List.map_injective_iff.2 (fun _ _ h => BitVec.toNat_inj.1 h) hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvContract, stackArgs_ten, List.append_eq] [cvSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using cvSatState

/-- `vg_rsa_crt_values`, given that its code never loads MXCSR (which the
registration file evaluates). -/
theorem cv_verified (hmx : CrtValues.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target CrtValues.code (Spec.Rsa.crtValuesContract abi) :=
  Verified.of_correct (cvCode_correct hmx) cvCode_constantTime cv_implies

end VG.Proof.Rsa.X86_64
