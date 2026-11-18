module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint0
import VerifiedGarbage.Impl.Dsa.Arm.ProbablePrime
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint0
meta import VerifiedGarbage.Impl.Dsa.Arm.ProbablePrime
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
meta import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate

/-! ### `Dsa.Arm.Prime.Taint1`, which the modules that import this one used -/

section

/-! # A candidate on ARMv7: the taint analysis of the entry and the candidate's loads -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate

/-- The carry of `r1 − r2` made a value, then Z iff it is 0. -/
abbrev carryTail : List Instr := [.subs .r3 .r1 (.reg .r2), .mov .r3 (.imm 0), .adc .r3 .r3 (.imm 0), .cmp .r3 (.imm 0)]

theorem carryTail_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r1, .r2]) (.block carryTail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `setupC` after the loads of `scratch` and `out_len`. -/
abbrev setupTail : List Instr :=
  [.mov .r9 (.shifted .r9 .lsr 2), .dp .add .r9 .r9 (.imm 2)] ++ stride ++
  [.str .r9 .r8 16, .dp .add .r0 .r8 (.imm (BitVec.ofNat 32 hdr)), .mov .lr (.imm (BitVec.ofNat 32 nArr)),
    .mul .lr .lr .r7, .mov .lr (.shifted .lr .lsr 2), .mov .r3 (.imm 0)]

theorem setupC_eq : setupC = ctxB ++ (([.ldrSp .r9 foL] : List Instr) ++ setupTail) := rfl

theorem setupTail_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9]) (.block setupTail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A load with its pointer and length public. -/
abbrev LCert (j : Nat) : Prop := ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.CrtValues.load j) hc).isSome = true

theorem loadC_taint : LCert aC := ⟨_, by taint_decide⟩
theorem loadX_taint : LCert aX := ⟨_, by taint_decide⟩

theorem one_taint : Cert (.block (VG.Impl.RsaKeyGen.Arm.Key.setWd aOne 0 1)) := ⟨_, by taint_decide⟩
theorem two_taint : Cert (.block (VG.Impl.RsaKeyGen.Arm.Key.setWd aTwo 0 2)) := ⟨_, by taint_decide⟩
end VG.Proof.Dsa.Arm.Prime

end

end

/-! # DSA's probable-prime test on ARMv7: the taint analysis of the pieces RSA's candidate lacks -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate

theorem used0_taint : Cert (.block (setS sUsed 0)) := ⟨_, by taint_decide⟩
theorem mrInit1_taint : Cert (.block (setS sI 1 ++ setS sUni 0)) := ⟨_, by taint_decide⟩
theorem wl2d_taint : Cert (.block [.dp .add .r4 .r4 (.reg .r6), .dp .add .r1 .r1 (.reg .r6), .str .r1 .r8 sUsed]) :=
  ⟨_, by taint_decide⟩
theorem wl3d_taint : Cert (.block [.dp .sub .r4 .r4 (.reg .r6)]) := ⟨_, by taint_decide⟩
theorem clrBitXf_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r2, .r7, .r8, .r9]) (.block (ptr .r0 aXf ++ .dp .add .r0 .r0 (.reg .r2) ::
    .dp .sub .r0 .r0 (.imm 4) :: .ldr .r1 .r0 0 ::
    (([.mov .r1 (.shifted .r1 .lsl 1), .mov .r1 (.shifted .r1 .lsr 1)] : List Instr) ++
      ([.str .r1 .r0 0] : List Instr)))) hc).isSome = true := ⟨_, by taint_decide⟩
theorem strChk_taint : Cert (.block [.str .r1 .r8 sChk]) := ⟨_, by taint_decide⟩

end VG.Proof.Dsa.Arm.Prime
