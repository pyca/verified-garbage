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
