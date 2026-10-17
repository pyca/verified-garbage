module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint0
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint0
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A candidate on ARMv7: the taint analysis of the check against `p` -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate

theorem cmp0_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r1]) (.block [.cmp .r1 (.imm 0)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem clZero_taint : Cert (.block (setS sCl 0)) := ⟨_, by taint_decide⟩
theorem subD1_taint : Cert (seqs [sub3 aD1 aC aPr, .block [.str .r11 .r8 sLt]]) := ⟨_, by taint_decide⟩
theorem subD2_taint : Cert (sub3 aD2 aPr aC) := ⟨_, by taint_decide⟩
theorem selAbs_taint : Cert (sel aAbs aD1 aD2 sLt) := ⟨_, by taint_decide⟩
theorem bnd_taint : Cert (.block (VG.Impl.RsaKeyGen.Arm.Key.setHi aBnd 2 24 0x10000000)) := ⟨_, by taint_decide⟩
theorem ltCl_taint : Cert (seqs (ltS sCl aBnd aAbs)) := ⟨_, by taint_decide⟩
theorem notCl_taint : Cert (.block (VG.Impl.RsaKeyGen.Arm.Key.notS sCl sCl)) := ⟨_, by taint_decide⟩
theorem isCl_taint : Cert (.block (VG.Impl.RsaKeyGen.Arm.Key.isOne sCl)) := ⟨_, by taint_decide⟩

end VG.Proof.RsaKeyGen.Arm.Cand
