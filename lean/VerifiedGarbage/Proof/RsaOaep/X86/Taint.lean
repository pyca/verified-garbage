module

public import VerifiedGarbage.Proof.RsaOaep.X86.Base
meta import VerifiedGarbage.Proof.RsaOaep.X86.Base
public meta import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # RSAES-OAEP on x86: the taint checks of the pieces that do not depend on the hash functions

Each block from states in which only `esp` and `ebp` (or `esp` alone) are
known to agree, and each loop body from states in which its pointers and its
count agree (`Certs.lean` has those of the pieces whose immediates depend on
the hash function).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG VG.X86 VG.Impl.RsaOaep.X86
open VG.Impl.RsaPss.X86 (ld mi arg clrArgs)
open VG.Proof.RsaPss.X86 (TaintOk)

theorem initArgs_taint : TaintOk [.esp, .ebp] (.block initArgs) := ⟨_, by taint_decide⟩
theorem updSrcArgs_taint : TaintOk [.esp, .ebp] (.block updSrcArgs) := ⟨_, by taint_decide⟩
theorem ctrSet_taint : TaintOk [.esp, .ebp] (.block ctrSet) := ⟨_, by taint_decide⟩
theorem updCtrArgs_taint : TaintOk [.esp, .ebp] (.block updCtrArgs) := ⟨_, by taint_decide⟩
theorem finArgs_taint : TaintOk [.esp, .ebp] (.block finArgs) := ⟨_, by taint_decide⟩
theorem updLab6_taint : TaintOk [.esp, .ebp] (.block (updLabArgs 6)) := ⟨_, by taint_decide⟩
theorem updLab17_taint : TaintOk [.esp, .ebp] (.block (updLabArgs 17)) := ⟨_, by taint_decide⟩
theorem finLab6_taint : TaintOk [.esp, .ebp] (.block (finLabArgs 6 Impl.RsaPss.X86.oDig)) := ⟨_, by taint_decide⟩
theorem finLab17_taint : TaintOk [.esp, .ebp] (.block (finLabArgs 17 oLh)) := ⟨_, by taint_decide⟩
theorem encFailArgs_taint : TaintOk [.esp] (.block [ld .esi (arg 0), ld .ecx (arg 3), mi .eax 0]) :=
  ⟨_, by taint_decide⟩
theorem ret0_taint : TaintOk [.esp] (.block [mi .eax 0]) := ⟨_, by taint_decide⟩
theorem clrEm_taint : TaintOk [.esp, .ebp] (.block clrEm) := ⟨_, by taint_decide⟩
theorem msgPos_taint : TaintOk [.esp, .ebp] (.block msgPos) := ⟨_, by taint_decide⟩
theorem put1_taint : TaintOk [.esp, .ebx] (.block put1) := ⟨_, by taint_decide⟩
theorem pubArgs_taint : TaintOk [.esp, .ebp] (.block pubArgs) := ⟨_, by taint_decide⟩
theorem privArgs_taint : TaintOk [.esp] (.block (decStart ++ privArgs)) := ⟨_, by taint_decide⟩
theorem outClr_taint : TaintOk [.esp] (.block outClr) := ⟨_, by taint_decide⟩
theorem mlZeroHead_taint : TaintOk [.esp] (.block ((mlZero ++ faultBit).take 1)) := ⟨_, by taint_decide⟩
theorem mlZeroRest_taint : TaintOk [.esp, .esi] (.block ((mlZero ++ faultBit).drop 1)) := ⟨_, by taint_decide⟩
theorem accPut_taint : TaintOk [.esp, .ebp] (.block accPut) := ⟨_, by taint_decide⟩
theorem scanEnd_taint : TaintOk [.esp] (.block scanEnd) := ⟨_, by taint_decide⟩
theorem clrBuf_taint : TaintOk [.esp, .ebp] (.block (clrArgs oBuf 2048)) := ⟨_, by taint_decide⟩
theorem passSet_taint : TaintOk [.esp, .ebp] (.block passSet) := ⟨_, by taint_decide⟩
theorem okMask_taint : TaintOk [.esp, .ebp] (.block okMask) := ⟨_, by taint_decide⟩
theorem outSet_taint : TaintOk [.esp, .ebp] (.block outSet) := ⟨_, by taint_decide⟩
theorem outBody_taint : TaintOk [.esi, .edi, .ecx] (.block outBody) := ⟨_, by taint_decide⟩
theorem mlRest_taint : TaintOk [.esp, .esi] (.block ((mlSet (dShape 20)).drop 5)) := ⟨_, by taint_decide⟩
theorem decRet_taint : TaintOk [.esp, .ebp] (.block decRet) := ⟨_, by taint_decide⟩

end VG.Proof.RsaOaep.X86
