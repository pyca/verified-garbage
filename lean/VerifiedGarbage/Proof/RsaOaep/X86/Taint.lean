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

/-! ## MGF1 with its table -/

theorem tabArg15_taint : TaintOk [.esp, .ebp] (.block [ld .eax (arg 15), Impl.RsaPss.X86.st .eax sTab]) :=
  ⟨_, by taint_decide⟩
theorem tabArg23_taint : TaintOk [.esp, .ebp] (.block [ld .eax (arg 23), Impl.RsaPss.X86.st .eax sTab]) :=
  ⟨_, by taint_decide⟩
theorem tabArg17_taint : TaintOk [.esp, .ebp] (.block [ld .eax (arg 17), Impl.RsaPss.X86.st .eax sTab]) :=
  ⟨_, by taint_decide⟩
theorem tabArg24_taint : TaintOk [.esp, .ebp] (.block [ld .eax (arg 24), Impl.RsaPss.X86.st .eax sTab]) :=
  ⟨_, by taint_decide⟩

/-! ## The label's hash function's table -/

theorem tabSlot16_taint : TaintOk [.esp, .ebp] (.block (tabSlot 16)) := ⟨_, by taint_decide⟩
theorem tabSlot23_taint : TaintOk [.esp, .ebp] (.block (tabSlot 23)) := ⟨_, by taint_decide⟩
theorem lenArg16_taint : TaintOk [.esp] (.block [ld .edx (arg 16)]) := ⟨_, by taint_decide⟩
theorem lenArg23_taint : TaintOk [.esp] (.block [ld .edx (arg 23)]) := ⟨_, by taint_decide⟩
theorem lenWord_taint : TaintOk [.esp, .edx] (.block [.mov .edx (.mem (Impl.RsaPkcs1Sig.X86.at_ .edx 16))]) :=
  ⟨_, by taint_decide⟩
theorem cmpLens_taint : ∀ x ∈ lens, x < 2 ^ 32 ∧
    TaintOk [] (.block [.alu .cmp .edx (.imm (BitVec.ofNat 32 x))]) := by
  intro x hx
  simp only [lens, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, _, by taint_decide⟩

theorem tabHead_taint : TaintOk [.esp, .ebp, .eax]
    (.block (([.mov .eax (.mem (Impl.RsaPkcs1Sig.X86.at_ .eax 16)), Impl.RsaPss.X86.st .eax sHl] : List Instr) ++
      Impl.RsaPss.X86.mgfInit)) := ⟨_, by taint_decide⟩
theorem tload_taint : TaintOk [.esp, .ebp] (.block [ld .esi sTab]) := ⟨_, by taint_decide⟩
theorem tword_taint {k : Nat} (hk : k < 3) :
    TaintOk [.esp, .ebp, .esi] (.block [.mov .esi (.mem (Impl.RsaPkcs1Sig.X86.at_ .esi (4 * k)))]) := by
  rcases k with _ | _ | _ | k
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · omega
theorem xorSet_taint : TaintOk [.esp, .ebp] (.block xorSet) := ⟨_, by taint_decide⟩
theorem mgfNext_taint : TaintOk [.esp, .ebp] (.block mgfNext) := ⟨_, by taint_decide⟩

end VG.Proof.RsaOaep.X86
