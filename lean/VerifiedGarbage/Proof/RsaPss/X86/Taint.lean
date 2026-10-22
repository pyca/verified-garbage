module

public import VerifiedGarbage.Proof.RsaPss.X86.Hash
meta import VerifiedGarbage.Proof.RsaPss.X86.Hash

/-! # RSASSA-PSS on x86: the taint checks of the pieces that do not depend on the hash function

Each block from states in which only `esp` and `ebp` are known to agree,
and each loop body from states in which its pointers and its count agree
(`Proof/RsaPss/X86/Hash.lean` has those of the pieces whose immediates depend
on the hash function).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86 VG.Impl.RsaPss.X86

theorem initArgs_taint : TaintOk [.esp, .ebp] (.block initArgs) := ⟨_, by taint_decide⟩
theorem compInit_taint : TaintOk [.esp, .ebp] (.block compInit) := ⟨_, by taint_decide⟩
theorem compNext_taint : TaintOk [.esp, .ebp] (.block compNext) := ⟨_, by taint_decide⟩
theorem mgfInit_taint : TaintOk [.esp, .ebp] (.block mgfInit) := ⟨_, by taint_decide⟩
theorem topSet_taint : TaintOk [.esp, .ebp] (.block topSet) := ⟨_, by taint_decide⟩
theorem topAnd_taint : TaintOk [.esp, .esi] (.block topAnd) := ⟨_, by taint_decide⟩
theorem clrY2048_taint : TaintOk [.esp, .ebp] (.block (clrArgs oY 2048)) := ⟨_, by taint_decide⟩
theorem signChk_taint : TaintOk [.esp] (.block signChk) := ⟨_, by taint_decide⟩
theorem failArgs_taint : TaintOk [.esp] (.block [ld .esi (arg 0), ld .ecx (arg 3), mi .eax 0]) :=
  ⟨_, by taint_decide⟩
theorem clrEm_taint : TaintOk [.esp, .ebp] (.block clrEm) := ⟨_, by taint_decide⟩
theorem oneSet_taint : TaintOk [.esp, .ebp] (.block oneSet) := ⟨_, by taint_decide⟩
theorem put1_taint : TaintOk [.esp, .ebx] (.block put1) := ⟨_, by taint_decide⟩
theorem bcSet_taint : TaintOk [.esp, .ebp] (.block bcSet) := ⟨_, by taint_decide⟩
theorem putBc_taint : TaintOk [.esi] (.block putBc) := ⟨_, by taint_decide⟩
theorem privArgs_taint : TaintOk [.esp, .ebp] (.block privArgs) := ⟨_, by taint_decide⟩
theorem verifyChk_taint : TaintOk [.esp] (.block verifyChk) := ⟨_, by taint_decide⟩
theorem pubArgs_taint : TaintOk [.esp, .ebp] (.block pubArgs) := ⟨_, by taint_decide⟩
theorem accSet_taint : TaintOk [.esp, .ebp] (.block accSet) := ⟨_, by taint_decide⟩
theorem acc0_taint : TaintOk [.esp, .esi, .edi, .ebx] (.block acc0) := ⟨_, by taint_decide⟩
theorem scanSet_taint : TaintOk [.esp, .ebp] (.block scanSet) := ⟨_, by taint_decide⟩
theorem posChk_taint : TaintOk [.esp] (.block posChk) := ⟨_, by taint_decide⟩
theorem shInit_taint : TaintOk [.esp, .ebp] (.block shInit) := ⟨_, by taint_decide⟩
theorem passNext_taint : TaintOk [.esp, .ebp] (.block passNext) := ⟨_, by taint_decide⟩
theorem result_taint : TaintOk [.esp, .ebp] (.block result) := ⟨_, by taint_decide⟩
theorem ret0_taint : TaintOk [.esp, .ebp] (.block [mi .eax 0]) := ⟨_, by taint_decide⟩

theorem selBody_taint : TaintOk [.esi, .edi, .ecx] (.block selBody) := ⟨_, by taint_decide⟩
theorem xorBody_taint : TaintOk [.esi, .edi, .ecx] (.block xorBody) := ⟨_, by taint_decide⟩
theorem scanBody_taint : TaintOk [.esp, .esi, .edi, .ecx] (.block scanBody) := ⟨_, by taint_decide⟩
theorem passBody_taint : TaintOk [.esi, .edi, .ecx] (.block passBody) := ⟨_, by taint_decide⟩
theorem cmpBody_taint : TaintOk [.esi, .edi, .ecx] (.block cmpBody) := ⟨_, by taint_decide⟩
theorem zeroLoop_taint : TaintOk [.esi, .ecx] zeroLoop := ⟨_, by taint_decide⟩
theorem copy_taint : TaintOk [.esi, .ebx, .ecx] Impl.Bignum.X86.copyBytes := ⟨_, by taint_decide⟩

end VG.Proof.RsaPss.X86
