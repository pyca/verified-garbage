module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Decrypt
public import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Decrypt
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # RSAES-PKCS1-v1_5 decryption on x86: the pieces the taint analysis checks

Each straight-line piece of decryption, and the bodies of its loops, from
states in which only the registers given are public: the stack pointer,
and the pointers and counters that a stage of the proof fixes
(`Proof/RsaPkcs1Enc/X86/DecBody.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt
open VG.X86 hiding frameBytes

/-- The taint analysis proves `c` constant time from states that agree on `rs`. -/
abbrev TaintOk (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check VG.X86.taint (τr rs) c hc).isSome = true

theorem privArgs_taint : TaintOk [.esp] (.block privArgs) := ⟨_, by taint_decide⟩
theorem dZero_taint : TaintOk [.esp] (.block (saveR ++ dZero)) := ⟨_, by taint_decide⟩
theorem zeroLoop_taint : TaintOk [.esi, .ecx] zeroLoop := ⟨_, by taint_decide⟩
theorem dCopy_taint : TaintOk [.esp] (.block dCopy) := ⟨_, by taint_decide⟩
theorem copyBytes_taint : TaintOk [.esi, .ebx, .ecx] Impl.Bignum.X86.copyBytes := ⟨_, by taint_decide⟩
theorem shaInitArgs_taint : TaintOk [.esp] (.block shaInitArgs) := ⟨_, by taint_decide⟩
theorem shaUpdArgs_taint : TaintOk [.esp] (.block shaUpdArgs) := ⟨_, by taint_decide⟩
theorem shaFinArgs_taint : TaintOk [.esp] (.block shaFinArgs) := ⟨_, by taint_decide⟩
theorem macInitDH_taint : TaintOk [.esp] (.block (macInitArgs sDH)) := ⟨_, by taint_decide⟩
theorem macInitKDK_taint : TaintOk [.esp] (.block (macInitArgs sKDK)) := ⟨_, by taint_decide⟩
theorem kdkUpdArgs_taint : TaintOk [.esp] (.block kdkUpdArgs) := ⟨_, by taint_decide⟩
theorem kdkFinArgs_taint : TaintOk [.esp] (.block kdkFinArgs) := ⟨_, by taint_decide⟩
theorem msgPtr_taint : TaintOk [.esp] (.block msgPtr) := ⟨_, by taint_decide⟩
theorem msgCL_taint : TaintOk [.ebx] (.block (msgBytes lengthLabel clLen)) := ⟨_, by taint_decide⟩
theorem msgAM_taint : TaintOk [.ebx] (.block (msgBytes messageLabel amLen)) := ⟨_, by taint_decide⟩
theorem prfUpdCL_taint : TaintOk [.esp] (.block (prfUpdArgs (lengthLabel.length + 4))) := ⟨_, by taint_decide⟩
theorem prfUpdAM_taint : TaintOk [.esp] (.block (prfUpdArgs (messageLabel.length + 4))) := ⟨_, by taint_decide⟩
theorem prfFinCL_taint : TaintOk [.esp] (.block (prfFinArgs (lengthLabel.length + 4) sCL)) := ⟨_, by taint_decide⟩
theorem prfFinAM_taint : TaintOk [.esp] (.block (prfFinArgs (messageLabel.length + 4) sAM)) := ⟨_, by taint_decide⟩
theorem incr_taint : TaintOk [.esp] (.block incr) := ⟨_, by taint_decide⟩
theorem clInit_taint : TaintOk [.esp] (.block clInit) := ⟨_, by taint_decide⟩
theorem amInit_taint : TaintOk [.esp] (.block amInit) := ⟨_, by taint_decide⟩
theorem maskInit_taint : TaintOk [.esp] (.block maskInit) := ⟨_, by taint_decide⟩
theorem maskBody_taint : TaintOk [.eax, .ecx] (.block maskBody) := ⟨_, by taint_decide⟩
theorem alInit_taint : TaintOk [.esp] (.block alInit) := ⟨_, by taint_decide⟩
theorem alBody_taint : TaintOk [.esi, .ecx] (.block alBody) := ⟨_, by taint_decide⟩
theorem alSave_taint : TaintOk [.esp] (.block alSave) := ⟨_, by taint_decide⟩
theorem scanInit_taint : TaintOk [.esp] (.block scanInit) := ⟨_, by taint_decide⟩
theorem scanBody_taint : TaintOk [.esi, .ecx] (.block scanBody) := ⟨_, by taint_decide⟩
theorem validHead_taint : TaintOk [.esp] (.block (validBlock.take 1)) := ⟨_, by taint_decide⟩
theorem validRest_taint : TaintOk [.esp, .esi] (.block (validBlock.drop 1)) := ⟨_, by taint_decide⟩
theorem mlHead_taint : TaintOk [.esp] (.block (mlStore.take 1)) := ⟨_, by taint_decide⟩
theorem mlRest_taint : TaintOk [.esi] (.block (mlStore.drop 1)) := ⟨_, by taint_decide⟩
theorem selInit_taint : TaintOk [.esp] (.block selInit) := ⟨_, by taint_decide⟩
theorem selBody_taint : TaintOk [.esp, .esi, .edi, .ecx] (.block selBody) := ⟨_, by taint_decide⟩
theorem fin_taint : TaintOk [.esp] (.block fin) := ⟨_, by taint_decide⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
