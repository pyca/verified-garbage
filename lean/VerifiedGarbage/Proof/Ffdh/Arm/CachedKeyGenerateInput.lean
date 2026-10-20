module

import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateLift
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeneratePre
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateFn
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateFn

/-! The extended signature supplies the cached attempt's native input record. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm VG.Proof.Mont

theorem cachedKeyGenerate_input (s : State)
    (pre : (Spec.Ffdh.cachedGenerateKeyContract abi 176).pre s) {p : Inputs} {rb : List Byte}
    (base : stackArg s 5=p.base) (privateValue : s.gpr .r0=p.privateValue)
    (publicValue : s.gpr .r2=p.publicValue) (domain : stackArg s 0=p.domain)
    (count : (stackArg s 2).toNat=p.k) (capacity : (stackArg s 6).toNat=p.len)
    (entropy : stackArg s 3=p.entropy) (cachePointer : stackArg s 7=p.cachedContext)
    (outputY : p.output=p.publicValue) (privateLength : p.privateLength=p.k)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat=p.dom)
    (entropyBytes : Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k=rb) :
    CachedKeyGenerateFnInput p rb s := by
  have plain := cachedKeyGenerate_plain_pre s pre
  have inputPlain := keyGenerate_input (cachedPlainState s) plain base privateValue publicValue domain count capacity
    entropy outputY privateLength domainBytes entropyBytes
  sig_pre [Spec.Ffdh.cachedGenerateKeyContract,Spec.Ffdh.cachedGenerateKeySig,Spec.Ffdh.generateKeySig,
    abi,argRegs,reduceClassify,Loc.val,State.addr] at pre
  obtain ⟨stackFit,argFit,rd,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_stackArgs,_⟩ := pre
  have input := cachedKeyGenerate_lift rd inputPlain
  have cache : IncomingWord p.cachedContext 156 (entered s) := by
    have address : stackArgAddr s 7=off (State.addr s.sp) 28 := VG.Arm.addr_add (by omega)
    have argSub : (⟨stackArgAddr s 7,4⟩ : Region).Sub ⟨stackArgAddr s 0,36⟩ := by
      rw [show stackArgAddr s 0=State.addr s.sp from by simp [stackArgAddr],address]
      exact Offset.sub_base _ (by decide)
    apply enteredIncoming s (i:=7) (by omega) (by omega)
    · refine ⟨⟨stackArgAddr s 0,36⟩,List.mem_append_left _ (by rw [rd]; simp),?_⟩
      rw [show stackArgAddr s 0=State.addr s.sp from by simp [stackArgAddr],address]
      exact Offset.contains_base _ (by decide) (by decide)
    · rw [belowA,addr_sub' (by omega : 128≤s.sp.toNat)]
      exact (_stackArgs.sub_left (Offset.below_mono _ (by decide : 128≤176) (by decide))).sub_right argSub
    · exact cachePointer
  exact ⟨input,cache⟩

end VG.Proof.Ffdh.Arm
