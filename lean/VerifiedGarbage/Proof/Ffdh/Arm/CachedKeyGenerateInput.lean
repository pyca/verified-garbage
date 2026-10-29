module

public import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateFn
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract

import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeneratePre
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGeneratePre
/-! The extended signature supplies the cached attempt's native input record. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedKeyGenerateLift.lean`, which only this module imported.
section

/-! Appending the immutable context only enlarges the attempt's readable memory. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

private theorem plainRead {s : State} {a : Addr} {n : Nat}
    (rd : s.rd=[⟨State.addr (stackArg s 0),(stackArg s 1).toNat⟩,
      ⟨State.addr (stackArg s 3),(stackArg s 4).toNat⟩,
      ⟨State.addr (stackArg s 7),(stackArg s 8).toNat*8⟩,⟨stackArgAddr s 0,36⟩])
    (h : InRegions ((entered (cachedPlainState s)).rd++(entered (cachedPlainState s)).wr) a n) :
    InRegions ((entered s).rd++(entered s).wr) a n := by
  obtain ⟨r,member,contains⟩ := h
  rcases List.mem_append.mp member with read|write
  · change r∈[⟨State.addr (stackArg s 0),(stackArg s 1).toNat⟩,
      ⟨State.addr (stackArg s 3),(stackArg s 4).toNat⟩,⟨stackArgAddr s 0,28⟩] at read
    simp only [List.mem_cons,List.not_mem_nil,or_false] at read
    rcases read with rfl|rfl|rfl
    · exact ⟨_,List.mem_append_left _ (by change _∈s.rd; rw [rd]; simp),contains⟩
    · exact ⟨_,List.mem_append_left _ (by change _∈s.rd; rw [rd]; simp),contains⟩
    · refine ⟨⟨stackArgAddr s 0,36⟩,List.mem_append_left _ (by change _∈s.rd; rw [rd]; simp),?_⟩
      simp only [Region.Contains] at contains ⊢
      omega
  · exact ⟨r,List.mem_append_right _ write,contains⟩

theorem cachedKeyGenerate_lift {s : State} {p : Inputs} {rb : List Byte}
    (rd : s.rd=[⟨State.addr (stackArg s 0),(stackArg s 1).toNat⟩,
      ⟨State.addr (stackArg s 3),(stackArg s 4).toNat⟩,
      ⟨State.addr (stackArg s 7),(stackArg s 8).toNat*8⟩,⟨stackArgAddr s 0,36⟩])
    (h : KeyGenerateFnInput p rb (cachedPlainState s)) : KeyGenerateFnInput p rb s := by
  have octets {base src : BitVec 32} {len : Nat} {bs : List Byte}
      (v : Octets base src len bs (entered (cachedPlainState s))) : Octets base src len bs (entered s) :=
    ⟨v.fits,plainRead rd v.readable,v.separate,v.bytes⟩
  have incoming {value : BitVec 32} {d : Nat}
      (v : IncomingWord value d (entered (cachedPlainState s))) : IncomingWord value d (entered s) :=
    ⟨v.fits,plainRead rd v.readable,v.word⟩
  refine ⟨⟨h.stackFits,?_,?_,h.privateValue,h.publicValue,h.outputY,h.privateLength,
    octets h.entropy,h.size,h.entropyStack,?_,h.entropySep,h.saved⟩,?_,h.savedCall⟩
  · exact ⟨h.args.workspace.congr rfl,⟨h.args.locals.space.congr rfl,h.args.locals.separate⟩,
      octets h.args.domain,h.args.domainStack,h.args.saved⟩
  · exact ⟨incoming h.incoming.domain,incoming h.incoming.domainLength,incoming h.incoming.count,
      incoming h.incoming.entropy,incoming h.incoming.scratch⟩
  · exact ⟨⟨h.outputs.privateBuffer.fits,h.outputs.privateBuffer.writable⟩,
      ⟨h.outputs.publicBuffer.fits,h.outputs.publicBuffer.writable⟩,h.outputs.privateDomain,
      h.outputs.publicDomain,h.outputs.privateStack,h.outputs.publicStack,
      h.outputs.privateWorkspace,h.outputs.publicWorkspace,h.outputs.separate⟩
  · exact ⟨⟨h.calls.stack.fit,h.calls.stack.separate⟩,h.calls.domain,h.calls.privateValue,
      h.calls.publicValue,h.calls.entropy,h.calls.privateFits⟩

end VG.Proof.Ffdh.Arm
end

end

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
