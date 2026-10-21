module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGeneratePre
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Appending the immutable context only enlarges the attempt's readable memory. -/

@[expose] public section
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
