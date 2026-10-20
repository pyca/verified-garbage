module

import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeneratePre
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn

/-! Adding read-only constant tables preserves the existing key-attempt
input geometry. The proofs reuse the full-width caller's stack and buffer
facts; only readable regions grow. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

private theorem entered_stripConsts_read {K : List (String × List (BitVec 64))}
    {s : State} {a : Addr} {n : Nat}
    (h : InRegions ((entered (stripConsts K s)).rd ++ (entered (stripConsts K s)).wr) a n) :
    InRegions ((entered s).rd ++ (entered s).wr) a n := by
  obtain ⟨r, member, contains⟩ := h
  refine ⟨r, ?_, contains⟩
  rcases List.mem_append.mp member with read | write
  · exact List.mem_append_left _ (List.mem_of_mem_take read)
  · exact List.mem_append_right _ write

private theorem octets_entered_stripConsts {K : List (String × List (BitVec 64))}
    {s : State} {base src : BitVec 32} {len : Nat} {bs : List Byte}
    (h : Octets base src len bs (entered (stripConsts K s))) :
    Octets base src len bs (entered s) :=
  ⟨h.fits, entered_stripConsts_read h.readable, h.separate, h.bytes⟩

private theorem incoming_entered_stripConsts {K : List (String × List (BitVec 64))}
    {s : State} {value : BitVec 32} {d : Nat}
    (h : IncomingWord value d (entered (stripConsts K s))) :
    IncomingWord value d (entered s) :=
  ⟨h.fits, entered_stripConsts_read h.readable, h.word⟩

theorem keyGenerate_input_stripConsts {K : List (String × List (BitVec 64))}
    {s : State} {p : Inputs} {rb : List Byte}
    (h : KeyGenerateFnInput p rb (stripConsts K s)) : KeyGenerateFnInput p rb s := by
  refine ⟨⟨h.stackFits, ?_, ?_, h.privateValue, h.publicValue, h.outputY, h.privateLength,
    octets_entered_stripConsts h.entropy, h.size, h.entropyStack, ?_,
    h.entropySep, h.saved⟩, ?_, h.savedCall⟩
  · exact ⟨h.args.workspace.congr rfl, ⟨h.args.locals.space.congr rfl, h.args.locals.separate⟩, octets_entered_stripConsts h.args.domain,
      h.args.domainStack, h.args.saved⟩
  · exact ⟨incoming_entered_stripConsts h.incoming.domain,
      incoming_entered_stripConsts h.incoming.domainLength,
      incoming_entered_stripConsts h.incoming.count,
      incoming_entered_stripConsts h.incoming.entropy,
      incoming_entered_stripConsts h.incoming.scratch⟩
  · exact ⟨⟨h.outputs.privateBuffer.fits, h.outputs.privateBuffer.writable⟩,
      ⟨h.outputs.publicBuffer.fits, h.outputs.publicBuffer.writable⟩, h.outputs.privateDomain,
      h.outputs.publicDomain, h.outputs.privateStack, h.outputs.publicStack,
      h.outputs.privateWorkspace, h.outputs.publicWorkspace, h.outputs.separate⟩
  · exact ⟨⟨h.calls.stack.fit, h.calls.stack.separate⟩, h.calls.domain,
      h.calls.privateValue, h.calls.publicValue, h.calls.entropy, h.calls.privateFits⟩

end VG.Proof.Ffdh.Arm
