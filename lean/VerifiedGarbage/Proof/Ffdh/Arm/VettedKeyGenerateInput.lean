module

public import VerifiedGarbage.Spec.Ffdh.VettedKeyGenerationContract
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts

import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeneratePre
import VerifiedGarbage.Proof.Framework.Arm.Exec
/-! The vetted attempt uses the same caller-owned buffers and stack frame,
with the reviewed group table added to readable regions. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SampleKeyGeneratePre.lean`, which only this module imported.
section

/-! Adding read-only constant tables preserves the existing key-attempt
input geometry. The proofs reuse the full-width caller's stack and buffer
facts; only readable regions grow. -/

section
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
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts)

theorem vettedKeyGenerate_pre {s : State}
    (pre : (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s) :
    (Spec.Ffdh.generateKeyContract abi 176).pre (stripConsts tableConsts s) ∧ ConstsOk tableConsts 176 s :=
  pre_consts.mp pre

theorem vettedKeyGenerate_input (s : State)
    (pre : (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s)
    {p : Inputs} {rb : List Byte}
    (base : stackArg s 5 = p.base) (privateValue : s.gpr .r0 = p.privateValue)
    (publicValue : s.gpr .r2 = p.publicValue) (domain : stackArg s 0 = p.domain)
    (count : (stackArg s 2).toNat = p.k) (capacity : (stackArg s 6).toNat = p.len)
    (entropy : stackArg s 3 = p.entropy) (outputY : p.output = p.publicValue) (privateLength : p.privateLength = p.k)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat = p.dom)
    (entropyBytes : Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k = rb) :
    KeyGenerateFnInput p rb s :=
  keyGenerate_input_stripConsts (keyGenerate_input (stripConsts tableConsts s)
    (vettedKeyGenerate_pre pre).1 base privateValue publicValue domain count capacity
    entropy outputY privateLength domainBytes entropyBytes)

theorem vettedKeyGenerate_data_base (s : State)
    (pre : (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s) :
    ∃ (p : Inputs) (rb : List Byte), stackArg s 5 = p.base ∧ s.gpr .r0 = p.privateValue ∧
      s.gpr .r2 = p.publicValue ∧ stackArg s 0 = p.domain ∧ (stackArg s 2).toNat = p.k ∧
      (stackArg s 6).toNat = p.len ∧ stackArg s 3 = p.entropy ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k = rb ∧ KeyGenerateFnInput p rb s := by
  obtain ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy,
    domainBytes, entropyBytes, input⟩ := keyGenerate_data (stripConsts tableConsts s) (vettedKeyGenerate_pre pre).1
  exact ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy,
    domainBytes, entropyBytes, keyGenerate_input_stripConsts input⟩

end VG.Proof.Ffdh.Arm
