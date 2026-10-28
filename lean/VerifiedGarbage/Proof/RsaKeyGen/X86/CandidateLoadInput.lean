module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
public import VerifiedGarbage.TCB.X86.State

/-! # The candidate body draws exactly its first entropy block -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

def candidateValue (E : Environment) (entropy : List Byte) : Nat :=
  Spec.RsaKeyGen.candidate (8 * E.length) (Spec.Rsa.os2ip (entropy.take E.length))

structure Drawn (E : Environment) (eBytes pBytes entropy : List Byte) (s : State) : Prop where
  input : Input E eBytes pBytes entropy s
  candidate : val32 s.mem E.base (slot E.width 0) (2 * E.width) = candidateValue E entropy
  used : w32 s.mem E.base 152 = E.length
  zeros : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0

end VG.Proof.RsaKeyGen.X86.Candidate
