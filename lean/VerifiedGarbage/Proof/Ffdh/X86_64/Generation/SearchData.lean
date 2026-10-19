module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchContract
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Start

/-! # Public search inputs and the persistent native loop state -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Ffdh.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

structure SearchPublic where
  candidate : CandidateP
  control : Addr
  remaining : Nat

abbrev SearchPublic.c (p : SearchPublic) := p.candidate

def searchOfState (s : State) : SearchPublic :=
  ⟨candidateOfState s, stackArg s 3, (s.mem.readW (stackArg s 3) 64).toNat⟩

def SearchInput (p : SearchPublic) (s : State) : Prop := searchPre s ∧ searchOfState s = p

def SearchPublic.headers (p : SearchPublic) (used remaining : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 remaining), (1, BitVec.ofNat 64 p.c.k),
    (2, BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)),
    (5, p.c.op), (6, BitVec.ofNat 64 p.c.k), (7, p.c.up), (8, BitVec.ofNat 64 p.c.bits),
    (9, BitVec.ofNat 64 p.c.gen), (10, off p.c.rp used),
    (11, BitVec.ofNat 64 (p.c.rand.length - used)), (12, BitVec.ofNat 64 used),
    (13, p.c.B), (15, BitVec.ofNat 64 (p.c.Z / 8))]

/-- The original ABI snapshot is functional-proof data, not public data.
In particular its callee-saved registers may contain secrets. Only the
`SearchPublic` descriptor is shared between constant-time runs. -/
structure SearchLive (p : SearchPublic) (original : State) (used remaining : Nat) (s : State) : Prop where
  input : SearchInput p original
  used_le : used ≤ p.c.rand.length
  remaining_le : remaining ≤ p.remaining
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  rsp : s.gpr .rsp = p.c.sp
  r12 : s.gpr .r12 = p.control
  saved : ∀ r ∈ calleeSaved, r ≠ .r12 → s.gpr r = original.gpr r
  savedR12 : word s.mem p.control 32 = original.gpr .r12
  random : Spec.Rsa.bytesAt s.mem p.c.rp p.c.rand.length = p.c.rand
  headers : Slots s.mem p.control (p.headers used remaining)

end VG.Proof.Ffdh.X86_64.Generation
