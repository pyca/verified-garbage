module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract

/-!
# A candidate for an RSA prime on x86-64: the shared contract implies `candContract`
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64

/-- A state meeting the precondition: a 32-byte prime, a one-byte `e`, no
`p`, no randomness, the stack arguments at `0x6008`. -/
def candSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 32 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .r9 => 0x4000
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6021 then 0x80 else if a = 0x6028 then 0x20 else if a = 0x6029 then 0x02 else 0
  rd := [⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0, 0⟩, ⟨0x6008, 40⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 8⟩, ⟨0x8000, 4352⟩]

theorem stackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4] := rfl

end VG.Proof.RsaKeyGen.X86_64
