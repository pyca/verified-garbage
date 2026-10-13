module

public import VerifiedGarbage.Impl.X25519.X86

/-! Expand an unsigned scalar at esi into one byte per bit, at edi+7168: a loop over its bytes
(counted by `ecx`), each byte's eight bits to `[edx]`, …, `[edx + 7]`. Only the pointers
affect the addresses; bytes is 32 for scalarbase and 64 for challenge. -/

@[expose] public section

namespace VG.Impl.Ed25519.X86
open VG.X86 VG.Impl.X25519.X86

/-- Bit `j` of the byte at `esi`, to the byte at `edx + j`. -/
def expandBit (j : Nat) : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .alu .add .eax (.reg .eax),
    .shift .shr .eax (j + 1), .alu .and .eax (.imm 1), .store8 (at_ .edx j) .al]

/-- The eight bits of the byte at `esi`, and on to the next byte. -/
def expandByte : List Instr :=
  (List.range 8).flatMap expandBit ++ [.alu .add .esi (.imm 1), .alu .add .edx (.imm 8), .alu .sub .ecx (.imm 1)]

def expandScalarBits (bytes : Nat) : Prog isa :=
  .seq (.block [.mov .edx (.reg .edi), .alu .add .edx (.imm 7168), .mov .ecx (.imm (BitVec.ofNat 32 bytes))])
    (.loop (.block expandByte) .ne)
end VG.Impl.Ed25519.X86
