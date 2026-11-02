module

public import VerifiedGarbage.Impl.Sha3.RISCV64.Stream
public import VerifiedGarbage.Impl.Sha3.RISCV64.Zero
public import VerifiedGarbage.Spec.Sha3.Contract

/-!
# SHAKE256 of pieces on RISC-V

As on PPC64LE (`Impl/Sha3/PPC64LE/Pieces.lean`), and as Ed448's whole
functions hash (`Impl/Ed448/RISCV64/Whole.lean`), for any output length:
`hash sc ps f o n` zeroes the Keccak state at `sc`, absorbs the pieces `ps`
one after the other, each from the position the previous one returned, pads
with SHAKE's suffix, and squeezes `n` bytes (`SHAKE256`, rate 136) to
`o(f)`, by calls of the verified sponge functions
(`Impl/Sha3/RISCV64/Stream.lean`), which take no working space but the 1168
bytes below the stack pointer. A piece is a pointer in a register plus an
offset, and a length: a constant, or a register.
-/

@[expose] public section

namespace VG.Impl.Sha3.RISCV64.Pieces

open VG.RISCV64
open VG.Impl.Sha3.RISCV64.Stream (mov)

/-- A piece's length: a constant, or a register. -/
inductive Len where
  | imm (n : Nat)
  | reg (r : Reg)

/-- `a4` set to the length. -/
def Len.set : Len → Instr
  | .imm n => .li .a4 n
  | .reg r => mov .a4 r

/-- A piece of the message: `off` bytes past the pointer in `base`. -/
structure Piece where
  base : Reg
  off : Nat
  len : Len

/-- `absorb(state = sc, rate = 136, pos, data, len)`: `pos` 0 for the first
piece, else the position the previous absorption returned. -/
def absorbArgs (sc : Reg) (first : Bool) (p : Piece) : List Instr :=
  [.addi .a3 p.base p.off, if first then .li .a2 0 else mov .a2 .a0, mov .a0 sc, .li .a1 136, p.len.set]

def callAbsorb : Prog isa := .call Spec.Sha3.absorbApi.name Impl.Sha3.RISCV64.Stream.absorb
def callPad : Prog isa := .call Spec.Sha3.padApi.name Impl.Sha3.RISCV64.Stream.pad
def callSqueeze : Prog isa := .call Spec.Sha3.squeezeApi.name Impl.Sha3.RISCV64.Stream.squeeze

/-- Absorbing the pieces `ps`. -/
def absorbs (sc : Reg) : Bool → List Piece → Prog isa
  | _, [] => .block []
  | first, p :: ps => .seq (.block (absorbArgs sc first p)) (.seq callAbsorb (absorbs sc false ps))

/-- `pad(state = sc, rate = 136, pos = a0, suffix = 0x1f)`. -/
def padArgs (sc : Reg) : List Instr := [mov .a2 .a0, mov .a0 sc, .li .a1 136, .li .a3 0x1f]

/-- `squeeze(state = sc, rate = 136, pos = 0, out = o(f), len = n)`. -/
def squeezeArgs (sc f : Reg) (o n : Nat) : List Instr :=
  [mov .a0 sc, .li .a1 136, .li .a2 0, .addi .a3 f o, .li .a4 n]

/-- `SHAKE256` of the concatenation of the pieces `ps`, `n` bytes, into `o(f)`. -/
def hash (sc : Reg) (ps : List Piece) (f : Reg) (o n : Nat) : Prog isa :=
  .seq (.block (Impl.Sha3.RISCV64.zeroState sc)) <| .seq (absorbs sc true ps) <| .seq (.block (padArgs sc)) <|
  .seq callPad <| .seq (.block (squeezeArgs sc f o n)) callSqueeze

end VG.Impl.Sha3.RISCV64.Pieces
