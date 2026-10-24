module

public import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Sample

/-!
# SHAKE256 of pieces on PPC64LE

As Ed448's whole functions hash (`Impl/Ed448/PPC64LE/Whole.lean`), for any
output length: `hash sc ps f o n` zeroes the Keccak state at `sc` (as
ML-KEM's do), absorbs the pieces `ps` one after the other, each from the
position the previous one returned, pads with SHAKE's suffix, and squeezes
`n` bytes (`SHAKE256`, rate 136) to `o(f)`, by calls of the verified sponge
functions (`Impl/Sha3/PPC64LE/Stream.lean`), with their working space at
`200(sc)`. A piece is a pointer in a register plus an offset, and a length:
a constant, or a register.
-/

@[expose] public section

namespace VG.Impl.Sha3.PPC64LE.Pieces

open VG.PPC64LE
open VG.Impl.Sha3.PPC64LE.Stream (mov)

/-- Where in the scratch space the sponge functions' working space is. -/
def KW : Nat := 200

/-- A piece's length: a constant, or a register. -/
inductive Len where
  | imm (n : Nat)
  | reg (r : Reg)

/-- `r7` set to the length. -/
def Len.set : Len → Instr
  | .imm n => .li .r7 n
  | .reg r => mov .r7 r

/-- A piece of the message: `off` bytes past the pointer in `base`. -/
structure Piece where
  base : Reg
  off : Nat
  len : Len

/-- `absorb(state = sc, rate = 136, pos, data, len, sc + 200)`: `pos` 0 for the
first piece, else the position the previous absorption returned. -/
def absorbArgs (sc : Reg) (first : Bool) (p : Piece) : List Instr :=
  [if first then .li .r5 0 else mov .r5 .r3, mov .r3 sc, .li .r4 136, .addi .r6 p.base p.off, p.len.set,
    .addi .r8 sc KW]

def callAbsorb : Prog isa := .call "vg_keccak_absorb_scratch" Impl.Sha3.PPC64LE.Stream.absorb
def callPad : Prog isa := .call "vg_keccak_pad_scratch" Impl.Sha3.PPC64LE.Stream.pad
def callSqueeze : Prog isa := .call "vg_keccak_squeeze_scratch" Impl.Sha3.PPC64LE.Stream.squeeze

/-- Absorbing the pieces `ps`. -/
def absorbs (sc : Reg) : Bool → List Piece → Prog isa
  | _, [] => .block []
  | first, p :: ps => .seq (.block (absorbArgs sc first p)) (.seq callAbsorb (absorbs sc false ps))

/-- `pad(state = sc, rate = 136, pos = r3, suffix = 0x1f, sc + 200)`. -/
def padArgs (sc : Reg) : List Instr := [mov .r5 .r3, mov .r3 sc, .li .r4 136, .li .r6 0x1f, .addi .r7 sc KW]

/-- `squeeze(state = sc, rate = 136, pos = 0, out = o(f), len = n, sc + 200)`. -/
def squeezeArgs (sc f : Reg) (o n : Nat) : List Instr :=
  [mov .r3 sc, .li .r4 136, .li .r5 0, .addi .r6 f o, .li .r7 n, .addi .r8 sc KW]

/-- `SHAKE256` of the concatenation of the pieces `ps`, `n` bytes, into `o(f)`. -/
def hash (sc : Reg) (ps : List Piece) (f : Reg) (o n : Nat) : Prog isa :=
  .seq (.block (Impl.MlKem.PPC64LE.zeroState sc)) <| .seq (absorbs sc true ps) <| .seq (.block (padArgs sc)) <|
  .seq callPad <| .seq (.block (squeezeArgs sc f o n)) callSqueeze

end VG.Impl.Sha3.PPC64LE.Pieces
