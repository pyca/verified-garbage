module

public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Round
public import VerifiedGarbage.Impl.Sha3.AArch64.RoundConstants
public import VerifiedGarbage.Impl.Sha3.AArch64.Callee

/-!
# Keccak-f[1600] on AArch64, in general registers

`core` (the internal function `vg_keccak_f1600_lanes`) is the 24 rounds on
the lanes in their registers (`Round.lean`), with 24 bytes of working space at
`x28` for the spilled lanes. `x16`, `x17` and `x30` are its free registers, so
its return address is in `v27` while it runs, and the address of the table of
round constants in `v28`: `umov` then costs no integer unit.

The functions around it keep the callee-saved registers in `v16–v26` and
their own arguments in further vector registers, so that all the general
registers they may use are the lanes' and `core`'s:

* `permute(state = x0, scratch = x1)`, the permutation;
* `absorbBlocks(state = x0, rate = x1, data = x2, len = x3, scratch = x4)`,
  which absorbs all of `data`'s whole blocks (at least one) with the state in
  registers throughout, and returns the number of bytes left.
-/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Scalar

open VG.AArch64
open VG.Impl.Sha3.AArch64.RoundConstants (rcs sym)

/-- The lanes spilled to memory at `x28`. -/
def conf : Conf where
  temps := [.x16, .x17, .x30]
  lazy := true
  sp := ⟨fun k r => .str .x r .x28 (8 * k), fun k r => .ldr .x r .x28 (8 * k)⟩

/-- ι of round `r`. -/
def iota (r : Nat) : List Instr :=
  [.umov .x .x16 .v28 0, .ldrTbl .x .x16 .x16 (8 * r) sym rcs, .logic .eor .x .x0 .x0 .x16]

/-- Round `r`. -/
def fullRound (r : Nat) : List Instr := conf.round (r % 2) ++ iota r

/-- The 24 rounds, as a function. -/
def coreCode : List Instr :=
  ([.vop (.dup .d2 .v27 .x30), .adrSym .x16 sym, .vop (.dup .d2 .v28 .x16)] : List Instr) ++
  (List.range 24).flatMap fullRound ++ ([.umov .x .x30 .v27 0] : List Instr)

def core : Prog isa := .block coreCode

def coreName : String := "vg_keccak_f1600_lanes"

def callCore : Prog isa := .call coreName core

/-- The callee-saved registers the code writes. -/
def savedReg (i : Nat) : Reg :=
  [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30].getD i .x19

/-- Where register `i` of them is kept. -/
def savedVec (i : Nat) : VReg :=
  [VReg.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26].getD i .v16

def save : List Instr := (List.range 11).map fun i => .vop (.dup .d2 (savedVec i) (savedReg i))
def restore : List Instr := (List.range 11).map fun i => .umov .x (savedReg i) (savedVec i) 0

/-- Load lane `i` from `[b, #off]`, pending its rotation. -/
def loadLane (b : Reg) (i off : Nat) : List Instr :=
  ([.ldr .x (lreg i) b off] : List Instr) ++ if pend i = 0 then [] else [.ror .x (lreg i) (lreg i) (pend i)]

/-- Store lane `i` at `[b, #off]`. -/
def storeLane (b : Reg) (i off : Nat) : List Instr :=
  (if pend i = 0 then [] else [.ror .x (lreg i) (lreg i) (64 - pend i)]) ++ ([.str .x (lreg i) b off] : List Instr)

/-- Load the state at `b`, whose lane `i` is at `stride i + off`. -/
def load (b : Reg) (stride off : Nat) : List Instr := (List.range 25).flatMap fun i => loadLane b i (stride * i + off)

/-- Store it. -/
def store (b : Reg) (stride off : Nat) : List Instr := (List.range 25).flatMap fun i => storeLane b i (stride * i + off)

/-- The permutation: `v29` and `v30` hold `state` and `scratch`. -/
def permute : Prog isa :=
  .seq (.block (save ++ [.vop (.dup .d2 .v29 .x0), .vop (.dup .d2 .v30 .x1), .umov .x .x16 .v29 0] ++ load .x16 8 0 ++
    ([.umov .x .x28 .v30 0] : List Instr)))
  (.seq callCore (.block (([.umov .x .x16 .v29 0] : List Instr) ++ store .x16 8 0 ++ restore)))

/-- Lane `i` of the data at `x16` XORed into the state. -/
def xorLane (i : Nat) : List Instr := [.ldr .x .x17 .x16 (8 * i), eor (lreg i) (lreg i) .x17 (pend i)]

/-- Lanes `a … b - 1` of the data. -/
def xorLanes (a b : Nat) : List Instr := (List.range (b - a)).flatMap fun k => xorLane (a + k)

/-- Skip `c` if the rate (in `v0`) is `rate`. -/
def unlessRate (rate : Nat) (c : Prog isa) : Prog isa :=
  .seq (.block [.umov .x .x17 .v0 0, .subImm .x .x17 .x17 rate]) (.ite (.zero .x .x17) (.block []) c)

/-- A block of the data at `x16` XORed into the state, `v0` holding the rate. -/
def xorBlock : Prog isa :=
  .seq (.block (xorLanes 0 9))
  (unlessRate 72 (.seq (.block (xorLanes 9 13))
  (unlessRate 104 (.seq (.block (xorLanes 13 17))
  (unlessRate 136 (.seq (.block (xorLanes 17 18))
  (unlessRate 144 (.block (xorLanes 18 21)))))))))

/-- A block absorbed: `v1` holds the pointer to the data left, `v2` its length;
then `x17` is zero if another whole block is left. -/
def absorbStep : Prog isa :=
  .seq (.block [.umov .x .x16 .v1 0])
  (.seq xorBlock
  (.seq (.block [.umov .x .x16 .v1 0, .umov .x .x17 .v0 0, .add .x .x16 .x16 .x17, .vop (.dup .d2 .v1 .x16),
      .umov .x .x28 .v30 0])
  (.seq callCore
    (.block [.umov .x .x16 .v2 0, .umov .x .x17 .v0 0, .sub .x .x16 .x16 .x17, .vop (.dup .d2 .v2 .x16),
      .sub .x .x17 .x16 .x17, .lsr .x .x17 .x17 63]))))

def absorbBlocks : Prog isa :=
  .seq (.block (save ++ [.vop (.dup .d2 .v29 .x0), .vop (.dup .d2 .v30 .x4), .vop (.dup .d2 .v0 .x1),
    .vop (.dup .d2 .v1 .x2), .vop (.dup .d2 .v2 .x3), .umov .x .x16 .v29 0] ++ load .x16 8 0))
  (.seq (.loop absorbStep (.zero .x .x17))
    (.block (([.umov .x .x16 .v29 0] : List Instr) ++ store .x16 8 0 ++ restore ++ ([.umov .x .x0 .v2 0] : List Instr))))

/-- The sponge's callee. -/
def callee : Callee where
  name := "vg_keccak_f1600"
  code := permute
  suffix := ""
  clear := Callee.generalClear
  blocks := some ("vg_keccak_absorb_blocks", absorbBlocks)

end VG.Impl.Sha3.AArch64.Scalar
