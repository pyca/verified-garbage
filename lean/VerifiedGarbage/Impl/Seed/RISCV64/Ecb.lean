module

public import VerifiedGarbage.Impl.Seed.RISCV64.G16
public import VerifiedGarbage.Impl.Words.RISCV64
public import VerifiedGarbage.Impl.Words64.RISCV64
public import VerifiedGarbage.Spec.Seed

/-!
# SEED ECB on RISC-V

`vg_seed_ecb_{en,de}crypt(schedule = a0, data = a1, n = a2, scratch = a3)`.
As on PPC64LE (`Impl/Seed/PPC64LE/Ecb.lean`): sixteen blocks at a time
(fewer in the last batch), each round's three `G`s computed for all of them
at once by `g16`. The scratch buffer (moved to `a5`, the base `g16` uses)
holds `g16`'s slots, the blocks' state as four arrays of sixteen 32-bit
words, one per word of the block (`L0`, `L1`, `R0`, `R1`:
`arrSlot 0 … arrSlot 3`), the intermediate arrays `a`, `c` and `d` of the
round function, the masks of `g16`'s linear layers (from slot `kSlot`,
built once by `buildMasks`, and pointed to by `a3`), and the callee-saved
registers `s0`–`s11`, which `g16` uses.

* A batch copies its blocks' big-endian words, a byte at a time (the
  contract states no alignment for the data), into the arrays, and back the
  same way; lanes past the batch hold whatever they held, and their results
  are not stored.
* A round loads its two round keys, little-endian a byte at a time, and
  computes, lane by lane, `a = R0 ⊕ K0` and `a ⊕ R1 ⊕ K1`; `c = G` of that;
  `c + a`; `d = G` of that; `d + c`; `e = G` of that; and `L0 ⊕ (e + d)`
  and `L1 ⊕ e`, which become the new `R0` and `R1` as the halves are
  exchanged (`swapHalves`). After sixteen rounds, the halves are exchanged
  once too often, so the copy out takes `R` first. The sums are 64-bit
  `add`s of the zero-extended words, of which `sw` keeps the low 32 bits.
* Encryption steps through the round keys from the first, decryption from
  the last (`keyStart`); the key pointer is moved back after the sixteen
  rounds.
* The key pointer (`a0`), the data pointer (`a1`), the blocks left (`a2`),
  the masks' pointer (`a3`) and the rounds left (`a4`) stay in registers that
  `g16` does not write. Every address and branch depends only on them, the
  scratch base and the copy loops' cursors and counter (`t2`, `t3`, `t4`).
-/

@[expose] public section

namespace VG.Impl.Seed.RISCV64

open VG.RISCV64 VG.Impl.Aes.RISCV64 VG.Impl.Words.RISCV64
open VG.Spec.Seed (Direction)

/-! ## Scratch slots -/

/-- The arrays of `a`, `c` and `d`. -/
def aSlot : Nat := 48
def cSlot : Nat := 56
def dSlot : Nat := 64
/-- The array of word `w` of the blocks: `L0`, `L1`, `R0`, `R1`. -/
def arrSlot (w : Nat) : Nat := 72 + 8 * w
/-- The callee-saved registers and their slots. -/
def seedSaved : List (Reg × Nat) :=
  [(.s0, 117), (.s1, 118), (.s2, 119), (.s3, 120), (.s4, 121), (.s5, 122), (.s6, 123),
   (.s7, 124), (.s8, 125), (.s9, 126), (.s10, 127), (.s11, 128)]

/-- The scratch buffer's size, in slots. -/
def scratchSlots : Nat := 129

/-! ## 32-bit lanes -/

/-- Lane `b` of the array starting at slot `k`, as a byte offset. -/
def laneOff (k b : Nat) : Nat := 8 * k + 4 * b

def ldW (d : Reg) (k b : Nat) : Instr := .load .w d sb (laneOff k b)
def stW (k b : Nat) (r : Reg) : Instr := .store .w r sb (laneOff k b)
def addW (d n m : Reg) : Instr := .add d n m

/-- The round keys `K0` and `K1`, during a round's first step. -/
def k0R : Reg := .t5
def k1R : Reg := .t6

/-! ## A round -/

def step1 (b : Nat) : List Instr :=
  [ldW t0 (arrSlot 2) b, xorR t0 t0 k0R, stW aSlot b t0, ldW t1 (arrSlot 3) b,
   xorR t0 t0 t1, xorR t0 t0 k1R, stW (tSlot 0) b t0]

/-- `c := G(…)`, `T := c + a`. -/
def step2 (b : Nat) : List Instr :=
  [ldW t0 (tSlot 0) b, stW cSlot b t0, ldW t1 aSlot b, addW t0 t0 t1, stW (tSlot 0) b t0]

/-- `d := G(…)`, `T := d + c`. -/
def step3 (b : Nat) : List Instr :=
  [ldW t0 (tSlot 0) b, stW dSlot b t0, ldW t1 cSlot b, addW t0 t0 t1, stW (tSlot 0) b t0]

/-- `e := G(…)`, `L1 := L1 ⊕ e`, `L0 := L0 ⊕ (e + d)`. -/
def step4 (b : Nat) : List Instr :=
  [ldW t0 (tSlot 0) b, ldW t1 (arrSlot 1) b, xorR t1 t1 t0, stW (arrSlot 1) b t1,
   ldW t1 dSlot b, addW t0 t0 t1, ldW t1 (arrSlot 0) b, xorR t0 t0 t1,
   stW (arrSlot 0) b t0]

def lanes16 (f : Nat → List Instr) : List Instr := (List.range 16).flatMap f

/-- Exchange the halves `L` and `R`, a slot at a time. -/
def swapHalves : List Instr :=
  (List.range 16).flatMap fun k =>
    [ldS t0 (arrSlot 0 + k), ldS t1 (arrSlot 2 + k), stS (arrSlot 0 + k) t1,
     stS (arrSlot 2 + k) t0]

/-- Where the first round's key is, from the schedule. -/
def keyStart : Direction → Nat
  | .encrypt => 0
  | .decrypt => 120

/-- Moves the key pointer to the next round's key. -/
def keyNext : Direction → Instr
  | .encrypt => .addi .a0 .a0 8
  | .decrypt => .addi .a0 .a0 (-8)

/-- Moves the key pointer back by sixteen rounds' keys. -/
def keyBack : Direction → Instr
  | .encrypt => .addi .a0 .a0 (-128)
  | .decrypt => .addi .a0 .a0 128

/-- One round, with its key at `a0`; advances `a0` and counts down `a4`. -/
def round (d : Direction) : List Instr :=
  loadLE32 k0R t0 .a0 0 ++ loadLE32 k1R t0 .a0 4 ++
  lanes16 step1 ++ g16 ++ lanes16 step2 ++ g16 ++ lanes16 step3 ++ g16 ++ lanes16 step4 ++
  swapHalves ++ [keyNext d, .addi .a4 .a4 (-1)]

/-- Sixteen rounds, then the key pointer back to the first round's key. -/
def rounds (d : Direction) : Prog isa :=
  .seq (.block [.li .a4 16])
    (.seq (.loop (.block (round d)) (.nonzero .a4)) (.block [keyBack d]))

/-! ## Batches -/

/-- `t2 := min(a2, 16)`, the blocks of this batch. -/
def batchSize : Prog isa :=
  .seq (.block [shrI t2 .a2 4])
    (.ite (.nonzero t2) (.block [.li t2 16]) (.block [movR t2 .a2]))

/-- Copy one block (at `t3`) into the arrays' lane at `t4`, its words
big-endian; move on to the next. -/
def copyInBody : List Instr :=
  ((List.range 4).flatMap fun w =>
    loadBE32 t0 t1 .t3 (4 * w) ++ [.store .w t0 .t4 (8 * arrSlot w)]) ++
  ([.addi .t3 .t3 16, .addi .t4 .t4 4, .addi t2 t2 (-1)] : List Instr)

/-- Copy a lane out to one block, `R` first (see the rounds). -/
def copyOutBody : List Instr :=
  ((List.range 4).flatMap fun w =>
    .load .w t0 .t4 (8 * arrSlot ((w + 2) % 4)) :: storeBE 4 t0 t1 .t3 (4 * w)) ++
  ([.addi .t3 .t3 16, .addi .t4 .t4 4, .addi t2 t2 (-1)] : List Instr)

def copyStart : List Instr := [movR .t3 .a1, movR .t4 sb]

def copyIn : Prog isa :=
  .seq batchSize (.seq (.block copyStart) (.loop (.block copyInBody) (.nonzero t2)))

/-- Copy out, then move the data pointer past the batch and count it. -/
def copyOut : Prog isa :=
  .seq batchSize (.seq (.block copyStart)
    (.seq (.loop (.block copyOutBody) (.nonzero t2))
      (.seq batchSize (.block [movR .a1 .t3, .sub .a2 .a2 t2]))))

def batch (d : Direction) : Prog isa := .seq copyIn (.seq (rounds d) copyOut)

/-! ## The function -/

def seedSave : List Instr := seedSaved.map fun (r, k) => stS k r
def seedRestore : List Instr := seedSaved.map fun (r, k) => ldS r k

/-- Build `g16`'s masks in their slots, through `t0` and `t1`. -/
def buildMasks : List Instr :=
  gKs.flatMap fun (j, v) => Words64.RISCV64.movImm64 t0 t1 v ++ [stS (kSlot + j) t0]

/-- The scratch buffer (passed in `r`) to `a5`, the callee-saved registers
saved, and the masks built and pointed to by `a3`. -/
def prologue (r : Reg) : List Instr :=
  [movR sb r] ++ seedSave ++ buildMasks ++ [.addi kb sb ((8 * kSlot : Nat) : Int)]

def setup (d : Direction) : List Instr :=
  prologue .a3 ++ ([.addi .a0 .a0 (keyStart d)] : List Instr)

def ecb (d : Direction) : Prog isa :=
  .seq (.block (setup d)) (.seq (.ite (.zero .a2) (.block []) (.loop (batch d) (.nonzero .a2)))
    (.block seedRestore))

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.Seed.RISCV64
