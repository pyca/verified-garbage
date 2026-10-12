module

public import VerifiedGarbage.Impl.Seed.AArch64.G16
public import VerifiedGarbage.Spec.Seed

/-!
# SEED ECB on AArch64

`vg_seed_ecb_{en,de}crypt(schedule = x0, data = x1, n = x2, scratch = x3)`.

As on x86-64 (`Impl/Seed/X86_64/Ecb.lean`): sixteen blocks at a time (fewer
in the last batch), each round's three `G`s computed for all of them at once
by `g16`. The scratch buffer (moved to `x5`, the base `g16` uses) holds
`g16`'s slots, the blocks' state as four arrays of sixteen 32-bit words, one
per word of the block (`L0`, `L1`, `R0`, `R1`: `arrSlot 0 … arrSlot 3`), the
intermediate arrays `a`, `c` and `d` of the round function, and the
callee-saved registers `x19`–`x28`, which `g16` uses.

* A batch copies its blocks' words, byte-reversed (`rev`) to the big-endian
  words of RFC 4269, into the arrays; lanes past the batch hold whatever
  they held, and their results are not stored.
* A round computes, lane by lane, `a = R0 ⊕ K0` and `a ⊕ R1 ⊕ K1`; `c = G`
  of that; `c + a`; `d = G` of that; `d + c`; `e = G` of that; and
  `L0 ⊕ (e + d)` and `L1 ⊕ e`, which become the new `R0` and `R1` as the
  halves are exchanged (`swapHalves`). After sixteen rounds, the halves are
  exchanged once too often, so the copy out takes `R` first.
* Encryption steps through the round keys from the first, decryption from
  the last (`keyStart`); the key pointer is moved back after the sixteen
  rounds.
* The key pointer (`x0`), the data pointer (`x1`), the blocks left (`x2`)
  and the rounds left (`x4`) stay in registers that `g16` does not write.
  Every address and branch depends only on them, the scratch base and the
  copy loops' cursors and counter (`x3`, `x4`, `x15`).
-/

@[expose] public section

namespace VG.Impl.Seed.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64
open VG.Spec.Seed (Direction)

/-! ## Scratch slots -/

/-- The arrays of `a`, `c` and `d`. -/
def aSlot : Nat := 56
def cSlot : Nat := 64
def dSlot : Nat := 72
/-- The array of word `w` of the blocks: `L0`, `L1`, `R0`, `R1`. -/
def arrSlot (w : Nat) : Nat := 80 + 8 * w
def savedRegs : List (Reg × Nat) :=
  [(.x19, 112), (.x20, 113), (.x21, 114), (.x22, 115), (.x23, 116), (.x24, 117), (.x25, 118),
   (.x26, 119), (.x27, 120), (.x28, 121)]
/-- The scratch buffer's size, in slots. -/
def scratchSlots : Nat := 122

/-! ## 32-bit lanes -/

/-- Lane `b` of the array starting at slot `k`, as a byte offset. -/
def laneOff (k b : Nat) : Nat := 8 * k + 4 * b

def ldW (d : Reg) (k b : Nat) : Instr := .ldr .w d sb (laneOff k b)
def stW (k b : Nat) (r : Reg) : Instr := .str .w r sb (laneOff k b)
def eorW (d n m : Reg) : Instr := .logic .eor .w d n m
def addW (d n m : Reg) : Instr := .add .w d n m

/-! ## A round -/

def step1 (b : Nat) : List Instr :=
  [ldW .x14 (arrSlot 2) b, eorW .x14 .x14 .x16, stW aSlot b .x14, ldW .x15 (arrSlot 3) b,
   eorW .x14 .x14 .x15, eorW .x14 .x14 .x17, stW (tSlot 0) b .x14]

/-- `c := G(…)`, `T := c + a`. -/
def step2 (b : Nat) : List Instr :=
  [ldW .x14 (tSlot 0) b, stW cSlot b .x14, ldW .x15 aSlot b, addW .x14 .x14 .x15, stW (tSlot 0) b .x14]

/-- `d := G(…)`, `T := d + c`. -/
def step3 (b : Nat) : List Instr :=
  [ldW .x14 (tSlot 0) b, stW dSlot b .x14, ldW .x15 cSlot b, addW .x14 .x14 .x15, stW (tSlot 0) b .x14]

/-- `e := G(…)`, `L1 := L1 ⊕ e`, `L0 := L0 ⊕ (e + d)`. -/
def step4 (b : Nat) : List Instr :=
  [ldW .x14 (tSlot 0) b, ldW .x15 (arrSlot 1) b, eorW .x15 .x15 .x14, stW (arrSlot 1) b .x15,
   ldW .x15 dSlot b, addW .x14 .x14 .x15, ldW .x15 (arrSlot 0) b, eorW .x14 .x14 .x15,
   stW (arrSlot 0) b .x14]

def lanes16 (f : Nat → List Instr) : List Instr := (List.range 16).flatMap f

/-- Exchange the halves `L` and `R`, a slot at a time. -/
def swapHalves : List Instr :=
  (List.range 16).flatMap fun k =>
    [ldS .x14 (arrSlot 0 + k), ldS .x15 (arrSlot 2 + k), stS (arrSlot 0 + k) .x15,
     stS (arrSlot 2 + k) .x14]

/-- Where the first round's key is, from the schedule. -/
def keyStart : Direction → Nat
  | .encrypt => 0
  | .decrypt => 120

/-- Moves the key pointer to the next round's key. -/
def keyNext : Direction → Instr
  | .encrypt => .addImm .x .x0 .x0 8
  | .decrypt => .subImm .x .x0 .x0 8

/-- Moves the key pointer back by sixteen rounds' keys. -/
def keyBack : Direction → Instr
  | .encrypt => .subImm .x .x0 .x0 128
  | .decrypt => .addImm .x .x0 .x0 128

/-- One round, with its key at `x0`; advances `x0` and counts down `x4`. -/
def round (d : Direction) : List Instr :=
  ([.ldr .w .x16 .x0 0, .ldr .w .x17 .x0 4] : List Instr) ++
  lanes16 step1 ++ g16 ++ lanes16 step2 ++ g16 ++ lanes16 step3 ++ g16 ++ lanes16 step4 ++
  swapHalves ++ [keyNext d, .subImm .x .x4 .x4 1]

/-- Sixteen rounds, then the key pointer back to the first round's key. -/
def rounds (d : Direction) : Prog isa :=
  .seq (.block [.movz .x .x4 16 0])
    (.seq (.loop (.block (round d)) (.nonzero .x .x4)) (.block [keyBack d]))

/-! ## Batches -/

/-- `x15 := min(x2, 16)`, the blocks of this batch. -/
def batchSize : Prog isa :=
  .seq (.block [lsrI .x15 .x2 4])
    (.ite (.nonzero .x .x15) (.block [.movz .x .x15 16 0]) (.block [movR .x15 .x2]))

/-- Copy one block (at `x3`) into the arrays' lane at `x4`, its words
byte-reversed; move on to the next. -/
def copyInBody : List Instr :=
  ((List.range 4).flatMap fun w =>
    [.ldr .w .x14 .x3 (4 * w), .rev32 .x14 .x14, .str .w .x14 .x4 (8 * arrSlot w)]) ++
  ([.addImm .x .x3 .x3 16, .addImm .x .x4 .x4 4, .subImm .x .x15 .x15 1] : List Instr)

/-- Copy a lane out to one block, `R` first (see the rounds). -/
def copyOutBody : List Instr :=
  ((List.range 4).flatMap fun w =>
    [.ldr .w .x14 .x4 (8 * arrSlot ((w + 2) % 4)), .rev32 .x14 .x14, .str .w .x14 .x3 (4 * w)]) ++
  ([.addImm .x .x3 .x3 16, .addImm .x .x4 .x4 4, .subImm .x .x15 .x15 1] : List Instr)

def copyStart : List Instr := [movR .x3 .x1, movR .x4 sb]

def copyIn : Prog isa :=
  .seq batchSize (.seq (.block copyStart) (.loop (.block copyInBody) (.nonzero .x .x15)))

/-- Copy out, then move the data pointer past the batch and count it. -/
def copyOut : Prog isa :=
  .seq batchSize (.seq (.block copyStart)
    (.seq (.loop (.block copyOutBody) (.nonzero .x .x15))
      (.seq batchSize (.block [movR .x1 .x3, .sub .x .x2 .x2 .x15]))))

def batch (d : Direction) : Prog isa := .seq copyIn (.seq (rounds d) copyOut)

/-! ## The function -/

def saveRegs : List Instr := savedRegs.map fun (r, k) => stS k r
def restore : List Instr := savedRegs.map fun (r, k) => ldS r k

def setup (d : Direction) : List Instr :=
  [movR sb .x3] ++ saveRegs ++ ([.addImm .x .x0 .x0 (keyStart d)] : List Instr)

def ecb (d : Direction) : Prog isa :=
  .seq (.block (setup d)) (.seq (.ite (.zero .x .x2) (.block []) (.loop (batch d) (.nonzero .x .x2)))
    (.block restore))

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.Seed.AArch64
