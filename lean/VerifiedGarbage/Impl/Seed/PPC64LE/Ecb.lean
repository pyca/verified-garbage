module

public import VerifiedGarbage.Impl.Seed.PPC64LE.G16
public import VerifiedGarbage.Spec.Seed

/-!
# SEED ECB on PPC64LE

`vg_seed_ecb_{en,de}crypt(schedule = r3, data = r4, n = r5, scratch = r6)`.
As on AArch64 (`Impl/Seed/AArch64/Ecb.lean`) and x86-64
(`Impl/Seed/X86_64/Ecb.lean`): sixteen blocks at a time (fewer in the last
batch), each round's three `G`s computed for all of them at once by `g16`.
The scratch buffer (moved to `r8`, the base `g16` uses) holds `g16`'s slots,
the blocks' state as four arrays of sixteen 32-bit words, one per word of
the block (`L0`, `L1`, `R0`, `R1`: `arrSlot 0 … arrSlot 3`), the
intermediate arrays `a`, `c` and `d` of the round function, and the
callee-saved registers `r14`–`r31`, which `g16` uses.

* A batch copies its blocks' words, byte-reversed (`lwbrx`, `stwbrx`,
  indexed by `r0`) to the big-endian words of RFC 4269, into the arrays;
  lanes past the batch hold whatever they held, and their results are not
  stored.
* A round computes, lane by lane, `a = R0 ⊕ K0` and `a ⊕ R1 ⊕ K1`; `c = G`
  of that; `c + a`; `d = G` of that; `d + c`; `e = G` of that; and
  `L0 ⊕ (e + d)` and `L1 ⊕ e`, which become the new `R0` and `R1` as the
  halves are exchanged (`swapHalves`). After sixteen rounds, the halves are
  exchanged once too often, so the copy out takes `R` first. The sums are
  64-bit `add`s of the zero-extended words, of which `stw` keeps the low
  32 bits.
* Encryption steps through the round keys from the first, decryption from
  the last (`keyStart`); the key pointer is moved back after the sixteen
  rounds.
* The key pointer (`r3`), the data pointer (`r4`), the blocks left (`r5`)
  and the rounds left (`r7`) stay in registers that `g16` does not write.
  Every address and branch depends only on them, the scratch base and the
  copy loops' cursors and counter (`r6`, `r7`, `r10`).
-/

@[expose] public section

namespace VG.Impl.Seed.PPC64LE

open VG.PPC64LE VG.Impl.Aes.PPC64LE
open VG.Spec.Seed (Direction)

/-! ## Scratch slots -/

/-- The arrays of `a`, `c` and `d`. -/
def aSlot : Nat := 56
def cSlot : Nat := 64
def dSlot : Nat := 72
/-- The array of word `w` of the blocks: `L0`, `L1`, `R0`, `R1`. -/
def arrSlot (w : Nat) : Nat := 80 + 8 * w
def savedRegs : List (Reg × Nat) :=
  [(.r14, 112), (.r15, 113), (.r16, 114), (.r17, 115), (.r18, 116), (.r19, 117), (.r20, 118),
   (.r21, 119), (.r22, 120), (.r23, 121), (.r24, 122), (.r25, 123), (.r26, 124), (.r27, 125),
   (.r28, 126), (.r29, 127), (.r30, 128), (.r31, 129)]

/-- The scratch buffer's size, in slots. -/
def scratchSlots : Nat := 130

/-! ## 32-bit lanes -/

/-- Lane `b` of the array starting at slot `k`, as a byte offset. -/
def laneOff (k b : Nat) : Nat := 8 * k + 4 * b

def ldW (d : Reg) (k b : Nat) : Instr := .load .w d sb (laneOff k b)
def stW (k b : Nat) (r : Reg) : Instr := .store .w r sb (laneOff k b)
def eorW (d n m : Reg) : Instr := .logic .xor d n m
def addW (d n m : Reg) : Instr := .add d n m

/-! ## A round -/

def step1 (b : Nat) : List Instr :=
  [ldW .r9 (arrSlot 2) b, eorW .r9 .r9 .r11, stW aSlot b .r9, ldW .r10 (arrSlot 3) b,
   eorW .r9 .r9 .r10, eorW .r9 .r9 .r12, stW (tSlot 0) b .r9]

/-- `c := G(…)`, `T := c + a`. -/
def step2 (b : Nat) : List Instr :=
  [ldW .r9 (tSlot 0) b, stW cSlot b .r9, ldW .r10 aSlot b, addW .r9 .r9 .r10, stW (tSlot 0) b .r9]

/-- `d := G(…)`, `T := d + c`. -/
def step3 (b : Nat) : List Instr :=
  [ldW .r9 (tSlot 0) b, stW dSlot b .r9, ldW .r10 cSlot b, addW .r9 .r9 .r10, stW (tSlot 0) b .r9]

/-- `e := G(…)`, `L1 := L1 ⊕ e`, `L0 := L0 ⊕ (e + d)`. -/
def step4 (b : Nat) : List Instr :=
  [ldW .r9 (tSlot 0) b, ldW .r10 (arrSlot 1) b, eorW .r10 .r10 .r9, stW (arrSlot 1) b .r10,
   ldW .r10 dSlot b, addW .r9 .r9 .r10, ldW .r10 (arrSlot 0) b, eorW .r9 .r9 .r10,
   stW (arrSlot 0) b .r9]

def lanes16 (f : Nat → List Instr) : List Instr := (List.range 16).flatMap f

/-- Exchange the halves `L` and `R`, a slot at a time. -/
def swapHalves : List Instr :=
  (List.range 16).flatMap fun k =>
    [ldS .r9 (arrSlot 0 + k), ldS .r10 (arrSlot 2 + k), stS (arrSlot 0 + k) .r10,
     stS (arrSlot 2 + k) .r9]

/-- Where the first round's key is, from the schedule. -/
def keyStart : Direction → Nat
  | .encrypt => 0
  | .decrypt => 120

/-- Moves the key pointer to the next round's key. -/
def keyNext : Direction → Instr
  | .encrypt => .addi .r3 .r3 8
  | .decrypt => .subi .r3 .r3 8

/-- Moves the key pointer back by sixteen rounds' keys. -/
def keyBack : Direction → Instr
  | .encrypt => .subi .r3 .r3 128
  | .decrypt => .addi .r3 .r3 128

/-- One round, with its key at `r3`; advances `r3` and counts down `r7`. -/
def round (d : Direction) : List Instr :=
  ([.load .w .r11 .r3 0, .load .w .r12 .r3 4] : List Instr) ++
  lanes16 step1 ++ g16 ++ lanes16 step2 ++ g16 ++ lanes16 step3 ++ g16 ++ lanes16 step4 ++
  swapHalves ++ [keyNext d, .subi .r7 .r7 1]

/-- Sixteen rounds, then the key pointer back to the first round's key. -/
def rounds (d : Direction) : Prog isa :=
  .seq (.block [.li .r7 16])
    (.seq (.loop (.block (round d)) (.nonzero .d .r7)) (.block [keyBack d]))

/-! ## Batches -/

/-- `r10 := min(r5, 16)`, the blocks of this batch. -/
def batchSize : Prog isa :=
  .seq (.block [shrI .r10 .r5 4])
    (.ite (.nonzero .d .r10) (.block [.li .r10 16]) (.block [movR .r10 .r5]))

/-- Copy one block (at `r6`) into the arrays' lane at `r7`, its words
byte-reversed; move on to the next. -/
def copyInBody : List Instr :=
  ((List.range 4).flatMap fun w =>
    [.li .r0 (4 * w), .loadRev .w .r9 .r6 .r0, .store .w .r9 .r7 (8 * arrSlot w)]) ++
  ([.addi .r6 .r6 16, .addi .r7 .r7 4, .subi .r10 .r10 1] : List Instr)

/-- Copy a lane out to one block, `R` first (see the rounds). -/
def copyOutBody : List Instr :=
  ((List.range 4).flatMap fun w =>
    [.load .w .r9 .r7 (8 * arrSlot ((w + 2) % 4)), .li .r0 (4 * w), .storeRev .w .r9 .r6 .r0]) ++
  ([.addi .r6 .r6 16, .addi .r7 .r7 4, .subi .r10 .r10 1] : List Instr)

def copyStart : List Instr := [movR .r6 .r4, movR .r7 sb]

def copyIn : Prog isa :=
  .seq batchSize (.seq (.block copyStart) (.loop (.block copyInBody) (.nonzero .d .r10)))

/-- Copy out, then move the data pointer past the batch and count it. -/
def copyOut : Prog isa :=
  .seq batchSize (.seq (.block copyStart)
    (.seq (.loop (.block copyOutBody) (.nonzero .d .r10))
      (.seq batchSize (.block [movR .r4 .r6, .sub .r5 .r5 .r10]))))

def batch (d : Direction) : Prog isa := .seq copyIn (.seq (rounds d) copyOut)

/-! ## The function -/

def saveRegs : List Instr := savedRegs.map fun (r, k) => stS k r
def restore : List Instr := savedRegs.map fun (r, k) => ldS r k

def setup (d : Direction) : List Instr :=
  [movR sb .r6] ++ saveRegs ++ ([.addi .r3 .r3 (keyStart d)] : List Instr)

def ecb (d : Direction) : Prog isa :=
  .seq (.block (setup d)) (.seq (.ite (.zero .d .r5) (.block []) (.loop (batch d) (.nonzero .d .r5)))
    (.block restore))

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.Seed.PPC64LE
