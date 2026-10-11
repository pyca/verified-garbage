import VerifiedGarbage.Impl.Seed.Arm.G8
import VerifiedGarbage.Spec.Seed

/-!
# SEED ECB on ARMv7

`ecb d(schedule = r0, data = r1, n = r2, scratch = r3)`:
`vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt` with their working space in
the scratch buffer, which the artifact allocates on the stack. Eight blocks
at a time, each round's three `G`s computed for all eight at once by `g8`.

The scratch buffer at `r8` holds, in 4-byte slots: the S-box's spills
(0–31) and `g8`'s other slots (32–52, `G.lean`); the arrays `a`, `c` and
`d` of the round function, one word per block (56–79); the blocks' state
as four arrays of eight words, one per word of the block, `L0`, `L1`, `R0`,
`R1` (`arrSlot`, 80–111); the tail buffer of eight blocks (112–143); the
table of round keys, in the order the rounds use them (144–175); the
callee-saved registers `r4`–`r11` and `lr` (176–184); and the data pointer
and the blocks left (185, 186).

* The callee-saved registers are saved, and the scratch buffer moves to
  `r8`. The round keys are copied to the table: `K1,0`, `K1,1`, …,
  `K16,1` for encryption, and the rounds' keys in reverse order for
  decryption (RFC 4269 §2.4), so that both run the same rounds (`keyTable`).
* Each group of up to eight blocks is copied to the tail buffer and
  transformed there by `crypt8`, which needs only the table: a block
  cipher's core for the modes. `crypt8` copies each block's words,
  byte-reversed (`rev`) to the big-endian words of RFC 4269, to the arrays,
  runs the sixteen rounds, and copies them back. Blocks of the tail buffer
  past the group hold whatever they held; their results are not copied out.
* A round computes, block by block, `a = R0 ⊕ K0` and `a ⊕ R1 ⊕ K1`; `c = G`
  of that; `c + a`; `d = G` of that; `d + c`; `e = G` of that; and
  `L0 ⊕ (e + d)` and `L1 ⊕ e`, written over `L0` and `L1`. Instead of
  exchanging the halves, the next round takes the arrays the other way
  round: the loop runs two rounds, with the round key at `kp` (`r9`). After
  sixteen rounds the halves are where they started, `R` the output's first
  half (`crypt` has no exchange after the last round).
* The data pointer and the blocks left wait in their slots during
  `crypt8`, which uses every register but `r8` and `r9`.

Only the pointers, `n`, and what is computed from them (the copies'
pointers and counts, `kp`, the loop tests, and the slots holding them) are
public; no address and no branch depends on anything else.
-/

namespace VG.Impl.Seed.Arm

open VG.Arm VG.Impl.Aes.Arm
open VG.Spec.Seed (Direction)

/-! ## Slots -/

/-- The arrays of `a`, `c` and `d`. -/
def aSlot : Nat := 56
def cSlot : Nat := 64
def dSlot : Nat := 72
/-- The array of word `w` of the blocks: `L0`, `L1`, `R0`, `R1`. -/
def arrSlot (w : Nat) : Nat := 80 + 8 * w

/-- Word `w` of block `b` of the tail buffer. -/
def tailSlot : Nat := 112
def tailAt (b w : Nat) : Nat := tailSlot + 4 * b + w

/-- The table of round keys, and its end. -/
def tableSlot : Nat := 144
def tableEnd : Nat := tableSlot + 32

def savedSlot : Nat := tableEnd
def ptrSlot : Nat := savedSlot + 9
def cntSlot : Nat := ptrSlot + 1

/-- The number of slots, rounded up to a whole number of 64-bit words (the
artifacts allocate the buffer as `[u64; 94]`). -/
def slots : Nat := cntSlot + 2

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.r4, savedSlot), (.r5, savedSlot + 1), (.r6, savedSlot + 2), (.r7, savedSlot + 3), (.r8, savedSlot + 4),
   (.r9, savedSlot + 5), (.r10, savedSlot + 6), (.r11, savedSlot + 7), (.lr, savedSlot + 8)]

/-- Save and restore them, with the scratch buffer's base in `b`. -/
def saveRegs (b : Reg) : List Instr := savedRegs.map fun (r, k) => .str r b (4 * k)
def restoreRegs (b : Reg) : List Instr := savedRegs.map fun (r, k) => .ldr r b (4 * k)

def addR (d n m : Reg) : Instr := .dp .add d n (.reg m)

/-! ## A round, block by block -/

/-- `a := R0 ⊕ K0`, `T := a ⊕ R1 ⊕ K1`, the round key in `u7` and `lr`, `R`
at `r`. -/
def step1 (r b : Nat) : List Instr :=
  [ldS t0 (r + b), eorR t0 t0 u7, stS (aSlot + b) t0, ldS t1 (r + 8 + b), eorR t0 t0 t1,
   eorR t0 t0 .lr, stS (tSlot b) t0]

/-- `c := G(…)`, `T := c + a`. -/
def step2 (b : Nat) : List Instr :=
  [ldS t0 (tSlot b), stS (cSlot + b) t0, ldS t1 (aSlot + b), addR t0 t0 t1, stS (tSlot b) t0]

/-- `d := G(…)`, `T := d + c`. -/
def step3 (b : Nat) : List Instr :=
  [ldS t0 (tSlot b), stS (dSlot + b) t0, ldS t1 (cSlot + b), addR t0 t0 t1, stS (tSlot b) t0]

/-- `e := G(…)`, `L1 := L1 ⊕ e`, `L0 := L0 ⊕ (e + d)`, `L` at `l`. -/
def step4 (l b : Nat) : List Instr :=
  [ldS t0 (tSlot b), ldS t1 (l + 8 + b), eorR t1 t1 t0, stS (l + 8 + b) t1, ldS t1 (dSlot + b),
   addR t0 t0 t1, ldS t1 (l + b), eorR t0 t0 t1, stS (l + b) t0]

def lanes8 (f : Nat → List Instr) : List Instr := (List.range 8).flatMap f

/-- One round, with `L` at `l`, `R` at `r` and its key at `kp`, which moves
on to the next round's key. -/
def round (l r : Nat) : List Instr :=
  ([.ldr u7 kp 0, .ldr .lr kp 4] : List Instr) ++
  lanes8 (step1 r) ++ g8 ++ lanes8 step2 ++ g8 ++ lanes8 step3 ++ g8 ++ lanes8 (step4 l) ++
  ([.dp .add kp kp (.imm 8)] : List Instr)

/-- Two rounds, the second with the halves the other way round, and whether
`kp` is at the table's end. -/
def roundPair : List Instr :=
  round (arrSlot 0) (arrSlot 2) ++ round (arrSlot 2) (arrSlot 0) ++
  ([.dp .sub t0 kp (.reg sb), .cmp t0 (.imm (BitVec.ofNat 32 (4 * tableEnd)))] : List Instr)

/-- `kp := ` the address of slot `k`. -/
def kpAt (k : Nat) : Instr := .dp .add kp sb (.imm (BitVec.ofNat 32 (4 * k)))

/-- The sixteen rounds, with `kp` from the table's start to its end. -/
def rounds : Prog isa := .seq (.block [kpAt tableSlot]) (.loop (.block roundPair) .ne)

/-! ## Eight blocks -/

/-- Word `w` of block `b` of the tail buffer, byte-reversed, to the arrays. -/
def toArr : List Instr :=
  (List.range 8).flatMap fun b => (List.range 4).flatMap fun w =>
    [ldS t0 (tailAt b w), .rev t0 t0, stS (arrSlot w + b) t0]

/-- The arrays back to the tail buffer, `R` first. -/
def fromArr : List Instr :=
  (List.range 8).flatMap fun b => (List.range 4).flatMap fun w =>
    [ldS t0 (arrSlot ((w + 2) % 4) + b), .rev t0 t0, stS (tailAt b w) t0]

/-- The eight blocks of the tail buffer, in place, under the table's keys. -/
def crypt8 : Prog isa := .seq (.block toArr) (.seq rounds (.block fromArr))

/-! ## The round keys -/

/-- The schedule's word for the table's word `i`: round `i / 2 + 1`'s for
encryption, round `16 - i / 2`'s for decryption. -/
def keySrc : Direction → Nat → Nat
  | .encrypt, i => i
  | .decrypt, i => 2 * (15 - i / 2) + i % 2

/-- The schedule (at `r0`) to the table. -/
def keyTable (d : Direction) : List Instr :=
  (List.range 32).flatMap fun i => [.ldr t0 .r0 (4 * keySrc d i), stS (tableSlot + i) t0]

/-! ## The groups -/

/-- Copy `r3` blocks from `r0` to `r12` (through `t0`). -/
def copyBlocks : Prog isa :=
  .loop (.block [.ldr t0 .r0 0, .str t0 .r12 0, .ldr t0 .r0 4, .str t0 .r12 4,
      .ldr t0 .r0 8, .str t0 .r12 8, .ldr t0 .r0 12, .str t0 .r12 12,
      .dp .add .r0 .r0 (.imm 16), .dp .add .r12 .r12 (.imm 16), .subs .r3 .r3 (.imm 1)]) .ne

/-- `r3 := min(r2, 8)`, the blocks of this group. -/
def groupCount : Prog isa :=
  .seq (.block [.mov t0 (lsrOp .r2 3), .cmp t0 (.imm 0)])
    (.ite .ne (.block [.mov .r3 (.imm 8)]) (.block [movR .r3 .r2]))

/-- The tail buffer's address, in `r`. -/
def tailAddr (r : Reg) : Instr := .dp .add r sb (.imm (BitVec.ofNat 32 (4 * tailSlot)))

/-- The group's blocks (at `r1`) to the tail buffer. -/
def copyIn : Prog isa := .seq groupCount (.seq (.block [movR .r0 .r1, tailAddr .r12]) copyBlocks)

/-- The tail buffer back to the group's blocks. -/
def copyOut : Prog isa := .seq groupCount (.seq (.block [tailAddr .r0, movR .r12 .r1]) copyBlocks)

/-- The eight blocks of the tail buffer, with the data pointer and the blocks
left in their slots meanwhile: `crypt8` uses every register but `r8` and
`r9`, and stores only through `sb`, which keeps the slots' values public
for the analysis of constant time. -/
def cryptSaved : Prog isa :=
  .seq (.block [stS ptrSlot .r1, stS cntSlot .r2]) (.seq crypt8 (.block [ldS .r1 ptrSlot, ldS .r2 cntSlot]))

/-- On to the next group, or none left (Z set). -/
def advance : Prog isa := .seq groupCount (.block [.dp .add .r1 .r1 (.imm 128), .subs .r2 .r2 (.reg .r3)])

/-- Eight blocks, or the last one to seven. -/
def group : Prog isa := .seq copyIn (.seq cryptSaved (.seq copyOut advance))

/-- The whole function: the table, then the groups. -/
def ecb (d : Direction) : Prog isa :=
  .seq (.block (saveRegs .r3 ++ [movR sb .r3] ++ keyTable d))
    (.seq (.block [.cmp .r2 (.imm 0)])
      (.seq (.ite .eq (.block []) (.loop group .ne)) (.block ([movR .r12 sb] ++ restoreRegs .r12))))

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.Seed.Arm
