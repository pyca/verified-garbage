import VerifiedGarbage.Impl.Seed.X86.G8
import VerifiedGarbage.Impl.Aes.X86.Ctr32
import VerifiedGarbage.Spec.Seed

/-!
# SEED ECB on x86 (32-bit)

`ecb d(schedule, data, n, scratch)`, cdecl (the arguments at `[esp + 4]` …
`[esp + 16]`): `vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt` with their
working space in the scratch buffer, which the artifact allocates on the
stack. As on ARMv7 (`Impl/Seed/Arm/Ecb.lean`): eight blocks at a time, each
round's three `G`s computed for all eight at once by `g8`.

The scratch buffer at `edi` holds, in 4-byte slots: `g8`'s slots (0–79,
`G8.lean`); the arrays `a`, `c` and `d` of the round function, one word per
block (80–103); the blocks' state as four arrays of eight words, one per
word of the block, `L0`, `L1`, `R0`, `R1` (`arrSlot`, 104–135); the tail
buffer of eight blocks (136–167); the table of round keys, in the order the
rounds use them (168–199); the callee-saved registers `ebx`, `esi`, `edi`
and `ebp` (200–203); and the data pointer and the blocks left (204, 205).

* The callee-saved registers are saved, and the scratch buffer's address
  moves to `edi`. The round keys are copied to the table: `K1,0`, `K1,1`,
  …, `K16,1` for encryption, and the rounds' keys in reverse order for
  decryption (RFC 4269 §2.4), so that both run the same rounds
  (`keyTable`).
* Each group of up to eight blocks is copied to the tail buffer and
  transformed there by `crypt8`, which needs only the table: a block
  cipher's core for the modes. `crypt8` copies each block's words,
  byte-reversed (`bswap`) to the big-endian words of RFC 4269, to the
  arrays, runs the sixteen rounds, and copies them back.
* A round computes, block by block, `a = R0 ⊕ K0` and `a ⊕ R1 ⊕ K1`
  (the round key in `ecx` and `edx`); `c = G` of that; `c + a`; `d = G` of
  that; `d + c`; `e = G` of that; and `L0 ⊕ (e + d)` and `L1 ⊕ e`, written
  over `L0` and `L1`. Instead of exchanging the halves, the next round
  takes the arrays the other way round: the loop runs two rounds, with the
  round key at `kp` (`esi`). After sixteen rounds the halves are where they
  started, `R` the output's first half.
* The rounds use every register but `esi` and `edi`, so the data pointer
  and the blocks left wait in their slots, stored again after each copy
  (the analysis of constant time forgets what the buffer holds after a
  store through another pointer than `edi`).

Only the pointers, `n`, and what is computed from them (the copies'
pointers and counts, `kp`, the loop tests, and the slots holding them) are
public; no address and no branch depends on anything else.
-/

namespace VG.Impl.Seed.X86

open VG.X86 VG.Impl.Aes.X86
open VG.Spec.Seed (Direction)

/-- The round keys' pointer. -/
def kp : Reg := .esi

/-! ## Slots -/

/-- The arrays of `a`, `c` and `d`. -/
def aSlot : Nat := 80
def cSlot : Nat := 88
def dSlot : Nat := 96
/-- The array of word `w` of the blocks: `L0`, `L1`, `R0`, `R1`. -/
def arrSlot (w : Nat) : Nat := 104 + 8 * w

/-- Word `w` of block `b` of the tail buffer. -/
def tailSlot : Nat := 136
def tailAt (b w : Nat) : Nat := tailSlot + 4 * b + w

/-- The table of round keys, and its end. -/
def tableSlot : Nat := 168
def tableEnd : Nat := tableSlot + 32

def savedSlot : Nat := tableEnd
def ptrSlot : Nat := savedSlot + 4
def cntSlot : Nat := ptrSlot + 1

/-- The number of slots, a whole number of 64-bit words (the artifacts
allocate the buffer as `[u64; 103]`). -/
def slots : Nat := cntSlot + 1

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.ebx, savedSlot), (.esi, savedSlot + 1), (.edi, savedSlot + 2), (.ebp, savedSlot + 3)]

/-- Load the scratch buffer's address (argument `k`) to `edi`, saving the
registers there first. -/
def saveRegs (k : Nat) : List Instr :=
  [.mov .eax (.mem (argOp k))] ++ savedRegs.map (fun (r, j) => .store (slotAt .eax j) r) ++ [movR .edi .eax]

/-- Restore the registers (`edi`, the base, last). -/
def restoreRegs : List Instr :=
  [movS .ebx savedSlot, movS .esi (savedSlot + 1), movS .ebp (savedSlot + 3), movS .edi (savedSlot + 2)]

def addS (d : Reg) (k : Nat) : Instr := .alu .add d (.mem (slotAt sb k))
def subS (d : Reg) (k : Nat) : Instr := .alu .sub d (.mem (slotAt sb k))

/-! ## A round, block by block -/

/-- `a := R0 ⊕ K0`, `T := a ⊕ R1 ⊕ K1`, the round key in `ecx` and `edx`,
`R` at `r`. -/
def step1 (r b : Nat) : List Instr :=
  [movS .eax (r + b), xorR .eax .ecx, st (aSlot + b) .eax, xorS .eax (r + 8 + b), xorR .eax .edx,
   st (tSlot b) .eax]

/-- `c := G(…)`, `T := c + a`. -/
def step2 (b : Nat) : List Instr :=
  [movS .eax (tSlot b), st (cSlot + b) .eax, addS .eax (aSlot + b), st (tSlot b) .eax]

/-- `d := G(…)`, `T := d + c`. -/
def step3 (b : Nat) : List Instr :=
  [movS .eax (tSlot b), st (dSlot + b) .eax, addS .eax (cSlot + b), st (tSlot b) .eax]

/-- `e := G(…)`, `L1 := L1 ⊕ e`, `L0 := L0 ⊕ (e + d)`, `L` at `l`. -/
def step4 (l b : Nat) : List Instr :=
  [movS .eax (tSlot b), movS .ebx (l + 8 + b), xorR .ebx .eax, st (l + 8 + b) .ebx, addS .eax (dSlot + b),
   xorS .eax (l + b), st (l + b) .eax]

def lanes8 (f : Nat → List Instr) : List Instr := (List.range 8).flatMap f

/-- One round, with `L` at `l`, `R` at `r` and its key at `kp`, which moves
on to the next round's key. -/
def round (l r : Nat) : List Instr :=
  ([.mov .ecx (.mem (at_ kp 0)), .mov .edx (.mem (at_ kp 4))] : List Instr) ++
  lanes8 (step1 r) ++ g8 ++ lanes8 step2 ++ g8 ++ lanes8 step3 ++ g8 ++ lanes8 (step4 l) ++
  ([addI kp 8] : List Instr)

/-- Two rounds, the second with the halves the other way round, and whether
`kp` is at the table's end. -/
def roundPair : List Instr :=
  round (arrSlot 0) (arrSlot 2) ++ round (arrSlot 2) (arrSlot 0) ++
  ([movR .eax kp, subR .eax .edi, .alu .cmp .eax (.imm (BitVec.ofNat 32 (4 * tableEnd)))] : List Instr)

/-- `kp := ` the address of slot `k`. -/
def kpAt (k : Nat) : List Instr := [movR kp .edi, addI kp (BitVec.ofNat 32 (4 * k))]

/-- The sixteen rounds, with `kp` from the table's start to its end. -/
def rounds : Prog isa := .seq (.block (kpAt tableSlot)) (.loop (.block roundPair) .ne)

/-! ## Eight blocks -/

/-- Word `w` of block `b` of the tail buffer, byte-reversed, to the arrays. -/
def toArr : List Instr :=
  (List.range 8).flatMap fun b => (List.range 4).flatMap fun w =>
    [movS .eax (tailAt b w), .bswap .eax, st (arrSlot w + b) .eax]

/-- The arrays back to the tail buffer, `R` first. -/
def fromArr : List Instr :=
  (List.range 8).flatMap fun b => (List.range 4).flatMap fun w =>
    [movS .eax (arrSlot ((w + 2) % 4) + b), .bswap .eax, st (tailAt b w) .eax]

/-- The eight blocks of the tail buffer, in place, under the table's keys. -/
def crypt8 : Prog isa := .seq (.block toArr) (.seq rounds (.block fromArr))

/-! ## The round keys -/

/-- The schedule's word for the table's word `i`: round `i / 2 + 1`'s for
encryption, round `16 - i / 2`'s for decryption. -/
def keySrc : Direction → Nat → Nat
  | .encrypt, i => i
  | .decrypt, i => 2 * (15 - i / 2) + i % 2

/-- The schedule (argument 0, through `ecx`) to the table. -/
def keyTable (d : Direction) : List Instr :=
  .mov .ecx (.mem (argOp 0)) ::
    (List.range 32).flatMap fun i => [.mov .eax (.mem (at_ .ecx (4 * keySrc d i))), st (tableSlot + i) .eax]

/-! ## The groups -/

/-- Copy `ecx` blocks from `edx` to `ebx` (through `eax`). -/
def copyBlocks : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .edx 0)), .store (at_ .ebx 0) .eax, .mov .eax (.mem (at_ .edx 4)),
      .store (at_ .ebx 4) .eax, .mov .eax (.mem (at_ .edx 8)), .store (at_ .ebx 8) .eax,
      .mov .eax (.mem (at_ .edx 12)), .store (at_ .ebx 12) .eax, addI .edx 16, addI .ebx 16, subI .ecx 1]) .ne

/-- `ecx := min(ebp, 8)`, the blocks of this group. -/
def countR : Prog isa :=
  .seq (.block [movR .ecx .ebp, .alu .cmp .ebp (.imm 8)]) (.ite .b (.block []) (.block [movI .ecx 8]))

/-- The data pointer and the blocks left from their slots to `esi` and `ebp`,
and the blocks of this group to `ecx`. -/
def groupCount : Prog isa := .seq (.block [movS .esi ptrSlot, movS .ebp cntSlot]) countR

/-- `r := ` the tail buffer's address. -/
def tailAddr (r : Reg) : List Instr := [movR r .edi, addI r (BitVec.ofNat 32 (4 * tailSlot))]

/-- The group's blocks to the tail buffer, and the data pointer and the
blocks left back to their slots. -/
def copyIn : Prog isa :=
  .seq groupCount (.seq (.block ([movR .edx .esi] ++ tailAddr .ebx))
    (.seq copyBlocks (.block [st ptrSlot .esi, st cntSlot .ebp])))

/-- The tail buffer back to the group's blocks. -/
def copyOut : Prog isa := .seq groupCount (.seq (.block (tailAddr .edx ++ [movR .ebx .esi])) copyBlocks)

/-- On to the next group, the data pointer and the blocks left (still in
`esi` and `ebp`) back to their slots (Z set when none are left). -/
def advance : Prog isa :=
  .seq countR (.block [addI .esi 128, subR .ebp .ecx, st ptrSlot .esi, st cntSlot .ebp])

/-- Eight blocks, or the last one to seven. -/
def group : Prog isa := .seq copyIn (.seq crypt8 (.seq copyOut advance))

/-- The whole function: the table, then the groups. -/
def ecb (d : Direction) : Prog isa :=
  .seq (.block (saveRegs 3 ++ keyTable d))
    (.seq (.block [.mov .eax (.mem (argOp 1)), st ptrSlot .eax, .mov .eax (.mem (argOp 2)), st cntSlot .eax,
        .alu .test .eax (.reg .eax)])
      (.seq (.ite .e (.block []) (.loop group .ne)) (.block restoreRegs)))

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.Seed.X86
