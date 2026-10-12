import VerifiedGarbage.Impl.Seed.AArch64.Ecb

/-!
# SEED key expansion on AArch64

`vg_seed_expand_key(key = x0, schedule = x1, scratch = x2)`.

As on x86-64 (`Impl/Seed/X86_64/ExpandKey.lean`): RFC 4269 §2.3's round
keys `Ki0 = G(Key0 + Key2 - KCi)` and `Ki1 = G(Key1 - Key3 + KCi)`: the
inputs of `G` do not depend on its outputs, so all 32 are computed first
(`keyRound`), the first sixteen into `g16`'s words (`tSlot`) and the rest
into `uSlot`, and `G` of each sixteen is computed by `g16`, then copied to
the schedule, whose words are in the same order: a loop of two (`keyHalf`),
counting the halves left in `x3` once the rounds are done with it. The
scratch buffer is laid out as ECB's (`Ecb.lean`).

`Key0 || Key1` is kept in `x3` and `Key2 || Key3` in `x4`, as 64-bit words,
so that the rotations by eight bits are `ror`s. Nothing depends on the key
but the data: only the count decides the branches.
-/

namespace VG.Impl.Seed.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64

/-- The second sixteen inputs of `G`. -/
def uSlot : Nat := aSlot

/-- RFC 4269 §2.3's `KC1` to `KC16`. -/
def kcs : List (BitVec 32) :=
  [0x9E3779B9, 0x3C6EF373, 0x78DDE6E6, 0xF1BBCDCC, 0xE3779B99, 0xC6EF3733, 0x8DDE6E67, 0x1BBCDCCF,
   0x3779B99E, 0x6EF3733C, 0xDDE6E678, 0xBBCDCCF1, 0x779B99E3, 0xEF3733C6, 0xDE6E678D, 0xBCDCCF1B]

/-- The array of `G`'s input `i` (`0 ≤ i < 32`): `tSlot` or `uSlot`. -/
def gSlot (i : Nat) : Nat := if i < 16 then tSlot 0 else uSlot

def subW (d n m : Reg) : Instr := .sub .w d n m

/-- Round `j + 1`'s two inputs of `G` (`KCj+1` built in `x16`), then the
rotation of `Key0 || Key1` (odd rounds) or `Key2 || Key3` (even). -/
def keyRound (j : Nat) : List Instr :=
  [lsrI .x14 .x3 32, lsrI .x15 .x4 32, addW .x14 .x14 .x15,
   .movz .w .x16 ((kcs.getD j 0).extractLsb' 0 16) 0, .movk .w .x16 ((kcs.getD j 0).extractLsb' 16 16) 1,
   subW .x14 .x14 .x16, stW (gSlot (2 * j)) (2 * j % 16) .x14,
   subW .x14 .x3 .x4, addW .x14 .x14 .x16, stW (gSlot (2 * j + 1)) ((2 * j + 1) % 16) .x14] ++
  (if j % 2 = 0 then [rorI .x3 .x3 8] else [rorI .x4 .x4 56])

/-- The key's big-endian words `k` and `k + 4` into `d = Key_k || Key_k+1`. -/
def keyLoad2 (d : Reg) (k : Nat) : List Instr :=
  [.ldr .w .x14 .x0 k, .rev32 .x14 .x14, .lsl .x .x14 .x14 32,
   .ldr .w d .x0 (k + 4), .rev32 d d, orrR d d .x14]

/-- The key's big-endian words into `x3 = Key0 || Key1` and `x4 = Key2 || Key3`. -/
def keyLoad : List Instr := keyLoad2 .x3 0 ++ keyLoad2 .x4 8

/-- Copy `G`'s sixteen outputs to the schedule's words from `k`. -/
def keyStore (k : Nat) : List Instr :=
  (List.range 16).flatMap fun w => [ldW .x14 (tSlot 0) w, .str .w .x14 .x1 (4 * (k + w))]

/-- The second sixteen inputs to `g16`'s words. -/
def keyMove : List Instr :=
  (List.range 16).flatMap fun w => [ldW .x14 uSlot w, stW (tSlot 0) w .x14]

/-- `G` of `g16`'s words, copied to the schedule at `x1`, which moves on by
64 bytes, and the halves left in `x3` down; then, unless none is left, the
second sixteen inputs to `g16`'s words. -/
def keyHalf : Prog isa :=
  .seq (.block (g16 ++ keyStore 0 ++ [.addImm .x .x1 .x1 64, .subImm .x .x3 .x3 1]))
    (.ite (.nonzero .x .x3) (.block keyMove) (.block []))

def expandKey : Prog isa :=
  .seq (.block ([movR sb .x2] ++ saveRegs ++ keyLoad ++ (List.range 16).flatMap keyRound ++ [.movz .x .x3 2 0]))
    (.seq (.loop keyHalf (.nonzero .x .x3)) (.block restore))

end VG.Impl.Seed.AArch64
