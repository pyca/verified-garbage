module

public import VerifiedGarbage.Impl.Seed.PPC64LE.Ecb

/-!
# SEED key expansion on PPC64LE

`vg_seed_expand_key(key = r3, schedule = r4, scratch = r5)`.
As on AArch64 (`Impl/Seed/AArch64/ExpandKey.lean`) and x86-64
(`Impl/Seed/X86_64/ExpandKey.lean`): RFC 4269 §2.3's round keys
`Ki0 = G(Key0 + Key2 - KCi)` and `Ki1 = G(Key1 - Key3 + KCi)`: the inputs
of `G` do not depend on its outputs, so all 32 are computed first
(`keyRound`), the first sixteen into `g16`'s words (`tSlot`) and the rest
into `uSlot`, and `G` of each sixteen is computed by `g16`, then copied to
the schedule, whose words are in the same order: a loop of two (`keyHalf`),
counting the halves left in `r6` once the rounds are done with it. The
scratch buffer is laid out as ECB's (`Ecb.lean`).

`Key0 || Key1` is kept in `r6` and `Key2 || Key3` in `r7`, as 64-bit words,
so that the rotations by eight bits are `rotldi`s; the key's big-endian
words are loaded with `lwbrx`, indexed by the register each loads. The
sums and differences are 64-bit, of which `stw` keeps the low 32 bits, and
`KCi` is built in the low 32 bits of `r11` with `lis` and `ori`. Nothing
depends on the key but the data: only the count decides the branches.
-/

@[expose] public section

namespace VG.Impl.Seed.PPC64LE

open VG.PPC64LE VG.Impl.Aes.PPC64LE

/-- The second sixteen inputs of `G`. -/
def uSlot : Nat := aSlot

/-- RFC 4269 §2.3's `KC1` to `KC16`. -/
def kcs : List (BitVec 32) :=
  [0x9E3779B9, 0x3C6EF373, 0x78DDE6E6, 0xF1BBCDCC, 0xE3779B99, 0xC6EF3733, 0x8DDE6E67, 0x1BBCDCCF,
   0x3779B99E, 0x6EF3733C, 0xDDE6E678, 0xBBCDCCF1, 0x779B99E3, 0xEF3733C6, 0xDE6E678D, 0xBCDCCF1B]

/-- The array of `G`'s input `i` (`0 ≤ i < 32`): `tSlot` or `uSlot`. -/
def gSlot (i : Nat) : Nat := if i < 16 then tSlot 0 else uSlot

def subW (d n m : Reg) : Instr := .sub d n m

/-- Round `j + 1`'s two inputs of `G` (`KCj+1` built in `r11`), then the
rotation of `Key0 || Key1` (odd rounds) or `Key2 || Key3` (even). -/
def keyRound (j : Nat) : List Instr :=
  [shrI .r9 .r6 32, shrI .r10 .r7 32, addW .r9 .r9 .r10,
   .lis .r11 ((kcs.getD j 0).extractLsb' 16 16), .ori .r11 .r11 ((kcs.getD j 0).extractLsb' 0 16),
   subW .r9 .r9 .r11, stW (gSlot (2 * j)) (2 * j % 16) .r9,
   subW .r9 .r6 .r7, addW .r9 .r9 .r11, stW (gSlot (2 * j + 1)) ((2 * j + 1) % 16) .r9] ++
  (if j % 2 = 0 then [rorI .r6 .r6 8] else [rorI .r7 .r7 56])

/-- The key's big-endian words `k` and `k + 4` into `d = Key_k || Key_k+1`. -/
def keyLoad2 (d : Reg) (k : Nat) : List Instr :=
  [.li .r9 k, .loadRev .w .r9 .r3 .r9, .lsl .r9 .r9 32,
   .li d (k + 4), .loadRev .w d .r3 d, .logic .or d d .r9]

/-- The key's big-endian words into `r6 = Key0 || Key1` and `r7 = Key2 || Key3`. -/
def keyLoad : List Instr := keyLoad2 .r6 0 ++ keyLoad2 .r7 8

/-- Copy `G`'s sixteen outputs to the schedule's words from `k`. -/
def keyStore (k : Nat) : List Instr :=
  (List.range 16).flatMap fun w => [ldW .r9 (tSlot 0) w, .store .w .r9 .r4 (4 * (k + w))]

/-- The second sixteen inputs to `g16`'s words. -/
def keyMove : List Instr :=
  (List.range 16).flatMap fun w => [ldW .r9 uSlot w, stW (tSlot 0) w .r9]

/-- `G` of `g16`'s words, copied to the schedule at `r4`, which moves on by
64 bytes, and the halves left in `r6` down; then, unless none is left, the
second sixteen inputs to `g16`'s words. -/
def keyHalf : Prog isa :=
  .seq (.block (g16 ++ keyStore 0 ++ [.addi .r4 .r4 64, .subi .r6 .r6 1]))
    (.ite (.nonzero .d .r6) (.block keyMove) (.block []))

def expandKey : Prog isa :=
  .seq (.block ([movR sb .r5] ++ saveRegs ++ keyLoad ++ (List.range 16).flatMap keyRound ++ [.li .r6 2]))
    (.seq (.loop keyHalf (.nonzero .d .r6)) (.block restore))

end VG.Impl.Seed.PPC64LE
