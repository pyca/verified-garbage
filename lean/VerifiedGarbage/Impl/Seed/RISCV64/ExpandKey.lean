module

public import VerifiedGarbage.Impl.Seed.RISCV64.Ecb
public import VerifiedGarbage.Impl.Words.RISCV64.Word64

/-!
# SEED key expansion on RISC-V

`vg_seed_expand_key(key = a0, schedule = a1, scratch = a2)`.
As on PPC64LE (`Impl/Seed/PPC64LE/ExpandKey.lean`): RFC 4269 §2.3's round
keys `Ki0 = G(Key0 + Key2 - KCi)` and `Ki1 = G(Key1 - Key3 + KCi)`: the
inputs of `G` do not depend on its outputs, so all 32 are computed first
(`keyRound`), the first sixteen into `g16`'s words (`tSlot`) and the rest
into `uSlot`, and `G` of each sixteen is computed by `g16`, then copied to
the schedule, whose words are in the same order: a loop of two (`keyHalf`),
counting the halves left in `a4`. The scratch buffer is laid out as ECB's
(`Ecb.lean`).

`Key0 || Key1` is kept in `t5` and `Key2 || Key3` in `t6`, as 64-bit words
loaded big-endian a byte at a time (the contract states no alignment for
the key), so that the rotations by eight bits are two shifts and an `or`.
The sums and differences are 64-bit, of which `sw` keeps the low 32 bits,
and `KCi` is built in the low 32 bits of `t2` with `lui` and `addiw`. The
round keys are stored little-endian a byte at a time. Nothing depends on
the key but the data: only the count decides the branches.
-/

@[expose] public section

namespace VG.Impl.Seed.RISCV64

open VG.RISCV64 VG.Impl.Aes.RISCV64 VG.Impl.Words.RISCV64

/-- The second sixteen inputs of `G`. -/
def uSlot : Nat := aSlot

/-- RFC 4269 §2.3's `KC1` to `KC16`. -/
def kcs : List (BitVec 32) :=
  [0x9E3779B9, 0x3C6EF373, 0x78DDE6E6, 0xF1BBCDCC, 0xE3779B99, 0xC6EF3733, 0x8DDE6E67, 0x1BBCDCCF,
   0x3779B99E, 0x6EF3733C, 0xDDE6E678, 0xBBCDCCF1, 0x779B99E3, 0xEF3733C6, 0xDE6E678D, 0xBCDCCF1B]

/-- The array of `G`'s input `i` (`0 ≤ i < 32`): `tSlot` or `uSlot`. -/
def gSlot (i : Nat) : Nat := if i < 16 then tSlot 0 else uSlot

/-- `Key0 || Key1` and `Key2 || Key3`. -/
def keyA : Reg := .t5
def keyB : Reg := .t6

/-- Round `j + 1`'s two inputs of `G` (`KCj+1` built in `t2`), then the
rotation of `Key0 || Key1` right (odd rounds) or `Key2 || Key3` left (even)
by eight bits. -/
def keyRound (j : Nat) : List Instr :=
  [shrI t0 keyA 32, shrI t1 keyB 32, addW t0 t0 t1] ++ li32 t2 (kcs.getD j 0) ++
  [.sub t0 t0 t2, stW (gSlot (2 * j)) (2 * j % 16) t0,
   .sub t0 keyA keyB, addW t0 t0 t2, stW (gSlot (2 * j + 1)) ((2 * j + 1) % 16) t0] ++
  (if j % 2 = 0 then [shrI t0 keyA 8, shlI keyA keyA 56, .logic .or keyA keyA t0]
   else [shrI t0 keyB 56, shlI keyB keyB 8, .logic .or keyB keyB t0])

/-- The key's big-endian doublewords into `keyA` and `keyB`. -/
def keyLoad : List Instr := loadBE64 keyA t0 .a0 0 ++ loadBE64 keyB t0 .a0 8

/-- Copy `G`'s sixteen outputs to the schedule's words from `k`. -/
def keyStore (k : Nat) : List Instr :=
  (List.range 16).flatMap fun w => ldW t0 (tSlot 0) w :: storeLE32 t0 t1 .a1 (4 * (k + w))

/-- The second sixteen inputs to `g16`'s words. -/
def keyMove : List Instr :=
  (List.range 16).flatMap fun w => [ldW t0 uSlot w, stW (tSlot 0) w t0]

/-- `G` of `g16`'s words, copied to the schedule at `a1`, which moves on by
64 bytes, and the halves left in `a4` down; then, unless none is left, the
second sixteen inputs to `g16`'s words. -/
def keyHalf : Prog isa :=
  .seq (.block (g16 ++ keyStore 0 ++ [.addi .a1 .a1 64, .addi .a4 .a4 (-1)]))
    (.ite (.nonzero .a4) (.block keyMove) (.block []))

def expandKey : Prog isa :=
  .seq (.block (prologue .a2 ++ keyLoad ++ (List.range 16).flatMap keyRound ++ [.li .a4 2]))
    (.seq (.loop keyHalf (.nonzero .a4)) (.block seedRestore))

end VG.Impl.Seed.RISCV64
