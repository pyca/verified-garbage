import VerifiedGarbage.Impl.Seed.X86_64.Ecb

/-!
# SEED key expansion on x86-64

`vg_seed_expand_key(key = rdi, schedule = rsi, scratch = rdx)`.

RFC 4269 §2.3's round keys `Ki0 = G(Key0 + Key2 - KCi)` and
`Ki1 = G(Key1 - Key3 + KCi)`: the inputs of `G` do not depend on its
outputs, so all 32 are computed first (`keyRound`), the first sixteen into
`g16`'s words (`tSlot`) and the rest into `uSlot`, and `G` of each sixteen
is computed by `g16`, then copied to the schedule, whose words are in the
same order. The scratch buffer is laid out as ECB's (`Ecb.lean`), whose
callee-saved registers' slots it shares.

`Key0 || Key1` is kept in `r10` and `Key2 || Key3` in `r11`, as 64-bit
words, so that the rotations by eight bits are `ror`s. Nothing depends on
the key but the data: the code is straight-line.
-/

namespace VG.Impl.Seed.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

/-- The second sixteen inputs of `G`. -/
def uSlot : Nat := aSlot

/-- RFC 4269 §2.3's `KC1` to `KC16`. -/
def kcs : List (BitVec 32) :=
  [0x9E3779B9, 0x3C6EF373, 0x78DDE6E6, 0xF1BBCDCC, 0xE3779B99, 0xC6EF3733, 0x8DDE6E67, 0x1BBCDCCF,
   0x3779B99E, 0x6EF3733C, 0xDDE6E678, 0xBBCDCCF1, 0x779B99E3, 0xEF3733C6, 0xDE6E678D, 0xBCDCCF1B]

/-- The array of `G`'s input `i` (`0 ≤ i < 32`): `tSlot` or `uSlot`. -/
def gSlot (i : Nat) : Nat := if i < 16 then tSlot 0 else uSlot

/-- Where `G`'s input `i` goes: lane `i % 16` of its array. -/
def gIn (i : Nat) : MemOp := lane .r9 (gSlot i) (i % 16)

/-- Round `j + 1`'s two inputs of `G`, then the rotation of `Key0 || Key1`
(odd rounds) or `Key2 || Key3` (even). -/
def keyRound (j : Nat) : List Instr :=
  [movR .rax .r10, shrI .rax 32, movR .rcx .r11, shrI .rcx 32, .alu32 .add .rax (.reg .rcx),
   .alu32 .sub .rax (.imm (kcs.getD j 0)), .store32 (gIn (2 * j)) .rax,
   movR .rax .r10, .alu32 .sub .rax (.reg .r11), .alu32 .add .rax (.imm (kcs.getD j 0)),
   .store32 (gIn (2 * j + 1)) .rax] ++
  (if j % 2 = 0 then [rorI .r10 8] else [rorI .r11 56])

/-- The key's big-endian words `k` and `k + 4` into `d = Key_k || Key_k+1`. -/
def keyLoad2 (d : Reg) (k : Nat) : List Instr :=
  [.mov32 .rax (.mem { base := .rdi, disp := ((k : Nat) : Int) }), .bswap32 .rax, .shift .shl .rax 32,
   .mov32 d (.mem { base := .rdi, disp := ((k + 4 : Nat) : Int) }), .bswap32 d, .alu .or d (.reg .rax)]

/-- The key's big-endian words into `r10 = Key0 || Key1` and `r11 = Key2 || Key3`. -/
def keyLoad : List Instr := keyLoad2 .r10 0 ++ keyLoad2 .r11 8

/-- Copy `G`'s sixteen outputs to the schedule's words from `k`. -/
def keyStore (k : Nat) : List Instr :=
  (List.range 16).flatMap fun w =>
    [.mov32 .rax (.mem (lane .r9 (tSlot 0) w)),
     .store32 { base := .rsi, disp := ((4 * (k + w) : Nat) : Int) } .rax]

/-- The second sixteen inputs to `g16`'s words. -/
def keyMove : List Instr :=
  (List.range 16).flatMap fun w => [.mov32 .rax (.mem (lane .r9 uSlot w)), .store32 (lane .r9 (tSlot 0) w) .rax]

def expandKey : Prog isa :=
  .block ([movR .r9 .rdx] ++ savedRegs.map (fun (r, k) => st k r) ++ setG16Masks ++ keyLoad ++
    (List.range 16).flatMap keyRound ++ g16 ++ keyStore 0 ++ keyMove ++ g16 ++ keyStore 16 ++ restore)

end VG.Impl.Seed.X86_64
