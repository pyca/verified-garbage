module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.TComb

/-!
# x86-64: a table's selection in parts, to weave among other code

The constant-time selection of an entry of a table in memory (`selPassY`,
`selPassAt`), cut into parts that keep their state in vector registers
alone, so that other code, of scalar instructions, may run between them:
`selSetW` broadcasts the magnitude in `r8` (through `rcx`) and clears the
accumulators; `selChunkW … N i`, after part `i` of `N` of the other code,
computes the table's address in `rdx` and keeps entries
`chunkW N i + 1 … chunkW N (i + 1)` in the accumulators; `storeW` stores them.
An entry's first `np` 16-byte pieces are selected, 32 bytes at a time with
AVX2 (`selEntryY`), else 16 with SSE2 (`selEntryX`): the mask of an entry is
`pcmpeqd` of a counter (`ymm14` with AVX2, else `xmm11`) and the broadcast
magnitude (`xmm13`), so that no part needs a general-purpose register but
`rdx`.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

/-- Entry `m` (from 1) of a table at `rdx` whose entries are `st` bytes
apart, with SSE2: the mask of `xmm11 = xmm13` (both broadcasts of a
doubleword: `m` and the magnitude) in `xmm15`, `xmm11` incremented by
`xmm12` (one in every doubleword), and the entry's `np` 16-byte pieces kept
in the accumulators under the mask, through `xmm14`, as `selEntryAt` keeps
them. -/
def selEntryX (st np : Nat) (m : Nat) : List Instr :=
  [.xop (.bin .movdqa .xmm15 .xmm11), .xop (.bin .pcmpeqd .xmm15 .xmm13), .xop (.bin .paddd .xmm11 .xmm12)] ++
  (List.range np).flatMap fun c =>
    [.movdquLoad .xmm14 (tblAt (st * (m - 1) + 16 * c)), .xop (.bin .pand .xmm14 .xmm15),
      .xop (.bin .por (selAcc c) .xmm14)]

/-- Entry `m` of the table at `rdx`, its first `np` 16-byte pieces kept in
the accumulators: with AVX2 32 bytes at a time, else 16. -/
def selEntryW (avx2 : Bool) (st np m : Nat) : List Instr :=
  if avx2 then selEntryY st ((np + 1) / 2) (qY np) m else selEntryX st np m

/-- The entries selected before part `i` of `N` of the other code is done:
`16 i / N`, all sixteen after the last. -/
def chunkW (N i : Nat) : Nat := 16 * i / N

/-- After part `i` of `N`: `rdx = rdi + tbl`, and entries
`chunkW N i + 1 … chunkW N (i + 1)` kept in the accumulators. -/
def selChunkW (avx2 : Bool) (tbl st np N i : Nat) : List Instr :=
  if chunkW N (i + 1) = chunkW N i then [] else
  [.mov .rdx (.reg .rdi), .alu .add .rdx (.imm (BitVec.ofNat 32 tbl))] ++
  (List.range (chunkW N (i + 1) - chunkW N i)).flatMap fun e => selEntryW avx2 st np (chunkW N i + e + 1)

/-- The magnitude in `r8` broadcast to `xmm13` (`ymm13` with AVX2), one to
`xmm12` and the counter (`ymm14` with AVX2, else `xmm11`), through `rcx`,
and the accumulators of `np` pieces cleared. -/
def selSetW (avx2 : Bool) (np : Nat) : List Instr :=
  if avx2 then
    [.vop (.vmovq .xmm13 .r8), .vop (.vpbroadcastd .l256 .xmm13 .xmm13), .mov32 .rcx (.imm 1),
      .vop (.vmovq .xmm12 .rcx), .vop (.vpbroadcastd .l256 .xmm12 .xmm12), .vop (.vmovdqa .l256 .xmm14 .xmm12)] ++
    (List.range ((np + 1) / 2)).map fun c => .vop (.vbin .vpxor .l256 (selAcc c) (selAcc c) (selAcc c))
  else
    [.xop (.movq .xmm13 .r8), .xop (.pshufd .xmm13 .xmm13 0), .mov32 .rcx (.imm 1),
      .xop (.movq .xmm12 .rcx), .xop (.pshufd .xmm12 .xmm12 0), .xop (.bin .movdqa .xmm11 .xmm12)] ++
    (List.range np).map fun c => .xop (.bin .pxor (selAcc c) (selAcc c))

/-- The accumulators of `np` pieces stored to `o` (and the upper halves of
the `ymm` registers cleared, with AVX2). -/
def storeW (avx2 : Bool) (o np : Nat) : List Instr :=
  if avx2 then
    (List.range ((np + 1) / 2)).map (fun c => .vmovdquStore .l256 (sc (o + 16 * qY np c)) (selAcc c)) ++
      [.vop .vzeroupper]
  else (List.range np).map fun c => .movdquStore (sc (o + 16 * c)) (selAcc c)

end VG.Impl.Weierstrass.X86_64
