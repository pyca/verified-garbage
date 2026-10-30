module

public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt4

/-!
# ML-DSA matrix sampling with five initial SHAKE128 blocks

Squeeze three blocks and parse them, then two more and parse 112 candidates.
If all four polynomials have 256 coefficients, return without a sixth
permutation. Otherwise squeeze the sixth block and parse its 56 candidates.
The failure bound and sampled coefficients are those of the six-block code.
Counts are saved between batches; checking them is allowed to leak the
public matrix seeds, just like the rejection sampler itself.

A segment parses its candidates eight at a time (`vgrp`, counted in `r10`):
while fewer than 249 coefficients are sampled (`j ≤ 248`), with AVX2 code,
which makes the eight 23-bit candidates of the 24 bytes at `rsi` the
doublewords of `ymm0`, the first four in the low lane (`vcand`: `vpermq`
puts bytes 0 to 15 of the 32 it loads in the low lane and 8 to 23 in the
high one, `vpshufb` the three bytes of each candidate in its doubleword and
`vpand` clears bit 23); `x - q` is negative exactly for the candidates less
than `q`, whose sign bytes `vpshufb` moves to the bottom of each lane, so
that `vpmovmskb` gives the mask `m₀` of the low lane's in bits 0 to 3 of
`eax` and `m₁` of the high lane's in bits 16 to 19. The static's mask of
each (`idxD`) moves its candidates to the bottom of its lane (`vpshufb`),
whose four doublewords are stored to `a[j..j+4)`, and `j` advances by the
static's count of the mask (`vput`). Otherwise it runs eight iterations of
`vg_mldsa_rej_ntt_poly`'s loop (`rnBody`, counted in `rcx`), which stores
nothing once `j` = 256. A value stored but not counted lies past the
coefficients sampled, and is overwritten by the next. The static's address
is in `r11`, and its constants in `ymm8` to `ymm11`.
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86_64.Sample.Rej5

open VG.X86_64
open VG.Impl.MlKem.X86_64 (at_)
open VG.Impl.MlKem.X86_64.Sample4 (idxE)
open VG.Impl.MlDsa.X86_64.Sample (rnBody)
open VG.Impl.Sha3.X86_64.X4 (vb)
open VG.Impl.MlKem.X86_64.Sample4 (pro epi absorb4 squeezes oRc oBuf)
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ zeroJ)
open VG.Impl.Sha3.X86_64.X4 (rcTable)

/-! ## Eight candidates at a time -/

/-- The bits set in the 4-bit `m`, in increasing order. -/
def setBits4 (m : Nat) : List Nat := (List.range 4).filter fun i => m / 2 ^ i % 2 = 1

/-- The `vpshufb` mask that moves the doublewords of the set bits of `m` to
the bottom, in order: bytes `4c` to `4c + 3` of the mask are `4i` to
`4i + 3` for the `c`-th set bit `i`, and the others `0x80` (zero). -/
def idxD (m : Nat) : BitVec 128 := ofBytes fun j =>
  if j / 4 < (setBits4 m).length then BitVec.ofNat 8 (4 * (setBits4 m).getD (j / 4) 0 + j % 4) else 0x80

/-- Quadword `h` (0 or 1) of `idxD m`. -/
def idxDQ (m h : Nat) : BitVec 64 := (idxD m).extractLsb' (64 * h) 64

/-- The constants of the vector code, four quadwords each, from byte `oCst`
of the static (in `ymm8` to `ymm11`): the `vpshufb` mask that puts bytes
`3i` to `3i + 2` of the 24 in doubleword `i`, from bytes 0 to 15 in the low
lane and 8 to 23 in the high one; `2²³ - 1` and `q` in each doubleword; and
the `vpshufb` mask that moves byte `4i + 3` of each lane to byte `i`. -/
def consts : List (BitVec 64) :=
  [0x8005040380020100, 0x800b0a0980080706, 0x8009080780060504, 0x800f0e0d800c0b0a,
    0x007fffff007fffff, 0x007fffff007fffff, 0x007fffff007fffff, 0x007fffff007fffff,
    0x007fe001007fe001, 0x007fe001007fe001, 0x007fe001007fe001, 0x007fe001007fe001,
    0x808080800f0b0703, 0x8080808080808080, 0x808080800f0b0703, 0x8080808080808080]

/-- The offset of the constants in the static, after the masks. -/
def oCst : Nat := 256

/-- The offset of the counts in the static, after the constants. -/
def oNum : Nat := 384

/-- The static: the masks (`idxDQ`, two quadwords for each `m < 16`), the
constants and, from `oNum`, the number of set bits of each `m`
(`(setBits4 m).length`, a quadword each). -/
def tblWords : List (BitVec 64) :=
  (List.range 32).map (fun i => idxDQ (i / 2) (i % 2)) ++ consts ++
    (List.range 16).map fun m => BitVec.ofNat 64 (setBits4 m).length

/-- The static's name. -/
def tblName : String := "VG_MLDSA_REJ_TBL"

/-- The static's address to `r11`, and its constants into `ymm8` to `ymm11`. -/
def cstLoad : List Instr :=
  [.leaSym .r11 tblName, .vmovdquTbl .xmm8 (at_ .r11 oCst) tblName tblWords,
    .vmovdquTbl .xmm9 (at_ .r11 (oCst + 32)) tblName tblWords,
    .vmovdquTbl .xmm10 (at_ .r11 (oCst + 64)) tblName tblWords,
    .vmovdquTbl .xmm11 (at_ .r11 (oCst + 96)) tblName tblWords]

/-- `[r11 + 4 r + oNum]`: the count of `m`, for `r = 2 m`. -/
def numE (r : Reg) : MemOp := { base := .r11, index := some r, scale := 4, disp := oNum }

/-- `[rbp + 4 rdi]`: `a[j]`. -/
def aJ : MemOp := { base := .rbp, index := some .rdi, scale := 4 }

/-- The eight candidates of the 24 bytes at `rsi` in the doublewords of
`ymm0`, and the masks `m₀`, `m₁` of those less than `q` of each lane in bits
0 to 3 and 16 to 19 of `eax`. -/
def vcand : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rsi 0), .vop (.vpermq .xmm0 .xmm0 0x94), vb .vpshufb .xmm0 .xmm0 .xmm8,
    vb .vpand .xmm0 .xmm0 .xmm9, vb .vpsubd .xmm1 .xmm0 .xmm10, vb .vpshufb .xmm1 .xmm1 .xmm11,
    .vpmovmskb .l256 .rax .xmm1]

/-- The candidates less than `q` of the low lane to `a[j..]`, and `j` advanced
by their count: `rdx` and `rax` become `2 m₀` and `2 m₁`, and the masks of
`m₀` and `m₁` move those of each lane to its bottom (`vpshufb`). -/
def vputA : List Instr :=
  [.mov32 .rdx (.reg .rax), .alu32 .and .rdx (.imm 0xf), .shift32 .shr .rax 16,
    .alu32 .add .rdx (.reg .rdx), .alu32 .add .rax (.reg .rax),
    .vmovdquTbl .xmm2 (idxE .rdx) tblName tblWords, .vmovdquTbl .xmm3 (idxE .rax) tblName tblWords,
    .vop (.vinserti128 .xmm2 .xmm2 .xmm3 1), vb .vpshufb .xmm0 .xmm0 .xmm2,
    .vmovdquStore .l128 aJ .xmm0, .aluTbl .add .rdi (numE .rdx) tblName tblWords]

/-- Those of the high lane to `a[j..]`, `j` advanced by their count, and `rsi`
by 24. -/
def vputB : List Instr :=
  [.vop (.vextracti128 .xmm0 .xmm0 1), .vmovdquStore .l128 aJ .xmm0,
    .aluTbl .add .rdi (numE .rax) tblName tblWords, .alu .add .rsi (.imm 24)]

/-- The candidates less than `q` to `a[j..]`, and `j` and `rsi` advanced. -/
def vput : List Instr := vputA ++ vputB

/-- Eight iterations of `vg_mldsa_rej_ntt_poly`'s loop. -/
def sca8 : Prog isa := .seq (.block [.mov32 .rcx (.imm 8)]) (.loop rnBody .ne)

/-- Eight candidates: with AVX2 if `j ≤ 248`, and otherwise with `sca8`; then
`r10` counts down. -/
def vgrp : Prog isa :=
  .seq (.block [.alu .cmp .rdi (.imm 249)])
    (.seq (.ite .b (.block (vcand ++ vput)) sca8) (.block [.alu .sub .r10 (.imm 1)]))

/-- Start a segment of `count` candidates (a multiple of 8) at candidate
`off` of one 504-byte buffer. -/
def setup (k off count : Nat) : List Instr :=
  [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * k + 3 * off))),
   .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * k))),
   .mov .rdi (.mem (at_ .rbx (oJ + 8 * k))), .mov32 .r10 (.imm (BitVec.ofNat 32 (count / 8)))] ++ cstLoad

/-- Parse `count` candidates, starting at `off`. -/
def parse (k off count : Nat) : Prog isa := .seq (.block (setup k off count)) (.loop vgrp .ne)

/-- Parse a segment and save its coefficient count. -/
def segment (k off count : Nat) : Prog isa :=
  .seq (parse k off count) (.block [.store (at_ .rbx (oJ + 8 * k)) .rdi])

/-- Parse a segment of all four buffers. -/
def batch (off count : Nat) : Prog isa :=
  .seq (segment 0 off count) (.seq (segment 1 off count) (.seq (segment 2 off count) (segment 3 off count)))

/-- `r14` is one iff every stored count is 256. Counts never exceed 256. -/
def flags : List Instr := .mov32 .r14 (.imm 1) :: (List.range 4).flatMap fun k =>
  [.mov .rax (.mem (at_ .rbx (oJ + 8 * k))), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax)]

/-- The optional sixth block, with the accumulator reset before squeezing. -/
def fallback : Prog isa :=
  .seq (.block [.mov32 .r14 (.imm 1)])
    (.seq (squeezes 2 1) (.seq (batch 112 56) (.block flags)))

/-- Check the five-block result and finish with the original six-block bound. -/
def finish : Prog isa :=
  .seq (.block (flags ++ ([.alu32 .cmp .r14 (.imm 0)] : List Instr)))
    (.seq (.ite .e fallback (.block [])) (.block (([.vop .vzeroupper] : List Instr) ++ VG.Impl.MlKem.X86_64.Sample4.epi)))

def rejNTT4Avx2 : Prog isa :=
  .seq (.block (VG.Impl.MlKem.X86_64.Sample4.pro ++ rcTable .rbx (oRc / 32) ++ absorb4))
    (.seq (squeezes 0 3) (.seq (.block zeroJ)
      (.seq (segment 0 0 168) (.seq (segment 1 0 168) (.seq (segment 2 0 168) (.seq (segment 3 0 168)
        (.seq (squeezes 0 2) (.seq (batch 0 112) finish))))))))

end VG.Impl.MlDsa.X86_64.Sample.Rej5
