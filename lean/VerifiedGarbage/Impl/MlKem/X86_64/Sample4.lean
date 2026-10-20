module

public import VerifiedGarbage.Impl.MlKem.X86_64.Sample
public import VerifiedGarbage.Impl.Sha3.X86_64.X4

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4` and `vg_mlkem_sample_ntt4_avx2`

`sampleNTT4(seeds = rdi, a = rsi, scratch = rdx) -> eax` runs `SampleNTT`
on four seeds. The baseline implementation (`sampleNTT4`) calls
`vg_mlkem_sample_ntt` on each, with the prologue and epilogue below and its
scratch space from byte 6144 of `scratch`. The one for AVX2
(`sampleNTT4Avx2`) runs the four at once: the four SHAKE128 instances in the four 64-bit
elements of `ymm` registers (`Impl/Sha3/X86_64/X4.lean`). It keeps
`scratch` in `rbx`, `seeds` in `r12`, `a` in `r13` and the AND of the
results in `r14`, and saves their caller's values and `rbp`'s in
`scratch[4384..4424)`. `scratch` holds, from byte 0, the four states
(interleaved, 800 bytes), the second buffer of the permutation (800
bytes), the table of the round constants (768 bytes), a buffer of 504
bytes of the XOF output of each seed (from byte `2368 + 504 k`), the
number `j` of coefficients of each seed sampled so far (from byte
`4424 + 8 k`). The masks of the compaction (`idxQ`, 4096 bytes), the
constants of the vector code (`consts`, 96 bytes) and the number of set
bits of each byte are a static (`tblWords`, `tblName`), whose address it
keeps in `r11`.

Each seed is at most 34 bytes, so the padded message is one block: the
code zeroes the states, writes the seed's bytes, SHAKE's suffix `0x1f` (at
byte 34) and the last bit of the padding (`0x80`, at byte 167) into each,
and permutes them. It then copies the first 168 bytes of each state to its
buffer, and permutes them again, three times in all, in a loop (`squeezes`)
whose output pointer is `rbp` and whose count is `r10`. It then loads the
static's address (`tabAddr`), and the constants into `ymm8` to `ymm10`.

For each seed it runs 168 iterations of `SampleNTT`'s loop on its 504 bytes
(`run1`), which samples 256 coefficients but for about one seed in 120,
eight at a time (`vgrp`). For 16-bit coefficients, while fewer than 241
coefficients are sampled (`j ≤ 240`), it does so with AVX2 code, which
computes the sixteen candidates `d₁`, `d₂` of the 24 bytes in the words of
`ymm0`, the first eight in the low lane, and the masks `m₀`, `m₁` of those
less than `q` of each lane in `eax` (`vcand`); it then moves those of each
lane to its bottom with `vpshufb`, whose indices are the static's masks of
`m₀` and `m₁`, stores the low lane's eight words to `a[j..j+8)`, adds to
`j` the static's count of `m₀`, and does the same with the high lane and
`m₁` (`vput`). Otherwise (`j ≥ 241`, or 32-bit coefficients), while
`j < 256`, it runs eight iterations of the loop of `vg_mlkem_sample_ntt`
(`snBody`), which stops at 256; once `j` = 256 it only moves past their 24
bytes (`scaG`), since they would store nothing. A value stored but not
counted lies past the coefficients sampled, and is overwritten by the next.
It keeps each seed's `j`.

Only if a seed has fewer than 256 coefficients (`tail4`), the states are
still there: the code squeezes two more blocks of each seed to its buffer
(bytes 504 to 839 of its output), and runs 112 more iterations of the loop
on them for each seed, from its `j` (`run2`; for a seed that has 256, they
store nothing). That is `SampleNTT`'s loop bounded by `minIterations` = 280
iterations, so a seed that still has fewer than 256 coefficients fails the
specification's bound too. It returns 1 if every seed has 256 coefficients
(the AND of `j >> 8`), and 0 otherwise.

The loops' branches, the addresses of their loads from the table and of
their stores, and whether the function squeezes the two more blocks, depend
on the XOF output, a function of the seeds, and on nothing else; every other
address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64.Sample4

open VG.X86_64
open VG.Impl.MlKem.X86_64 (snBody sampleNTT)
open VG.Impl.Sha3.X86_64.X4 (vb st permute4 rcTable)

/-- The offsets in the scratch space. -/
def oTmp : Nat := 800
def oRc : Nat := 1600
def oBuf : Nat := 2368
def oSave : Nat := 4384
def oScalar : Nat := 6144
/-- Where `j` of seed `k` is kept, at `scratch + oCnt + 8 k`. -/
def oCnt : Nat := 4424

/-- The registers saved, at `scratch + oSave + 8 k`. -/
def saved : List Reg := [.rbx, .rbp, .r12, .r13, .r14]

/-- Save the callee-saved registers, keep the pointers, and `r14 ← 1`. -/
def pro : List Instr :=
  (List.range 5).map (fun k => .store (at_ .rdx (oSave + 8 * k)) (saved.getD k .rbx)) ++
    [.mov .rbx (.reg .rdx), .mov .r12 (.reg .rdi), .mov .r13 (.reg .rsi), .mov32 .r14 (.imm 1)]

/-- The four states, zeroed. -/
def zero4 : List Instr :=
  vb .vpxor .xmm0 .xmm0 .xmm0 :: (List.range 25).flatMap fun i => [st .rbx i .xmm0]

/-- Bytes 0 to 33 of state `k`: the 34 bytes of seed `k`, as four lanes and
two bytes. -/
def seedLanes (k : Nat) : List Instr :=
  (List.range 4).flatMap (fun i =>
    [.mov .rax (.mem (at_ .r12 (34 * k + 8 * i))), .store (at_ .rbx (32 * i + 8 * k)) .rax]) ++
  [.movzx8 .rax (at_ .r12 (34 * k + 32)), .store8 (at_ .rbx (128 + 8 * k)) .rax,
    .movzx8 .rax (at_ .r12 (34 * k + 33)), .store8 (at_ .rbx (128 + 8 * k + 1)) .rax]

/-- The padded blocks of the four seeds, XORed into the zero states: the
seeds, SHAKE's suffix at byte 34 (byte 2 of lane 4) and `0x80` at byte 167
(byte 7 of lane 20). -/
def absorb4 : List Instr :=
  zero4 ++ (List.range 4).flatMap seedLanes ++
    .mov32 .rax (.imm 0x1f) :: (List.range 4).flatMap (fun k => [.store8 (at_ .rbx (128 + 8 * k + 2)) .rax]) ++
    .mov32 .rax (.imm 0x80) :: (List.range 4).flatMap fun k => [.store8 (at_ .rbx (640 + 8 * k + 7)) .rax]

/-- The arguments of `permute4`. -/
def permArgs : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 oTmp)),
    .mov .rdx (.reg .rbx), .alu .add .rdx (.imm (BitVec.ofNat 32 oRc)), .mov .rcx (.reg .rbx),
    .alu .add .rcx (.imm (BitVec.ofNat 32 oBuf))]

/-- The first 168 bytes of each state to the block of its output at `rbp`
(that of state `k` at `rbp + 504 k`). -/
def extract : List Instr :=
  (List.range 4).flatMap fun k => (List.range 21).flatMap fun i =>
    [.mov .rax (.mem (at_ .rbx (32 * i + 8 * k))), .store (at_ .rbp (504 * k + 8 * i)) .rax]

/-- `n` iterations of `body` (`n > 0`), with `rbp` from `rbx + start`,
advanced by `step` after each, and `r10` counting them down. -/
def blocks (start step n : Nat) (body : Prog isa) : Prog isa :=
  .seq (.block [.mov .rbp (.reg .rbx), .alu .add .rbp (.imm (BitVec.ofNat 32 start)),
      .mov32 .r10 (.imm (BitVec.ofNat 32 n))])
    (.loop (.seq body (.block [.alu .add .rbp (.imm (BitVec.ofNat 32 step)), .alu .sub .r10 (.imm 1)])) .ne)

/-- Permute the states and squeeze a block to `rbp`. -/
def squeeze (fast : Bool := false) : Prog isa :=
  .seq (.block permArgs) (.seq (permute4 fast) (.block extract))

/-- Squeeze blocks `b` to `b + n - 1`. -/
def squeezes (b n : Nat) (fast : Bool := false) : Prog isa := blocks (oBuf + 168 * b) 168 n (squeeze fast)

/-! ## The vector sampling -/

/-- The positions of the set bits of the byte `m`, in order. -/
def setBits (m : Nat) : List Nat := (List.range 8).filter fun i => m / 2 ^ i % 2 = 1

/-- The `vpshufb` mask that moves the words of the set bits of `m` to the
bottom, in order: bytes `2c, 2c + 1` of the mask are `2i, 2i + 1` for the
`c`-th set bit `i`, and the others `0x80` (zero). -/
def idxV (m : Nat) : BitVec 128 := ofBytes fun j =>
  if j / 2 < (setBits m).length then BitVec.ofNat 8 (2 * (setBits m).getD (j / 2) 0 + j % 2) else 0x80

/-- Quadword `h` (0 or 1) of `idxV m`. -/
def idxQ (m h : Nat) : BitVec 64 := (idxV m).extractLsb' (64 * h) 64

/-- The constants of the vector code, four quadwords each, from byte `oCst`
of the static (in `ymm8` to `ymm10`): the `vpshufb` mask that puts bytes
`3i, 3i + 1` and `3i + 1, 3i + 2` of the 24 in words `2i` and `2i + 1`
(bytes 0 to 11 in the low lane and 12 to 23, from byte 8, in the high one),
`0xfff` and `q` in each word. -/
def consts : List (BitVec 64) :=
  [0x0504040302010100, 0x0b0a0a0908070706, 0x0908080706050504, 0x0f0e0e0d0c0b0b0a,
    0x0fff0fff0fff0fff, 0x0fff0fff0fff0fff, 0x0fff0fff0fff0fff, 0x0fff0fff0fff0fff,
    0x0d010d010d010d01, 0x0d010d010d010d01, 0x0d010d010d010d01, 0x0d010d010d010d01]

/-- The offset of the constants in the static, after the masks. -/
def oCst : Nat := 4096

/-- The offset of the counts in the static, after the constants. -/
def oNum : Nat := 4192

/-- The static: the masks (`idxQ`, two quadwords for each byte `m`), the
constants and, from `oNum`, the number of set bits of each byte
(`(setBits m).length`, a quadword each): the words the instructions that read
it carry, and the emitter writes. -/
def tblWords : List (BitVec 64) :=
  (List.range 512).map (fun i => idxQ (i / 2) (i % 2)) ++ consts ++
    (List.range 256).map fun m => BitVec.ofNat 64 (setBits m).length

/-- The static's name. -/
def tblName : String := "VG_MLKEM_SAMPLE_TBL"

/-- The static's address to `r11`. -/
def tabAddr : List Instr := [.leaSym .r11 tblName]

/-- The constants into `ymm8` to `ymm10`, from the static at `r11`. -/
def cstLoad : List Instr :=
  [.vmovdquTbl .xmm8 (at_ .r11 oCst) tblName tblWords, .vmovdquTbl .xmm9 (at_ .r11 (oCst + 32)) tblName tblWords,
    .vmovdquTbl .xmm10 (at_ .r11 (oCst + 64)) tblName tblWords]

/-- `[r11 + 8 r]`: the mask of `m`, for `r = 2 m`. -/
def idxE (r : Reg) : MemOp := { base := .r11, index := some r, scale := 8 }

/-- `[r11 + 4 r + oNum]`: the count of `m`, for `r = 2 m`. -/
def numE (r : Reg) : MemOp := { base := .r11, index := some r, scale := 4, disp := oNum }

/-- `[rbp + 2 rdi]`: `a[j]`. -/
def aJ16 : MemOp := { base := .rbp, index := some .rdi, scale := 2 }

/-- The bytes of a polynomial: 512 for 16-bit coefficients, 1024 otherwise. -/
def pBytes (w16 : Bool) : Nat := if w16 then 512 else 1024

/-- The sixteen candidates of the 24 bytes at `rsi` in the words of `ymm0`
(the first eight in the low lane), and in `eax` the masks `m₀` (bits 0 to 7)
and `m₁` (bits 24 to 31) of those less than `q`, bit `i` for candidate `i`
of each half: of the 32 bytes at `rsi`, `vpermq` puts bytes 0 to 15 in the low
lane and 8 to 23 in the high one; `vpshufb` puts bytes `3i, 3i + 1` in word
`2i` and `3i + 1, 3i + 2` in word `2i + 1`; the odd words are shifted right by
4 (`vpsrlw`, `vpblendw`) and all are cut to 12 bits (`vpand`). `vpcmpgtw` and
`vpacksswb` turn the comparisons with `q` into bytes for `vpmovmskb`. -/
def vcand : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rsi 0), .vop (.vpermq .xmm0 .xmm0 0x94), vb .vpshufb .xmm0 .xmm0 .xmm8,
    .vop (.vshift .psrlw .l256 .xmm1 .xmm0 4), .vop (.vpblendw .l256 .xmm0 .xmm0 .xmm1 0xAA),
    vb .vpand .xmm0 .xmm0 .xmm9, vb .vpcmpgtw .xmm1 .xmm10 .xmm0, vb .vpacksswb .xmm1 .xmm1 .xmm1,
    .vpmovmskb .l256 .rax .xmm1]

/-- The candidates less than `q` of the low half to `a[j..]`, and `j` advanced
by their count: `rdx` and `rax` become `2 m₀` and `2 m₁`; the masks of `m₀` and
`m₁` move those of each half to its bottom (`vpshufb`), and the low half's
eight words go to `a[j]`. -/
def vputA : List Instr :=
  [.mov32 .rdx (.reg .rax), .alu32 .and .rdx (.imm 0xff), .shift32 .shr .rax 24,
    .alu32 .add .rdx (.reg .rdx), .alu32 .add .rax (.reg .rax),
    .vmovdquTbl .xmm2 (idxE .rdx) tblName tblWords, .vmovdquTbl .xmm3 (idxE .rax) tblName tblWords,
    .vop (.vinserti128 .xmm2 .xmm2 .xmm3 1), vb .vpshufb .xmm0 .xmm0 .xmm2,
    .vmovdquStore .l128 aJ16 .xmm0, .aluTbl .add .rdi (numE .rdx) tblName tblWords]

/-- The high half's eight words to `a[j]`, `j` advanced by their count, and
`rsi` by 24. -/
def vputB : List Instr :=
  [.vop (.vextracti128 .xmm0 .xmm0 1), .vmovdquStore .l128 aJ16 .xmm0,
    .aluTbl .add .rdi (numE .rax) tblName tblWords, .alu .add .rsi (.imm 24)]

/-- The candidates less than `q` to `a[j..]`, and `j` and `rsi` advanced. -/
def vput : List Instr := vputA ++ vputB

/-- Eight iterations of the loop of `vg_mlkem_sample_ntt` (`snBody`). -/
def sca8 (w16 : Bool) : Prog isa := .seq (.block [.mov32 .rcx (.imm 8)]) (.loop (snBody w16) .ne)

/-- Eight iterations of the loop with `snBody` if `j < 256`; otherwise they
would store nothing, and only `rsi` moves past their 24 bytes. -/
def scaG (w16 : Bool) : Prog isa :=
  .seq (.block [.alu .cmp .rdi (.imm 256)]) (.ite .b (sca8 w16) (.block [.alu .add .rsi (.imm 24)]))

/-- Eight iterations of the loop: for 16-bit coefficients with AVX2 if
`j ≤ 240`, and otherwise with `scaG`. -/
def vgrp (w16 : Bool := false) : Prog isa :=
  if w16 then .seq (.block [.alu .cmp .rdi (.imm 241)]) (.ite .b (.seq (.block vcand) (.block vput)) (scaG w16))
  else scaG w16

/-- Eight iterations of the loop; `r10` counts down. -/
def vbody (w16 : Bool := false) : Prog isa := .seq (vgrp w16) (.block [.alu .sub .r10 (.imm 1)])

/-- The setup of the loop of seed `k`. -/
def setup (k : Nat) (w16 : Bool := false) : List Instr :=
  [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * k))),
    .mov32 .rdi (.imm 0), .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (pBytes w16 * k))),
    .mov32 .r10 (.imm 21)]

/-- Return `r14`, and restore the callee-saved registers (`rbx` last). -/
def epi : List Instr :=
  .mov32 .rax (.reg .r14) ::
    ((List.range 4).map fun k => .mov (saved.getD (4 - k) .rbx) (.mem (at_ .rbx (oSave + 8 * (4 - k))))) ++
    [.mov .rbx (.mem (at_ .rbx oSave))]

/-- 168 iterations of the loop on the buffer of seed `k`, to polynomial
`k`, and `j` kept. -/
def run1 (k : Nat) (w16 : Bool := false) : Prog isa :=
  .seq (.block (setup k w16 ++ cstLoad)) (.seq (.loop (vbody w16) .ne) (.block [.store (at_ .rbx (oCnt + 8 * k)) .rdi]))

/-- The setup of the continuation of seed `k`: from `j` kept. -/
def contSetup (k : Nat) (w16 : Bool := false) : List Instr :=
  [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * k))),
    .mov .rdi (.mem (at_ .rbx (oCnt + 8 * k))), .mov .rbp (.reg .r13),
    .alu .add .rbp (.imm (BitVec.ofNat 32 (pBytes w16 * k))), .mov32 .r10 (.imm 14)]

/-- 112 more iterations of the loop, on the buffer of seed `k` (bytes 504
to 839 of its output), and `j` kept. -/
def run2 (k : Nat) (w16 : Bool := false) : Prog isa :=
  .seq (.block (contSetup k w16 ++ cstLoad)) (.seq (.loop (vbody w16) .ne) (.block [.store (at_ .rbx (oCnt + 8 * k)) .rdi]))

/-- `r14` is 1 if every seed has 256 coefficients, and 0 otherwise: the AND of
the seeds' `j >> 8` (`j ≤ 256`). -/
def cntFlags : List Instr := .mov32 .r14 (.imm 1) :: (List.range 4).flatMap fun k =>
  [.mov .rax (.mem (at_ .rbx (oCnt + 8 * k))), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax)]

/-- Two more blocks of each seed, and 112 more iterations on each. -/
def more4 (fast : Bool := false) (w16 : Bool := false) : Prog isa :=
  .seq (.block [.mov32 .r14 (.imm 1)]) (.seq (squeezes 0 2 fast) (.seq (.block tabAddr)
    (.seq (run2 0 w16) (.seq (run2 1 w16) (.seq (run2 2 w16) (.seq (run2 3 w16) (.block cntFlags)))))))

/-- If a seed has fewer than 256 coefficients, `more4`; then the return
value. `vzeroupper` clears the upper halves of the vector registers, so that
the caller's SSE code does not pay for mixing them. -/
def tail4 (fast : Bool := false) (w16 : Bool := false) : Prog isa :=
  .seq (.block (cntFlags ++ ([.alu32 .cmp .r14 (.imm 0)] : List Instr)))
    (.seq (.ite .e (more4 fast w16) (.block [])) (.block (([.vop .vzeroupper] : List Instr) ++ epi)))

/-- `vg_mlkem_sample_ntt4_avx2`. -/
def sampleNTT4Avx2 (fast : Bool := false) (w16 : Bool := false) : Prog isa :=
  .seq (.block (pro ++ rcTable .rbx (oRc / 32) ++ absorb4))
    (.seq (squeezes 0 3 fast) (.seq (.block tabAddr)
      (.seq (run1 0 w16) (.seq (run1 1 w16) (.seq (run1 2 w16) (.seq (run1 3 w16) (tail4 fast w16)))))))

/-- `vg_mlkem_sample_ntt` on seed `k`, and `r14 ← r14 ∧ result`. -/
def callK (k : Nat) (w16 : Bool := false) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * k))),
      .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (pBytes w16 * k))), .mov .rdx (.reg .rbx),
      .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))])
    (.seq (.call (if w16 then "vg_mlkem16_sample_ntt" else "vg_mlkem_sample_ntt") (sampleNTTW w16))
      (.block [.alu32 .and .r14 (.reg .rax)]))

/-- `vg_mlkem_sample_ntt4`: `vg_mlkem_sample_ntt` on each seed, with the
prologue and epilogue of `vg_mlkem_sample_ntt4_avx2`. -/
def sampleNTT4 (w16 : Bool := false) : Prog isa :=
  .seq (.block pro) (.seq (callK 0 w16) (.seq (callK 1 w16) (.seq (callK 2 w16) (.seq (callK 3 w16) (.block epi)))))

end VG.Impl.MlKem.X86_64.Sample4
