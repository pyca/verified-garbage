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
`4424 + 8 k`), and, from byte 4480, a table for the sampling (`tabQ`,
2048 bytes) and the constants of the vector code (`consts`, 192 bytes).

Each seed is at most 34 bytes, so the padded message is one block: the
code zeroes the states, writes the seed's bytes, SHAKE's suffix `0x1f` (at
byte 34) and the last bit of the padding (`0x80`, at byte 167) into each,
and permutes them. It then copies the first 168 bytes of each state to its
buffer, and permutes them again, three times in all, in a loop (`squeezes`)
whose output pointer is `rbp` and whose count is `r10`. It then writes the
table and the constants, which it loads into `ymm8` to `ymm13`.

For each seed it runs 168 iterations of `SampleNTT`'s loop on its 504 bytes
(`run1`), which samples 256 coefficients but for about one seed in 120, four at a time (`vgrp`): while
fewer than 249 coefficients are sampled (`j ≤ 248`), with AVX2 code, which
computes the eight candidates `d₁`, `d₂` of the 12 bytes in the
doublewords of `ymm0` and the mask `m` of those less than `q` in `eax`
(bit `i` for candidate `i`, `vcand`), moves those to the bottom of `ymm0`
with `vpermd`, whose indices are the nibbles of entry `m` of the table,
stores the eight doublewords to `a[j..j+8)`, and adds to `j` the number
of candidates less than `q`, the entry's high doubleword (`vput`);
otherwise (`j ≥ 249`), with four iterations of the loop of
`vg_mlkem_sample_ntt` (`snBody`), which stops at 256. A value stored but
not counted lies past the coefficients sampled, and is overwritten by the
next. It keeps each seed's `j`.

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
/-- The table and the constants of the vector code. -/
def oTab : Nat := 4480

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

/-- Entry `m` of the table: the positions of the set bits of `m` in the
nibbles of the low doubleword, from nibble 0, and their number in the high
doubleword. -/
def tabEntry (m : Nat) : Nat := (setBits m).foldr (fun p acc => p + 16 * acc) 0 + 2 ^ 32 * (setBits m).length

/-- The constants of the vector code, four quadwords each, from byte
`oTab + oCst` of `scratch` (in `ymm8` to `ymm13`): the `vpshufb` mask that puts
bytes `3i, 3i+1` and `3i+1, 3i+2` of the 12 in the low half of doublewords
`2i` and `2i+1` (bytes 0 to 5 in the low lane, 6 to 11 in the high one);
the shifts of the doublewords (`0, 4, …`); `0xfff`; `q`; the `vpshufb`
mask that puts byte 3 of each doubleword in bytes 0 to 3 of the low lane
and 4 to 7 of the high one; and the shifts of the nibbles of an entry
(`0, 4, …, 28`). -/
def consts : List (BitVec 64) :=
  [0x8080020180800100, 0x8080050480800403, 0x8080080780800706, 0x80800b0a80800a09,
    0x0000000400000000, 0x0000000400000000, 0x0000000400000000, 0x0000000400000000,
    0x00000fff00000fff, 0x00000fff00000fff, 0x00000fff00000fff, 0x00000fff00000fff,
    0x00000d0100000d01, 0x00000d0100000d01, 0x00000d0100000d01, 0x00000d0100000d01,
    0x8080808080808080, 0x0f0b070380808080, 0x808080800f0b0703, 0x8080808080808080,
    0x0000000400000000, 0x0000000c00000008, 0x0000001400000010, 0x0000001c00000018]

/-- The offset of the constants in the table. -/
def oCst : Nat := 2048

/-- Quadword `i` of the table and the constants, from byte `oTab` of `scratch`. -/
def tabQ (i : Nat) : BitVec 64 := if i < 256 then BitVec.ofNat 64 (tabEntry i) else consts.getD (i - 256) 0

/-- The table and the constants, through `rax`. -/
def tabBuild : List Instr :=
  (List.range 280).flatMap fun i => [.movImm64 .rax (tabQ i), .store (at_ .rbx (oTab + 8 * i)) .rax]

/-- The constants into `ymm8` to `ymm13`. -/
def cstLoad : List Instr :=
  [.vmovdquLoad .l256 .xmm8 (at_ .rbx (oTab + oCst)), .vmovdquLoad .l256 .xmm9 (at_ .rbx (oTab + oCst + 32)),
    .vmovdquLoad .l256 .xmm10 (at_ .rbx (oTab + oCst + 64)), .vmovdquLoad .l256 .xmm11 (at_ .rbx (oTab + oCst + 96)),
    .vmovdquLoad .l256 .xmm12 (at_ .rbx (oTab + oCst + 128)), .vmovdquLoad .l256 .xmm13 (at_ .rbx (oTab + oCst + 160))]

/-- `[rbx + 8 rax + oTab]`: entry `rax` of the table. -/
def tabE : MemOp := { base := .rbx, index := some .rax, scale := 8, disp := oTab }

/-- `[rbp + 4 rdi]`: `a[j]`. -/
def aV : MemOp := { base := .rbp, index := some .rdi, scale := 4 }

/-- The eight candidates of the 12 bytes at `rsi` in `ymm0`, and their mask
in `eax`. -/
def vcand : List Instr :=
  [.vbroadcasti128 .xmm0 (at_ .rsi 0), vb .vpshufb .xmm0 .xmm0 .xmm8, .vop (.vvar .vpsrlvd .l256 .xmm0 .xmm0 .xmm9),
    vb .vpand .xmm0 .xmm0 .xmm10, vb .vpsubd .xmm1 .xmm0 .xmm11, vb .vpshufb .xmm1 .xmm1 .xmm12,
    .vpmovmskb .l256 .rax .xmm1, .shift32 .shr .rax 12]

/-- The candidates less than `q` to `a[j..]`, and `j` and `rsi` advanced. -/
def vput : List Instr :=
  [.vmovdquLoad .l128 .xmm1 tabE, .vop (.vpbroadcastd .l256 .xmm1 .xmm1),
    .vop (.vvar .vpsrlvd .l256 .xmm1 .xmm1 .xmm13), .vop (.vpermd .xmm0 .xmm1 .xmm0), .vmovdquStore .l256 aV .xmm0,
    .alu32 .add .rdi (.mem { tabE with disp := oTab + 4 }), .alu .add .rsi (.imm 12)]

/-- Four iterations of the loop: with AVX2 if `j < 249`, and otherwise with
`snBody`. -/
def vgrp : Prog isa :=
  .seq (.block [.alu .cmp .rdi (.imm 249)])
    (.ite .b (.seq (.block vcand) (.block vput)) (.seq (.block [.mov32 .rcx (.imm 4)]) (.loop snBody .ne)))

/-- Eight iterations of the loop; `r10` counts down. -/
def vbody : Prog isa := .seq vgrp (.seq vgrp (.block [.alu .sub .r10 (.imm 1)]))

/-- The setup of the loop of seed `k`. -/
def setup (k : Nat) : List Instr :=
  [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * k))),
    .mov32 .rdi (.imm 0), .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * k))),
    .mov32 .r10 (.imm 21)]

/-- Return `r14`, and restore the callee-saved registers (`rbx` last). -/
def epi : List Instr :=
  .mov32 .rax (.reg .r14) ::
    ((List.range 4).map fun k => .mov (saved.getD (4 - k) .rbx) (.mem (at_ .rbx (oSave + 8 * (4 - k))))) ++
    [.mov .rbx (.mem (at_ .rbx oSave))]

/-- 168 iterations of the loop on the buffer of seed `k`, to polynomial
`k`, and `j` kept. -/
def run1 (k : Nat) : Prog isa :=
  .seq (.block (setup k ++ cstLoad)) (.seq (.loop vbody .ne) (.block [.store (at_ .rbx (oCnt + 8 * k)) .rdi]))

/-- The setup of the continuation of seed `k`: from `j` kept. -/
def contSetup (k : Nat) : List Instr :=
  [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * k))),
    .mov .rdi (.mem (at_ .rbx (oCnt + 8 * k))), .mov .rbp (.reg .r13),
    .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * k))), .mov32 .r10 (.imm 14)]

/-- 112 more iterations of the loop, on the buffer of seed `k` (bytes 504
to 839 of its output), and `j` kept. -/
def run2 (k : Nat) : Prog isa :=
  .seq (.block (contSetup k ++ cstLoad)) (.seq (.loop vbody .ne) (.block [.store (at_ .rbx (oCnt + 8 * k)) .rdi]))

/-- `r14` is 1 if every seed has 256 coefficients, and 0 otherwise: the AND of
the seeds' `j >> 8` (`j ≤ 256`). -/
def cntFlags : List Instr := .mov32 .r14 (.imm 1) :: (List.range 4).flatMap fun k =>
  [.mov .rax (.mem (at_ .rbx (oCnt + 8 * k))), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax)]

/-- Two more blocks of each seed, and 112 more iterations on each. -/
def more4 (fast : Bool := false) : Prog isa :=
  .seq (.block [.mov32 .r14 (.imm 1)]) (.seq (squeezes 0 2 fast)
    (.seq (run2 0) (.seq (run2 1) (.seq (run2 2) (.seq (run2 3) (.block cntFlags))))))

/-- If a seed has fewer than 256 coefficients, `more4`; then the return
value. `vzeroupper` clears the upper halves of the vector registers, so that
the caller's SSE code does not pay for mixing them. -/
def tail4 (fast : Bool := false) : Prog isa :=
  .seq (.block (cntFlags ++ ([.alu32 .cmp .r14 (.imm 0)] : List Instr)))
    (.seq (.ite .e (more4 fast) (.block [])) (.block (([.vop .vzeroupper] : List Instr) ++ epi)))

/-- `vg_mlkem_sample_ntt4_avx2`. -/
def sampleNTT4Avx2 (fast : Bool := false) : Prog isa :=
  .seq (.block (pro ++ rcTable .rbx (oRc / 32) ++ absorb4))
    (.seq (squeezes 0 3 fast) (.seq (.block tabBuild)
      (.seq (run1 0) (.seq (run1 1) (.seq (run1 2) (.seq (run1 3) (tail4 fast)))))))

/-- `vg_mlkem_sample_ntt` on seed `k`, and `r14 ← r14 ∧ result`. -/
def callK (k : Nat) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * k))),
      .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * k))), .mov .rdx (.reg .rbx),
      .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))])
    (.seq (.call "vg_mlkem_sample_ntt" sampleNTT) (.block [.alu32 .and .r14 (.reg .rax)]))

/-- `vg_mlkem_sample_ntt4`: `vg_mlkem_sample_ntt` on each seed, with the
prologue and epilogue of `vg_mlkem_sample_ntt4_avx2`. -/
def sampleNTT4 : Prog isa :=
  .seq (.block pro) (.seq (callK 0) (.seq (callK 1) (.seq (callK 2) (.seq (callK 3) (.block epi)))))

end VG.Impl.MlKem.X86_64.Sample4
