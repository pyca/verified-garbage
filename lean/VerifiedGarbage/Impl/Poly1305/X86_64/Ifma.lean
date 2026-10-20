module

public import VerifiedGarbage.Impl.Poly1305.X86_64.Avx512

/-!
# Poly1305 blocks: x86-64 implementation with AVX-512 IFMA

`vg_poly1305_blocks_ifma(state = rdi, blocks = rsi, n = rdx)`, with the
contract of `vg_poly1305_blocks`, for CPUs with AVX-512F and AVX512_IFMA
(and AVX2, whose implementation it calls).

Fewer than `minBlocks` blocks are left to `vg_poly1305_blocks_avx2`.
Otherwise the first `8 ⌊n / 8⌋` blocks are absorbed eight at a time, in the
eight quadwords of `zmm` registers as `vg_poly1305_blocks_avx512` absorbs
them, and the rest (fewer than eight) by calling `vg_poly1305_blocks`.

* Numbers modulo `p = 2¹³⁰ - 5` are kept in three limbs of 44 bits (the
  last, of weight `2⁸⁸`, may reach 44 bits too), one per quadword, eight
  numbers to a set of three `zmm` registers: the accumulators `H`
  (`zmm0`–`zmm2`) of eight interleaved Horner evaluations. Quadword `k` of a
  group holds block `π k = 4 (k mod 2) + ⌊k / 2⌋` (the blocks' low and high
  quadwords interleaved with `vpunpck{l,h}qdq`).
* A product `H · Y` (`mul`) sums the 52-bit halves of the limbs' products
  with `vpmadd52luq` and `vpmadd52huq` into `D` (`zmm8`–`zmm13`, the low
  and high sums of each limb of the product), the multipliers `Y`
  (`zmm3`–`zmm5`) and twenty times their limbs 1 and 2 (`zmm6`, `zmm7`)
  standing for the terms past `2¹³⁰` (`2¹³² ≡ 20`). A high sum, of weight
  `2⁵²` over its limb, is shifted by 8 into the next limb's low sum, the
  last (of weight `2¹⁴⁰ ≡ 5 · 2¹⁰`) multiplied by `5 · 2¹⁰` into limb 0's;
  then the limbs are carried, the carry out of the top limb (of weight
  `2¹³²`) multiplied by 20 into limb 0.
* `Y` is `r⁸`, in every quadword, in the loop: `r` from the key squared
  three times. `r²` and `r⁴` are kept in the state for the end.
* After the last group, `Σ_b A_b r^(8 - b)` over the accumulators `A_b` of
  the blocks `b` is folded in three steps: quadword `2 j` (block `j`) is
  multiplied by `r⁴` and the odd quadwords (blocks `j + 4`) by 1, and each
  odd quadword added to the even one before it (`B_j`, in lane `j`); lanes
  0 and 2 are multiplied by `r` and 1 and 3 by 1, and lanes 1 and 3 added to
  lanes 0 and 2 (`C₀ = r B₀ + B₁`, `C₁ = r B₂ + B₃`); lane 0 is multiplied
  by `r²` and lane 2 added to it, and the result by `r`:
  `r (r² (r B₀ + B₁) + r B₂ + B₃) = Σ_j B_j r^(4 - j)`.
* `vpmadd52luq` and `vpmadd52huq` take secret operands, so the vector code
  runs between Intel's MCDT prologue and epilogue, as in
  `vg_poly1305_blocks_avx2`.
* The accumulator then goes to general-purpose registers as the three words
  of `vg_poly1305_blocks`, its bits from `2¹³⁰` on folded back (times 5),
  and is reduced and stored by `vg_poly1305_blocks`'s code, which uses (and
  saves in the state, restoring them after) callee-saved registers.

The working space of the state holds `r²` and `r⁴` (bytes 56–103, a limb
per quadword), the mask `2⁴⁴ - 1` (byte 104) and the pad bit `2⁴⁰` (byte
112); MXCSR is saved at bytes 120–127. `vzeroupper` precedes the calls and
the return. The branches are on `n` only, and every address is a pointer
plus a constant, so only the pointers and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.Poly1305.X86_64.Ifma

open VG.X86_64
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Impl.Poly1305.X86_64.Avx512 (z srl sll mov shuf bcast zb)

/-- Below this many blocks, `vg_poly1305_blocks_avx2` is faster: it absorbs
fewer than 32 with `vg_poly1305_blocks`, a quarter faster at 28–31 blocks on a
Sapphire Rapids Xeon than this code with its powers of `r`. From 32 blocks on
the two are within a few percent of each other, depending on the CPU. -/
def minBlocks : Nat := 32

/-! ## Registers -/

/-- The accumulator `H`. -/
def hreg : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | _ => .xmm2
/-- The multipliers `Y`. -/
def yreg : Nat → XReg
  | 0 => .xmm3 | 1 => .xmm4 | _ => .xmm5
/-- Twenty times limbs 1 and 2 of `Y`. -/
def sreg : Nat → XReg
  | 1 => .xmm6 | _ => .xmm7
/-- The low sums of the product's limbs. -/
def lreg : Nat → XReg
  | 0 => .xmm8 | 1 => .xmm9 | _ => .xmm10
/-- The high sums. -/
def ureg : Nat → XReg
  | 0 => .xmm11 | 1 => .xmm12 | _ => .xmm13
/-- Scratch. -/
def t0 : XReg := .xmm14
def t1 : XReg := .xmm15

def madLo (d a b : XReg) : Instr := .zop (.vpmadd52 false d a b)
def madHi (d a b : XReg) : Instr := .zop (.vpmadd52 true d a b)

/-! ## The state's working space -/

/-- Limb `i` of `r²` and of `r⁴`, the mask `2⁴⁴ - 1` and the pad bit `2⁴⁰`. -/
def mR2 (i : Nat) : MemOp := at_ .rdi (56 + 8 * i)
def mR4 (i : Nat) : MemOp := at_ .rdi (80 + 8 * i)
def mMask : MemOp := at_ .rdi 104
def mPad : MemOp := at_ .rdi 112

/-! ## The product -/

/-- `S = 20 Y₁, 20 Y₂` (`16 y + 4 y`). -/
def twenty : List Instr :=
  [1, 2].flatMap fun i =>
    [sll (sreg i) (yreg i) 4, sll t0 (yreg i) 2, z .vpaddq (sreg i) (sreg i) t0]

/-- `D = 0`. -/
def zeroD : List Instr :=
  [0, 1, 2].flatMap fun j => [z .vpxord (lreg j) (lreg j) (lreg j), z .vpxord (ureg j) (ureg j) (ureg j)]

/-- The 52-bit halves of `H_i · M` added to the low and high sums of limb `j`. -/
def madd (j i : Nat) (m : XReg) : List Instr :=
  [madLo (lreg j) (hreg i) m, madHi (ureg j) (hreg i) m]

/-- `d₀ = H₀ Y₀ + H₁ S₂ + H₂ S₁`, `d₁ = H₀ Y₁ + H₁ Y₀ + H₂ S₂`,
`d₂ = H₀ Y₂ + H₁ Y₁ + H₂ Y₀`, in halves. -/
def prods : List Instr :=
  madd 0 0 (yreg 0) ++ madd 1 0 (yreg 1) ++ madd 2 0 (yreg 2) ++
  madd 0 1 (sreg 2) ++ madd 1 1 (yreg 0) ++ madd 2 1 (yreg 1) ++
  madd 0 2 (sreg 1) ++ madd 1 2 (sreg 2) ++ madd 2 2 (yreg 0)

/-- The high sums into the low ones: `u₀ << 8` into `l₁`, `u₁ << 8` into
`l₂`, `5 · 2¹⁰ · u₂ = (u₂ << 12) + (u₂ << 10)` into `l₀`. -/
def fold : List Instr :=
  [sll t0 (ureg 0) 8, z .vpaddq (lreg 1) (lreg 1) t0,
   sll t0 (ureg 1) 8, z .vpaddq (lreg 2) (lreg 2) t0,
   sll t0 (ureg 2) 12, z .vpaddq (lreg 0) (lreg 0) t0,
   sll t0 (ureg 2) 10, z .vpaddq (lreg 0) (lreg 0) t0]

/-- The limbs carried: `H_j = l_j mod 2⁴⁴` with `l_j >> 44` into `l_(j+1)`,
the top carry `c = l₂ >> 44` times 20 into `H₀`, and `H₀ >> 44` into `H₁`. -/
def carry : List Instr :=
  [srl t0 (lreg 0) 44, zb .vpandq (hreg 0) (lreg 0) mMask, z .vpaddq (lreg 1) (lreg 1) t0,
   srl t0 (lreg 1) 44, zb .vpandq (hreg 1) (lreg 1) mMask, z .vpaddq (lreg 2) (lreg 2) t0,
   srl t0 (lreg 2) 44, zb .vpandq (hreg 2) (lreg 2) mMask,
   sll t1 t0 4, z .vpaddq (hreg 0) (hreg 0) t1, sll t1 t0 2, z .vpaddq (hreg 0) (hreg 0) t1,
   srl t0 (hreg 0) 44, zb .vpandq (hreg 0) (hreg 0) mMask, z .vpaddq (hreg 1) (hreg 1) t0]

/-- `H = H · Y` quadword by quadword (with `S = 20 Y₁, 20 Y₂`). -/
def mul : List Instr := zeroD ++ prods ++ fold ++ carry

/-! ## Loading -/

/-- `r` into every quadword of `Y`: the clamped words of `r` (in `r10` and
`r11`) split into limbs in `rax`, `rcx` and `r9`, with the mask in `r8`. -/
def splitRg : List Instr :=
  [.mov .rax (.reg .r10), .alu .and .rax (.reg .r8),
   .mov .rcx (.reg .r11), .shift .shl .rcx 20, .mov .r9 (.reg .r10), .shift .shr .r9 44,
   .alu .or .rcx (.reg .r9), .alu .and .rcx (.reg .r8),
   .mov .r9 (.reg .r11), .shift .shr .r9 24] ++
  bcast (yreg 0) .rax ++ bcast (yreg 1) .rcx ++ bcast (yreg 2) .r9

/-- The clamped `r` into `r10` and `r11`, the mask `2⁴⁴ - 1` into `r8` and
the state, and the pad bit `2⁴⁰` into the state. -/
def loadR : List Instr := [
  .movImm64 .rax 0x0ffffffc0fffffff, .mov .r10 (.mem (at_ .rdi 24)), .alu .and .r10 (.reg .rax),
  .movImm64 .rax 0x0ffffffc0ffffffc, .mov .r11 (.mem (at_ .rdi 32)), .alu .and .r11 (.reg .rax),
  .movImm64 .r8 0xfffffffffff, .store mMask .r8,
  .movImm64 .rax 0x10000000000, .store mPad .rax]

/-- `H = Y` and `Y = H`. -/
def hOfY : List Instr := [0, 1, 2].map fun i => mov (hreg i) (yreg i)
def yOfH : List Instr := [0, 1, 2].map fun i => mov (yreg i) (hreg i)

/-- Quadword 0 of `H` stored at `m i`, through `rax`. -/
def storeH (m : Nat → MemOp) : List Instr :=
  [0, 1, 2].flatMap fun i => [.movqR .rax (hreg i), .store (m i) .rax]

/-- `Y = r⁸` (and `S`), with `r²` and `r⁴` stored in the state. -/
def powers : List Instr :=
  loadR ++ splitRg ++ twenty ++ hOfY ++ mul ++ storeH mR2 ++
  yOfH ++ twenty ++ mul ++ storeH mR4 ++ yOfH ++ twenty ++ mul ++ yOfH ++ twenty

/-- The accumulator `h` (the words at `rdi`, `rdi + 8` and `rdi + 16`) into
quadword 0 of `H` as limbs, zeros elsewhere, through `rax`, `rcx` and `r9`. -/
def loadH : List Instr := [
  .mov .r9 (.mem (at_ .rdi 16)), .shift .shl .r9 40, .mov .rcx (.mem (at_ .rdi 8)), .shift .shr .rcx 24,
  .alu .or .r9 (.reg .rcx),
  .mov .rcx (.mem (at_ .rdi 8)), .shift .shl .rcx 20, .mov .rax (.mem (at_ .rdi 0)), .shift .shr .rax 44,
  .alu .or .rcx (.reg .rax), .alu .and .rcx (.reg .r8),
  .mov .rax (.mem (at_ .rdi 0)), .alu .and .rax (.reg .r8),
  .vop (.vmovq (hreg 0) .rax), .vop (.vmovq (hreg 1) .rcx), .vop (.vmovq (hreg 2) .r9)]

/-- The eight blocks at `rsi` (block `π k` in quadword `k`) split into limbs,
with the pad bit, added to `H`. -/
def addGroup : List Instr := [
  .vmovdqu32Load t0 (at_ .rsi 0), .vmovdqu32Load t1 (at_ .rsi 64),
  z .vpunpcklqdq (lreg 0) t0 t1, z .vpunpckhqdq (lreg 1) t0 t1,
  zb .vpandq t0 (lreg 0) mMask, z .vpaddq (hreg 0) (hreg 0) t0,
  srl t0 (lreg 0) 44, sll t1 (lreg 1) 20, z .vporq t0 t0 t1, zb .vpandq t0 t0 mMask,
  z .vpaddq (hreg 1) (hreg 1) t0,
  srl t0 (lreg 1) 24, zb .vporq t0 t0 mPad, z .vpaddq (hreg 2) (hreg 2) t0]

/-- One group of eight blocks, multiplied by `r⁸`. -/
def groupBody : Prog isa :=
  .block (addGroup ++ mul ++ ([.alu .add .rsi (.imm 128), .alu .sub .rcx (.imm 1)] : List Instr))

/-! ## The end -/

/-- `t1 = 0` and `t0 = 1` in every quadword (the mask `2⁴⁴ - 1` shifted
right by 43). -/
def zeroOne : List Instr :=
  [z .vpxord t1 t1 t1, zb .vporq t0 t1 mMask, srl t0 t0 43]

/-- `Y` the limbs at `m i` broadcast, through `rax`, `rcx` and `r9`. -/
def loadY (m : Nat → MemOp) : List Instr :=
  [.mov .rax (.mem (m 0)), .mov .rcx (.mem (m 1)), .mov .r9 (.mem (m 2))] ++
  bcast (yreg 0) .rax ++ bcast (yreg 1) .rcx ++ bcast (yreg 2) .r9

/-- Step 1: `Y = r⁴` in the even quadwords and 1 in the odd ones; then each
odd quadword of the product added to the even one before it. -/
def step1 : List Instr :=
  loadY mR4 ++ zeroOne ++
  [z .vpunpcklqdq (yreg 0) (yreg 0) t0, z .vpunpcklqdq (yreg 1) (yreg 1) t1,
   z .vpunpcklqdq (yreg 2) (yreg 2) t1] ++ twenty ++ mul ++
  [0, 1, 2].flatMap fun i => [z .vpunpckhqdq t0 (hreg i) (hreg i), z .vpaddq (hreg i) (hreg i) t0]

/-- Step 2: `Y = r` in lanes 0 and 2 and 1 in lanes 1 and 3 (from
`(r, r, 1, 1)`); then lanes 1 and 3 of the product added to lanes 0 and 2. -/
def step2 : List Instr :=
  splitRg ++ zeroOne ++
  [shuf (yreg 0) (yreg 0) t0 0x00, shuf (yreg 1) (yreg 1) t1 0x00, shuf (yreg 2) (yreg 2) t1 0x00,
   shuf (yreg 0) (yreg 0) (yreg 0) 0x88, shuf (yreg 1) (yreg 1) (yreg 1) 0x88,
   shuf (yreg 2) (yreg 2) (yreg 2) 0x88] ++ twenty ++ mul ++
  [0, 1, 2].flatMap fun i => [shuf t0 (hreg i) (hreg i) 0xF5, z .vpaddq (hreg i) (hreg i) t0]

/-- Step 3: `Y = r²` in lanes 0 and 1 and 1 in lanes 2 and 3; then lane 2
of the product added to lane 0, and the result multiplied by `r`. -/
def step3 : List Instr :=
  loadY mR2 ++ zeroOne ++
  [shuf (yreg 0) (yreg 0) t0 0x00, shuf (yreg 1) (yreg 1) t1 0x00, shuf (yreg 2) (yreg 2) t1 0x00] ++
  twenty ++ mul ++
  ([0, 1, 2].flatMap fun i => [shuf t0 (hreg i) (hreg i) 0xEE, z .vpaddq (hreg i) (hreg i) t0]) ++
  splitRg ++ twenty ++ mul

/-- The accumulator (quadword 0 of `H`) as the words `r11`, `rbx`, `rbp`
of `vg_poly1305_blocks`: `w = h₀ + 2⁴⁴ h₁ + 2⁸⁸ h₂`, then its bits from
`2¹³⁰` on times 5 added back (`rbp` its top word, below 5 after). -/
def toWords : List Instr := [
  .movqR .r11 (hreg 0), .movqR .rax (hreg 1), .movqR .rcx (hreg 2),
  .mov .rbx (.reg .rax), .shift .shl .rax 44, .shift .shr .rbx 20,
  .mov .rbp (.reg .rcx), .shift .shl .rcx 24, .shift .shr .rbp 40,
  .alu .add .r11 (.reg .rax), .alu .adc .rbx (.reg .rcx), .alu .adc .rbp (.imm 0),
  .mov .rax (.reg .rbp), .alu .and .rbp (.imm 3), .shift .shr .rax 2,
  .mov .rcx (.reg .rax), .shift .shl .rcx 2, .alu .add .rax (.reg .rcx),
  .alu .add .r11 (.reg .rax), .alu .adc .rbx (.imm 0), .alu .adc .rbp (.imm 0)]

/-- The first `8 ⌊n / 8⌋` blocks absorbed; `rsi` advanced past them,
`rdx = n mod 8`. The groups before the last are counted down in `rcx`;
`n` waits in `r9` while `vg_poly1305_blocks`'s reduction uses `rdx`. -/
def body : Prog isa :=
  .seq (.block (Avx2.mxcsrIn ++ powers ++ loadH ++
    ([.mov .rcx (.reg .rdx), .shift .shr .rcx 3, .alu .sub .rcx (.imm 1)] : List Instr)))
  (.seq (.loop groupBody .ne)
    (.block (addGroup ++ step1 ++ step2 ++ step3 ++ Avx2.mxcsrOut ++ [.vop .vzeroupper] ++
      save ++ toWords ++ ([.mov .r9 (.reg .rdx)] : List Instr) ++ reduce ++
      ([.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx, .store (at_ .rdi 16) .rbp] : List Instr) ++
      restore ++
      ([.mov .rdx (.reg .r9), .alu .add .rsi (.imm 128), .alu .and .rdx (.imm 7)] : List Instr))))

def scalar : Prog isa := .call "vg_poly1305_blocks" blocks
def avx2 : Prog isa := .call "vg_poly1305_blocks_avx2" Avx2.blocksAvx2

def blocksIfma : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 minBlocks))])
    (.ite .b avx2
      (.seq body
        (.seq (.block [.alu .test .rdx (.reg .rdx)]) (.ite .e (.block []) scalar))))

end VG.Impl.Poly1305.X86_64.Ifma
