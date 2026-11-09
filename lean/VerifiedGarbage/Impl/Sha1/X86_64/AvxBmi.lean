module

public import VerifiedGarbage.Impl.Sha1.X86_64

/-!
# SHA-1 compression function: x86-64 implementation with AVX and BMI

`vg_sha1_compress_avx_bmi(state = rdi, blocks = rsi, n = rdx, scratch = rcx)`,
with the contract of `vg_sha1_compress`, for CPUs with AVX, BMI1 and BMI2
(and without the SHA extensions, which `vg_sha1_compress_shani` uses). The
message schedule is computed four words at a time in SSE registers, as in
OpenSSL's AVX SHA-1 (`sha1-x86_64.pl`, by Andy Polyakov), and the rounds in
general-purpose registers.

* The working variables `a … e` are kept and renamed as in
  `vg_sha1_compress` (`var`), and so is the hash value loaded and updated
  (`load`, `update`), and the callee-saved registers saved
  (`scratch[64..112)`).
* `Wₜ + Kₜ` is kept as a 16-word window in `scratch[0..64)`, `Wₜ + Kₜ` at
  `4 * (t mod 16)`, from which round `t` adds it to `e`. `f(b, c, d)` is
  added to `e` as one or two terms: `Ch` as `(¬b ∧ d) + (c ∧ b)` and `Maj`
  as `(b ∧ c) + ((b ⊕ c) ∧ d)` (sums of masks with no bit in common), then
  `ROTL⁵(a)`, by `rorx`; `ROTL³⁰(b)` is a `rorx` too.
* The message words `W₄ᵢ … W₄ᵢ₊₃` are kept in `msg i` (`xmm0 … xmm3`,
  `W₄ᵢ` in the low doubleword). The first sixteen are loaded from the block
  (`xmm6` holds the `pshufb` mask that makes them big-endian); words
  `4i+16 … 4i+19` are computed after rounds `4i … 4i+3`, which read their
  slots last, from the previous sixteen (with `xmm4` and `xmm5` as
  temporaries): their `⊕` without `Wₜ₋₃` of the last word, which is the
  first word computed, rotated left by one, then the last corrected by that
  first word rotated left by one more.
* `xmm8 … xmm11` hold the constants `K` of the four groups of twenty rounds,
  four times each; `xmm7` is a temporary while they are built.
* `rdi, rsi, rdx, rcx` (the pointers and the block count) are public; no
  address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sha1.X86_64.AvxBmi

open VG.X86_64
open VG.Impl.Sha1.X86_64 (at_ var Fn fn slot T1 save restore load update advance)

/-! ## Rounds -/

/-- `e := e + f(b, c, d)`, with `T1` as a temporary. -/
def fcode (f : Fn) (b c d e : Reg) : List Instr :=
  match f with
  | .ch => -- `Ch(b, c, d)`, as `(¬b ∧ d) + (c ∧ b)`
    [.andn32 T1 b d, .alu32 .add e (.reg T1), .mov32 T1 (.reg c), .alu32 .and T1 (.reg b),
      .alu32 .add e (.reg T1)]
  | .parity => [.mov32 T1 (.reg b), .alu32 .xor T1 (.reg c), .alu32 .xor T1 (.reg d), .alu32 .add e (.reg T1)]
  | .maj => -- `Maj(b, c, d)`, as `(b ∧ c) + ((b ⊕ c) ∧ d)`
    [.mov32 T1 (.reg b), .alu32 .and T1 (.reg c), .alu32 .add e (.reg T1),
      .mov32 T1 (.reg b), .alu32 .xor T1 (.reg c), .alu32 .and T1 (.reg d), .alu32 .add e (.reg T1)]

/-- Round `t`: `e + (Wₜ + Kₜ) + f(b, c, d) + ROTL⁵(a)` goes into `e`'s
register (the new `a`), and `b` becomes `ROTL³⁰(b)`. -/
def round (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let e := var t 4
  [.alu32 .add e (.mem (slot t))] ++ fcode (fn t) b (var t 2) (var t 3) e ++
    [.rorx32 T1 a 27, .alu32 .add e (.reg T1), .rorx32 b b 2]

/-! ## Message schedule -/

/-- The register holding `W₄ᵢ … W₄ᵢ₊₃`. -/
def msg (i : Nat) : XReg := [.xmm0, .xmm1, .xmm2, .xmm3].getD (i % 4) .xmm0

def t0 : XReg := .xmm4
def t1 : XReg := .xmm5
/-- `pshufb` mask: big-endian words. -/
def mBswap : XReg := .xmm6
def tmp : XReg := .xmm7

/-- The register holding `K` of group `g` of twenty rounds, four times. -/
def kreg (g : Nat) : XReg := [.xmm8, .xmm9, .xmm10, .xmm11].getD g .xmm8

def vb (op : VBinOp) (d a b : XReg) : Instr := .vop (.vbin op .l128 d a b)
def vs (op : XShiftOp) (d a : XReg) (n : BitVec 8) : Instr := .vop (.vshift op .l128 d a n)

/-- `Wₜ + Kₜ` for `t = 4i … 4i+3`, from `msg i`, into its slots. -/
def storeWK (i : Nat) : List Instr :=
  [vb .vpaddd t0 (msg i) (kreg (i / 5)), .vmovdquStore .l128 (at_ .rcx (16 * (i % 4))) t0]

/-- `W₄ᵢ … W₄ᵢ₊₃` (`i ≥ 4`) into `msg i`, from the previous sixteen words
(whose register `msg i` held the oldest four), and stored with `K`. -/
def schedule (i : Nat) : List Instr :=
  let x0 := msg i; let x1 := msg (i + 1); let x2 := msg (i + 2); let x3 := msg (i + 3)
  [ .vop (.vpalignr .l128 t0 x1 x0 8),      -- W₄ᵢ₋₁₄ … W₄ᵢ₋₁₁
    vs .psrldq t1 x3 4,                     -- W₄ᵢ₋₃, W₄ᵢ₋₂, W₄ᵢ₋₁, 0
    vb .vpxor x0 x0 x2,                     -- W₄ᵢ₋₁₆ ⊕ W₄ᵢ₋₈ …
    vb .vpxor t0 t0 t1,
    vb .vpxor x0 x0 t0,
    vs .psrld t1 x0 31,
    vs .pslld x0 x0 1,
    vb .vpor x0 x0 t1,                      -- W₄ᵢ … W₄ᵢ₊₂, W₄ᵢ₊₃ without W₄ᵢ
    vs .pslldq t0 x0 12,                    -- 0, 0, 0, W₄ᵢ
    vs .psrld t1 t0 31,
    vs .pslld t0 t0 1,
    vb .vpxor x0 x0 t1,
    vb .vpxor x0 x0 t0] ++                  -- W₄ᵢ … W₄ᵢ₊₃
  storeWK i

/-- `W₄ᵢ … W₄ᵢ₊₃` (`i < 4`) of the block at `rsi` into `msg i`, and stored with `K`. -/
def loadW (i : Nat) : List Instr :=
  [.vmovdquLoad .l128 (msg i) (at_ .rsi (16 * i)), vb .vpshufb (msg i) (msg i) mBswap] ++ storeWK i

/-- Rounds `4i … 4i+3`, then words `4i+16 … 4i+19`, into the slots the rounds
read. -/
def group (i : Nat) : List Instr :=
  round (4 * i) ++ round (4 * i + 1) ++ round (4 * i + 2) ++ round (4 * i + 3) ++
    (if i < 16 then schedule (i + 4) else [])

/-- Groups `0 … n-1`. -/
def groups : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (groups n) (.block (group n))

/-! ## The blocks -/

/-- The 128-bit constant `c` into `x`, through `rax` and `tmp`. -/
def const (x : XReg) (c : BitVec 128) : List Instr :=
  [.movImm64 .rax (c.extractLsb' 0 64), .vop (.vmovq x .rax),
   .movImm64 .rax (c.extractLsb' 64 64), .vop (.vmovq tmp .rax),
   vb .vpunpcklqdq x x tmp]

def bswapMask : BitVec 128 := 0x0c0d0e0f08090a0b0405060700010203#128

/-- `K` of group `g`, four times. -/
def kvec (g : Nat) : BitVec 128 := let k := Spec.Sha1.K (20 * g); k ++ k ++ k ++ k

def consts : List Instr :=
  const mBswap bswapMask ++ const (kreg 0) (kvec 0) ++ const (kreg 1) (kvec 1) ++
    const (kreg 2) (kvec 2) ++ const (kreg 3) (kvec 3)

/-- One block. -/
def body : Prog isa :=
  .seq (.block (loadW 0 ++ loadW 1 ++ loadW 2 ++ loadW 3 ++ load))
    (.seq (groups 20) (.block (update ++ advance)))

def compress : Prog isa :=
  .seq (.block (save ++ consts ++ ([.alu .test .rdx (.reg .rdx)] : List Instr)))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block restore))

end VG.Impl.Sha1.X86_64.AvxBmi
