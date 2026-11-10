module

public import VerifiedGarbage.Impl.Sha512.X86_64.Avx2Rolled

/-!
# SHA-512 compression function: x86-64 implementations with AVX-512VL

Two functions, for CPUs with AVX512F and AVX512VL:

* `compress`, the compression function of `Impl.Sha512.X86_64.Avx2Rolled`
  with its message schedule computed with `vprorq` and `vpternlogd`
  (`schedule`): a rotation is one instruction, not two shifts and an xor,
  and each of `σ₀` and `σ₁` is two rotations, a shift and one three-way xor.
* `compress2`, the compression function on two hash values and two blocks
  at once, for callers with two blocks that do not depend on each other
  (HMAC's two padded keys). Each `xmm` register holds a 64-bit value of
  each: the first's in quadword 0 and the second's in quadword 1.

## `compress2 (state₀ = rdi, block₀ = rsi, state₁ = rdx, block₁ = rcx, scratch = r8)`

* `xmm0`–`xmm7` hold the working variables `a … h` of both, renamed each
  round as the integer registers of `Avx2.round` are (`sv`).
* A round is `Σ₁(e)` and `Σ₀(a)` as three `vprorq` and a three-way xor
  (`vpternlogd` with `0x96`), and `Ch` and `Maj` as one `vpternlogd` each
  (`0xCA`: the bits of the second operand where the first has a one, of
  the third where it has a zero; `0xE8`: the majority).
* The message words are a linear array in the scratch space, sixteen bytes
  each (`Wₜ` of both blocks at `scratch + 16 t`), so that the words a
  schedule step reads are unaligned 256-bit loads: a `ymm` register holds
  two consecutive words of both blocks, and a step computes `Wₜ` and
  `Wₜ₊₁` (`t` even) from `Wₜ₋₁₆ … Wₜ₋₁`, none of which it writes.
* `Kₜ` is read from a table with each round constant twice (`Ks2`), 32
  bytes for two rounds, as the words are: `r9 = 256 j` indexes both in
  iteration `j`, sixteen rounds.
* Only `rax`, `r9` and vector registers are written beside the hash values
  and `scratch[0..1280)`; `vzeroupper` before returning.
* The pointers are public; no address and no branch depends on anything
  else.
-/

@[expose] public section

namespace VG.Impl.Sha512.X86_64.Avx512

open VG.X86_64
open VG.Impl.Sha512.X86_64.Avx2 (at_ msg t0 t1 t2 t3 vb vs bswapMask)

/-! ## The message schedule of `compress` -/

def vror (d a : XReg) (n : BitVec 8) : Instr := .vop (.vprorq .l256 d a n)
def vxor3 (d a b : XReg) : Instr := .vop (.vpternlogd .l256 d a b 0x96)

/-- `Impl.Sha512.X86_64.Avx2.schedule i` with AVX-512VL: `W₂ᵢ` and `W₂ᵢ₊₁`
of both blocks into `msg i` (for `i ≥ 8`), and stored. -/
def schedule (i : Nat) : List Instr :=
  let x0 := msg i; let x1 := msg (i + 1); let x4 := msg (i + 4); let x5 := msg (i + 5)
  let x7 := msg (i + 7)
  [ .vop (.vpalignr .l256 t0 x1 x0 8),      -- W₂ᵢ₋₁₅, W₂ᵢ₋₁₄
    .vop (.vpalignr .l256 t1 x5 x4 8),      -- W₂ᵢ₋₇, W₂ᵢ₋₆
    vb .vpaddq x0 x0 t1,                    -- W₂ᵢ₋₁₆ + W₂ᵢ₋₇, …
    vror t2 t0 1, vror t3 t0 8, vs .psrlq t0 t0 7, vxor3 t2 t3 t0,       -- σ₀
    vb .vpaddq x0 x0 t2,
    vror t2 x7 19, vror t3 x7 61, vs .psrlq t0 x7 6, vxor3 t2 t3 t0,     -- σ₁
    vb .vpaddq x0 x0 t2,                    -- W₂ᵢ, W₂ᵢ₊₁
    .vmovdquStore .l256 (at_ .rcx (32 * i)) x0]

/-- `vg_sha512_compress_avx512`. -/
def compress : Prog isa := Avx2Rolled.compressWith schedule

/-! ## Two compressions at once -/

/-- The registers holding the working variables of both. -/
def work : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7]

/-- The register holding working variable `k` (`a = 0, …, h = 7`) of both at the start of round `t`. -/
def sv (t k : Nat) : XReg := work.getD ((k + 8 - t % 8) % 8) .xmm0

/-- Temporaries of a round and of a schedule step. -/
def u0 : XReg := .xmm8
def u1 : XReg := .xmm9
def u2 : XReg := .xmm10
/-- The words of a step, then `Kₜ + Wₜ` (quadwords 0 and 1 of the low
half: both blocks'). -/
def w0 : XReg := .xmm12
/-- A step's other temporary, then `Kₜ₊₁ + Wₜ₊₁`. -/
def w1 : XReg := .xmm13
/-- `pshufb` mask: big-endian words. -/
def mB : XReg := .xmm15

def xb (op : VBinOp) (d a b : XReg) : Instr := .vop (.vbin op .l128 d a b)
def xror (d a : XReg) (n : BitVec 8) : Instr := .vop (.vprorq .l128 d a n)
def xtern (d a b : XReg) (imm : BitVec 8) : Instr := .vop (.vpternlogd .l128 d a b imm)

/-- Round `t` of both, with `Kₜ + Wₜ` in `kw`: `T₁ = h + Kₜ + Wₜ + Ch(e, f, g)
+ Σ₁(e)`, `T₂ = Σ₀(a) + Maj(a, b, c)`. -/
def round2 (t : Nat) (kw : XReg) : List Instr :=
  let a := sv t 0; let b := sv t 1; let c := sv t 2; let d := sv t 3
  let e := sv t 4; let f := sv t 5; let g := sv t 6; let h := sv t 7
  [ xror u0 e 14, xror u1 e 18, xror u2 e 41, xtern u0 u1 u2 0x96,   -- Σ₁(e)
    .vop (.vmovdqa .l128 u1 e), xtern u1 f g 0xCA,                   -- Ch(e, f, g)
    xb .vpaddq h h kw, xb .vpaddq u0 u0 u1, xb .vpaddq h h u0,       -- T₁
    xb .vpaddq d d h,                                                -- e' := d + T₁
    xror u0 a 28, xror u1 a 34, xror u2 a 39, xtern u0 u1 u2 0x96,   -- Σ₀(a)
    .vop (.vmovdqa .l128 u1 a), xtern u1 b c 0xE8,                   -- Maj(a, b, c)
    xb .vpaddq h h u0, xb .vpaddq h h u1 ]                           -- a' := T₁ + T₂

/-- The name of the table of round constants, each twice. -/
def kSym : String := "VG_SHA512_K2"

/-- The round constants, each twice: `Kₜ` of both in 16 bytes. -/
def Ks2 : List (BitVec 64) := Spec.Sha512.Ks.flatMap fun k => [k, k]

/-- Where step `i` of an iteration keeps its two words of both blocks,
`d` bytes on: `r9 = 256 j` in iteration `j`. -/
def wSlot (i : Nat) (d : Int := 0) : MemOp :=
  { base := .r8, index := some .r9, scale := 1, disp := ((32 * i : Nat) : Int) + d }

/-- Where step `i` of an iteration reads its two round constants. -/
def kSlot (i : Nat) : MemOp := { base := .rax, index := some .r9, scale := 1, disp := ((32 * i : Nat) : Int) }

/-- Rounds `2i` and `2i+1` of an iteration, whose words are in `w0`. -/
def rounds2 (i : Nat) : List Instr :=
  [ .vmovdquTbl w1 (kSlot i) kSym Ks2, .vop (.vbin .vpaddq .l256 w0 w0 w1), .vop (.vextracti128 w1 w0 1) ] ++
    round2 (2 * i) w0 ++ round2 (2 * i + 1) w1

/-- Words `2i` and `2i+1` (`i < 8`) of the blocks at `rsi` and `rcx` into
`w0`, and stored. -/
def load (i : Nat) : List Instr :=
  [ .vmovdquLoad .l128 w0 (at_ .rsi (16 * i)), .vmovdquLoad .l128 w1 (at_ .rcx (16 * i)),
    .vop (.vinserti128 w0 w0 w1 1), .vop (.vbin .vpshufb .l256 w0 w0 mB),
    .vop (.vpermq w0 w0 0xD8), .vmovdquStore .l256 (wSlot i) w0 ]

/-- Words `t` and `t+1` of an iteration's step `i` (`t = 16 j + 2 i`,
`j ≥ 1`) into `w0`, and stored: `Wₜ = σ₁(Wₜ₋₂) + Wₜ₋₇ + σ₀(Wₜ₋₁₅) + Wₜ₋₁₆`. -/
def sched (i : Nat) : List Instr :=
  [ .vmovdquLoad .l256 w0 (wSlot i (-240)), .vmovdquLoad .l256 w1 (wSlot i (-32)),
    vror u0 w0 1, vror u1 w0 8, .vop (.vshift .psrlq .l256 w0 w0 7), vxor3 w0 u0 u1,       -- σ₀
    vror u0 w1 19, vror u1 w1 61, .vop (.vshift .psrlq .l256 w1 w1 6), vxor3 w1 u0 u1,     -- σ₁
    .vbinLoad .vpaddq .l256 w0 w0 (wSlot i (-256)), .vbinLoad .vpaddq .l256 w0 w0 (wSlot i (-112)),
    .vop (.vbin .vpaddq .l256 w0 w0 w1), .vmovdquStore .l256 (wSlot i) w0 ]

/-- Steps `0 … n-1` of the first iteration. -/
def steps0 : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (steps0 n) (.block (load n ++ rounds2 n))

/-- Steps `0 … n-1` of a later iteration. -/
def steps : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (steps n) (.block (sched n ++ rounds2 n))

/-- Both hash values into the variables of round 0. -/
def loadState : List Instr :=
  (List.range 4).flatMap fun j =>
    [ .vmovdquLoad .l128 u0 (at_ .rdi (16 * j)), .vmovdquLoad .l128 u1 (at_ .rdx (16 * j)),
      xb .vpunpcklqdq (sv 0 (2 * j)) u0 u1, xb .vpunpckhqdq (sv 0 (2 * j + 1)) u0 u1 ]

/-- Add the variables into the hash values. -/
def addState : List Instr :=
  (List.range 4).flatMap fun j =>
    [ xb .vpunpcklqdq u0 (sv 0 (2 * j)) (sv 0 (2 * j + 1)), xb .vpunpckhqdq u1 (sv 0 (2 * j)) (sv 0 (2 * j + 1)),
      .vbinLoad .vpaddq .l128 u0 u0 (at_ .rdi (16 * j)), .vbinLoad .vpaddq .l128 u1 u1 (at_ .rdx (16 * j)),
      .vmovdquStore .l128 (at_ .rdi (16 * j)) u0, .vmovdquStore .l128 (at_ .rdx (16 * j)) u1 ]

/-- The 128-bit constant `c` into both lanes of `x`, through `rax` and `w1`. -/
def const (x : XReg) (c : BitVec 128) : List Instr :=
  [.movImm64 .rax (c.extractLsb' 0 64), .vop (.vmovq x .rax),
   .movImm64 .rax (c.extractLsb' 64 64), .vop (.vmovq w1 .rax),
   .vop (.vbin .vpunpcklqdq .l128 x x w1), .vop (.vinserti128 x x x 1)]

/-- The next iteration: `r9` steps by 256, up to 1280. -/
def step : List Instr := [.alu .add .r9 (.imm 256), .alu .cmp .r9 (.imm 1280)]

/-- `vg_sha512_compress2_avx512`. -/
def compress2 : Prog isa :=
  .seq (.block (const mB bswapMask ++ loadState ++ ([.leaSym .rax kSym, .mov .r9 (.imm 0)] : List Instr)))
  (.seq (.seq (steps0 8) (.seq (.block step) (.loop (.seq (steps 8) (.block step)) .ne)))
    (.block (addState ++ ([.vop .vzeroupper] : List Instr))))

end VG.Impl.Sha512.X86_64.Avx512
