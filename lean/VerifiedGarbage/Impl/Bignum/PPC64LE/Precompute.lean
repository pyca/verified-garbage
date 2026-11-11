module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul

/-!
# The precomputed values of an RSA modulus on PPC64LE

`vg_rsa_public_precompute(pre = r3, pre_len = r4, n = r5, n_len = r6,
scratch = r7, scratch_len = r8)`: with the modulus `n` (`k = n_len` bytes,
most significant first) of `w = ⌈k / 8⌉` words, writes `n` and `R² mod n`
for `R = 2^(64 w)` to `pre` and returns 1, or writes zeros and returns 0 if
`n` is not a valid modulus (odd, its first byte not zero, and at least
`2^511`, which for `k = 64` is its top bit).

The working space (`scratch`) is laid out as `vg_rsa_mont_mul`'s, with `n`
in array 0, the accumulator in array 2, the temporary in array 3 and `x` in
array 1; the nonvolatile registers are saved in its header's words 16–24.
`R² mod n = 2^(128 w) mod n` (`r2Fast`) is computed from `x = 2^(64 (w - 1))`,
which is below a valid `n`, by `w + 1` word steps of long division, each
`x := x 2^64 mod n`, for any top word of `n`. `r2Hi` instead makes `64 + w`
modular doublings of it to `2^w R mod n` (the double into the accumulator,
`n + 1` digits of 32 bits, as `vg_rsa_mont_mul` reads numbers, then
`MontMul.lean`'s `subMod` and `selectAcc` into `x`), then six Montgomery
squares (`MontMul.tail`) (other callers). For moduli whose top word may be
zero, `r2Prime` starts from 1, with `64 w + w` doublings (the private key's
primes), and `r2`, `128 w` doublings from 1, needs no `-n⁻¹ mod 2³²` (other
callers).

`n` is public: timing may depend on it, and the code branches on its
validity.

Registers: `r19` `pre` (`r3` is `subMod`'s), `r6` `k`, `r12` `n`'s bytes, `r21` the working
space; `r10` `n`'s base, `r5` `x`'s, `r8` the accumulator's, `r9` the
temporary's, `r11` `2 w`, `r4` the doublings left.
-/

@[expose] public section

namespace VG.Impl.Bignum.PPC64LE.Precompute

open VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE

/-- The header words where the nonvolatile registers are saved. -/
def saveOff (i : Nat) : Nat := 8 * sFn i

/-- Save the nonvolatile registers in the working space at `r7`, and keep
its address in `r21`. -/
def save : List Instr :=
  (List.range 9).flatMap (fun i => [.store .d (saved i) .r7 (saveOff i)]) ++ [.addi .r21 .r7 0]

/-- Restore them, through `r21`, which is restored last. -/
def restore : List Instr :=
  (List.range 8).flatMap (fun i => [.load .d (saved i) .r21 (saveOff i)]) ++
    [.load .d .r21 .r21 (saveOff 8)]

/-- `do body; cnt -= 1 while cnt ≠ 0`, for `cnt` at least 1. -/
def countLoop (cnt : Reg) (body : List Instr) : Prog isa :=
  .loop (.block (body ++ ([.subi cnt cnt 1] : List Instr))) (.nonzero .d cnt)

/-- `pre` into `r19`, `n`'s bytes into `r12`, `w = ⌈k / 8⌉` and `2 w` (`r11`), the arrays'
bases (each `w + 2` words: `8 w + 16` bytes, in `r4`) and the header's `w`. -/
def setup : List Instr :=
  [.addi .r19 .r3 0, .addi .r12 .r5 0, .addi .r11 .r6 7, .lsr .d .r11 .r11 3, .store .d .r11 .r21 (8 * sW),
    .lsl .r4 .r11 3, .addi .r4 .r4 16, .addi .r10 .r21 hdrBytes, .add .r5 .r10 .r4,
    .add .r8 .r5 .r4, .add .r9 .r8 .r4, .lsl .r11 .r11 1]

/-- The `w` words (`2 w` digits) at `r14` := 0, through `r17`. -/
def zeroWords : Prog isa :=
  .seq (.block [.lsr .d .r17 .r11 1, .li .r0 0])
    (countLoop .r17 [.store .d .r0 .r14 0, .addi .r14 .r14 8])

/-- `n`'s `k` bytes (at `r12`), most significant first, into array 0: byte
`i` is byte `k - 1 - i` of the number, which is little-endian in memory. -/
def loadN : Prog isa :=
  .seq (.block [.addi .r14 .r10 0]) (.seq zeroWords
    (.seq (.block [.add .r15 .r10 .r6, .subi .r15 .r15 1, .addi .r16 .r12 0, .addi .r17 .r6 0])
      (countLoop .r17 [.lbz .r0 .r16 0, .stb .r0 .r15 0, .addi .r16 .r16 1, .subi .r15 .r15 1])))

/-- `n`'s last byte's low bit, inverted, into `r0`, its first byte into
`r15`, and 1 into `r18`. -/
def check1 : List Instr :=
  [.add .r15 .r12 .r6, .subi .r15 .r15 1, .lbz .r0 .r15 0, .li .r18 1,
    .logic .and .r0 .r0 .r18, .logic .xor .r0 .r0 .r18, .lbz .r15 .r12 0]

/-- The rest of `check`, from the bytes `check1` loaded. -/
def check2 : Prog isa :=
  .seq (.ite (.zero .d .r15) (.block [.li .r0 1]) (.block []))
    (.seq (.block [.subi .r16 .r6 64])
      (.ite (.zero .d .r16) (.block [.lsr .d .r15 .r15 7, .logic .xor .r15 .r15 .r18,
        .logic .or .r0 .r0 .r15]) (.block [])))

/-- Whether `n` is a valid modulus, in `r0`: 0 if it is. Its last byte is
odd, its first is not zero, and if `k = 64`, its first byte's top bit is
set: `r0 := (1 - last & 1) | (first = 0) | (k = 64 ∧ first < 128)`. -/
def check : Prog isa := .seq (.block check1) check2

/-- `x := 1` in array 1 (`r5`). -/
def one : Prog isa :=
  .seq (.block [.addi .r14 .r5 0]) (.seq zeroWords (.block [.li .r0 1, .store .w .r0 .r5 0]))

/-- `acc := 2 x`, `n + 1` digits. -/
def double : Prog isa :=
  .seq (.block [.addi .r14 .r8 0, .addi .r15 .r5 0, .addi .r17 .r11 0, .li .r20 0])
    (.seq (countLoop .r17 [.load .w .r0 .r15 0, .add .r0 .r0 .r0, .add .r0 .r0 .r20,
        .store .w .r0 .r14 0, .lsr .d .r20 .r0 32, .addi .r14 .r14 4, .addi .r15 .r15 4])
      (.block [.store .w .r20 .r14 0]))

/-- `x := 2 x mod n`. -/
def doubleMod : Prog isa := .seq double (.seq subMod selectAcc)

/-- `acc := 2 x + b`, `w + 1` words of 64 bits, for `x` in array 1 (`r5`) and
the bit `b` in `r20`. -/
def double64 : Prog isa :=
  .seq (.block [.addi .r14 .r8 0, .addi .r15 .r5 0, .lsr .d .r17 .r11 1])
    (.seq (countLoop .r17 [.load .d .r0 .r15 0, .lsl .r3 .r0 1, .add .r3 .r3 .r20, .lsr .d .r20 .r0 63,
        .store .d .r3 .r14 0, .addi .r14 .r14 8, .addi .r15 .r15 8])
      (.block [.store .d .r20 .r14 0]))

/-- `x := 2 x + b mod n` (`b` in `r20`), on words of 64 bits: `double64`, then
`MontMul.lean`'s `subMod64` and `selectAcc64`. -/
def dblMod64 : Prog isa := .seq double64 (.seq subMod64 selectAcc64)

/-- `x := 2 x mod n`, on words of 64 bits. -/
def doubleMod64 : Prog isa := .seq (.block [.li .r20 0]) dblMod64

/-- `x := 2^(128 w) mod n`, by `128 w` doublings counted by `r4`. -/
def r2 : Prog isa :=
  .seq one (.seq (.block [.lsl .r4 .r11 6])
    (.loop (.seq doubleMod (.block [.subi .r4 .r4 1])) (.nonzero .d .r4)))

/-! ## `R² mod n` with Montgomery squares -/

/-- `r12 := -n⁻¹ mod 2³²`, from `n`'s low word (`r10`), by Newton's
iteration (`PublicChecked.minv`, whose file imports this one). -/
def r2Minv : List Instr :=
  [.load .d .r0 .r10 0, .load .d .r12 .r10 0] ++
    (List.range 4).flatMap (fun _ => [.mul .r3 .r0 .r12, .li .r4 2, .sub .r3 .r4 .r3, .mul .r12 .r12 .r3]) ++
    [.li .r3 0, .sub .r12 .r3 .r12, .lsl .r12 .r12 32, .lsr .d .r12 .r12 32]

/-- `r3 :=` an array's size, `4 (2 w) + 16` bytes, from `2 w` in `r11`. -/
def r2Stride : List Instr := [.lsl .r3 .r11 2, .addi .r3 .r3 16]

/-- `rd :=` the base of array `j`, from array 0's (`r10`) and the size in `r3`. -/
def r2Base (rd : Reg) (j : Nat) : List Instr := .addi rd .r10 0 :: List.replicate j (.add rd rd .r3)

/-- `x := 2^(64 (w - 1))`: array 1 (`r5`) zeroed, then its word `w - 1` := 1. -/
def r2Top : Prog isa :=
  .seq (.block [.addi .r14 .r5 0]) (.seq zeroWords
    (.block [.lsl .r14 .r11 2, .add .r14 .r14 .r5, .subi .r14 .r14 8, .li .r0 1, .store .d .r0 .r14 0]))

/-- `x := x² R⁻¹ mod n` in array 1: `MontMul.tail` with the bases from `r10`
and `r11`. -/
def r2Sq : Prog isa :=
  .seq (.block (r2Stride ++ r2Base .r5 1 ++ r2Base .r6 1 ++ r2Base .r7 1 ++ r2Base .r8 2 ++ r2Base .r9 3 ++ [.addi .r4 .r11 0]))
    tail

/-- Six Montgomery squares of `x` in array 1 (`r2Sq`), each doubling the
power of 2 of `x = 2^e R mod n` (`(2^e R)² R⁻¹ = 2^(2 e) R`): from `2^w R mod n`
to `2^(64 w) R mod n = R² mod n`. -/
def r2Squares : Prog isa := .seq r2Sq (.seq r2Sq (.seq r2Sq (.seq r2Sq (.seq r2Sq r2Sq))))

/-- `64 + w` doublings of `x = 2^(64 (w - 1))` (`r2Top`), counted by `r4`:
`2^w R mod n`, for `n` above `2^(64 (w - 1))`. -/
def r2HiDbl : Prog isa :=
  .seq r2Top (.seq (.block [.lsr .d .r4 .r11 1, .addi .r4 .r4 64])
    (.loop (.seq doubleMod (.block [.subi .r4 .r4 1])) (.nonzero .d .r4)))

/-- `x := R² mod n = 2^(128 w) mod n` in array 1, for `n` of `w` words with its
top word not zero, `-n⁻¹ mod 2³²` in `r12` and the bases of arrays 1–3 in
`r5`, `r8` and `r9`: `r2HiDbl`, then `r2Squares`. -/
def r2Hi : Prog isa := .seq r2HiDbl r2Squares

/-- `w` words from `r15` to `r14`, both advanced past them. -/
def copyWords : Prog isa :=
  .seq (.block [.lsr .d .r17 .r11 1])
    (countLoop .r17 [.load .d .r0 .r15 0, .store .d .r0 .r14 0, .addi .r14 .r14 8, .addi .r15 .r15 8])

/-! ## `R² mod n` by word steps of long division

For `vg_rsa_public_precompute`: `x := 2^(64 (w - 1))` (`r2Top`), below a
valid `n`, then `w + 1` steps `x := x 2^64 mod n`, each a step of long
division (Knuth, TAOCP vol. 2, §4.3.1, Algorithm D) whose quotient is
estimated from the top words of `x P` and `n P` for `P = 2^z`, `z` the
leading zeros of `n`'s top word (`norm`), so that the divisor's top word
`d' = ⌊n P / 2^(64 (w - 1))⌋` has its top bit set, for any `n`:
`min(⌊(u₂ 2^64 + u₁) / d'⌋, 2^64 - 1)` by the reciprocal of `d'`, computed
once (`recip`, `quot`), corrected by the top three words `U` of `x P` and
the top two `D` of `n P` to `q̂ = min(⌊U / D⌋, 2^64 - 1)` (`quot3`), at most 1
more than the quotient, then `t = x 2^64 - q̂ n` in place of `x` (`mulSub`),
and `n` added to `t` once if it is negative (`addBack`). The arithmetic is
branch-free, by masks and carries, and every count depends only on `w`. -/

/-- `n`'s top word `T` (`r15`) and the one below (`r16`); `P := 1` (`r6`),
zero (`r20`), one (`r22`) and 63 (`r17`). -/
def normHead : List Instr :=
  [.lsl .r14 .r11 2, .add .r14 .r14 .r10, .subi .r14 .r14 16, .load .d .r15 .r14 8, .load .d .r16 .r14 0,
    .li .r6 1, .li .r20 0, .li .r22 1, .li .r17 63]

/-- `r15` and `P` doubled if `r15`'s top bit is clear, by a mask. -/
def normStep : List Instr :=
  [.lsr .d .r3 .r15 63, .logic .xor .r3 .r3 .r22, .sub .r3 .r20 .r3, .logic .and .r0 .r15 .r3,
    .add .r15 .r15 .r0, .logic .and .r0 .r6 .r3, .add .r6 .r6 .r0]


/-- The top two words `u₂` (`r15`) and `u₁` (`r16`) of `x P` from `x`'s top
three words (at `r14`), `P` (`r6`), `d'` (`r7`), `v` (`r18`), `e = d' - u₂`
(`r22`) and zero (`r20`). -/
def quotHead : List Instr :=
  [.lsl .r14 .r11 2, .add .r14 .r14 .r5, .subi .r14 .r14 24, .load .d .r0 .r14 16, .load .d .r3 .r14 8,
    .load .d .r12 .r14 0, .load .d .r6 .r9 0, .load .d .r7 .r9 8, .load .d .r18 .r9 16,
    .mul .r15 .r0 .r6, .mulhu .r16 .r3 .r6, .add .r15 .r15 .r16, .mul .r16 .r3 .r6, .mulhu .r0 .r12 .r6,
    .add .r16 .r16 .r0, .sub .r22 .r7 .r15, .li .r20 0]

/-- A bit of restoring division by `d'` (`r7`) of the remainder `r`
(`r15`), the next bit the top of `r16`: `r := 2 r + b`, its carry into `r3`;
`d'` subtracted if the carry is set or `r ≥ d'`, by a mask; `q := 2 q +`
that bit. -/
def divBit : List Instr :=
  [.lsr .d .r3 .r15 63, .add .r15 .r15 .r15, .lsr .d .r0 .r16 63, .add .r15 .r15 .r0, .add .r16 .r16 .r16,
    .subc .r0 .r15 .r7, .addze .r12 .r20, .logic .or .r3 .r3 .r12, .sub .r12 .r20 .r3, .logic .and .r0 .r7 .r12,
    .sub .r15 .r15 .r0, .add .r18 .r18 .r18, .add .r18 .r18 .r3]

/-- `d' := T P + ⌊n_{w-2} P / 2^64⌋` and `d'ₗ := n_{w-2} P + ⌊n_{w-3} P /
2^64⌋ mod 2^64`, the top two words of `n P`; `P`, `d'` and `d'ₗ` into the
temporary's words 0, 1 and 3. -/
def normTail : List Instr :=
  [.mulhu .r0 .r16 .r6, .add .r15 .r15 .r0, .mul .r16 .r16 .r6, .subi .r3 .r14 8, .load .d .r3 .r3 0,
    .mulhu .r3 .r3 .r6, .add .r16 .r16 .r3, .store .d .r6 .r9 0, .store .d .r15 .r9 8, .store .d .r16 .r9 24]

/-- `d'` (`r7`, from the temporary's word 1, at `r9`), zero (`r20`) and the
reciprocal's dividend `2^128 - 1 - d' 2^64`: `r := 2^64 - 1 - d'` (`r15`),
its low word all ones (`r16`), `q := 0` (`r18`) and 64 (`r17`). -/
def recipHead : List Instr :=
  [.load .d .r7 .r9 8, .li .r20 0, .subi .r16 .r20 1, .sub .r15 .r16 .r7, .li .r18 0, .li .r17 64]

/-- `v := ⌊(2^128 - 1) / d'⌋ - 2^64` into the temporary's word 2, by 64 bits
of restoring division (`divBit`). -/
def recip : Prog isa :=
  .seq (.block recipHead) (.seq (countLoop .r17 divBit) (.block [.store .d .r18 .r9 16]))

/-- `P`, `d'` and `d'ₗ`, from `n`'s top three words: 63 steps of `normStep`. -/
def norm : Prog isa := .seq (.block normHead) (.seq (countLoop .r17 normStep) (.block normTail))

/-- `q̂ := q`, or all ones if `u₂ = d'` (`e = 0`). -/
def quotFix : List Instr :=
  [.sub .r12 .r20 .r22, .logic .or .r12 .r12 .r22, .lsr .d .r12 .r12 63, .subi .r12 .r12 1,
    .logic .or .r18 .r18 .r12]

/-- `q := ⌊(u₂ 2^64 + u₁) / d'⌋` (`r18`), for `u₂ < d'`, by the reciprocal
`v` (`r18`) (Möller and Granlund, "Improved division by invariant
integers", Algorithm 4): `(q₁, q₀) := v u₂ + (u₂, u₁)`, `q₁ := q₁ + 1`,
`r := u₁ - q₁ d'`; `q₁ - 1` and `r + d'` if `r > q₀`, then `q₁ + 1` if
`r ≥ d'`, by the carry. -/
def quotMG : List Instr :=
  [.mul .r0 .r18 .r15, .mulhu .r3 .r18 .r15, .addc .r0 .r0 .r16, .adde .r3 .r3 .r15, .addi .r3 .r3 1,
    .mul .r12 .r3 .r7, .sub .r12 .r16 .r12, .subc .r17 .r0 .r12, .sube .r17 .r20 .r20, .add .r3 .r3 .r17,
    .logic .and .r17 .r17 .r7, .add .r12 .r12 .r17, .subc .r17 .r12 .r7, .addze .r18 .r3]

/-- `q̂` into `r18`: `min(⌊(u₂ 2^64 + u₁) / d'⌋, 2^64 - 1)`. -/
def quot : List Instr := quotHead ++ quotMG ++ quotFix

/-- `u₀ = x₀ P + ⌊x₋₁ P / 2^64⌋ mod 2^64` (`r0`), the third word of `x P`,
from `x`'s words `x₀` and `x₋₁` below its top two (at `r14`), `d'ₗ` (`r22`)
and `q̂ D` (`r6`, `r17`, `r12`) for `D = (d', d'ₗ)` (`r7`, `r22`) and `q̂`
(`r18`). -/
def quot3Mul : List Instr :=
  [.load .d .r0 .r14 0, .mul .r0 .r0 .r6, .subi .r3 .r14 8, .load .d .r3 .r3 0, .mulhu .r3 .r3 .r6,
    .add .r0 .r0 .r3, .load .d .r22 .r9 24, .mul .r12 .r18 .r22, .mulhu .r3 .r18 .r22, .mul .r17 .r18 .r7,
    .mulhu .r6 .r18 .r7, .addc .r17 .r17 .r3, .addze .r6 .r6]

/-- `t = U - q̂ D` over three words (`r15`, `r16`, `r0`), for `U = (u₂, u₁, u₀)`,
with its borrows. -/
def quot3Sub : List Instr := [.subc .r0 .r0 .r12, .sube .r16 .r16 .r17, .sube .r15 .r15 .r6]

/-- `q̂ := q̂ - 1` and `t := t + D` if `t` is negative (its top word's sign),
by a mask. -/
def quot3Fix : List Instr :=
  [.lsr .d .r3 .r15 63, .sub .r18 .r18 .r3, .sub .r3 .r20 .r3, .logic .and .r12 .r22 .r3,
    .logic .and .r17 .r7 .r3, .addc .r0 .r0 .r12, .adde .r16 .r16 .r17, .addze .r15 .r15]

/-- `q̂ := min(⌊U / D⌋, 2^64 - 1)` from `quot`'s `min(⌊(u₂ 2^64 + u₁) / d'⌋,
2^64 - 1)`, at most 2 more (Knuth, TAOCP vol. 2, §4.3.1, Theorem B): `t = U -
q̂ D`, and `q̂` one less while `t` is negative, twice (the second time only
`q̂`). -/
def quot3 : List Instr :=
  quot3Mul ++ (quot3Sub ++ (quot3Fix ++ [.lsr .d .r3 .r15 63, .sub .r18 .r18 .r3]))

/-- `x`'s pointer (`r14`), `n`'s (`r15`), `w` (`r17`), the carry `c := 0`
(`r3`), the borrow as a carry `b := 1` (`r22`, no borrow), `x`'s previous
word `0` (`r16`) and all ones (`r6`). -/
def mulSubHead : List Instr :=
  [.addi .r14 .r5 0, .addi .r15 .r10 0, .lsr .d .r17 .r11 1, .li .r3 0, .li .r22 1, .li .r16 0, .subi .r6 .r20 1]

/-- A word of `t := x 2^64 - q̂ n` in place: `(c, l) := n_i q̂ + c` (`r3`,
`r12`), then `t_i := x_{i-1} - l` less the borrow (the carry `b` restored
into `CA` by `b + 2^64 - 1`, and the next `b` taken from it), `x_i` kept as
the next previous word. -/
def mulSubWord : List Instr :=
  [.load .d .r0 .r15 0, .mul .r12 .r0 .r18, .mulhu .r0 .r0 .r18, .addc .r12 .r12 .r3, .addze .r3 .r0,
    .load .d .r7 .r14 0, .addc .r0 .r22 .r6, .sube .r12 .r16 .r12, .addze .r22 .r20, .store .d .r12 .r14 0,
    .addi .r16 .r7 0, .addi .r14 .r14 8, .addi .r15 .r15 8]

/-- `t`'s top word, `x_{w-1} - c` less the borrow. -/
def mulSubTop : List Instr := [.addc .r0 .r22 .r6, .sube .r12 .r16 .r3, .store .d .r12 .r14 0]

/-- `mulSub` after its head: the `w` words and the top word. -/
def mulSubRest : Prog isa := .seq (countLoop .r17 mulSubWord) (.block mulSubTop)

/-- `x`'s first `w + 1` words := `t = x 2^64 - q̂ n` modulo `2^(64 (w + 1))`
(`x` at `r5`, `n` at `r10`, `q̂` in `r18`). -/
def mulSub : Prog isa := .seq (.block mulSubHead) mulSubRest

/-- `mulSubHead`, but `x`'s previous word `u` loaded from `r8`: the word
below `x` in a division. -/
def mulSubHeadU : List Instr :=
  [.addi .r14 .r5 0, .addi .r15 .r10 0, .lsr .d .r17 .r11 1, .li .r3 0, .li .r22 1, .load .d .r16 .r8 0,
    .subi .r6 .r20 1]

/-- `x`'s first `w + 1` words := `t = x 2^64 + u - q̂ n` modulo `2^(64 (w + 1))`,
`u` the word at `r8`. -/
def mulSubU : Prog isa := .seq (.block mulSubHeadU) mulSubRest

/-- `t := t + n` if `t` (`x`'s `w + 1` words, at `r5`) is negative, by a
mask of its sign. -/
def addBack : Prog isa :=
  .seq (.block [.lsl .r14 .r11 2, .add .r14 .r14 .r5, .load .d .r0 .r14 0, .lsr .d .r0 .r0 63, .sub .r12 .r20 .r0,
      .addi .r14 .r5 0, .addi .r15 .r10 0, .lsr .d .r17 .r11 1, .addc .r0 .r20 .r20])
    (.seq (countLoop .r17 [.load .d .r0 .r15 0, .logic .and .r0 .r0 .r12, .load .d .r3 .r14 0, .adde .r3 .r3 .r0,
        .store .d .r3 .r14 0, .addi .r14 .r14 8, .addi .r15 .r15 8])
      (.block [.load .d .r3 .r14 0, .adde .r3 .r3 .r20, .store .d .r3 .r14 0]))

/-- `x := x 2^64 mod n`. -/
def wordStep : Prog isa := .seq (.block (quot ++ quot3)) (.seq mulSub addBack)

/-- `x := (x 2^64 + u) mod n`, for `u` the word at `r8`: a step of long
division, `wordStep` with the word below `x` in place of zero. -/
def wordStepU : Prog isa := .seq (.block (quot ++ quot3)) (.seq mulSubU addBack)

/-- `w + 1` of `wordStep`, counted by `r4`. -/
def wordSteps : Prog isa :=
  .seq (.block [.lsr .d .r4 .r11 1, .addi .r4 .r4 1])
    (.loop (.seq wordStep (.block [.subi .r4 .r4 1])) (.nonzero .d .r4))

/-- `x := R² mod n` in array 1 for `vg_rsa_public_precompute`, for `n` of
`w ≥ 4` words with its top word not zero: `norm`, the reciprocal (`recip`),
`x := 2^(64 (w - 1))` (`r2Top`), and `w + 1` word steps:
`2^(64 (w - 1) + 64 (w + 1)) = R²`. -/
def r2Fast : Prog isa := .seq norm (.seq recip (.seq r2Top wordSteps))

/-- `x := R² mod n = 2^(128 w) mod n` in array 1, for any odd `n` of `w`
words, with `-n⁻¹ mod 2³²` in `r12` and the bases of arrays 1–3 in `r5`, `r8`
and `r9`: `x := 1`; `64 w + w` doublings to `2^w R mod n` (`doubleMod64`);
then six Montgomery squares to `2^(64 w) R mod n`, as in `r2Hi`, counted by
`r24`. -/
def r2Prime : Prog isa :=
  .seq one (.seq (.block [.lsl .r4 .r11 5, .lsr .d .r3 .r11 1, .add .r4 .r4 .r3])
    (.seq (.loop (.seq doubleMod64 (.block [.subi .r4 .r4 1])) (.nonzero .d .r4))
      (.seq (.block [.li .r24 6]) (.loop (.seq r2Sq (.block [.subi .r24 .r24 1])) (.nonzero .d .r24)))))

/-- `n` and `x` into `pre`. -/
def write : Prog isa :=
  .seq (.block [.addi .r14 .r19 0, .addi .r15 .r10 0]) (.seq copyWords
    (.seq (.block [.addi .r15 .r5 0]) copyWords))

/-- `pre`'s `2 w` words := 0. -/
def zeroPre : Prog isa :=
  .seq (.block [.addi .r14 .r19 0]) (.seq zeroWords zeroWords)

/-- Load and check `n`, then write `n` and `R² mod n` to `pre` and return 1,
or zero `pre` and return 0. -/
def core : Prog isa :=
  .seq loadN (.seq check (.ite (.zero .d .r0) (.seq r2Fast (.seq write (.block [.li .r3 1])))
    (.seq zeroPre (.block [.li .r3 0]))))

/-- `vg_rsa_public_precompute(pre, pre_len, n, n_len, scratch, scratch_len)`. -/
def precompute : Prog isa :=
  .seq (.block (save ++ setup)) (.seq core (.block restore))

end VG.Impl.Bignum.PPC64LE.Precompute
