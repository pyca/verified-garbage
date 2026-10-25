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
which is below a valid `n`, by `64 + w` modular doublings to `2^w R mod n`
(the double into the accumulator, `n + 1` digits of 32 bits, as
`vg_rsa_mont_mul` reads numbers, then `MontMul.lean`'s `subMod` and
`selectAcc` into `x`), then six Montgomery squares (`MontMul.tail`). For
moduli whose top word may be zero, `r2Prime` starts from 1, with `64 w + w`
doublings (the private key's primes), and `r2`, `128 w` doublings from 1,
needs no `-n⁻¹ mod 2³²` (other callers).

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

/-- `r2Hi` for `vg_rsa_public_precompute`, which computes `-n⁻¹ mod 2³²` after
the doublings and keeps `pre` (`r19`) in `r21` across the squares, which
`tail` does not write; then the working space's address back in `r21`
(array 0's less the header) and the bases of arrays 1–3. -/
def r2Fast : Prog isa :=
  .seq r2HiDbl (.seq (.block (r2Minv ++ [.addi .r21 .r19 0])) (.seq r2Squares
    (.block ([.addi .r19 .r21 0, .subi .r21 .r10 hdrBytes] ++ r2Stride ++ r2Base .r5 1 ++ r2Base .r8 2 ++
      r2Base .r9 3))))

/-- `x := R² mod n = 2^(128 w) mod n` in array 1, for any odd `n` of `w`
words, with `-n⁻¹ mod 2³²` in `r12` and the bases of arrays 1–3 in `r5`, `r8`
and `r9`: `x := 1`; `64 w + w` doublings to `2^w R mod n`; then six Montgomery
squares to `2^(64 w) R mod n`, as in `r2Fast`, counted by `r24`. -/
def r2Prime : Prog isa :=
  .seq one (.seq (.block [.lsl .r4 .r11 5, .lsr .d .r3 .r11 1, .add .r4 .r4 .r3])
    (.seq (.loop (.seq doubleMod (.block [.subi .r4 .r4 1])) (.nonzero .d .r4))
      (.seq (.block [.li .r24 6]) (.loop (.seq r2Sq (.block [.subi .r24 .r24 1])) (.nonzero .d .r24)))))

/-- `w` words from `r15` to `r14`, both advanced past them. -/
def copyWords : Prog isa :=
  .seq (.block [.lsr .d .r17 .r11 1])
    (countLoop .r17 [.load .d .r0 .r15 0, .store .d .r0 .r14 0, .addi .r14 .r14 8, .addi .r15 .r15 8])

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
