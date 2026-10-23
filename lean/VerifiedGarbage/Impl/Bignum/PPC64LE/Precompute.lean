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
`R² mod n = 2^(128 w) mod n` is computed from `x = 1` by `128 w` modular
doublings: the double into the accumulator (`n + 1` digits of 32 bits, as
`vg_rsa_mont_mul` reads numbers), then `MontMul.lean`'s `subMod` and
`selectAcc` into `x`.

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

/-- Whether `n` is a valid modulus, in `r0`: 0 if it is. Its last byte is
odd, its first is not zero, and if `k = 64`, its first byte's top bit is
set: `r0 := (1 - last & 1) | (first = 0) | (k = 64 ∧ first < 128)`. -/
def check : Prog isa :=
  .seq (.block [.add .r15 .r12 .r6, .subi .r15 .r15 1, .lbz .r0 .r15 0, .li .r18 1,
      .logic .and .r0 .r0 .r18, .logic .xor .r0 .r0 .r18, .lbz .r15 .r12 0])
    (.seq (.ite (.zero .d .r15) (.block [.li .r0 1]) (.block []))
      (.seq (.block [.subi .r16 .r6 64])
        (.ite (.zero .d .r16) (.block [.lsr .d .r15 .r15 7, .logic .xor .r15 .r15 .r18,
          .logic .or .r0 .r0 .r15]) (.block []))))

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
  .seq loadN (.seq check (.ite (.zero .d .r0) (.seq r2 (.seq write (.block [.li .r3 1])))
    (.seq zeroPre (.block [.li .r3 0]))))

/-- `vg_rsa_public_precompute(pre, pre_len, n, n_len, scratch, scratch_len)`. -/
def precompute : Prog isa :=
  .seq (.block (save ++ setup)) (.seq core (.block restore))

end VG.Impl.Bignum.PPC64LE.Precompute
