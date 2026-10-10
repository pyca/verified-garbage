import VerifiedGarbage.Impl.Bignum.AArch64

/-!
# The RSA public-key operations on AArch64

The working space, header and arrays of `Impl/Bignum/Layout.lean`, and
Montgomery multiplication `mul o a b` (`[o] = [a] [b] R⁻¹ mod m`), the
baseline `Public.mm` or one for other CPU features.

* `vg_rsa_public_precompute` (`Precompute.code`) writes what Montgomery
  multiplication needs of a modulus, `m` and `R² mod m`, once per key.
* `vg_rsa_public_precomputed_checked` (`Checked.precomputedChecked`)
  computes RSAEP from them, for an exponent within BoringSSL's limits.
* `vg_rsa_public_checked` (`Checked.publicChecked`) runs `Precompute`'s
  steps and then `Precomputed`'s in one working space: `m` and `R² mod m`
  are already in the arrays where `Precomputed` loads them.

The arguments are those of x86-64's (`Impl/Rsa/X86_64.lean`), in `x0`–`x7`
and, from the ninth, on the stack (AAPCS64): the working space `scratch` is
the first stack argument for the public-key operations.
-/

namespace VG.Impl.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64

/-- `w := ⌈k / 8⌉` (`k` from the header, into `x3`) into `x12` and its slot,
and the arrays' bases. -/
def head : List Instr :=
  [ldh .x3 sK, .addImm .x .x12 .x3 7, .lsr .x .x12 .x12 3, sth .x12 sW] ++ setBases

/-- `x9` zero if the modulus (`k` bytes at `x2`, `k` in `x3`) is not valid:
its first byte is zero, it is even, or it is below `2^511`, which for
`k ≥ 64` is `256 (k - 64) + m[0] < 128`. Each condition is a comparison's
carry, made 0 or 1 by `csel`. -/
def invalid : List Instr :=
  [.ldrb .x5 .x2 0, .subImm .x .x6 .x3 1, .add .x .x6 .x2 .x6, .ldrb .x6 .x6 0, movi .x7 0, movi .x8 1,
    .subs .x .x10 .x5 .x8, .csel .x .x10 .x8 .x7, .logic .and .x .x6 .x6 .x8,
    .subImm .x .x11 .x3 64, .lsl .x .x11 .x11 8, .add .x .x11 .x11 .x5, movi .x12 128,
    .subs .x .x12 .x11 .x12, .csel .x .x11 .x8 .x7, .logic .and .x .x9 .x10 .x6,
    .logic .and .x .x9 .x9 .x11]

/-- The modulus' bytes (pointer in slot `sN`) into array `aN`, and `-m⁻¹`
into its slot. -/
def pcLoad : List (Prog isa) := [
  .block (head ++ [ldh .x1 sN, ldh .x8 (sArr aN), ldh .x2 sK]),
  loadBE,
  .block ([ld .x3 .x8] ++ minv ++ [sth .x15 sMinv])]

/-- `R² mod m` into array `aR2`: `2^(b - 1)` for the bit length `b` of `m`,
doubled `64 - (b - 1) mod 64 + w` times (`2^w R mod m`), then squared six
times. -/
def r2Steps (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  .block [ldh .x12 sW, ldh .x8 (sArr aN), .subImm .x .x4 .x12 1, .lsl .x .x4 .x4 3, .add .x .x4 .x8 .x4,
    ld .x3 .x4],
  topBit,
  .block [sth .x13 sCnt, .subImm .x .x13 .x12 1],
  setWord aR2,
  .block [ldh .x13 sCnt, ldh .x12 sW, .add .x .x13 .x13 .x12],
  doubles aN aAcc aTmp aR2 sCnt,
  mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2]

/-! ## `vg_rsa_public_precompute`

`(pre, pre_len, n, n_len, scratch, scratch_len)`, all in registers: `pre`
in slot `sOut`, `n` in `sN` and `n_len` in `sK`. -/

namespace Precompute

/-- The arguments in the header at `scratch` (`x4`), whose base goes in `x0`. -/
def entry : List Instr := [.str .x .x0 .x4 (8 * sOut), .str .x .x2 .x4 (8 * sN), .str .x .x3 .x4 (8 * sK), mov .x0 .x4]

/-- Zeros to the `2 ⌈k / 8⌉` words of `pre`, and 0 returned. -/
def fail : Prog isa :=
  .seq (.block [ldh .x1 sOut, ldh .x2 sK, .addImm .x .x2 .x2 7, .lsr .x .x2 .x2 3, .lsl .x .x2 .x2 1, movi .x3 0])
    (.seq (countLoop .x2 [st .x3 .x1, next .x1]) (.block [movi .x0 0]))

/-- `m`, then `R² mod m`, to `pre`, and 1 returned. -/
def pcOut : List (Prog isa) := [
  .block [ldh .x12 sW, ldh .x16 (sArr aN), ldh .x17 sOut],
  copyWords,
  .block [ldh .x16 (sArr aR2)],
  copyWords,
  .block [movi .x0 1]]

/-- The computation, once `m` is known valid. -/
def main (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs (pcLoad ++ (r2Steps mul ++ pcOut))

/-- `vg_rsa_public_precompute`. -/
def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block (entry ++ invalid)) (.ite (.zero .x .x9) fail (main mul))

end Precompute

/-! ## The exponentiation from precomputed values

`(out, out_len, pre, pre_len, e, e_len, input, input_len, scratch,
scratch_len)`: the arguments in slots `sOut`, `sN` (`pre`, or `n`), `sK`
(`out_len`, or `n_len`), `sE`, `sElen` and `sIn`. -/

namespace Precomputed

/-- The arguments in the header at `scratch` (the first stack argument),
whose base goes in `x0`; `k` is `x1` (`out_len`, `pk = false`) or `x3`
(`n_len`). -/
def entry (pk : Bool := false) : List Instr :=
  [.ldrSp .x8 0, .str .x .x0 .x8 (8 * sOut), .str .x .x2 .x8 (8 * sN),
    .str .x (if pk then .x3 else .x1) .x8 (8 * sK), .str .x .x4 .x8 (8 * sE), .str .x .x5 .x8 (8 * sElen),
    .str .x .x6 .x8 (8 * sIn), mov .x0 .x8]

/-- Zeros to the `k` bytes of `out`, and 0 returned. -/
def fail : Prog isa :=
  .seq (.block [ldh .x1 sOut, ldh .x2 sK, movi .x3 0])
    (.seq (countLoop .x2 [.strb .x3 .x1 0, .addImm .x .x1 .x1 1]) (.block [movi .x0 0]))

/-- `m` and `R² mod m` from `pre` into their arrays, then `x9` nonzero iff
`m` is odd, its top word is not zero and `R² mod m < m`: the values of no
modulus are refused before any arithmetic on them. -/
def load : List (Prog isa) := [
  .block (head ++ [ldh .x16 sN, ldh .x17 (sArr aN)]),
  copyWords,
  .block [ldh .x17 (sArr aR2)],
  copyWords,
  .block [ldh .x16 (sArr aR2), ldh .x17 (sArr aN), movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7],
  cmpLoop,
  .block [movi .x8 1, .csel .x .x9 .x7 .x8, ldh .x17 (sArr aN), ld .x3 .x17, .logic .and .x .x3 .x3 .x8,
    .logic .and .x .x9 .x9 .x3, .subImm .x .x4 .x12 1, .lsl .x .x4 .x4 3, .add .x .x4 .x17 .x4, ld .x3 .x4,
    .subs .x .x3 .x3 .x8, .csel .x .x3 .x8 .x7, .logic .and .x .x9 .x9 .x3]]

/-- Whether the exponentiation has started, into `x3` (0 if not). -/
def startedTest : List Instr := [ldh .x3 sStarted]

/-- The bit of `e` at the top of the byte in `sV`, into `x3`. -/
def bitTest : List Instr := [ldh .x3 sV, .lsr .x .x3 .x3 7, movi .x4 1, .logic .and .x .x3 .x3 .x4]

/-- The next bit: `sV := 2 sV`, `sBit := sBit - 1`, into `x3`. -/
def bitNext : List Instr :=
  [ldh .x3 sV, .add .x .x3 .x3 .x3, sth .x3 sV, ldh .x3 sBit, .subImm .x .x3 .x3 1, sth .x3 sBit]

/-- Byte `sI` of `e` into `sV`, and `sBit := 8`. -/
def byteHead : List Instr :=
  [ldh .x3 sE, ldh .x4 sI, .add .x .x3 .x3 .x4, .ldrb .x3 .x3 0, sth .x3 sV, movi .x3 8, sth .x3 sBit]

/-- The next byte: `sI := sI + 1`, and `e_len - sI` into `x3`. -/
def byteNext : List Instr :=
  [ldh .x3 sI, .addImm .x .x3 .x3 1, sth .x3 sI, ldh .x4 sElen, .sub .x .x3 .x4 .x3]

/-- `Y := X` (the input in Montgomery form), and the exponentiation started. -/
def start : Prog isa :=
  .seq (.block [ldh .x12 sW, ldh .x16 (sArr aXm), ldh .x17 (sArr aY)])
    (.seq copyWords (.block [movi .x3 1, sth .x3 sStarted]))

variable (mul : Nat → Nat → Nat → Prog isa)

/-- One bit of `e`, once started: `Y := Y²`; then if the bit is set,
`Y := Y X` once started, or `Y := X` and started. Before the first set bit
`Y` is not used, and squaring 1 is skipped. -/
def expBit : Prog isa :=
  .seq (.block startedTest) (.seq (.ite (.nonzero .x .x3) (mul aY aY aY) (.block []))
    (.seq (.block bitTest)
      (.seq (.ite (.nonzero .x .x3) (.seq (.block startedTest) (.ite (.nonzero .x .x3) (mul aY aY aXm) start))
          (.block []))
        (.block bitNext))))

/-- The exponentiation, over the bytes of `e` and their bits, most
significant first. -/
def expLoop : Prog isa :=
  .seq (.block [movi .x3 0, sth .x3 sI, sth .x3 sStarted])
    (.loop (.seq (.block byteHead) (.seq (.loop (expBit mul) (.nonzero .x .x3)) (.block byteNext)))
      (.nonzero .x .x3))

/-- `Y R⁻¹`, or 1 if `e = 0`. -/
def finish : Prog isa :=
  .seq (.block startedTest)
    (.ite (.nonzero .x .x3) (mul aY aY aOne)
      (.seq (.block [ldh .x12 sW, movi .x9 1, movi .x13 0]) (setWord aY)))

/-- The computation, once `m` and `R² mod m` are in their arrays: the input
into array `aX`, the mask of `input < m` into `sMask`, `-m⁻¹` and the number
1, the exponentiation, and the result stored masked, with the mask's low
bit returned. -/
def rest : Prog isa := seqs [
  .block [ldh .x1 sIn, ldh .x2 sK, ldh .x8 (sArr aX)],
  loadBE,
  -- The mask of `input < m`: all ones on a borrow.
  .block [ldh .x12 sW, ldh .x16 (sArr aX), ldh .x17 (sArr aN), movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7],
  cmpLoop,
  -- `-m⁻¹`, and the number 1.
  .block (([.subImm .x .x4 .x7 1, .csel .x .x15 .x7 .x4, sth .x15 sMask, ldh .x8 (sArr aN), ld .x3 .x8] : List Instr) ++ minv ++
    [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0]),
  setWord aOne,
  -- `X = input R mod m`, the exponentiation, and the result.
  mul aXm aX aR2, expLoop mul, finish mul,
  .block [ldh .x8 (sArr aY), ldh .x1 sOut, ldh .x9 sK, .add .x .x1 .x1 .x9, ldh .x15 sMask],
  storeBE,
  .block [ldh .x0 sMask, movi .x3 1, .logic .and .x .x0 .x0 .x3]]

/-- `vg_rsa_public_precomputed`'s code, without the check of `e`. -/
def code : Prog isa :=
  .seq (.block (entry false)) (.seq (seqs load) (.ite (.zero .x .x9) fail (rest mul)))

end Precomputed

/-! ## The public-key operation from the modulus -/

namespace Public

/-- RSAEP from the modulus' bytes: `Precompute`'s steps, but for writing the
values out, then `Precomputed`'s. -/
def code : Prog isa :=
  .seq (.block (Precomputed.entry true ++ invalid))
    (.ite (.zero .x .x9) Precomputed.fail (seqs (pcLoad ++ (r2Steps Bignum.AArch64.Public.mm ++ [Precomputed.rest Bignum.AArch64.Public.mm]))))

end Public

/-! ## BoringSSL's limits on the public exponent

`expCheck` decides whether `e` (`x4`, `e_len ≥ 1` bytes in `x5`) is odd and
from 3 to `2^33 - 1` (BoringSSL's `rsa_check_public_key`), into `x9`
(nonzero iff it is), using only `x9`–`x17`, so that the arguments stay where
the function it guards expects them. Its bytes, most significant first, are
read into `x10` saturated: `x` while the bytes so far make `x < 2^33`,
`2^34 - 1` from the first that does not (`256 (2^34 - 1) + 255 < 2^64`). -/

namespace Checked

/-- `2^34 - 1` into `x16`, 0 into `x17`, 1 into `x15`. -/
def consts : List Instr :=
  [.movz .x .x16 (BitVec.ofNat 16 0xFFFF) 0, .movk .x .x16 (BitVec.ofNat 16 0xFFFF) 1,
    .movk .x .x16 (BitVec.ofNat 16 3) 2, movi .x17 0, movi .x15 1]

/-- One byte of `e`: `x10 := 256 x10 + e[x11]`, then `2^34 - 1` if that is
`2^33` or more; `x11 += 1`, and `e_len - x11` into `x14`. -/
def expStep : List Instr :=
  [.lsl .x .x10 .x10 8, .add .x .x12 .x4 .x11, .ldrb .x12 .x12 0, .add .x .x10 .x10 .x12,
    .lsr .x .x13 .x10 33, .adds .x .x13 .x13 .x17, .cselc .x .x10 .x10 .x16 .eq, .addImm .x .x11 .x11 1,
    .sub .x .x14 .x5 .x11]

/-- `x9` nonzero iff the saturated `e` in `x10` is below `2^33`, odd and at
least 3. -/
def expTest : List Instr :=
  [.lsr .x .x13 .x10 33, .adds .x .x13 .x13 .x17, .cselc .x .x13 .x15 .x17 .eq,
    .logic .and .x .x14 .x10 .x15, movi .x12 3, .subs .x .x12 .x10 .x12, .csel .x .x12 .x15 .x17,
    .logic .and .x .x9 .x13 .x14, .logic .and .x .x9 .x9 .x12]

/-- `x9` nonzero iff `e` is within BoringSSL's limits. -/
def expCheck : Prog isa :=
  .seq (.block (consts ++ [movi .x10 0, movi .x11 0]))
    (.seq (.loop (.block expStep) (.nonzero .x .x14)) (.block expTest))

/-- Zeros to the `out_len` (at least 1) bytes of `out`, and 0 returned. -/
def failOut : Prog isa :=
  .seq (.block [mov .x10 .x0, mov .x11 .x1, movi .x12 0])
    (.seq (countLoop .x11 [.strb .x12 .x10 0, .addImm .x .x10 .x10 1]) (.block [movi .x0 0]))

/-- `c`, if `e` is within BoringSSL's limits. -/
def guarded (c : Prog isa) : Prog isa := .seq expCheck (.ite (.zero .x .x9) failOut c)

/-- `vg_rsa_public_checked`. -/
def publicChecked : Prog isa := guarded Public.code

/-- `vg_rsa_public_precomputed_checked`, with Montgomery multiplication `mul`. -/
def precomputedChecked (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  guarded (Precomputed.code mul)

end Checked

end VG.Impl.Rsa.AArch64
