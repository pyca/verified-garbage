module

public import VerifiedGarbage.Impl.Bignum.RISCV64.Precompute

/-!
# The RSA public-key operation on RISC-V

`vg_rsa_public_precomputed_checked(out = a0, out_len = a1, pre = a2,
pre_len = a3, e = a4, e_len = a5, input = a6, input_len = a7, scratch,
scratch_len)`, `scratch` and `scratch_len` on the stack: with `pre` holding
`n` and `R² mod n` of a modulus of `k = out_len` bytes and `w = ⌈k / 8⌉`
words, writes `input^e mod n` (`k` bytes, most significant first) to `out`
and returns 1, or writes zeros and returns 0 if `e` is not odd and from 3 to
`2^33 - 1` or the input is not below `n`.

As on PPC64LE (`Impl/Bignum/PPC64LE/PublicChecked.lean`), nothing branches
on a value read from memory but `e`, which is public: `e` is read into `s7`,
saturated at `2^33`, and its leading zeros skipped (`skip`); with `a = x R
mod n`, each later bit is a Montgomery square of `a` and, if it is set, a
Montgomery multiplication by `x R mod n`, but the last, whose multiplication
is by `x` itself (or 1), which also converts out of Montgomery form. The
Montgomery multiplications are `MontMul.lean`'s `tail`, inline, in its
working space (`n` in array 0, `R² mod n` in array 1, its accumulator and
temporary in arrays 2 and 3, the input and then the result in array 4, `a`
in array 5, `x R mod n` in array 6, 1 in array 7). The result is written
with a mask of whether `e` and the input are valid.

`pre` may hold anything, so before the multiplications `n` is made odd and
at least 2 and `R² mod n` below it (`sanitize`), which changes nothing in the
values of a valid modulus.

Registers kept throughout: `s6` the working space, `s7` the exponent's bits,
`s8` the bits left, `s9` the validity mask, `s10` `out`, `s11` `k`, `s5` an
array's size in bytes, `a7` array 0's base, `t0` `w`, `t1` `-n⁻¹ mod 2⁶⁴`.
The callee-saved registers are saved in the header's words 16–27.
-/

@[expose] public section

namespace VG.Impl.Bignum.RISCV64.PublicChecked

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64

/-- The callee-saved registers saved, `s6` (the working space) last. -/
def saved (i : Nat) : Reg :=
  [.s0, .s1, .s2, .s3, .s4, .s5, .s7, .s8, .s9, .s10, .s11, .s6].getD i .s0

/-- The working space's address, the first argument on the stack, into `t0`. -/
def loadS : List Instr := [.addSp .t0 0, .load .d .t0 .t0 0]

/-- The registers saved in the working space at `t0`, and its address into
`s6`. -/
def saveRegs : List Instr :=
  (List.range 12).flatMap (fun i => [.store .d (saved i) .t0 (128 + 8 * i)]) ++ [.addi .s6 .t0 0]

/-- The working space from the stack, the registers saved there. -/
def save : List Instr := loadS ++ saveRegs

/-- The registers back, through `s6`, which is restored last. -/
def restore : List Instr :=
  (List.range 11).flatMap (fun i => [.load .d (saved i) .s6 (128 + 8 * i)]) ++
    [.load .d .s6 .s6 (128 + 8 * 11)]

/-- `out` and `k` kept, `w`, the arrays' size and array 0's base. -/
def setup : List Instr :=
  [.addi .s10 .a0 0, .addi .s11 .a1 0, .addi .t0 .a1 7, .shift .srl .d .t0 .t0 3,
    .shift .sll .d .s5 .t0 3, .addi .s5 .s5 16, .addi .a7 .s6 hdrBytes]

/-- `e`'s `e_len` bytes (`a4`, `a5`) into `s7`, as a number saturated at
`2^33`: after each byte, `s7 := 2^33` if it is at least that. -/
def readE : Prog isa :=
  .seq (.block [.li .s7 0])
    (countLoop .a5 [.load .b .t2 .a4 0, .shift .sll .d .s7 .s7 8, .logic .or .s7 .s7 .t2,
      .shift .srl .d .t3 .s7 33, .li .t4 0, .sub .t3 .t4 .t3, .shift .srl .d .t3 .t3 63, .sub .t3 .t4 .t3,
      .li .t4 1, .shift .sll .d .t4 .t4 33, .logic .xor .t2 .s7 .t4, .logic .and .t2 .t2 .t3,
      .logic .xor .s7 .s7 .t2, .addi .a4 .a4 1])

/-- `s9 :=` all ones if `s7` is odd, at least 3 and below `2^33`, else 0;
then `s7`'s bit 32 to the top. -/
def checkE : List Instr :=
  [.li .t4 1, .logic .and .t2 .s7 .t4, .addi .t3 .s7 (-3), .shift .srl .d .t3 .t3 63, .logic .xor .t3 .t3 .t4,
    .logic .and .t2 .t2 .t3, .shift .sll .d .t3 .t4 33, .sub .t3 .s7 .t3, .shift .srl .d .t3 .t3 63,
    .logic .and .t2 .t2 .t3, .li .t3 0, .sub .s9 .t3 .t2, .shift .sll .d .s7 .s7 31]

/-- `rd :=` the base of array `j`: array 0's plus `j` arrays. -/
def base (rd : Reg) (j : Nat) : List Instr :=
  .addi rd .a7 0 :: List.replicate j (.add rd rd .s5)

/-- `n` (`w` words at `pre`, `a2`) into array 0 and `R² mod n` (the next `w`)
into array 1. -/
def copyPre : Prog isa :=
  .seq (.block [.addi .t3 .a7 0, .addi .t4 .a2 0]) (.seq Precompute.copyWords
    (.seq (.block [.add .t3 .a7 .s5]) Precompute.copyWords))

/-- The input's `k` bytes (`a6`) into array 4, and the array's word `w` :=
0, through `Precompute.loadN` with array 4's base in `a7` and the input and
`k` in `s7` and `s8`; `e`'s bits are kept in `a1` meanwhile. -/
def loadX : Prog isa :=
  .seq (.block (base .a7 4 ++ [.addi .a1 .s7 0, .addi .s7 .a6 0, .addi .s8 .s11 0]))
    (.seq Precompute.loadN
      (.block [.add .t3 .a7 .s5, .addi .t3 .t3 (-16), .li .s0 0, .store .d .s0 .t3 0,
        .addi .a7 .s6 hdrBytes, .addi .s7 .a1 0]))

/-- `n` (array 0) made odd (`n₀ |= 1`) and its top word not zero (`|= 1` if
it is), and word `w` of array 1 zeroed: whatever `pre` held, the Montgomery
multiplications can take it. A valid modulus is unchanged. -/
def fixN : List Instr :=
  [.load .d .s0 .a7 0, .logicImm .or .s0 .s0 1, .store .d .s0 .a7 0,
    .shift .sll .d .t3 .t0 3, .add .t3 .t3 .a7, .addi .t3 .t3 (-8), .load .d .s0 .t3 0,
    .shift .srl .d .s1 .s0 1, .logicImm .and .s2 .s0 1, .logic .or .s1 .s1 .s2, .addi .s1 .s1 (-1),
    .shift .srl .d .s1 .s1 63, .logic .or .s0 .s0 .s1, .store .d .s0 .t3 0,
    .add .t3 .a7 .s5, .shift .sll .d .s1 .t0 3, .add .s1 .t3 .s1, .li .s0 0, .store .d .s0 .s1 0]

/-- Array 1's `w` words `&= s4`. -/
def maskRR : Prog isa :=
  .seq (.block (base .t3 1 ++ [.addi .t5 .t0 0]))
    (countLoop .t5 [.load .d .s0 .t3 0, .logic .and .s0 .s0 .s4, .store .d .s0 .t3 0,
      .addi .t3 .t3 8])

/-- `fixN`, then array 1 zeroed unless `R² mod n` is below `n` (the mask of
`subMod64`, into array 3). -/
def sanitize : Prog isa :=
  .seq (.block (fixN ++ base .a5 1 ++ base .a6 3)) (.seq subMod64 maskRR)

/-- `r12 := -n⁻¹ mod 2⁶⁴`, from `n`'s low word: `Precompute.minv`. -/
def minv : List Instr := Precompute.minv

/-- `s9 &=` all ones if the input (array 4) is below `n`: the mask of
`subMod64`, into array 3. -/
def checkX : Prog isa :=
  .seq (.block (base .a5 4 ++ base .a6 3)) (.seq subMod64 (.block [.logic .and .s9 .s9 .s4]))

/-- `[o] := [a] [b] R⁻¹ mod n`: `tail`, with the bases. -/
def montOp (o a b : Nat) : Prog isa :=
  .seq (.block (base .a2 o ++ base .a3 a ++ base .a4 b ++ base .a5 2 ++ base .a6 3)) tail

/-- 1 in array 7. -/
def one : Prog isa :=
  .seq (.block (base .t3 7)) (.seq Precompute.zeroWords
    (.block (base .t3 7 ++ [.li .s0 1, .store .d .s0 .t3 0])))

/-- `e`'s leading zeros skipped: `s8 := 33`, then, until a set bit has been
shifted out of the top of `s7` or `s8` is 0, `s7` shifted left and `s8`
counted down. Then `s8` is the number of bits after `e`'s first set bit, at
the top of `s7`. -/
def skip : Prog isa :=
  .seq (.block [.li .s8 33])
    (.loop (.block [.shift .srl .d .t3 .s7 63, .shift .sll .d .s7 .s7 1, .addi .s8 .s8 (-1),
      .addi .t3 .t3 (-1), .logic .and .t3 .t3 .s8]) (.nonzero .t3))

/-- `a := x R mod n`: array 6 into array 5, by `selectAcc64` with a mask of
all ones. -/
def initA : Prog isa :=
  .seq (.block ([.li .s4 (-1)] ++ base .a5 6 ++ base .a6 6 ++ base .a2 5)) selectAcc64

/-- A bit of `e` after the first but the last: `a := a²`, then `a := a x` if
the top bit of `s7` is set, which is shifted left. -/
def bitStep : Prog isa :=
  .seq (montOp 5 5 5) (.seq (.block [.shift .srl .d .t3 .s7 63, .shift .sll .d .s7 .s7 1])
    (.ite (.nonzero .t3) (montOp 5 5 6) (.block [])))

/-- The last bit of `e`: `a := a²`, then out of Montgomery form into array 4
by a multiplication by the input (array 4) if the top bit of `s7` is set,
else by 1. -/
def lastBit : Prog isa :=
  .seq (montOp 5 5 5) (.seq (.block [.shift .srl .d .t3 .s7 63])
    (.ite (.nonzero .t3) (montOp 4 4 5) (montOp 4 7 5)))

/-- The bits after the first, `s8` of them at the top of `s7`. -/
def bits : Prog isa :=
  .ite (.nonzero .s8)
    (.seq (.block [.addi .s8 .s8 (-1)])
      (.seq (.ite (.nonzero .s8) (.loop (.seq bitStep (.block [.addi .s8 .s8 (-1)])) (.nonzero .s8))
        (.block [])) lastBit))
    (montOp 4 7 5)

/-- `x^e mod n` into array 4: 1 in array 7, `x R mod n` into array 6, `e`'s
leading zeros skipped, `a := x R mod n`, then a square per later bit and a
multiplication by `x R mod n` per later set bit but the last, which instead
multiplies by `x` and so converts out of Montgomery form. `e` is public:
the branches depend on it alone. -/
def power : Prog isa :=
  .seq one (.seq (montOp 6 4 1) (.seq skip (.seq initA bits)))

/-- The result's `k` bytes, most significant first, masked by `s9`, to
`out`; `a0 := 1` if valid, else 0. -/
def output : Prog isa :=
  .seq (.block (base .t4 4 ++ [.add .t4 .t4 .s11, .addi .t4 .t4 (-1), .addi .t3 .s10 0,
      .addi .t5 .s11 0]))
    (.seq (countLoop .t5 [.load .b .s0 .t4 0, .logic .and .s0 .s0 .s9, .store .b .s0 .t3 0,
        .addi .t3 .t3 1, .addi .t4 .t4 (-1)])
      (.block [.li .a0 1, .logic .and .a0 .a0 .s9]))

/-- From `e` to the checks: everything before the power. -/
def prep : Prog isa :=
  .seq readE (.seq (.block checkE) (.seq copyPre (.seq loadX (.seq sanitize (.seq (.block minv) checkX)))))

/-- `vg_rsa_public_precomputed_checked`. -/
def publicChecked : Prog isa :=
  .seq (.block (save ++ setup)) (.seq prep (.seq power (.seq output (.block restore))))

end VG.Impl.Bignum.RISCV64.PublicChecked
