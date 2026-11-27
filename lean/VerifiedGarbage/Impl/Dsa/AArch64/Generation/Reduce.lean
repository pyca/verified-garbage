module

public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate

/-! Native p-candidate reduction and generator-exponent arithmetic. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate

def doubleArray (dst : Nat) : Prog isa :=
  .seq (.block (ws ++ [movi .x7 0, mov .x14 .x12, .adds .x .x3 .x7 .x7] ++ base dst .x16))
    (countLoop .x14 shlBody)

def incrementEven (dst : Nat) : List Instr :=
  ws ++ base dst .x16 ++ [ld .x3 .x16, .addImm .x .x3 .x3 1, st .x3 .x16]

def reduceRemainder (dst src rem : Nat) : Prog isa :=
  .seq (seqs (subA dst src rem)) (.block (incrementEven dst))

/-! ## Division by a narrow divisor

`Keys.divmod` shifts the quotient and the remainder over all `w` words for
each of the dividend's `64 w` bits. The divisor here, `2 q`, has at most 257
bits, so `divNarrow` keeps the remainder over `k` words and takes the dividend
a word at a time: for each of a word's 64 bits, the remainder doubled with the
bit (`narrowShift`), the divisor subtracted from it into `[x8]`
(`narrowSub`), the difference taken if it did not borrow (`narrowSelect`), and
the carry, the quotient's bit, into `x15`. -/

/-- `[x16] := 2 [x16] + C` over the words `i` to `i + n - 1`: the carry out in `C`. -/
def narrowShift : Nat → Nat → List Instr
  | _, 0 => []
  | i, n + 1 => [ld .x3 .x16 (8 * i), .adcs .x .x3 .x3 .x3, st .x3 .x16 (8 * i)] ++ narrowShift (i + 1) n

/-- `[x8] := [x16] - [x17] - !C` over the words `i` to `i + n - 1`: no borrow in `C`. -/
def narrowSub : Nat → Nat → List Instr
  | _, 0 => []
  | i, n + 1 => [ld .x3 .x16 (8 * i), ld .x4 .x17 (8 * i), .sbcs .x .x3 .x3 .x4, st .x3 .x8 (8 * i)] ++
      narrowSub (i + 1) n

/-- `[x16] := C ? [x8] : [x16]` over the words `i` to `i + n - 1`. -/
def narrowSelect : Nat → Nat → List Instr
  | _, 0 => []
  | i, n + 1 => [ld .x3 .x16 (8 * i), ld .x4 .x8 (8 * i), .csel .x .x3 .x4 .x3, st .x3 .x16 (8 * i)] ++
      narrowSelect (i + 1) n

/-- One bit: `[x16] := 2 [x16] + C mod [x17]` over `k` words (`x7` zero), the
quotient's bit shifted into `x15`, and the dividend's next bit from `x14` into `C`. -/
def narrowBit (k : Nat) : List Instr :=
  narrowShift 0 k ++ ([.subs .x .x3 .x7 .x7] : List Instr) ++ narrowSub 0 k ++ narrowSelect 0 k ++
    ([.adcs .x .x15 .x15 .x15, .adds .x .x14 .x14 .x14] : List Instr)

/-- One word of the dividend, the one below `x13`: its 64 bits, and the
quotient's word in its place. `x6` counts the words. -/
def narrowWord (k : Nat) : Prog isa :=
  .seq (.block [.subImm .x .x13 .x13 8, ld .x14 .x13, movi .x15 0, movi .x9 64, .adds .x .x14 .x14 .x14])
    (.seq (countLoop .x9 (narrowBit k)) (.block [st .x15 .x13, .subImm .x .x6 .x6 1]))

/-- `[r] := [q] mod [d]` and `[q] := [q] / [d]`, as `Keys.divmod`, for a
divisor `[d]` with `2 [d] ≤ 2^(64 k)` and `k ≤ w`; `[t]` working space. Its
loops are counted by `w` and 64 alone. -/
def divNarrow (k iQ iR iD iT : Nat) : Prog isa :=
  .seq (zeroA iR) (.seq
    (.block (base iQ .x13 ++ ([.lsl .x .x3 .x12 3, .add .x .x13 .x13 .x3, mov .x6 .x12] : List Instr) ++
      base iR .x16 ++ base iD .x17 ++ base iT .x8))
    (.loop (narrowWord k) (.nonzero .x .x6)))

/-- The words of the remainder by `2 q`: `q` has at most 256 bits. -/
def reduceWords : Nat := 5

/-- X is in array 0 and 2q in array 2. Array 5 receives p, array 0 the quotient. -/
def reduceCandidate : Prog isa :=
  .seq (copyA 4 0) (.seq (divNarrow reduceWords 0 1 2 3) (reduceRemainder 5 4 1))

end VG.Impl.Dsa.AArch64.Generation
