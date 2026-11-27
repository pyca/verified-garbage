module

public import VerifiedGarbage.Impl.Dsa.AArch64.Checks

/-!
# g^x and g^q in one pass, for DSA's private-key checks on AArch64

Deriving and validating a private key both need `y = g^x mod p`, constant
time in the secret `x`, and the domain's `g^q mod p = 1`, over the public
`q`. `x` and `q` have the same length, so one right-to-left pass computes
both and shares the squarings: with `A = g^(8^i)` at digit `i` (three bits
of each exponent), bucket `d` of an exponent collects the product of the
`A` whose digit was `d`, and the power is the product of `bucket_d^d`.

The sixteen-entry table after the workspace's arrays holds both sets of
buckets: entries 0–7 for `x` (entry 0 for the digit 0, which nothing
reads), entries 9–15 for `q`'s digits 1–7.

* `x`'s digit is secret: its bucket is read by the scan of every entry
  (`Crt.select`), multiplied by `A`, and written back by `store`, which
  rewrites all of `x`'s buckets under a mask. Every digit, zero or not,
  makes the same reads, multiplication and writes.
* `q`'s digit is public: its bucket is read, multiplied and written
  directly, and a zero digit is skipped.

The exponents' bytes are taken three at a time from the end, eight digits
(fewer for the last one or two bytes), so every shift is by a constant.

The multiplications are among those `Mont` proves constant time (`MmUse`):
`T := T A`, `A := A²`, and in the final products `Y := Y T`, `X := X Y`
and `T := X · 1`.
-/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.SharedPower

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt
open VG.Impl.Bignum.Public hiding sI sBit sV
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout
open VG.Impl.Rsa.AArch64.WindowSelectVector (accs)

/-! ## The masked store -/

/-- One entry's 64 bytes at `x16` `:=` the accumulators' where the entry's
index (`v23`) is the digit (`v22`), and themselves elsewhere; then the next
entry. The addresses do not depend on the digit. -/
def storeRow : List Instr :=
  [.vop (.cmeq .d2 .v20 .v23 .v22)] ++
  (accs.zipIdx.flatMap fun (r, i) =>
    [.ldrq .v21 .x16 (16 * i), .vop (.bsel .bit .v21 r .v20), .strq .v21 .x16 (16 * i)]) ++
  [.add .x .x16 .x16 .x6, .vop (.add .d2 .v23 .v23 .v24)]

/-- `T_j := j = v ? [aT] : T_j` for the first eight entries, `v` in `sNib`,
64 bytes of each at a time: for a width of whole 64-byte tiles. -/
def store : Prog isa :=
  .seq (.block [ldh .x12 sW, .addImm .x .x6 .x12 2, .lsl .x .x6 .x6 3,
    .lsr .x .x13 .x12 3, ldh .x5 sNib, .vop (.dup .d2 .v22 .x5), movi .x2 1, .vop (.dup .d2 .v24 .x2),
    ldh .x17 (sArr aT)])
  (.loop
    (.seq (.block ([ldh .x16 (sArr aT), .sub .x .x16 .x17 .x16, ldh .x3 sTab, .add .x .x16 .x16 .x3,
        .vop (.movi0 .v23), movi .x14 8] ++ accs.zipIdx.map fun (r, i) => .ldrq r .x17 (16 * i)))
      (.seq (countLoop .x14 storeRow)
        (.block [.addImm .x .x17 .x17 64, .subImm .x .x13 .x13 1]))) (.nonzero .x .x13))

/-- `T_v := [aT]` for the public `v` in `sNib`, directly. -/
def put : Prog isa :=
  .seq (.block (PublicPower.selectHead ++ ([mov .x3 .x16, mov .x16 .x17, mov .x17 .x3] : List Instr))) copyWords

/-! ## The digits -/

/-- The last byte not yet taken of each exponent (`sI` counts them), into
`x5` and `x6`; `x4` the bytes then left, `x1` and `x2` at the bytes read. -/
def groupHead : List Instr :=
  [ldh .x4 sI, .subImm .x .x4 .x4 1, ldh .x1 sExp, .add .x .x1 .x1 .x4, ldh .x2 sSrc, .add .x .x2 .x2 .x4,
    .ldrb .x5 .x1 0, .ldrb .x6 .x2 0, movi .x3 3]

/-- The next byte down of each, `sh` bits up, for `cnt` digits in all. -/
def groupMore (sh cnt : Nat) : List Instr :=
  [.subImm .x .x4 .x4 1, .subImm .x .x1 .x1 1, .subImm .x .x2 .x2 1, .ldrb .x7 .x1 0, .lsl .x .x7 .x7 sh,
    .logic .orr .x .x5 .x5 .x7, .ldrb .x7 .x2 0, .lsl .x .x7 .x7 sh, .logic .orr .x .x6 .x6 .x7, movi .x3 cnt]

def groupEnd : List Instr := [sth .x4 sI, sth .x5 sV, sth .x6 sMaskX, sth .x3 sBit]

/-- Up to three bytes of each exponent, from the end: `x`'s into `sV`, `q`'s
into `sMaskX`, and their digits' count (8, or 6 or 3 for the last two bytes
or one) into `sBit`. -/
def group : Prog isa :=
  .seq (.block groupHead)
    (.seq (.ite (.zero .x .x4) (.block [])
        (.seq (.block (groupMore 8 6)) (.ite (.zero .x .x4) (.block []) (.block (groupMore 16 8)))))
      (.block groupEnd))

/-- `x`'s digit into `sNib`. -/
def secretDigit : List Instr := [ldh .x3 sV, movi .x4 7, .logic .and .x .x3 .x3 .x4, sth .x3 sNib]

/-- `q`'s digit into `x3`. -/
def publicDigit : List Instr := [ldh .x3 sMaskX, movi .x4 7, .logic .and .x .x3 .x3 .x4]

/-- The next digits, and their count down into `x3`. -/
def digitEnd : List Instr :=
  [ldh .x3 sV, .lsr .x .x3 .x3 3, sth .x3 sV, ldh .x3 sMaskX, .lsr .x .x3 .x3 3, sth .x3 sMaskX,
    ldh .x3 sBit, .subImm .x .x3 .x3 1, sth .x3 sBit]

/-- `q`'s bucket for its digit in `x3`, not zero: entry `8 + x3`. -/
def publicBucket (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block [.addImm .x .x3 .x3 8, sth .x3 sNib], PublicPower.select, mul aT aT aXc, put]

/-- One digit of each exponent: its bucket `*= A`, then `A := A⁸`. -/
def digit (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block secretDigit, Crt.select, mul aT aT aXc, store,
  .block publicDigit, .ite (.zero .x .x3) (.block []) (publicBucket mul),
  mul aXc aXc aXc, mul aXc aXc aXc, mul aXc aXc aXc,
  .block digitEnd]

/-- The table's base, and its sixteen entries `:= Y`. -/
def tableInit : List (Prog isa) := [
  .block [ldh .x3 (sArr aOne), ldh .x4 sW, .addImm .x .x4 .x4 2, .lsl .x .x4 .x4 3, .add .x .x3 .x3 .x4,
    sth .x3 sTab, sth .x3 sEnt, movi .x3 16, sth .x3 sBit],
  .loop (seqs (Crt.toEnt aY ++ [Crt.nextEnt, .block [ldh .x3 sBit, .subImm .x .x3 .x3 1, sth .x3 sBit]]))
    (.nonzero .x .x3)]

/-- The exponents' pointers and their length: `x`'s from the call's second
operand, `q` the domain's. -/
def expInit : List Instr :=
  [ldh .x5 sLink, Crt.ldw .x3 .x5 arg2, sth .x3 sExp, .ldr .x .x3 .x5 Field.q.offset, sth .x3 sSrc,
    Crt.ldw .x3 .x5 arg2Len, sth .x3 sI]

/-- Every digit of both exponents, least significant first. -/
def digits (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .loop (seqs [group, .loop (digit mul) (.nonzero .x .x3), .block [ldh .x3 sI]]) (.nonzero .x .x3)

/-! ## The products -/

def pick (off d : Nat) : Prog isa := .seq (.block [movi .x3 (off + d), sth .x3 sNib]) PublicPower.select

/-- `T := ∏ T_(off + d)^d` for `d` from 1 to 7, out of Montgomery form:
with `Y` the product of the buckets from 7 down to each `d` in turn, `X` is
the product of those products, in which bucket `d` appears `d` times. -/
def combine (mul : Nat → Nat → Nat → Prog isa) (off : Nat) : Prog isa := seqs ([pick off 7] ++
  Crt.copyArr aY aT ++ Crt.copyArr aX aT ++ [
  .block [movi .x3 6, sth .x3 sBit],
  .loop (seqs [.block [ldh .x3 sBit, .addImm .x .x3 .x3 off, sth .x3 sNib], PublicPower.select,
    mul aY aY aT, mul aX aX aY, .block [ldh .x3 sBit, .subImm .x .x3 .x3 1, sth .x3 sBit]]) (.nonzero .x .x3),
  mul aT aX aOne])

/-- The mask of `g^q = 1`, `g^q` in `aT`, into `sMaskX`. -/
def orderCheck : Prog isa := seqs (Crt.copyArr aX aT ++
  [Checks.oneScan, .block (Checks.zeroMask .x15 ++ ([sth .x3 sMaskX] : List Instr))])

/-- `Y := g^x`, and the mask of `g^q = 1` into `sMaskX`, for `g` and `x`
the call's operands and the domain's `q`. -/
def power (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs ([
  Arithmetic.constants mul, Arithmetic.load aX arg argLen, Arithmetic.encodePower mul] ++ tableInit ++ [
  .block expInit, digits mul,
  combine mul 8, orderCheck,
  combine mul 0] ++ Crt.copyArr aY aT)

/-- `output := base^exponent mod p`, and `g^q = 1` into the acceptance
mask: `exponent` is secret, of `q`'s length. -/
def pow (mul : Nat → Nat → Nat → Prog isa) (base exponent output : Operand) : Prog isa :=
  seqs ([.block (Core.operand arg argLen base ++ Core.operand arg2 arg2Len exponent ++
    Core.operand result resultLen output ++ Core.enter pWorkspace), power mul] ++ Core.finish ++
    [.block (([.ldr .x .x3 .x0 (pWorkspace + 8 * sMaskX)] : List Instr) ++ Checks.accumulate)])

end VG.Impl.Dsa.AArch64.SharedPower
