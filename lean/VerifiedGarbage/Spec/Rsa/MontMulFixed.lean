module

public import VerifiedGarbage.Spec.Rsa.Mont

/-!
# Fixed-index Montgomery products in the RSA working space

**Trusted.** Callable specializations of RSA's Montgomery multiplication
(`Rsa/Mont.lean`'s `mulContract`) to fixed array indices: the product of
arrays `a` and `b`, written to array `o`. They use the existing layout and
integer relation of `Rsa/Mont.lean`. Fixing the indices in the function's
identity lets a caller that multiplies the same arrays at many places share
one copy of the code without passing the indices, as the fixed-slot squares
of `Rsa/MontSquare.lean` do for squares.
-/

@[expose] public section

namespace VG.Spec.Rsa.MontMulFixed

open VG.Spec.Rsa.Mont

/-- The indices of a product: array `o` is set to the product of arrays `a`
and `b`. -/
structure Indices where
  o : Nat
  a : Nat
  b : Nat

/-- The working space, in 64-bit words; its address and length are public. -/
def sig : Sig where
  params := [("ws", .slice true .u64 "ws_len")]

/-- `mulContract` with the fixed indices `ix`, which must be operands (below
8, and not the function's own arrays 2 and 3). For `-m⁻¹ mod 2⁶⁴` in the
header (the inverse of the low word of `m`, negated: so `m` is odd) and the
number at `b` below `m`: the number at `o` is below `m` and its product with
`R = 2^(64 w)` is congruent to the product of the numbers at `a` and `b`
modulo `m`. Only array `o` and arrays 2 and 3 may change. The width is
public; all arithmetic values, including the modulus, remain secret. -/
def mulContract {I : ISA} (ix : Indices) (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws wsLen m =>
      let w := wOf m ws
      Operand ix.o ∧ Operand ix.a ∧ Operand ix.b ∧ Layout m ws wsLen.toNat ∧
        ((m.readW (ws + BitVec.ofNat 64 (arrAt w aM)) 64).toNat *
          (wordAt m ws minvWord).toNat + 1) % 2 ^ 64 = 0 ∧
        numAt m ws w ix.b < numAt m ws w aM)
    (post := fun ws wsLen m m' _ =>
      let w := wOf m ws
      let M := numAt m ws w aM
      numAt m' ws w ix.o < M ∧
        numAt m' ws w ix.o * 2 ^ (64 * w) % M = numAt m ws w ix.a * numAt m ws w ix.b % M ∧
        Keeps ws wsLen.toNat w ix.o m m')
    (stack := stack)
    (leak := some fun ws _ m => [wOf m ws])

/-- A fixed-index product, with the same meaning on every target. -/
def mulApi (ix : Indices) : Api where
  module := "rsa"
  name := s!"vg_rsa_mul_{ix.o}_{ix.a}_{ix.b}"
  sig := sig
  contracts := some fun A stack => mulContract ix A stack
  summary := s!"Montgomery multiplication in the working space of the RSA functions, for \
    fixed arrays: writes to array {ix.o} the number below the modulus `m` (array 0) \
    congruent to `a b 2^(-64 w)` modulo `m`, for the numbers a in array {ix.a} and b in \
    array {ix.b}. The working space has a header of 32 words and 8 arrays of `w + 2` words, \
    as `vg_rsa_mont_mul` takes it (`VG.Spec.Rsa.Mont.Layout`). Every byte of `ws` but those \
    of arrays 2 and 3 (the function's own) and of array {ix.o} keeps its value.\n\n\
    Contract: `VG.Spec.Rsa.MontMulFixed.mulContract`. Constant time except for the \
    public working-space address, its length, and the limb count `w`; the modulus and \
    the numbers remain secret."
  safety := ["Header word 6 of `ws`, `w`, must be in 2..2^31, and `ws_len` at least \
      `32 + 8 * (w + 2)`.",
    "Header word `8 + j` must point to word `32 + j * (w + 2)` of `ws`, for every `j < 8`.",
    "Header word 7 must be `-m⁻¹ mod 2^64` for the odd modulus `m` in array 0.",
    s!"The number in array {ix.b} must be below `m`.",
    "Arrays 2 and 3 are unspecified on return and may hold intermediate values, which the \
      caller must destroy if they are secret."]

end VG.Spec.Rsa.MontMulFixed
