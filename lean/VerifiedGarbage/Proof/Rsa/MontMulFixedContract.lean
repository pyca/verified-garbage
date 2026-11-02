module

public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Fixed-index Montgomery products in the RSA working space

Not trusted: the contracts of internal functions (`Rust.Internal`), which only
verified code calls, that their proofs and their callers' compose.

Callable specializations of RSA's Montgomery multiplication
(`Proof/Rsa/MontContract.lean`'s `mulContract`) to fixed array indices: the product of
arrays `a` and `b`, written to array `o`. They use the existing layout and
integer relation of `Proof/Rsa/MontContract.lean`. Fixing the indices in the function's
identity lets a caller that multiplies the same arrays at many places share
one copy of the code without passing the indices, as the fixed-slot squares
of `Proof/Rsa/MontSquareContract.lean` do for squares.
-/

@[expose] public section

namespace VG.Proof.Rsa.MontMulFixed

open VG.Proof.Rsa.Mont

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

end VG.Proof.Rsa.MontMulFixed
