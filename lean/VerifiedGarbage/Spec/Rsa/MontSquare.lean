module

public import VerifiedGarbage.Spec.Rsa.Mont

/-!
# Fixed-slot Montgomery squares in the RSA working space

**Trusted.** Two callable specializations of RSA's Montgomery arithmetic:
the square of array 4 (R² during setup), and of array 6 (the exponentiation
accumulator). These use the existing layout and integer relation from
`Rsa/Mont.lean`. Fixing the array in the function's identity lets callers
share the code without passing operand indices at each square.
-/

@[expose] public section

namespace VG.Spec.Rsa.MontSquare

open VG.Spec.Rsa.Mont

/-- The two in-place squares shared by RSA setup and exponentiation. -/
inductive Slot where
  | r2
  | y

/-- Array indices in the existing RSA working-space layout. -/
def Slot.index : Slot → Nat
  | .r2 => 4
  | .y => 6

/-- The working space, in 64-bit words; its address and length are public. -/
def sig : Sig where
  params := [("ws", .slice true .u64 "ws_len")]

/-- Square the designated array in place modulo array 0, in Montgomery
form. Only that array and the existing accumulator/temporary may change.
The width is public; all arithmetic values, including the modulus, remain
secret. Bounds and the final canonical result match `Mont.mulContract`. -/
def squareContract {I : ISA} (slot : Slot) (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws wsLen m =>
      let w := wOf m ws
      Layout m ws wsLen.toNat ∧
        ((m.readW (ws + BitVec.ofNat 64 (arrAt w aM)) 64).toNat *
          (wordAt m ws minvWord).toNat + 1) % 2 ^ 64 = 0 ∧
        numAt m ws w slot.index < numAt m ws w aM)
    (post := fun ws wsLen m m' _ =>
      let w := wOf m ws
      let M := numAt m ws w aM
      numAt m' ws w slot.index < M ∧
        numAt m' ws w slot.index * 2 ^ (64 * w) % M =
          numAt m ws w slot.index * numAt m ws w slot.index % M ∧
        Keeps ws wsLen.toNat w slot.index m m')
    (stack := stack)
    (leak := some fun ws _ m => [wOf m ws])

/-- A fixed-slot square, with the same meaning on every target. -/
def squareApi (slot : Slot) : Api where
  module := "rsa"
  name := s!"vg_rsa_square_{slot.index}_{slot.index}"
  sig := sig
  contracts := some fun A stack => squareContract slot A stack
  summary := s!"Squares array {slot.index} in the RSA working space, in place: the result is \
    below the modulus `m` (array 0), and its product with `2^(64 w)` is congruent modulo \
    `m` to the square of the original array. The working space has a header of 32 words \
    and 8 arrays of `w + 2` words, as in `VG.Spec.Rsa.Mont.Layout`. Only array \
    {slot.index} and arrays 2 and 3 (the accumulator and temporary) may change.\n\n\
    Contract: `VG.Spec.Rsa.MontSquare.squareContract`. Constant time except for the \
    public working-space address, its length, and the limb count `w`; the modulus \
    and the number being squared remain secret."
  safety := ["Header word 6, `w`, must be in 2..2^31, and `ws_len` at least `32 + 8 * (w + 2)`.",
    "Header word `8 + j` must point to word `32 + j * (w + 2)` of `ws`, for every `j < 8`.",
    "Header word 7 must be `-m⁻¹ mod 2^64` for the odd modulus `m` in array 0.",
    s!"The number in array {slot.index} must be below `m`.",
    "Arrays 2 and 3 may contain secret intermediates on return; the caller must destroy them."]

end VG.Spec.Rsa.MontSquare
