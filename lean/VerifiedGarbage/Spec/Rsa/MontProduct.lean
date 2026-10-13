module

public import VerifiedGarbage.Spec.Rsa.Mont

/-!
# Montgomery products with already resolved RSA workspace addresses

**Trusted.** A callable form of RSA's existing Montgomery product that
receives the operand and result addresses rather than their array indices.
It lets callers share a kernel without resolving the same three public
indices again inside it. The layout, arithmetic bounds and canonical result
are those of `Rsa/Mont.lean`. The result may alias either operand; it may
not overwrite the modulus. No new arithmetic or machine instruction is
specified here.
-/

@[expose] public section

namespace VG.Spec.Rsa.MontProduct
open VG.Spec.Rsa.Mont

/-- An address of a complete operand array in the existing workspace. -/
def OperandAddress (ws : Addr) (w : Nat) (p : Addr) : Prop :=
  ∃ j, Operand j ∧ p = ws + BitVec.ofNat 64 (arrAt w j)

/-- Public addresses represented as `usize`. They designate arrays inside
`ws`, not additional buffers with independent disjointness requirements. -/
def sig : Sig where
  params := [("ws", .slice true .u64 "ws_len"),
    ("out_address", .int .usize true), ("a_address", .int .usize true),
    ("b_address", .int .usize true)]

/-- The product has the same asymmetric input bound as `Mont.mulContract`:
only the second operand must be below the modulus. This also covers a
noncanonical first operand on a caller's invalid-input path. -/
def productContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws wsLen out a b m =>
      let w := wOf m ws
      let op := out.setWidth 64
      let ap := a.setWidth 64
      let bp := b.setWidth 64
      Layout m ws wsLen.toNat ∧
        OperandAddress ws w op ∧ OperandAddress ws w ap ∧ OperandAddress ws w bp ∧
        op ≠ ws + BitVec.ofNat 64 (arrAt w aM) ∧
        ((m.readW (ws + BitVec.ofNat 64 (arrAt w aM)) 64).toNat *
          (wordAt m ws minvWord).toNat + 1) % 2 ^ 64 = 0 ∧
        (m.read bp (8*w)).toNat < numAt m ws w aM)
    (post := fun ws wsLen out a b m m' _ =>
      let w := wOf m ws
      let M := numAt m ws w aM
      let op := out.setWidth 64
      let ap := a.setWidth 64
      let bp := b.setWidth 64
      (m'.read op (8*w)).toNat < M ∧
        (m'.read op (8*w)).toNat * 2 ^ (64*w) % M =
          (m.read ap (8*w)).toNat * (m.read bp (8*w)).toNat % M ∧
        ∀ o, Operand o → op = ws + BitVec.ofNat 64 (arrAt w o) →
          Keeps ws wsLen.toNat w o m m')
    (stack := stack)
    (leak := some fun ws _ _ _ _ m => [wOf m ws])

/-- A shared RSA product, with the same contract on every target. -/
def productApi : Api where
  module := "rsa"
  name := "vg_rsa_product_shared"
  sig := sig
  contracts := some fun A stack => productContract A stack
  summary := "Montgomery multiplication of two arrays in the RSA working space. \
    The public `usize` arguments give the addresses of the result and operands, each \
    the start of an operand array in `VG.Spec.Rsa.Mont.Layout`. Writes the result below \
    the modulus `m` (array 0), with its product by `2^(64 w)` congruent to the product \
    of the input arrays modulo `m`. The result may alias either operand, and the \
    operands may be the same array. The result cannot be array 0. Only the result \
    array and arrays 2 and 3 may change.\n\n\
    Contract: `VG.Spec.Rsa.MontProduct.productContract`. Constant time except for \
    the public workspace address, its length, the three array addresses and the \
    limb count `w`. The modulus, inverse and operand values remain secret."
  safety := ["Header word 6, `w`, must be in 2..2^31, and `ws_len` at least `32 + 8 * (w + 2)`.",
    "Header word `8 + j` must point to word `32 + j * (w + 2)` of `ws`, for every `j < 8`.",
    "Each address must designate the start of an array with index below 8 and different from 2 and 3.",
    "The output address must not designate array 0 (the modulus).",
    "Header word 7 must be `-m⁻¹ mod 2^64` for the odd modulus in array 0.",
    "The second operand must be below the modulus; the first may be any `w`-word value.",
    "Arrays 2 and 3 may contain secret intermediates on return; the caller must destroy them."]

end VG.Spec.Rsa.MontProduct
