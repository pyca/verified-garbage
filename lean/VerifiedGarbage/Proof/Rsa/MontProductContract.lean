module

public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Montgomery products with already resolved RSA workspace addresses

Not trusted: the contracts of internal functions (`Rust.Internal`), which only
verified code calls, that their proofs and their callers' compose.

A callable form of RSA's existing Montgomery product that
receives the operand and result addresses rather than their array indices.
It lets callers share a kernel without resolving the same three public
indices again inside it. The layout, arithmetic bounds and canonical result
are those of `Proof/Rsa/MontContract.lean`. The result may alias either operand; it may
not overwrite the modulus. No new arithmetic or machine instruction is
specified here.
-/

@[expose] public section

namespace VG.Proof.Rsa.MontProduct
open VG.Proof.Rsa.Mont

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

end VG.Proof.Rsa.MontProduct
