module

public import VerifiedGarbage.Proof.Ed25519.Point64Contract
public import VerifiedGarbage.Proof.Ed25519.AArch64.Points
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ed25519.AArch64.Field
public import VerifiedGarbage.Spec.Ed25519

/-!
# Ed25519's point functions on AArch64: the affine addition's value

Untrusted: everything here is checked by Lean. The affine addition's program
computes `pointAdd` of an entry with `Z = 1` (`mixedResult_eq`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Point64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64

/-! ## The programs' values -/

/-- What `addAffineOps` computes, from the point's coordinates and the cached entry's. -/
def mixedResult (x y z t q₀ q₁ q₂ : Spec.X25519.Fe) : Spec.Ed25519.Point :=
  let a := (y - x) * q₀
  let b := (y + x) * q₁
  let c := t * q₂
  let dd := z + z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem mixedResult_eq (p q : Spec.Ed25519.Point) (hz : q.Z = 1) :
    mixedResult p.X p.Y p.Z p.T (q.Y - q.X) (q.Y + q.X) (q.T * 2 * Spec.Ed25519.d) =
      Spec.Ed25519.pointAdd p q := by
  simp only [mixedResult, Spec.Ed25519.pointAdd, hz]
  congr 1 <;> grind

end VG.Proof.Ed25519.AArch64.Point64
