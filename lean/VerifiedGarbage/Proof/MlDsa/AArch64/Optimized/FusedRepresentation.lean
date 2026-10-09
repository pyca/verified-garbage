import VerifiedGarbage.Spec.MlDsa.FusedInverse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotField

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem positiveReduced_iff {m : Mem} {p : Addr} :
    PositiveReduced m p ↔ PosPolyIs m p (polyAt m p) :=
  ⟨fun h => ⟨h,rfl⟩,fun h => h.bound⟩

theorem dotNTT_eq_dotPoly (f g : Nat → Poly) (count : Nat) :
    dotNTT f g count=dotPoly f g count := rfl

/-- The inverse cancels the internal Montgomery factor for a whole matrix row. -/
theorem inverse_dotNTT (f g : Nat → Poly) (count : Nat) :
    montgomeryNttInv (Representation.encode true (dotPoly f g count))=
      nttInv (dotNTT f g count) :=
  Representation.inverse_encode true _

end VG.Proof.MlDsa.AArch64.Optimized
