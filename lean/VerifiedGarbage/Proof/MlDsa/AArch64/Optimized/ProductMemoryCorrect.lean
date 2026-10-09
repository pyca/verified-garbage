import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemoryField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRawMemoryField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemoryCorrect
import VerifiedGarbage.Spec.MlDsa.FusedInverse

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Centered Montgomery products and the folded inverse scale cancel exactly,
leaving the ordinary polynomial product required by callers. -/
theorem productRawInverse_field {m : Mem} {p a b : Addr} {f g : Poly}
    (hf : PosPolyIs m a f) (hg : PosPolyIs m b g) :
    RawPolyIs (rawFinalPassMem (productPassMem m p a b 8) p 8) p
      (nttInv (multiplyNTT f g)) := by
  have h := rawFinalPass_field (productPass_field (p := p) hf hg)
  rw [InverseTraversal.traversal_montgomery] at h
  change RawPolyIs _ _ (Representation.inverse true (Representation.product true f g)) at h
  simpa only [Representation.inverse_product] using h

/-- The separately retained canonical fused helper has the same ordinary
field result, with its stronger canonical output promise. -/
theorem productInverse_field {m : Mem} {p a b : Addr} {f g : Poly} {qv : BitVec 128}
    (hf : PosPolyIs m a f) (hg : PosPolyIs m b g) (hq : ∀ e<4, vword qv e=8380417#32) :
    PolyIs (finalPassMem (productPassMem m p a b 8) p qv 8) p
      (nttInv (multiplyNTT f g)) := by
  have h := finalPass_field (productPass_field (p := p) hf hg) hq
  rw [InverseTraversal.traversal_montgomery] at h
  change PolyIs _ _ (Representation.inverse true (Representation.product true f g)) at h
  simpa only [Representation.inverse_product] using h

theorem positiveReduced_is {m : Mem} {p : Addr} (h : PositiveReduced m p) :
    PosPolyIs m p (polyAt m p) := ⟨h,rfl⟩

/-- Direct instantiation from the shared raw helper's input predicates. -/
theorem productRawInverse_contract_field {m : Mem} {p a b : Addr}
    (ha : PositiveReduced m a) (hb : PositiveReduced m b) :
    RawPolyIs (rawFinalPassMem (productPassMem m p a b 8) p 8) p
      (nttInv (multiplyNTT (polyAt m a) (polyAt m b))) :=
  productRawInverse_field (positiveReduced_is ha) (positiveReduced_is hb)

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
