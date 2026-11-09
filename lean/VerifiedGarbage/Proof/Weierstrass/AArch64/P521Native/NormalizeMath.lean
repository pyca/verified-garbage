module

public import VerifiedGarbage.Proof.Weierstrass.WindowJA
public import VerifiedGarbage.Proof.Weierstrass.JacAdd
import VerifiedGarbage.Proof.Framework.Omega

/-! Prefix products and affine back-substitution for the sixteen-entry table. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG.Proof.Weierstrass Spec.Weierstrass

/-- Products are indexed by the count of already included table rows. -/
def normalizeProduct {F : Type _} [Lean.Grind.CommRing F] (Z : Nat → F) : Nat → F
  | 0 => 1
  | n+1 => normalizeProduct Z n*Z n

theorem normalize_product_nonzero {C : Curve} (law : Law C) (Z : Nat → Fe C)
    (nonzero : ∀i,i<16 → Z i≠0) : ∀n,n≤16 → normalizeProduct Z n≠0
  | 0,_ => law.one_ne_zero
  | n+1,hn => law.mul_ne_zero (normalize_product_nonzero law Z nonzero n (by omega_arith)) (nonzero n (by omega_arith))

theorem normalize_back_step {C : Curve} (law : Law C) (Z : Nat → Fe C)
    (nonzero : ∀i,i<16 → Z i≠0) {n : Nat} (hn : n<16) :
    normalizeProduct Z (n+1)^(C.p-2)*normalizeProduct Z n=Z n^(C.p-2) ∧
      normalizeProduct Z (n+1)^(C.p-2)*Z n=normalizeProduct Z n^(C.p-2) :=
  trick_step law (normalize_product_nonzero law Z nonzero n (by omega_arith)) (nonzero n hn)

/-- The exact square/cube coordinate scaling used by normalization yields an affine table row. -/
theorem normalize_affine {C : Curve} (law : Law C) {X Y Z : Fe C} {Q : Point C}
    (point : InvJ C X Y Z Q) (nonzero : Z≠0) :
    RepA C (X*(Z^(C.p-2)*Z^(C.p-2))) (Y*(Z^(C.p-2)*Z^(C.p-2)*Z^(C.p-2))) 1 Q := by
  have inverse := law.fermat nonzero
  cases Q with
  | infinity =>
    exact False.elim (nonzero ((point.z_zero_iff law).mpr rfl))
  | affine x y =>
    obtain ⟨hx,hy⟩ := point.affine_coords law
    have ox : X*(Z^(C.p-2)*Z^(C.p-2))=x := by rw [hx]; grind
    have oy : Y*(Z^(C.p-2)*Z^(C.p-2)*Z^(C.p-2))=y := by rw [hy]; grind
    rw [ox,oy]
    exact ⟨⟨law.one_ne_zero,by grind,by grind⟩,Or.inl rfl⟩

end VG.Proof.Weierstrass.AArch64.P521Native
