import VerifiedGarbage.Proof.MlDsa.Arith.Mem

/-! Internal storage relations for lazy arithmetic. The canonical public
`Reduced` and `PolyIs` predicates retain their original meanings. -/
namespace VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.MlDsa

/-- Unsigned representatives below three times the modulus. -/
structure PosPolyIs (m : Mem) (p : Addr) (f : Poly) : Prop where
  bound : ∀ i < n, (coeffAt m p i).toNat < 3 * q
  value : polyAt m p = f

/-- Signed representatives, with explicit inclusive integer bounds.
`polyAt` cannot express this relation: it interprets words as unsigned. -/
structure SignedPolyIs (m : Mem) (p : Addr) (f : Poly) (lo hi : Int) : Prop where
  bound : ∀ i < n, lo ≤ (coeffAt m p i).toInt ∧ (coeffAt m p i).toInt ≤ hi
  value : ∀ i < n, ofInt (coeffAt m p i).toInt = f[i]!

theorem PosPolyIs.of_canonical {m : Mem} {p : Addr} {f : Poly} (h : PolyIs m p f) :
    PosPolyIs m p f := by
  refine ⟨fun i hi => ?_, h.2⟩
  have hq : 0 < q := by decide
  have := h.1 i hi
  omega

theorem PosPolyIs.canonical {m : Mem} {p : Addr} {f : Poly}
    (h : PosPolyIs m p f) (hr : Reduced m p) : PolyIs m p f := ⟨hr, h.value⟩

theorem SignedPolyIs.mono {m : Mem} {p : Addr} {f : Poly} {lo hi lo' hi' : Int}
    (h : SignedPolyIs m p f lo hi) (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    SignedPolyIs m p f lo' hi' :=
  ⟨fun i hn => by have := h.bound i hn; omega, h.value⟩

theorem SignedPolyIs.congr {m m' : Mem} {p p' : Addr} {f : Poly} {lo hi : Int}
    (h : SignedPolyIs m p f lo hi)
    (he : ∀ i < n, coeffAt m' p' i = coeffAt m p i) : SignedPolyIs m' p' f lo hi := by
  constructor
  · intro i hn
    rw [he i hn]
    exact h.bound i hn
  · intro i hn
    rw [he i hn]
    exact h.value i hn

end VG.Proof.MlDsa.AArch64.Optimized
