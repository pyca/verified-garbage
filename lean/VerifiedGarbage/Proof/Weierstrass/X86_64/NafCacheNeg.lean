module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCachePoint
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Weierstrass.JacAdd

/-! Negating a selected point leaves its cached powers of Z unchanged. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

def CachedPoint (n : Nat) (C : Curve) (E : Nat → Fe C) (p : Pt) (dst : Nat) (P : Point C) : Prop :=
  InvJ C (E p.x) (E p.y) (E p.z) P ∧ E dst=E p.z*E p.z ∧ E (dst+8*n)=E dst*E p.z

theorem CachedPoint.to_tmv {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv M base size C.p Sl V E s) {p : Pt} {dst : Nat} {P : Point C}
    (hV : ∀ x∈cachedSlots M.n p dst,x∈V) (hP : CachedPoint M.n C E p dst P) :
    CachedPoint M.n C (tmv C M.n base s) p dst P := by
  unfold CachedPoint tmv
  rw [hI.val _ (hV _ (by simp [cachedSlots,jacCoords])),
    hI.val _ (hV _ (by simp [cachedSlots,jacCoords])),
    hI.val _ (hV _ (by simp [cachedSlots,jacCoords])),
    hI.val _ (hV _ (by simp [cachedSlots])),hI.val _ (hV _ (by simp [cachedSlots]))]
  exact hP

end VG.Proof.Weierstrass.X86_64
