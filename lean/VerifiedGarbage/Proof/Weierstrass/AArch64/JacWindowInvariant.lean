module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLayout
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Jac
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem

/-! Invariants retained by the public five-bit Jacobian loop. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

def jacLive (K : WinCfg) : List Nat := winRo K ++
  [K.R.x,K.R.y,K.R.z,K.E.x,K.E.y,K.E.z,K.D.x,K.D.y,K.D.z] ++ jacTblSlots K

def jacLoopWrites (K : WinCfg) : List (Nat × Nat) :=
  (winOther K).map (·,8*K.M.n) ++ [(K.M.tmp,8*K.M.n)]

/-- An initialized environment can always be represented by the current
memory function, avoiding artificial relationships between temporary environments. -/
theorem Inv.to_tmv {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C} {s : State}
    (h : Inv M base size C.p Sl V E s) : Inv M base size C.p Sl V (tmv C M.n base s) s :=
  ⟨h.scr,h.mod,h.sl,h.lt,fun _ _ => rfl⟩

theorem Inv.point_tmv {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C} {s : State}
    (h : Inv M base size C.p Sl V E s) {p : Pt} {P : Point C}
    (hp : ∀ x ∈ [p.x,p.y,p.z], x ∈ V) (hJ : InvJ C (E p.x) (E p.y) (E p.z) P) :
    InvJ C (tmv C M.n base s p.x) (tmv C M.n base s p.y) (tmv C M.n base s p.z) P := by
  unfold tmv
  rw [h.val _ (hp _ (by simp)),h.val _ (hp _ (by simp)),h.val _ (hp _ (by simp))]
  exact hJ

end VG.Proof.Weierstrass.AArch64
