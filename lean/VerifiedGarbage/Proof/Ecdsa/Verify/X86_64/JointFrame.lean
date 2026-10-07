import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointInput
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFinal
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitLayout
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrep

/-! The joint multiplication preserves the fixed inputs of the final comparison. -/
namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)

def jointRanges (j : Joint.Cfg) : List (Nat×Nat) :=
  jointPrepRanges j++((jointInitWork j++jointWork j).map (·,8*j.K.M.n)++[(j.K.M.tmp,8*j.K.M.n)])

structure JointFrameLayout (c : Cfg) (j : Joint.Cfg) : Prop where
  fixed : FixedOk c (jointRanges j)
  k : ∀ w∈jointRanges j,c.sl K+8*c.n≤w.1 ∨ w.1+w.2≤c.sl K
  flag : ∀ w∈jointRanges j,c.sl FLAG+8≤w.1 ∨ w.1+w.2≤c.sl FLAG

theorem jointFrame_input {c : Cfg} {j : Joint.Cfg} (hc : CfgOk c)
    (hK : j.K=c.winCfg PX PY BP) (hF : JointFrameLayout c j)
    {s₀ s t : State} {base : Addr} {g : Reg → BitVec 64} (h : Mid c s₀ base g s)
    {Q A : Point c.C} {u v : Nat} {External : State → Prop}
    (ht : JointCore j c.C base size Q u v External A t)
    (hu : Unch base (jointRanges j) s.mem t.mem) : ProjectiveInput c s₀ base g t := by
  have rx := ht.field.lt j.K.R.x (jointLive_R j _ (by simp [jacCoords]))
  have rz := ht.field.lt j.K.R.z (jointLive_R j _ (by simp [jacCoords]))
  rw [hK] at rx rz
  refine ⟨ht.field.scr,h.fixed.unch hc.n10 h.scr.nowrap hF.fixed hu,
    (sv_unch hu hc.n10 h.scr.nowrap (by decide) hF.k).trans h.k,?_,rx,rz⟩
  refine (hu.word hF.flag ?_).trans h.flag
  have := sl_le c hc.n10 (i:=FLAG) (by decide)
  have := hc.n0
  have := h.scr.nowrap
  omega

end VG.Proof.Ecdsa.Verify.X86_64
