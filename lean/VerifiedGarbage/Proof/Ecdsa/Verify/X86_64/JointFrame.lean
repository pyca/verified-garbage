module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFinal
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitLayout
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrep

/-! The joint multiplication preserves the fixed inputs of the final comparison. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)

def jointRanges (j : Joint.Cfg) : List (Nat×Nat) :=
  jointPrepRanges j++((jointInitWork j++jointWork j).map (·,8*j.K.M.n)++[(j.K.M.tmp,8*j.K.M.n)])

/-- The ranges `W` of the working space, which a joint multiplication writes, miss the fixed inputs of
the final comparison. -/
structure FrameLayout (c : Cfg) (W : List (Nat×Nat)) : Prop where
  fixed : FixedOk c W
  k : ∀ w∈W,c.sl K+8*c.n≤w.1 ∨ w.1+w.2≤c.sl K
  flag : ∀ w∈W,c.sl FLAG+8≤w.1 ∨ w.1+w.2≤c.sl FLAG

abbrev JointFrameLayout (c : Cfg) (j : Joint.Cfg) : Prop := FrameLayout c (jointRanges j)

theorem frame_input {c : Cfg} {j : Joint.Cfg} (hc : BaseCfgOk c)
    (hK : j.K=c.winCfg PX PY BP) {W : List (Nat×Nat)} (hF : FrameLayout c W)
    {s₀ s t : State} {base : Addr} {g : Reg → BitVec 64} (h : Mid c s₀ base g s)
    {Q A : Point c.C} {u v : Nat} {External : State → Prop}
    (ht : JointCore j c.C base size Q u v External A t)
    (hu : Unch base W s.mem t.mem) : ProjectiveInput c s₀ base g t := by
  have rx := ht.field.lt j.K.R.x (jointLive_R j _ (by simp [jacCoords]))
  have rz := ht.field.lt j.K.R.z (jointLive_R j _ (by simp [jacCoords]))
  rw [hK] at rx rz
  refine ⟨ht.field.scr,h.fixed.unch hc.n10 h.scr.nowrap hF.fixed hu,
    (sv_unch hu hc.n10 h.scr.nowrap (by decide) hF.k).trans h.k,?_,rx,rz⟩
  refine (hu.word hF.flag ?_).trans h.flag
  have := sl_le c hc.n10 (i:=FLAG) (by decide)
  have := hc.n0
  have := h.scr.nowrap
  omega_arith

theorem jointFrame_input {c : Cfg} {j : Joint.Cfg} (hc : BaseCfgOk c)
    (hK : j.K=c.winCfg PX PY BP) (hF : JointFrameLayout c j)
    {s₀ s t : State} {base : Addr} {g : Reg → BitVec 64} (h : Mid c s₀ base g s)
    {Q A : Point c.C} {u v : Nat} {External : State → Prop}
    (ht : JointCore j c.C base size Q u v External A t)
    (hu : Unch base (jointRanges j) s.mem t.mem) : ProjectiveInput c s₀ base g t :=
  frame_input hc hK hF h ht hu

end VG.Proof.Ecdsa.Verify.X86_64
