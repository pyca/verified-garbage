import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFinish

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

/-- A final canonical homogeneous representative, including infinity. -/
theorem jointFinish_ok {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v : Nat}
    {External : State → Prop}
    (hL : JacWinLay c.K size) (hJ : c.K.J=52) (hAl : Aligned c.K.M (· ∈ jacWinSlots c.K))
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hC : Law C) (hOne : c.K.one<C.p)
    (hone : toM C.p (2^(64*c.K.M.n)) c.K.one=1) (hBits : c.K.bits+5≤4096)
    {P A : Point C} {s : State} (h : JointCore c C base size P u v External A s) :
    WP isa (Jacobian.jacFinish c.K) s fun t =>
      KeepRegs (tcombClob c.K.M.n) s t ∧ Unch base (jacLoopWrites c.K) s.mem t.mem ∧
      ModOkA c.K.M size C.p t.mem base ∧
      (∀ x ∈ [c.K.R.x,c.K.R.y,c.K.R.z], wordsVal t.mem base x c.K.M.n<C.p) ∧
      Rep C (tmv C c.K.M.n base t c.K.R.x) (tmv C c.K.M.n base t c.K.R.y)
        (tmv C c.K.M.n base t c.K.R.z) A := by
  have lay := jacFinishLayout hL hJ hBits
  have al : CombA (jacFinishCfg c.K).toComb := ⟨fun x hx => hAl.sl x (by
    apply hL.old_slots x
    simp only [combSlots,jacFinishCfg,TCombCfg.toComb,winSlots,winRo,winOther,rcbW,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind),hAl.mod,fun _ _ h => nomatch (callOf_small (M := c.K.M) (Nat.le_of_eq hL.n)).symm.trans h⟩
  have pn := wordsVal_lt s.mem base c.K.M.mo c.K.M.n
  rw [h.field.mod.val] at pn
  have hl : ∀ x ∈ rcbR c.K.S c.K.R ⟨c.K.zero,c.K.zero,c.K.zero⟩, wordsVal s.mem base x c.K.M.n<C.p := by
    intro x hx
    apply h.field.lt x
    apply List.mem_append_left
    simp only [rcbR,nafLive,winRo,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  exact jacComb_finish_ok lay al hC hm hL.n hOne hone pn h.field.scr h.field.mod hl h.stable.peer.zero h.point

end VG.Proof.Weierstrass.AArch64
