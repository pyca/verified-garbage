import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoop
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFinish

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

/-- A final canonical homogeneous representative, including infinity. -/
theorem nafFinish_ok {K : WinCfg} {C : Curve} {base : Addr} {size e : Nat} {β : Nat → BitVec 8}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (· ∈ jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (hOne : K.one<C.p)
    (hone : toM C.p (2^(64*K.M.n)) K.one=1) (hBits : K.bits+5≤4096)
    {P : Point C} {s : State} (h : NafCore K C base size P β e s) :
    WP isa (Jacobian.jacFinish K) s fun t =>
      KeepRegs (tcombClob K.M.n) s t ∧ Unch base (jacLoopWrites K) s.mem t.mem ∧
      ModOkA K.M size C.p t.mem base ∧
      (∀ x ∈ [K.R.x,K.R.y,K.R.z], wordsVal t.mem base x K.M.n<C.p) ∧
      Rep C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y)
        (tmv C K.M.n base t K.R.z) (mul e P) := by
  have lay := jacFinishLayout hL hJ hBits
  have al : CombA (jacFinishCfg K).toComb := ⟨fun x hx => hAl.sl x (by
    apply hL.old_slots x
    simp only [combSlots,jacFinishCfg,TCombCfg.toComb,winSlots,winRo,winOther,rcbW,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind),hAl.mod⟩
  have pn := wordsVal_lt s.mem base K.M.mo K.M.n
  rw [h.field.mod.val] at pn
  have hl : ∀ x ∈ rcbR K.S K.R ⟨K.zero,K.zero,K.zero⟩, wordsVal s.mem base x K.M.n<C.p := by
    intro x hx
    apply h.field.lt x
    simp only [rcbR,nafLive,winRo,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  exact jacComb_finish_ok lay al hC hm hL.n hOne hone pn h.field.scr h.field.mod hl h.stable.zero h.point

end VG.Proof.Weierstrass.AArch64
