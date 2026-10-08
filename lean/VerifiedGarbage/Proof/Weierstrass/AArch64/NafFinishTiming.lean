import VerifiedGarbage.Proof.Weierstrass.AArch64.NafFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacFinishTiming

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

/-- The common final conversion drops the no-longer-used precomputation table. -/
theorem nafFinish_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (hOne : K.one<C.p)
    (hone : toM C.p (2^(64*K.M.n)) K.one=1) (hBits : K.bits+5≤4096)
    (hpn : C.p<2^(64*K.M.n))
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
      (Jacobian.jacFinish K)) {E : Nat → Fe C} (hz : E K.zero=0) :
    RelCT isa (FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E)
      (Jacobian.jacFinish K) (fun s t => ∃ E',FieldPair K.M base size C.p
        (·∈combSlots (jacFinishCfg K).toComb) (jacFinishLive (jacFinishCfg K)) E' s t) := by
  have lay := jacFinishLayout hL hJ hBits
  have al : CombA (jacFinishCfg K).toComb := ⟨fun x hx => hAl.sl x (by
    apply hL.old_slots x
    simp only [combSlots,jacFinishCfg,TCombCfg.toComb,winSlots,winRo,winOther,rcbW,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind),hAl.mod,fun _ _ h => nomatch (callOf_small (M := K.M) (Nat.le_of_eq hL.n)).symm.trans h⟩
  have sub : ∀ x∈jacFinishLive (jacFinishCfg K),x∈nafLive K := by
    intro x hx
    simp only [jacFinishLive,jacFinishCfg,TCombCfg.toComb,combRo,nafLive,winRo,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have sl : ∀ x∈jacFinishLive (jacFinishCfg K),x∈combSlots (jacFinishCfg K).toComb := by
    intro x hx
    simp only [jacFinishLive,combSlots,combRo,jacFinishCfg,TCombCfg.toComb,rcbW,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  exact (jacCombFinish_relCT lay al hC hm hL.n hOne hone hpn hct hz).mono
    (fun _ _ p => ⟨⟨p.left.scr,p.left.mod,sl,fun x hx => p.left.lt x (sub x hx),
      fun x hx => p.left.val x (sub x hx)⟩,
      ⟨p.right.scr,p.right.mod,sl,fun x hx => p.right.lt x (sub x hx),
      fun x hx => p.right.val x (sub x hx)⟩,p.sp⟩) (fun _ _ h => h)

end VG.Proof.Weierstrass.AArch64
