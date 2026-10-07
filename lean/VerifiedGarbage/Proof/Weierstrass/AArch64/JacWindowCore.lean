import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFive
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowNeg

/-! The public Jacobian loop's arithmetic steps. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- The five doubles preserve all fixed data and multiply the accumulator by32. -/
theorem jacFiveCore_ok {K : WinCfg} {C : Curve} {base : Addr} {size k e : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (· ∈ jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {P : Point C} (hP : onCurve C P=true) {s : State} (h : JacCore K C base size P k e s) :
    WP isa (Jacobian.jacDoubles K 5) s fun t =>
      ProgKeep K.M base (winOther K) s t ∧ JacCore K C base size P k (32*e) t := by
  have old := hL.toWinLay hJ
  have hs : ∀ x ∈ rcbW K.S K.D ++ rcbW K.S K.R ++ rcbR K.S K.R K.D, x ∈ jacWinSlots K := by
    intro x hx
    apply hL.old_slots x
    simp only [rcbW,rcbR,winSlots,winRo,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  refine WP.mono (jacFive_ok hL.lay hAl hm hC ha hL.n
    (old.rcbApart_D (Or.inl rfl)) hL.rcbApart_DR hs (jacLive_read K) h.field hP h.point)
    fun t ⟨E,hk,hi,hp⟩ => ?_
  have hk' : ProgKeep K.M base (winOther K) s t := hk.mono (by
    intro x hx
    simp only [rcbW,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind)
  exact ⟨hk',h.next hL hJ hk' hi hp⟩

/-- Register-only instructions retain the arithmetic invariant. -/
theorem JacCore.of_keeps {K : WinCfg} {C : Curve} {base : Addr} {size k e : Nat}
    {P : Point C} {s t : State} {rs : List Reg} (h : JacCore K C base size P k e s)
    (hk : Keeps rs s t) (h0 : Reg.x0 ∉ rs) : JacCore K C base size P k e t := by
  have hm : tmv C K.M.n base t = tmv C K.M.n base s := by
    funext x; unfold tmv; rw [hk.mem]
  refine ⟨?_,?_,?_⟩
  · rw [hm]; exact h.field.of_keeps hk h0
  · refine ⟨?_,fun a ha h16 => ?_,fun i hi => ?_⟩
    · rw [hk.mem]; exact h.stable.zero
    · rw [hm]; exact h.stable.table a ha h16
    · rw [hk.mem]; exact h.stable.bits i hi
  · rw [hm]; exact h.point

/-- A point disjoint from the modified slots retains its Jacobian meaning. -/
theorem point_of_unch {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : JacWinLay K size) {p : Pt} {P : Point C} {s t : State} {W : List Nat}
    (hn : base.toNat+size ≤ 2^64) (hk : ProgKeep K.M base W s t)
    (hp : ∀ x ∈ [p.x,p.y,p.z], x ∈ jacWinSlots K)
    (hw : ∀ x ∈ [p.x,p.y,p.z], ∀ w ∈ W, x+8*K.M.n ≤ w ∨ w+8*K.M.n ≤ x)
    (h : InvJ C (tmv C K.M.n base s p.x) (tmv C K.M.n base s p.y) (tmv C K.M.n base s p.z) P) :
    InvJ C (tmv C K.M.n base t p.x) (tmv C K.M.n base t p.y) (tmv C K.M.n base t p.z) P := by
  have hv (x : Nat) (hx : x ∈ [p.x,p.y,p.z]) : tmv C K.M.n base t x = tmv C K.M.n base s x := by
    unfold tmv
    rw [hk.unch.wordsVal (fun q hq => ?_) (by have := hL.lay.le x (hp x hx); omega)]
    simp only [List.mem_append,List.mem_map,List.mem_singleton] at hq
    rcases hq with ⟨y,hy,rfl⟩ | rfl
    · exact hw x hx y hy
    · exact hL.lay.tmp x (hp x hx)
  rw [hv _ (by simp),hv _ (by simp),hv _ (by simp)]
  exact h

end VG.Proof.Weierstrass.AArch64
