import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowEntry

/-! Adding a signed digit to the doubled accumulator. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

local macro "jmem" : tactic => `(tactic| simp only [jacLive,jacWinSlots,jacWinWrites,
  winRo,winOther,rcbR,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,true_or,or_true])

/-- Complete Jacobian addition followed by copying the result into R. -/
theorem jacAddDigit_ok {K : WinCfg} {C : Curve} {base : Addr} {size k j : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (· ∈ jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hk : 16*Window5.geom 52≤k) (hj : j<52)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : JacCore K C base size P k (32*Window5.winE k 52 (j+1)) s)
    (hE : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y)
      (tmv C K.M.n base s K.E.z) (Window5.winPt C P k j)) :
    WP isa (.seq (Jacobian.jacAdd K K.R K.E K.D) (.block (copyPt 4 K.R K.D))) s fun t =>
      ProgKeep K.M base (winOther K) s t ∧ JacCore K C base size P k (Window5.winE k 52 j) t := by
  have old := hL.toWinLay hJ
  have sl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.E, x ∈ jacWinSlots K := by
    intro x hx
    simp only [rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with h | h
    all_goals simp_all only [jacWinSlots,winRo,winOther,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    all_goals grind
  have vr : ∀ x ∈ rcbR K.S K.R K.E, x ∈ jacLive K := by
    intro x hx
    simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jmem
  apply WP.seq
  refine WP.mono (jacAdd_ok hL.lay hAl hm hC ha (old.rcbApart_D (Or.inr rfl)) sl h.field vr hOne
    (hC.onCurve_mul hP _) (Window5.onCurve_winPt hC hP k j) h.point hE)
    fun s₁ ⟨E₁,k₁,i₁,j₁⟩ => ?_
  have sd : ∀ x ∈ rcbW K.S K.R ++ rcbR K.S K.D K.D, x ∈ jacWinSlots K := by
    intro x hx
    simp only [rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with h | h
    all_goals simp_all only [jacWinSlots,winRo,winOther,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    all_goals grind
  have vd : ∀ x ∈ rcbR K.S K.D K.D, x ∈ [K.D.x,K.D.y,K.D.z]++jacLive K := by
    intro x hx
    simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jmem
  rw [← hL.n]
  refine WP.mono (copyPoint_ok hL.lay hAl hL.rcbApart_DR sd i₁ vd)
    fun t ⟨E₂,k₂,i₂,hv⟩ => ?_
  have kp : ProgKeep K.M base (winOther K) s t := (k₁.mono (by
    intro x hx; simp only [rcbW,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jmem)).trans
    (k₂.mono (by
      intro x hx; simp only [rcbW,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jmem))
  have ip := i₂.sub (fun x (hx : x ∈ jacLive K) => List.mem_append_right _ (List.mem_append_right _ hx))
  refine ⟨kp,h.next hL hJ kp ip ?_⟩
  simp only [Prod.mk.injEq] at hv
  rw [hv.1,hv.2.1,hv.2.2]
  rw [Window5.win_add hC hP hk hj] at j₁
  exact j₁

end VG.Proof.Weierstrass.AArch64
