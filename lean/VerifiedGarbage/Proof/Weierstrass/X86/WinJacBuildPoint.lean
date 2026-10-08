import VerifiedGarbage.Proof.Weierstrass.X86.WinJacFrame
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacCache
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacDouble

/-! Connect table arithmetic to the cached-point and memory-frame predicates. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

/-- Populate the two cached powers after constructing a finite Jacobian point. -/
theorem cache_point_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C)
    {V : List Nat} {E : Nat → Fe C} {s₀ s : State}
    (hF : Frame K C base size wk s₀ s) (hI : Inv K.M base size C.p (·∈slots K) V E s)
    (hV : ∀ x∈[K.E.x,K.E.y,K.E.z],x∈V) {Q : Point C}
    (hJ : InvJ C (E K.E.x) (E K.E.y) (E K.E.z) Q) (hQ : Q≠.infinity) :
    WP isa (fprog K.F K.cacheOps) s fun t =>
      Cached C base t (fun c => K.T+32*c) Q ∧ Frame K C base size wk s₀ t ∧
      ProgKeep K.M base wk [K.z2,K.z3] s t ∧
      Inv K.M base size C.p (·∈slots K) ([K.z2,K.z3]++V) (runOps K.cacheOps E) t := by
  have hs : ∀ x∈[K.E.z,K.z2,K.z3],x∈slots K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [slots,work]
  have hw : ∀ x∈[K.z2,K.z3],x∈work K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> simp [work]
  refine WP.mono (cache_ok hL.lay hW hm hs hI (hV _ (by simp)))
    fun t ⟨hk,hi,he,h2,h3⟩ => ⟨?_,hF.field hL hW hk hw,hk,hi⟩
  have ep (x : Nat) (hx : x∈[K.E.x,K.E.y,K.E.z]) : runOps K.cacheOps E x=E x := by
    apply he
    all_goals
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> simp only [JacWinCfg.E,JacWinCfg.z2,JacWinCfg.z3] <;> omega
  apply Cached.of_inv hL.n hi
  · intro c hc
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    by_cases h0 : c=0
    · subst c; exact Or.inr (hV _ (by simp [JacWinCfg.E]))
    by_cases h1 : c=1
    · subst c; exact Or.inr (hV _ (by simp [JacWinCfg.E]))
    by_cases h2 : c=2
    · subst c; exact Or.inr (hV _ (by simp [JacWinCfg.E]))
    have : c=3 ∨ c=4 := by omega
    rcases this with rfl|rfl
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr rfl)
  · rw [ep _ (by simp),ep _ (by simp),ep _ (by simp)]
    exact hJ
  · rw [ep _ (by simp)]
    exact fun hz => hQ ((hJ.z_zero_iff hC).mp hz)
  · simpa only [ep K.E.z (by simp)] using h2
  · simpa only [ep K.E.z (by simp)] using h3

end VG.Proof.Weierstrass.X86.JWin
