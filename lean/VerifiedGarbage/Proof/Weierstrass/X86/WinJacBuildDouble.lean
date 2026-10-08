import VerifiedGarbage.Proof.Weierstrass.X86.WinJacBuildInit
import VerifiedGarbage.Proof.Weierstrass.WinJacMath

/-! Construct the second cached multiple with one in-place doubling. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem rcb_E_work (K : JacWinCfg) : ∀ x∈rcbW K.S K.E,x∈work K := by
  intro x hx
  simp only [rcbW,work,temps,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem rcb_E_nd {K : JacWinCfg} {size wk : Nat} (hL : Layout K size wk) :
    (rcbW K.S K.E).Nodup := by
  apply List.Nodup.sublist (l₂:=work K) _ hL.nd
  simp only [rcbW,work,temps,List.cons_append,List.nil_append]
  repeat first | exact List.Sublist.refl _ | apply List.Sublist.cons_cons | apply List.Sublist.cons

theorem build_double_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    (hn : 17≤C.n) {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity)
    {s₀ s : State} (h : BuildInv K C base size wk P s₀ 1 s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p) :
    WP isa (.seq (K.dbl K.E) (.seq (fprog K.F K.cacheOps)
      (.block (([.mov .esi (.imm 2)] : List Instr)++K.storeEntry)))) s
      (BuildInv K C base size wk P s₀ 2) := by
  have hi := h.frame.inv_cached hL hW hro h.point
  have hv : ∀ x∈[K.E.x,K.E.y,K.E.z],x∈live K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [live]
  have hj : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y)
      (tmv C K.M.n base s K.E.z) P := by
    simpa only [hL.n,mul_one_pt,JacWinCfg.E,Nat.reduceMul,Nat.add_zero] using h.point.jac
  have hs : ∀ x∈rcbW K.S K.E,x∈slots K := fun x hx => List.mem_append_right _ (rcb_E_work K x hx)
  apply WP.seq
  refine WP.mono (dbl_ok hL.lay hW hm hC ha (rcb_E_nd hL)
    (fun hx => hL.readonly K.S.a (by simp [ro]) (rcb_E_work K _ hx)) hs hi hv hP hj)
    fun a ⟨ka,ia,ja⟩ => ?_
  have ja : InvJ C (runOps (dblJMul K.S K.E K.E) (tmv C K.M.n base s) K.E.x)
      (runOps (dblJMul K.S K.E K.E) (tmv C K.M.n base s) K.E.y)
      (runOps (dblJMul K.S K.E K.E) (tmv C K.M.n base s) K.E.z) (mul 2 P) := by
    rw [←mul_one_pt P,hC.add_mul_mul hP] at ja
    exact ja
  apply WP.seq
  refine WP.mono (cache_point_ok hL hW hm hC (h.frame.field hL hW ka (rcb_E_work K)) ia
    (fun _ hx => List.mem_append_left _ hx) ja
    (Window5.mul_ne_infinity hO hP hP0 (by decide) (by omega))) fun b ⟨pb,fb,kb,_⟩ => ?_
  have hw : ∀ x∈[K.z2,K.z3],x∈work K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> simp [work]
  have tb := (h.table.field_keep hL h.frame.scr ka (rcb_E_work K) (by decide)).field_keep
    hL ia.scr kb hw (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mov_counter_ok b 2) fun t ⟨ct,kt⟩ => ?_
  apply build_store_ok hL hW (fb.keeps kt) (m:=1) (by decide) ct
  · intro m h1 hm
    exact (tb m h1 hm).congr fun _ _ => by rw [kt.2.1]
  · exact pb.congr fun _ _ => by rw [kt.2.1]

end VG.Proof.Weierstrass.X86.JWin
