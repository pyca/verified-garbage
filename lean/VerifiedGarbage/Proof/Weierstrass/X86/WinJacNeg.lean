import VerifiedGarbage.Proof.Weierstrass.X86.WinJacRead
import VerifiedGarbage.Proof.Weierstrass.X86.JacAdd

/-! Conditional Y negation without changing the cached powers of Z. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem neg_fields_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk v j : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) {Q : Point C} {s₀ s : State}
    (h : Frame K C base size wk s₀ s) (he : Entry K C base Q s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hz : tmv C K.M.n base s₀ K.zero=0) (hj : j<52) (hc : s.gpr .esi=BitVec.ofNat 32 j)
    (hb : ∀ i<260,s₀.mem (off base (K.bits+i))=if v.testBit i then 1 else 0) :
    WP isa K.tc.negY s fun t => Entry K C base (if Window5.nib v j<16 then negPt Q else Q) t ∧
      ProgKeep K.M base wk [K.neg,K.E.y] s t ∧
      t.gpr .esi=BitVec.ofNat 32 j := by
  have hi := h.inv_entry hL hW hro he
  have hw : ∀ x∈[K.neg,K.E.y],x∈work K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> simp [work]
  have ez : tmv C K.M.n base s K.zero=0 := by
    unfold tmv at hz ⊢
    rw [h.ro hL hW (by simp [ro])]; exact hz
  have hy : K.E.y∈ro K++coords K := by simp [coords]
  have hv0 : K.zero∈ro K++coords K := by simp [ro]
  have hn := entry_nd hL
  simp only [coords,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    or_false,not_or,List.nodup_nil,and_true] at hn
  have hs : ∀ x∈(FOp.sub K.neg K.zero K.E.y).out::(FOp.sub K.neg K.zero K.E.y).ins,x∈slots K := by
    intro x hx
    simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [slots,ro,work]
  unfold TCombCfg.negY
  apply WP.seq
  refine WP.mono (fop_ok hL.lay hW hm hi hs (by
    intro x hx
    simp only [FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact hv0
    · exact hy)) fun a ⟨ka,ia⟩ => ?_
  have kaw : ProgKeep K.M base wk [K.neg,K.E.y] s a := ka.mono (by simp [FOp.out])
  have aa := h.field hL hW kaw hw
  have bs : ∀ i<260,a.mem (off base (K.bits+i))=if v.testBit i then 1 else 0 := by
    intro i hi; rw [aa.bits hL hi]; exact hb i hi
  have hbs : K.bits+260≤size := by have := hL.bits; have := hL.table; omega
  rw [WP.block_append_iff]
  refine WP.mono (signMask_ok K.tc aa.scr (k:=v) (N:=260)
    (by change 1≤5; decide) (by change 5<2^31; decide) (by change 5*j+5≤260; omega) hbs
    ((ka.gpr _ (by decide)).trans hc) bs) fun b ⟨cb,kb⟩ => ?_
  have ib := ia.of_keeps kb (by decide)
  have kbk : ProgKeep K.M base wk [K.neg,K.E.y] a b := (keep_of_ckeeps (kb.mono (by decide))).mono (by simp)
  refine WP.mono (choose_field_ok hL.lay hW ib (o:=K.E.y) (by simp [slots,work])
    (a:=K.E.y) (List.mem_cons_of_mem _ hy) (b:=K.neg) (by simp [FOp.out])
    (decide (Window5.nib v j<16)) (by simpa only [JacWinCfg.tc,Window5.combWin_five] using cb))
    fun t ⟨kt,it⟩ => ?_
  have kk := kaw.trans (kbk.trans (kt.mono (by simp)))
  refine ⟨?_,kk,(kk.gpr _ (by decide)).trans hc⟩
  apply Entry.of_inv it
  · intro x hx
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
  all_goals
    simp only [FOp.run,Function.update_apply,ez]
    simp (disch := grind) only [ite_eq_right,ite_true]
  · have esub : 0-tmv C K.M.n base s K.E.y = -tmv C K.M.n base s K.E.y := by grind
    by_cases hsign : Window5.nib v j<16
    · simpa only [hsign,decide_true,ite_true,esub] using he.jac.negY
    · simpa only [hsign,decide_false,Bool.false_eq_true,ite_false] using he.jac
  · exact he.z2
  · exact he.z3

end VG.Proof.Weierstrass.X86.JWin
