import VerifiedGarbage.Proof.Weierstrass.X86.TCombInv
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont
open Spec.Weierstrass

theorem decEsi_ok (s : State) {j : Nat} (hj : 1 ≤ j) (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block [decCounter]) s fun t => t.gpr .esi = BitVec.ofNat 32 (j-1) ∧ CKeeps [.esi] s t :=
  wp_decCounter hj hb fun _t b k hm => WP.block_nil ⟨b, k.1, hm, k.2⟩

theorem testEsi_ok (s : State) {j : Nat} (hj : j < 2^32) (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block [testCounter]) s fun t => t.zf = some (decide (j=0)) ∧ CKeeps [] s t :=
  wp_testCounter hj hb fun _t f z => WP.block_nil ⟨z, fun r _ => congrFun f.gpr r, f.mem, f.rd, f.wr⟩

theorem tstep_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C)
    (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) {s₀ : State}
    (hF : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ K.J)
    (hI : TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s j) :
    WP isa K.step s fun s' =>
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (j - 1) ∧
        s'.zf = some (decide (j - 1 = 0)) := by
  have hn := hI.scr.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  unfold TCombCfg.step
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (decEsi_ok s hj hI.esi) fun s₁ ⟨b₁, k₁⟩ => ?_
  have hs₁ := hI.scr.of_keeps k₁.keeps (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have hM₁ : ModOkW K.M size C.p s₁.mem base := by rw [hm₁]; exact hI.mod
  have hbits₁ : ∀ t < K.w * K.J, s₁.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by rw [hm₁]; exact hI.bits t ht
  have hz : wordsVal s₁.mem base K.zero K.M.n = 0 := by
    rw [hm₁, hI.unch.wordsVal (tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb]))
      (by have := hle K.zero (by tcomb_mem); omega), hF.zero]
  have hT : (s₁.mem.readW (off base K.ptr) 32).setWidth 64 = T := by rw [hm₁]; exact hI.tsym
  have hTM : TblMem s₁ T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) :=
    hI.tbl.unch (by rw [k₁.2.2.1, k₁.2.2.2]) fun _ _ _ _ => by rw [hm₁]
  refine WP.mono (tentry_ok hL hC hV hpn hs₁ hM₁ (i := j - 1) (by omega) b₁ hbits₁ hz hT hTM)
    fun s₂ h₂ => WP.seq (WP.mono h₂ fun s₃ E₃ => ?_)
  have hEW : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n), (K.wk, accLen K.M)], w ∈ combWx K := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [combWx, combW, combWs, List.mem_append, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false, TCombCfg.toComb]
    rcases hw with h | h | h | h | h | h <;> subst h <;> simp
  have U₁₃ : Unch base (combWx K) s.mem s₃.mem := by
    rw [← hm₁]; exact E₃.unch.mono hEW
  have hmoW := tcombW_mo hL hI.mod
  have hM₃ : ModOkW K.M size C.p s₃.mem base :=
    hI.mod.unch U₁₃ (fun w hw => hmoW w (List.mem_append_left _ hw)) (by omega)
  -- What `A` and the read-only slots hold at `s₃`.
  have hAx : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₃.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    fun x hx => by
      have hxs : x ∈ combWs K.toComb := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> tcomb_mem
      rw [E₃.unch.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
        · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
        · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
        · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
        · exact hL.comb.lay.tmp x (combWs_slots _ x hxs)
        · exact .inl (hL.wk.sl x (combWs_slots _ x hxs)))
        (by have := hle x (combWs_slots _ x hxs); omega), hm₁]
  have U₃ : Unch base (tcombW K) s₀.mem s₃.mem :=
    (hI.unch.trans U₁₃).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ hw
  have hro : ∀ x ∈ combRo K.toComb, wordsVal s₃.mem base x K.M.n = wordsVal s₀.mem base x K.M.n :=
    fun x hx => U₃.wordsVal (tcombW_ro hL hx) (by have := hle x (combRo_slots x hx); omega)
  have hSl : ∀ x ∈ rcbR K.S K.A K.E, x ∈ combSlots K.toComb := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem
  have hlt₃ : ∀ x ∈ rcbR K.S K.A K.E, wordsVal s₃.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.ro_lt _ (by simp [combRo, TCombCfg.toComb])
    · rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.ro_lt _ (by simp [combRo, TCombCfg.toComb])
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · exact E₃.lt _ (by simp)
    · exact E₃.lt _ (by simp)
    · exact E₃.lt _ (by simp)
  have I₃ : Inv K.M base size C.p (· ∈ combSlots K.toComb) (rcbR K.S K.A K.E) (tmv C K.M.n base s₃) s₃ :=
    ⟨E₃.scr, hM₃, hSl, hlt₃, fun _ _ => rfl⟩
  have hSl' : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.A K.E, x ∈ combSlots K.toComb := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [combSlots, List.mem_append, TCombCfg.toComb]; exact Or.inr hx
    · exact hSl x hx
  refine WP.seq (WP.mono (rcb3_ok hL.comb.lay hL.wk hV.unit hL.comb.add hSl' I₃
    (fun _ h => h)) fun s₄ ⟨P₄, I₄, t₄⟩ => ?_)
  dsimp only [TCombCfg.toComb] at P₄ I₄ t₄
  -- The sum.
  have tb : tmv C K.M.n base s₃ K.S.b3 = Fin.ofNat C.p C.b := by
    show toM _ _ _ = _; rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.b
  have hRA : Rep C (tmv C K.M.n base s₃ K.A.x) (tmv C K.M.n base s₃ K.A.y)
      (tmv C K.M.n base s₃ K.A.z) (mul (combEW K.w k K.J j) (G C)) := by
    have ex : tmv C K.M.n base s₃ K.A.x = tmv C K.M.n base s K.A.x := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    have ey : tmv C K.M.n base s₃ K.A.y = tmv C K.M.n base s K.A.y := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    have ez : tmv C K.M.n base s₃ K.A.z = tmv C K.M.n base s K.A.z := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    rw [ex, ey, ez]; exact hI.rep
  rw [tb] at t₄
  have hP := hC.onCurve_mul hG (combEW K.w k K.J j)
  have hQ : onCurve C (signedPtW C K.w k (j - 1)) = true := by
    unfold signedPtW combPtW
    split
    · exact hC.onCurve_mul hG _
    · exact onCurve_negPt (hC.onCurve_mul hG _)
  have hR := hC.add3 hM3 hP hQ hRA E₃.rep t₄.symm
  have hadd := combW_add hC hG (w := K.w) (k := k) (J := K.J) (j := j - 1) (by omega)
  rw [Nat.sub_add_cancel hj] at hadd
  have hsp : signedPtW C K.w k (j - 1) = (if 2 ^ (K.w - 1) ≤ combWin K.w k (j - 1) then
      combPtW C K.w (j - 1) (combWin K.w k (j - 1) - 2 ^ (K.w - 1))
      else negPt (combPtW C K.w (j - 1) (2 ^ (K.w - 1) - combWin K.w k (j - 1)))) := rfl
  rw [hsp, hadd] at hR
  -- The copy and the test.
  have hDv : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.A K.E :=
    fun _ hx => List.mem_append_left _ hx
  have hs₄ := I₄.scr
  have hb₄ : s₄.gpr .esi = BitVec.ofNat 32 (j - 1) := by
    rw [P₄.gpr _ esi_not_clob, E₃.keep.gpr _ esi_not_clob, b₁]
  have hDslots : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ combWs K.toComb := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> tcomb_mem
  have hAslots : ∀ x ∈ [K.A.x, K.A.y, K.A.z], x ∈ combWs K.toComb := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> tcomb_mem
  rw [WP.block_append_iff]
  refine WP.mono (copyPt_ok hs₄ (n := K.M.n) (o := K.A) (a := K.D)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hle _ (by tcomb_mem))
    (fun x hx y hy hxy => hL.comb.apart₂ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> tcomb_mem) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem) hxy)
    (fun x hx hx' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hx'
      grind)
    (by grind)) fun s₅ ⟨ex₅, ey₅, ez₅, k₅, U₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  have hb₅ : s₅.gpr .esi = BitVec.ofNat 32 (j - 1) := by rw [k₅.gpr _ (by decide), hb₄]
  refine WP.mono (testEsi_ok s₅ (by omega) hb₅) fun s₆ ⟨z₆, k₆⟩ => ?_
  have m₆ : s₆.mem = s₅.mem := k₆.2.1
  have U₄ : Unch base (combWx K) s₃.mem s₄.mem := P₄.unch.mono fun w hw => by
    simp only [progW, combWx, combW, List.mem_append, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | rfl | rfl
    · exact Or.inl (Or.inl ⟨y, by simp only [combWs, List.mem_append, TCombCfg.toComb]; exact Or.inr hy, rfl⟩)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr rfl
  have U₆ : Unch base (combWx K) s₄.mem s₆.mem := by
    rw [m₆]
    exact U₅.mono fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      simp only [combWx, combW, combWs, List.mem_append, List.mem_map, List.mem_cons,
        List.not_mem_nil, or_false, TCombCfg.toComb]
      rcases hw with h | h | h <;> subst h <;> simp
  have U : Unch base (combWx K) s.mem s₆.mem := (U₁₃.trans (U₄.trans U₆)).mono fun w hw => by
    simp only [List.mem_append] at hw; rcases hw with h | h | h <;> exact h
  have hDval : ∀ x ∈ [K.D.x, K.D.y, K.D.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base x K.M.n) =
      runOps (rcb3 K.S K.A K.E K.D) (tmv C K.M.n base s₃) x := fun x hx => I₄.val x (hDv x hx)
  have hDlt : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₄.mem base x K.M.n < C.p := fun x hx => I₄.lt x (hDv x hx)
  refine ⟨⟨hs₅.of_keeps k₆.keeps (by decide), by rw [k₆.1 _ (by decide), hb₅], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [unch_read32 U (by have := hL.ptr_le; omega) (combW_ptr hL)]; exact hI.tsym⟩, z₆⟩
  · have c₁ : KeepRegs powClob s s₁ := (CKeeps.regs k₁).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..
    have c₃ : KeepRegs powClob s₁ s₃ := E₃.keep.mono clob_powClob
    have c₄ : KeepRegs powClob s₃ s₄ :=
      VG.Proof.Mont.X86.Keeps.mono ⟨P₄.gpr, P₄.rd, P₄.wr⟩ clob_powClob
    have c₅ : KeepRegs powClob s₄ s₅ := k₅.mono fun r hr => clob_powClob r (by
      simp only [List.mem_singleton] at hr; subst hr; simp [clob])
    have c₆ : KeepRegs powClob s₅ s₆ := (CKeeps.regs k₆).mono fun r hr => absurd hr List.not_mem_nil
    exact hI.keep.trans (c₁.trans (c₃.trans (c₄.trans (c₅.trans c₆))))
  · exact (hI.unch.trans U).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ hw
  · exact hI.mod.unch U (fun w hw => hmoW w (List.mem_append_left _ hw)) (by omega)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [m₆, ex₅]; exact hDlt _ (by simp)
    · rw [m₆, ey₅]; exact hDlt _ (by simp)
    · rw [m₆, ez₅]; exact hDlt _ (by simp)
  · have e : ∀ {x y : Nat}, wordsVal s₆.mem base x K.M.n = wordsVal s₄.mem base y K.M.n →
        tmv C K.M.n base s₆ x = tmv C K.M.n base s₄ y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
    rw [e (by rw [m₆, ex₅]), e (by rw [m₆, ey₅]), e (by rw [m₆, ez₅])]
    show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [hDval _ (by simp), hDval _ (by simp), hDval _ (by simp)]
    exact hR
  · intro t ht
    have hb := hL.bits
    have hz' : K.w * K.J ≤ K.kbytes + 4 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega
    rw [U.byte (combW_bits hL ht) (by omega_using [hb, hz', ht, hn])]
    exact hI.bits t ht
  · exact TblMem.of_unch hI.tbl (by rw [k₆.2.2.1, k₆.2.2.2, k₅.rd, k₅.wr, P₄.rd, P₄.wr, E₃.keep.rd,
      E₃.keep.wr, k₁.2.2.1, k₁.2.2.2]) U (fun w hw => tcombW_size hL hI.mod w (List.mem_append_left _ hw)) hF.out


end VG.Proof.Weierstrass.X86
