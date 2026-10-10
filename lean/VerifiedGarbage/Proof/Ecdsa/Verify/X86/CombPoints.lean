import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Points
import VerifiedGarbage.Proof.Ecdsa.X86.GMul

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdh.X86
open VG.Impl.Ecdh.X86 (PX PY)
open VG.Impl.Ecdsa.Verify.X86
variable {c : Impl.Ecdsa.X86.Cfg}

abbrev combPtsW : List Nat :=
  [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ, TMP, UX, UY, UZ, PT, EM]

theorem pointsCombLadder_ok (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c)
    (hCo : ∀ d, c.comb = some d → CombOk c d) (ham3 : AM3 c.C) {s₀ : State} {base : Addr} {s : State}
    (hM : Mid c s₀ base s) {Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hTb : ∀ d, c.comb = some d → TblMem s ((s₀.gpr .eax).setWidth 64) (c.combWords d) ∧
      (∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs base ((s₀.gpr .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) ∧
      ∀ r ∈ s₀.wr ++ [below (s₀.gpr .esp) c.stk],
        Region.Disjoint ⟨(s₀.gpr .eax).setWidth 64, 8 * (c.combWords d).length⟩ r)
    (hstep₂ : Step (Impl.Ecdh.X86.Cfg.ladderQ c) c.C base s (sv c base s V) Q₂)
    (hO₂ : Q₂ (64 * c.n) 0 1 0) (hspG : SpOk c.gMul 20)
    (hsp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.pointsCombLadder c) c.stk) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Pts c s₀ base (fun j X Y Z => Rep c.C X Y Z (mul (sv c base s U >>> j) (G c.C))) Q₂ s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.X86.Cfg.pointsCombLadder c) rest) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hM.fixed
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have tb : ∀ {i}, i < 45 → ∀ w ∈ [(bitsAt c.n 0, 64 * c.n)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
    fun hi => apart_tbl hi 0
  refine WP.seq (hM.keep.withSp hsp ?_)
  unfold Impl.Ecdsa.Verify.X86.Cfg.pointsCombLadder
  -- The table of `u`.
  refine WP.seq (WP.mono (bits_ok hM.scr h0 (sl_le c h7 (i := U) (by decide)) (tbl_le h7)
    (Or.inl (by have := sl_below_bits c (i := U) (by decide) 0 0; omega)))
    fun s₁ ⟨b₁, k₁, O₁⟩ => ?_)
  have hs₁ := hM.scr.of_keeps k₁ (by decide)
  have U₁ : Unch base [(bitsAt c.n 0, 64 * c.n)] s.mem s₁.mem := O₁.unch
  have F₁ := F.unch h7 hn (fixedOk_tbl 0) U₁
  have v₁ : ∀ {i}, i < 45 → sv c base s₁ i = sv c base s i := fun hi => sv_unch U₁ h7 hn hi (tb hi)
  -- `[u]G`.
  refine WP.seq (WP.mono (gMul_ok' hc hC hT hCo ham3 hs₁ F₁
    (wordsVal_lt s.mem base (c.sl U) c.n)
    (by rw [v₁ (by decide), hM.rx]) (by rw [v₁ (by decide), hM.ry])
    (by rw [v₁ (by decide), hM.rz]) b₁ (fun d hd => by
      obtain ⟨ht, ho, hap⟩ := hTb d hd
      refine ⟨ht.of_unch (by rw [k₁.rd, k₁.wr]) U₁
        (fun w hw => by rw [List.mem_singleton.mp hw]; exact tbl_le h7) ho, ho, ?_⟩
      rw [k₁.wr, k₁.1 _ (by decide), hM.wr, hM.esp]
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hap r (List.mem_append_left _ hr)
      · rw [List.mem_singleton.mp hr]
        exact (hap _ (List.mem_append_right _ (List.mem_singleton_self _))).sub_right
          (below_sub (Cfg.stk_ge c) hM.sp_lo))
    (by rw [k₁.1 _ (by decide), hM.esp]; exact Nat.le_trans (Cfg.stk_ge c) hM.sp_lo) hspG)
    fun s₂ ⟨K₂, U₂, M₂, L₂, q₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  have F₂ := F₁.unch h7 hn fixedOk_gW U₂
  -- `U = [u]G`, `R = O`.
  refine WP.seq (WP.mono (save_ok hc hs₂) fun s₃ ⟨hs₃, k₃, U₃, ux₃, uy₃, uz₃, rx₃, ry₃, rz₃⟩ => ?_)
  have F₃ := F₂.unch h7 hn (fixedOk_slW (by decide)) U₃
  -- The table of `v`.
  have sub₂ : ∀ i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ,
      TMP], i ∈ combPtsW := by decide
  have subG : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM],
      i ∈ combPtsW := by decide
  have sub₃ : ∀ i ∈ saveW, i ∈ combPtsW := by decide
  have W₃ : ∀ {i}, i < 45 → i ∉ combPtsW → sv c base s₃ i = sv c base s i := fun hi hl =>
    ((sv_unch U₃ h7 hn hi (apart_slW (fun h => hl (sub₃ _ h)))).trans
      (sv_unch U₂ h7 hn hi (apart_gW hi (fun h => hl (subG _ h))))).trans (v₁ hi)
  refine WP.seq (WP.mono (bits_ok hs₃ h0 (sl_le c h7 (i := V) (by decide)) (tbl_le h7)
    (Or.inl (by have := sl_below_bits c (i := V) (by decide) 0 0; omega)))
    fun s₄ ⟨b₄, k₄, O₄⟩ => ?_)
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have U₄ : Unch base [(bitsAt c.n 0, 64 * c.n)] s₃.mem s₄.mem := O₄.unch
  have F₄ := F₃.unch h7 hn (fixedOk_tbl 0) U₄
  have v₄ : ∀ {i}, i < 45 → sv c base s₄ i = sv c base s₃ i := fun hi => sv_unch U₄ h7 hn hi (tb hi)
  -- `[v]Q`.
  have hlt₄ : ∀ x ∈ ladR (Impl.Ecdh.X86.Cfg.ladderQ c), wordsVal s₄.mem base x c.MP'.n < c.C.p := by
    intro x hx
    have hx' : x ∈ [AP, B3P, PX, PY, ONEP, RX, RY, RZ].map c.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show sv c base s₄ i < c.C.p
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₄.ap (hmont _)
    · exact lt_of_eq_of_lt F₄.b3p (hmont _)
    · rw [v₄ (by decide), W₃ (by decide) (by decide)]; exact hM.px_lt
    · rw [v₄ (by decide), W₃ (by decide) (by decide)]; exact hM.py_lt
    · exact lt_of_eq_of_lt F₄.onep (Nat.mod_lt _ (by omega))
    · rw [v₄ (by decide), rx₃]; omega
    · rw [v₄ (by decide), ry₃]; exact hmont _
    · rw [v₄ (by decide), rz₃]; omega
  have tv₄ : ∀ {i}, i < 45 → i ∉ combPtsW → tmv c.C c.n base s₄ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hl => by
      show toM _ _ (sv c base s₄ _) = toM _ _ (sv c base s _)
      rw [v₄ hi, W₃ hi hl]
  have hR₄ : Q₂ (Impl.Ecdh.X86.Cfg.ladderQ c).nbits (tmv c.C c.n base s₄ (c.sl RX))
      (tmv c.C c.n base s₄ (c.sl RY)) (tmv c.C c.n base s₄ (c.sl RZ)) := by
    show Q₂ (64 * c.n) (toM _ _ (sv c base s₄ RX)) (toM _ _ (sv c base s₄ RY)) (toM _ _ (sv c base s₄ RZ))
    rw [v₄ (by decide), v₄ (by decide), v₄ (by decide), rx₃, ry₃, rz₃, toM_cmont hc, toM_zero]
    exact hO₂
  refine WP.seq (WP.mono (ladder_ok (ladLayQ hc) (ladWkQ hc) hpR hs₄ (modP_of hc F₄.mp) hlt₄
    (Step.congr hstep₂ (tv₄ (by decide) (by decide)) (tv₄ (by decide) (by decide))
      (tv₄ (by decide) (by decide)) (tv₄ (by decide) (by decide)) (tv₄ (by decide) (by decide))) hR₄
      (fun t ht => by
        show s₄.mem (off base (bitsAt c.n 0 + t)) = _
        rw [b₄ t ht, show wordsVal s₃.mem base (c.sl V) c.n = sv c base s V from
          W₃ (by decide) (by decide)]))
    fun s₅ ⟨K₅, U₅, M₅, L₅, q₅⟩ => ?_)
  rw [ladWxQ_eq] at U₅
  have hs₅ := hs₄.of_keeps K₅ (by decide)
  have F₅ := F₄.unch h7 hn (fixedOk_slWk (by decide)) U₅
  have v₅ : ∀ {i}, i < 45 → i ∉ combPtsW → sv c base s₅ i = sv c base s₄ i := fun hi hl =>
    sv_unch U₅ h7 hn hi (apart_slWk hi (fun h => hl (sub₂ _ h)))
  -- The sum.
  have u₅ : ∀ {i}, i ∈ [UX, UY, UZ] → sv c base s₅ i = sv c base s₃ i := fun {i} hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact (sv_unch U₅ h7 hn (by decide) (apart_slWk (by decide) (by decide))).trans (v₄ (by decide))
  refine WP.mono (sum_ok hc hs₅ M₅ (fun i hi => ?_)) fun s₆ ⟨hs₆, g₆, rd₆, wr₆, U₆, M₆, rz₆, t₆, rx₆⟩ f₆ => h s₆ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₅.ap (hmont _)
    · exact lt_of_eq_of_lt F₅.b3p (hmont _)
    · rw [u₅ (by decide), ux₃]; exact L₂ _ (List.mem_cons_self ..)
    · rw [u₅ (by decide), uy₃]; exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · rw [u₅ (by decide), uz₃]
      exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    · exact L₅ _ (List.mem_cons_self ..)
    · exact L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have F₆ := F₅.unch h7 hn (fixedOk_slWk (by decide)) U₆
  have sub₆ : ∀ i ∈ sumW, i ∈ combPtsW := by decide
  have tu : ∀ {i j}, i ∈ [UX, UY, UZ] → j ∈ [RX, RY, RZ] → sv c base s₃ i = sv c base s₂ j →
      tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s₂ (c.sl j) := fun hi _ e => by
    show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s₂ _)
    rw [u₅ hi, e]
  have tR₅ : ∀ {i}, i ∈ [AP, B3P] → tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun {i} hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s _)
      rcases hi with rfl | rfl <;> rw [v₅ (by decide) (by decide), v₄ (by decide), W₃ (by decide) (by decide)]
  have ha : tmv c.C c.n base s (c.sl AP) = Fin.ofNat c.C.p c.C.a := by
    show toM _ _ (wordsVal s.mem base (c.sl AP) c.n) = _
    rw [F.ap]; exact toM_cmont hc _
  have hb : tmv c.C c.n base s (c.sl B3P) = Fin.ofNat c.C.p (3 * c.C.b) := by
    show toM _ _ (wordsVal s.mem base (c.sl B3P) c.n) = _
    rw [F.b3p]; exact toM_cmont hc _
  have rm₆ : sv c base s₆ RM' = sv c base s RM' :=
    (sv_unch U₆ h7 hn (by decide) (apart_slWk (by decide) (by decide))).trans
      ((v₅ (by decide) (by decide)).trans ((v₄ (by decide)).trans (W₃ (by decide) (by decide))))
  have flag₆ : flagW c base s₆ = flagW c base s := by
    rw [flagW, flag_unch U₆ h7 h0 hn (by decide), flag_unch U₅ h7 h0 hn (by decide),
      Unch.readW32 U₄ (fun w hw => ((apart_tbl (c := c) (i := FLAG) (by decide) 0) w hw).imp (fun h => by omega) id) (by have := sl_le c h7 (i := FLAG) (by decide); omega),
      Unch.readW32 U₃ (fun w hw => (apart_slW (c := c) (i := FLAG) (by decide) w hw).imp (fun h => by omega) id) (by have := sl_le c h7 (i := FLAG) (by decide); omega),
      flag_unch_gW U₂ h7 h0 hn,
      Unch.readW32 U₁ (fun w hw => ((apart_tbl (c := c) (i := FLAG) (by decide) 0) w hw).imp (fun h => by omega) id) (by have := sl_le c h7 (i := FLAG) (by decide); omega)]
  refine ⟨hs₆, by rw [wr₆, K₅.2.2, k₄.2.2, k₃.2.2, K₂.2.2, k₁.2.2, hM.wr],
    by rw [rd₆, K₅.2.1, k₄.2.1, k₃.2.1, K₂.2.1, k₁.2.1, hM.rd],
    by rw [g₆ _ (by decide), K₅.1 _ (by decide), k₄.1 _ (by decide), k₃.1 _ (by decide), K₂.1 _ (by decide),
      k₁.1 _ (by decide), hM.esp], F₆, fun t ht => ?_,
    by rw [flag₆]; exact hM.flag,
    by rw [rm₆]; exact hM.rm_lt, by rw [rm₆]; exact hM.rm, rz₆,
    ⟨_, _, _, _, _, _, by simpa only [Nat.shiftRight_zero] using q₂, q₅, by
      rw [t₆, tR₅ (by decide), tR₅ (by decide), ha, hb, tu (by decide) (by decide) ux₃,
        tu (by decide) (by decide) uy₃, tu (by decide) (by decide) uz₃]
      rfl⟩, f₆, hM.sp_lo, rx₆, ?_⟩
  · rw [tbl_unch U₆ h7 (by decide) ht (tbl_apart_slWk (by decide) (by decide) ht),
      tbl_unch U₅ h7 (by decide) ht (tbl_apart_slWk (by decide) (by decide) ht),
      tbl_unch U₄ h7 (by decide) ht (tbl_apart_tbl (by decide) ht),
      tbl_unch U₃ h7 (by decide) ht (tbl_apart_slW (by decide) 1 _),
      tbl_unch U₂ h7 (by decide) ht (tbl_apart_gW (Or.inl rfl) ht),
      tbl_unch U₁ h7 (by decide) ht (tbl_apart_tbl (by decide) ht)]
    exact hM.t₁ t ht
  · exact (sv_unch U₆ h7 hn (i := K) (by decide) (apart_slWk (by decide) (by decide))).trans
      ((v₅ (by decide) (by decide)).trans ((v₄ (by decide)).trans
        ((W₃ (by decide) (by decide)).trans hM.k)))

end VG.Proof.Ecdsa.Verify.X86
