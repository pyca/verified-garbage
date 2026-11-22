module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Points
public import VerifiedGarbage.Proof.Ecdsa.X86.CombLays
import VerifiedGarbage.Proof.Ecdsa.X86.GMul
import VerifiedGarbage.Proof.Ecdsa.X86.Window
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section

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

theorem pointsCombLadder_ok (hc : CfgOk c) (hC : Law c.C) (hne : c.C.n < 2 ^ (8 * c.C.len)) (hT : CombTbls c)
    (hCo : ∀ d, c.comb = some d → CombOk c d) {s₀ : State} {base : Addr} {s : State}
    (hM : Mid c s₀ base s) {P : Point c.C}
    (hTb : ∀ d, c.comb = some d → TblMem s ((s₀.gpr .eax).setWidth 64) (c.combWords d) ∧
      (∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs base ((s₀.gpr .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) ∧
      ∀ r ∈ s₀.wr ++ [below (s₀.gpr .esp) c.stk],
        Region.Disjoint ⟨(s₀.gpr .eax).setWidth 64, 8 * (c.combWords d).length⟩ r)
    (hPc : onCurve c.C P = true)
    (hQ : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY)) 1 P)
    (hst : ∀ r ∈ s₀.wr, Region.Disjoint (below (s₀.gpr .esp) c.stk) r) (h24 : c.stk = 24)
    (hspG : SpOk c.gMul c.stk)
    (hsp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.pointsCombLadder c) c.stk) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Pts c s₀ base (fun j X Y Z => Rep c.C X Y Z (mul (sv c base s U >>> j) (G c.C)))
      (fun j X Y Z => Rep c.C X Y Z (mul (sv c base s V >>> j) P)) s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.X86.Cfg.pointsCombLadder c) rest) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hM.fixed
  obtain hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  obtain tb : ∀ {i}, i < 45 → ∀ w ∈ [(bitsAt c.n 0, 64 * c.n)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
    fun hi => apart_tbl hi 0
  refine WP.seq (hM.keep.withSp hsp ?_)
  unfold Impl.Ecdsa.Verify.X86.Cfg.pointsCombLadder
  -- The table of `u`.
  refine WP.seq (WP.mono (bits_ok hM.scr h0 (sl_le c h7 (i := U) (by decide)) (tbl_le h7)
    (Or.inl (by have := sl_below_bits c (i := U) (by decide) 0 0; omega_arith)))
    fun s₁ ⟨b₁, k₁, O₁⟩ => ?_)
  obtain hs₁ := hM.scr.of_keeps k₁ (by decide)
  have U₁ : Unch base [(bitsAt c.n 0, 64 * c.n)] s.mem s₁.mem := O₁.unch
  obtain F₁ := F.unch h7 hn (fixedOk_tbl 0) U₁
  obtain v₁ : ∀ {i}, i < 45 → sv c base s₁ i = sv c base s i := fun hi => sv_unch U₁ h7 hn hi (tb hi)
  -- `[u]G`.
  refine WP.seq (WP.mono (gMul_ok' hc hC hT hCo hs₁ F₁
    (wordsVal_lt s.mem base (c.sl U) c.n)
    (by rw [v₁ (by decide), hM.rx]) (by rw [v₁ (by decide), hM.ry])
    (by rw [v₁ (by decide), hM.rz]) b₁ (fun d hd => by
      obtain ⟨ht, ho, hap⟩ := hTb d hd
      refine ⟨ht.of_unch (by rw [k₁.rd, k₁.wr]) U₁
        (fun w hw => by rw [List.mem_singleton.mp hw]; exact tbl_le h7) ho, ho, ?_⟩
      rw [k₁.wr, k₁.1 _ (by decide), hM.wr, hM.esp]
      exact hap)
    (by rw [k₁.wr, k₁.1 _ (by decide), hM.wr, hM.esp]; exact hst)
    (by rw [k₁.1 _ (by decide), hM.esp]; exact hM.sp_lo) hspG)
    fun s₂ ⟨K₂, U₂, M₂, L₂, q₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keeps K₂ (by decide)
  obtain F₂ := F₁.unch h7 hn fixedOk_gW U₂
  -- `U = [u]G`, `R = O`.
  refine WP.seq (WP.mono (save_ok hc hs₂) fun s₃ ⟨hs₃, k₃, U₃, ux₃, uy₃, uz₃, rx₃, ry₃, rz₃⟩ => ?_)
  obtain F₃ := F₂.unch h7 hn (fixedOk_slW (by decide)) U₃
  -- The table of `v`.
  obtain subG : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM],
      i ∈ combPtsW := by decide
  obtain sub₃ : ∀ i ∈ saveW, i ∈ combPtsW := by decide
  obtain W₃ : ∀ {i}, i < 45 → i ∉ combPtsW → sv c base s₃ i = sv c base s i := fun hi hl =>
    ((sv_unch U₃ h7 hn hi (apart_slW (fun h => hl (sub₃ _ h)))).trans
      (sv_unch U₂ h7 hn hi (apart_gW hi (fun h => hl (subG _ h))))).trans (v₁ hi)
  refine WP.seq (WP.mono (bits_ok hs₃ h0 (sl_le c h7 (i := V) (by decide)) (tbl_le h7)
    (Or.inl (by have := sl_below_bits c (i := V) (by decide) 0 0; omega_arith)))
    fun s₄ ⟨b₄, k₄, O₄⟩ => ?_)
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  have U₄ : Unch base [(bitsAt c.n 0, 64 * c.n)] s₃.mem s₄.mem := O₄.unch
  obtain F₄ := F₃.unch h7 hn (fixedOk_tbl 0) U₄
  obtain v₄ : ∀ {i}, i < 45 → sv c base s₄ i = sv c base s₃ i := fun hi => sv_unch U₄ h7 hn hi (tb hi)
  -- `[v]Q`.
  obtain hG₄ : Rep c.C (tmv c.C c.n base s₄ (c.sl PX)) (tmv c.C c.n base s₄ (c.sl PY)) 1 P := by
    show Rep c.C (toM _ _ (sv c base s₄ PX)) (toM _ _ (sv c base s₄ PY)) 1 P
    rw [v₄ (by decide), v₄ (by decide), W₃ (by decide) (by decide), W₃ (by decide) (by decide)]
    exact hQ
  have hlen := hc.len_hi
  obtain hspW : SpOk (c.ecdhMul PX PY) 24 := by
    have := (show SpOk (Impl.Ecdsa.Verify.X86.Cfg.pointsCombLadder c) c.stk from hsp)
    unfold Impl.Ecdsa.Verify.X86.Cfg.pointsCombLadder at this
    rw [h24] at this
    exact this.right.right.right.right.left
  obtain e₄ : s₄.gpr .esp = s₀.gpr .esp := by
    rw [k₄.1 _ (by decide), k₃.1 _ (by decide), K₂.1 _ (by decide), k₁.1 _ (by decide), hM.esp]
  obtain w₄ : s₄.wr = s₀.wr := by rw [k₄.2.2, k₃.2.2, K₂.2.2, k₁.2.2, hM.wr]
  refine WP.seq (WP.mono (ecdhMul_ok hc hC (px := PX) (py := PY) (by decide) (by decide) hs₄ F₄.mp F₄.ap
    F₄.b3p F₄.zero F₄.onep
    (by rw [v₄ (by decide), W₃ (by decide) (by decide)]; exact hM.px_lt)
    (by rw [v₄ (by decide), W₃ (by decide) (by decide)]; exact hM.py_lt) hPc hG₄
    (k := sv c base s V) (Nat.lt_trans hM.v_lt hne)
    (fun t ht => by
      show s₄.mem (off base (bitsAt c.n 0 + t)) = _
      rw [b₄ t (Nat.lt_of_lt_of_le ht (by omega_using [hlen])),
        show wordsVal s₃.mem base (c.sl V) c.n = sv c base s V from W₃ (by decide) (by decide)])
    (fun r hr => by rw [w₄] at hr; rw [e₄, ← h24]; exact hst r hr)
    (by rw [e₄, ← h24]; exact hM.sp_lo) hspW)
    fun s₅ ⟨K₅, U₅, L₅, q₅⟩ => ?_)
  obtain hs₅ := hs₄.of_keeps K₅ (by decide)
  obtain F₅ := F₄.unch h7 hn ((winW_winTW h7).fixedOk h7) U₅
  obtain M₅ := modP_of hc F₅.mp
  obtain subW : ∀ i ∈ winWr, i ∈ combPtsW := by decide
  obtain v₅ : ∀ {i}, i < 45 → i ∉ combPtsW → sv c base s₅ i = sv c base s₄ i := fun hi hl =>
    sv_winTW U₅ h7 hn hi (fun h => hl (subW _ h))
  -- The sum.
  obtain u₅ : ∀ {i}, i ∈ [UX, UY, UZ] → sv c base s₅ i = sv c base s₃ i := fun {i} hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact (sv_winTW U₅ h7 hn (by decide) (by decide)).trans (v₄ (by decide))
  refine WP.mono (sum_ok hc hs₅ M₅ (fun i hi => ?_)) fun s₆ ⟨hs₆, g₆, rd₆, wr₆, U₆, M₆, rz₆, t₆, rx₆⟩ f₆ => h s₆ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₅.ap (hmont _)
    · exact lt_of_eq_of_lt F₅.b3p (hmont _)
    · rw [u₅ (by decide), ux₃]; exact L₂ _ (List.mem_cons_self ..)
    · rw [u₅ (by decide), uy₃]; exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · rw [u₅ (by decide), uz₃]
      exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    · exact L₅ RX (by decide)
    · exact L₅ RY (by decide)
    · exact L₅ RZ (by decide)
  obtain F₆ := F₅.unch h7 hn (fixedOk_slWk (by decide)) U₆
  obtain sub₆ : ∀ i ∈ sumW, i ∈ combPtsW := by decide
  obtain tu : ∀ {i j}, i ∈ [UX, UY, UZ] → j ∈ [RX, RY, RZ] → sv c base s₃ i = sv c base s₂ j →
      tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s₂ (c.sl j) := fun hi _ e => by
    show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s₂ _)
    rw [u₅ hi, e]
  obtain tR₅ : ∀ {i}, i ∈ [AP, B3P] → tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun {i} hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s _)
      rcases hi with rfl | rfl <;> rw [v₅ (by decide) (by decide), v₄ (by decide), W₃ (by decide) (by decide)]
  obtain ha : tmv c.C c.n base s (c.sl AP) = Fin.ofNat c.C.p c.C.a := by
    show toM _ _ (wordsVal s.mem base (c.sl AP) c.n) = _
    rw [F.ap]; exact toM_cmont hc _
  obtain hb : tmv c.C c.n base s (c.sl B3P) = Fin.ofNat c.C.p (3 * c.C.b) := by
    show toM _ _ (wordsVal s.mem base (c.sl B3P) c.n) = _
    rw [F.b3p]; exact toM_cmont hc _
  obtain rm₆ : sv c base s₆ RM' = sv c base s RM' :=
    (sv_unch U₆ h7 hn (by decide) (apart_slWk (by decide) (by decide))).trans
      ((v₅ (by decide) (by decide)).trans ((v₄ (by decide)).trans (W₃ (by decide) (by decide))))
  obtain flag₆ : flagW c base s₆ = flagW c base s := by
    rw [flagW, flag_unch U₆ h7 h0 hn (by decide),
      Unch.readW32 U₅ (fun w hw => (apart_winTW (c := c) h7 (i := FLAG) (by decide) (by decide) w hw).imp (fun h => by omega_arith) id) (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith),
      Unch.readW32 U₄ (fun w hw => ((apart_tbl (c := c) (i := FLAG) (by decide) 0) w hw).imp (fun h => by omega_arith) id) (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith),
      Unch.readW32 U₃ (fun w hw => (apart_slW (c := c) (i := FLAG) (by decide) w hw).imp (fun h => by omega_arith) id) (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith),
      flag_unch_gW U₂ h7 h0 hn,
      Unch.readW32 U₁ (fun w hw => ((apart_tbl (c := c) (i := FLAG) (by decide) 0) w hw).imp (fun h => by omega_arith) id) (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith)]
  refine ⟨hs₆, by rw [wr₆, K₅.2.2, k₄.2.2, k₃.2.2, K₂.2.2, k₁.2.2, hM.wr],
    by rw [rd₆, K₅.2.1, k₄.2.1, k₃.2.1, K₂.2.1, k₁.2.1, hM.rd],
    by rw [g₆ _ (by decide), K₅.1 _ (by decide), k₄.1 _ (by decide), k₃.1 _ (by decide), K₂.1 _ (by decide),
      k₁.1 _ (by decide), hM.esp], F₆, fun t ht => ?_,
    by rw [flag₆]; exact hM.flag,
    by rw [rm₆]; exact hM.rm_lt, by rw [rm₆]; exact hM.rm, rz₆,
    ⟨_, _, _, _, _, _, by simpa only [Nat.shiftRight_zero] using q₂,
      by simpa only [Nat.shiftRight_zero] using q₅, by
      rw [t₆, tR₅ (by decide), tR₅ (by decide), ha, hb, tu (by decide) (by decide) ux₃,
        tu (by decide) (by decide) uy₃, tu (by decide) (by decide) uz₃]⟩, f₆, hM.sp_lo, rx₆, ?_⟩
  · rw [tbl_unch U₆ h7 (by decide) ht (tbl_apart_slWk (by decide) (by decide) ht),
      tbl_unch U₅ h7 (by decide) ht ((winW_winTW h7).apart_bits h7 (by decide) ht),
      tbl_unch U₄ h7 (by decide) ht (tbl_apart_tbl (by decide) ht),
      tbl_unch U₃ h7 (by decide) ht (tbl_apart_slW (by decide) 1 _),
      tbl_unch U₂ h7 (by decide) ht (tbl_apart_gW (Or.inl rfl) ht),
      tbl_unch U₁ h7 (by decide) ht (tbl_apart_tbl (by decide) ht)]
    exact hM.t₁ t ht
  · exact fun _ => (sv_unch U₆ h7 hn (i := K) (by decide) (apart_slWk (by decide) (by decide))).trans
      ((v₅ (by decide) (by decide)).trans ((v₄ (by decide)).trans
        ((W₃ (by decide) (by decide)).trans hM.k)))

end VG.Proof.Ecdsa.Verify.X86
