import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad

/-!
# `vg_rsa_crt_values` on x86-64: the loads and the check of `p q = n`

The loads of `n`, `p`, `q` and `d` (`cvLoads_ok`), and the mask of
`p q = n` (`cvCheck_ok`), as `n mod p = 0`, `n / p = q` and `p` odd
(`pq_iff`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-- `p q = n` for an odd `n`, as `pqCheck` checks it. -/
theorem pq_iff {N P Q : Nat} (hN : N % 2 = 1) :
    (P % 2 = 1 ∧ N / P = Q ∧ N % P = 0) ↔ P * Q = N := by
  constructor
  · rintro ⟨hp, hq, hr⟩
    have := Nat.div_add_mod N P
    rw [hq, hr, Nat.add_zero] at this
    exact this
  · intro h
    have hp : P % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one P with hP | hP
      · rw [← h, Nat.mul_mod, hP, Nat.zero_mul] at hN; exact absurd hN (by decide)
      · exact hP
    have hP0 : 0 < P := by omega
    refine ⟨hp, ?_, ?_⟩
    · rw [← h, Nat.mul_div_cancel_left _ hP0]
    · rw [← h, Nat.mul_mod_right]

/-- The memory word of the mask. -/
abbrev mword (m : Mem) (B : Addr) : BitVec 64 := word m B (8 * Impl.Bignum.X86_64.Public.sMask)

/-- `CvS` and the mask, after a store to the mask's slot. -/
theorem CvS.mask {I : CvIn} {m₀ : Mem} {s t : State} (h : CvS I m₀ s) {v : BitVec 64}
    (hm : t.mem = s.mem.writeW (off I.B (8 * Impl.Bignum.X86_64.Public.sMask)) v) {regs : List Reg}
    (k : Keep regs s t) (hr : .rdi ∉ regs) : CvS I m₀ t ∧ mword t.mem I.B = v ∧
      ∀ j < 16, wv t.mem I.B (slot (wk I.k) j) (wk I.k + 2) = wv s.mem I.B (slot (wk I.k) j) (wk I.k + 2) := by
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have ho := writeW_outside s.mem I.B v (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by omega)
  rw [← hm] at ho
  refine ⟨h.step (Frm.of_outside ho (List.mem_singleton_self _)) (fun r hr => ?_) (fun r hr => ?_) k hr,
    by rw [hm]; exact word_writeW_self _ _ _ _, fun j hj => ho.wv (Or.inr ?_) (by have := h.ws.sl hj; omega)⟩
  · rw [List.mem_singleton.mp hr]; exact Or.inr (Or.inl rfl)
  · rw [List.mem_singleton.mp hr]; simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega
  · have := hdr_lt_slot (wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega

/-- The bounds on the lengths. -/
structure CvLens (I : CvIn) : Prop where
  k1 : 64 ≤ I.k
  k2 : I.k ≤ 1024
  pl1 : 1 ≤ I.pl
  pl2 : I.pl < I.k
  ql1 : 1 ≤ I.ql
  ql2 : I.ql < I.k
  dl1 : 1 ≤ I.dl
  dl2 : I.dl ≤ I.k
  nl : I.nb.length = I.k
  pbl : I.pb.length = I.pl
  qbl : I.qb.length = I.ql
  dbl : I.db.length = I.dl
  z : 128 * I.k ≤ I.Z

/-- An array other than the one that changed. -/
theorem outside_arr {m m' : Mem} {B : Addr} {Z w j i n L : Nat} (ho : Outside B (slot w j) L m m')
    (hL : L ≤ 8 * (w + 2)) (hij : i ≠ j) (hn : n ≤ w + 2) (hi : i < 16) (hZ : slot w 16 ≤ Z)
    (hB : B.toNat + Z ≤ 2 ^ 64) : wv m' B (slot w i) n = wv m B (slot w i) n :=
  ho.wv (by have := slot_far (w := w) hij; omega) (by have := Nat.le_trans (slot_lt (w := w) hi) hZ; omega)

/-- The loads of `n`, `p`, `q` and `d` into their arrays. -/
theorem cvLoads_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) :
    WP isa (seqs (loadA aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
      (loadA aP sP sPl ++ (loadA aQ sQ sQl ++ loadA aD sD sDl)))) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      wv t.mem I.B (slot (wk I.k) aN) (wk I.k) = Spec.Rsa.os2ip I.nb ∧
      wv t.mem I.B (slot (wk I.k) aP) (wk I.k) = Spec.Rsa.os2ip I.pb ∧
      wv t.mem I.B (slot (wk I.k) aQ) (wk I.k) = Spec.Rsa.os2ip I.qb ∧
      wv t.mem I.B (slot (wk I.k) aD) (wk I.k) = Spec.Rsa.os2ip I.db := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have k1 := L.k1
  have k2 := L.k2
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have hm : ∀ {m m' : Mem} {j : Nat}, Outside I.B (slot (wk I.k) j) (8 * (wk I.k + 2)) m m' →
      mword m' I.B = mword m I.B := fun {_ _ j} o =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega))
      (by have := hdr_lt_slot (wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok h.ws (by decide) (by decide)
    (by decide) h.args.n h.args.k h.n L.nl (by omega) (by unfold wk; omega)) fun s₁ ⟨hv₁, o₁, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok h₁.ws (by decide) (by decide)
    (by decide) h₁.args.p h₁.args.pl h₁.p L.pbl L.pl1 (by have := L.pl2; unfold wk; omega)) fun s₂ ⟨hv₂, o₂, k₂⟩ => ?_)
  have h₂ := h₁.arr (by decide) (Nat.le_refl _) o₂ k₂ (by decide)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok h₂.ws (by decide) (by decide)
    (by decide) h₂.args.q h₂.args.ql h₂.q L.qbl L.ql1 (by have := L.ql2; unfold wk; omega)) fun s₃ ⟨hv₃, o₃, k₃⟩ => ?_)
  have h₃ := h₂.arr (by decide) (Nat.le_refl _) o₃ k₃ (by decide)
  refine WP.mono (loadA_ok h₃.ws (by decide) (by decide) (by decide) h₃.args.d h₃.args.dl h₃.d L.dbl L.dl1
    (by have := L.dl2; unfold wk; omega)) fun t ⟨hv₄, o₄, k₄⟩ => ?_
  have h₄ := h₃.arr (by decide) (Nat.le_refl _) o₄ k₄ (by decide)
  refine ⟨h₄, ?_, ?_, ?_, ?_, hv₄⟩
  · rw [hm o₄, hm o₃, hm o₂, hm o₁]
  · rw [outside_arr o₄ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn,
      outside_arr o₃ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn,
      outside_arr o₂ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn]; exact hv₁
  · rw [outside_arr o₄ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn,
      outside_arr o₃ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn]; exact hv₂
  · rw [outside_arr o₄ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn]; exact hv₃

theorem mask_check {c : Bool} {A B1 B2 PQ : Prop} [Decidable A] [Decidable B1] [Decidable B2] [Decidable PQ]
    (h : A → ((A ∧ B1 ∧ B2) ↔ PQ)) (hA : ¬ A → ¬ PQ) :
    (decide A && (c && decide B1 && decide B2)) = (c && decide PQ) := by
  by_cases a : A
  · have := h a
    by_cases b1 : B1 <;> by_cases b2 : B2 <;> by_cases pq : PQ <;> simp_all
  · have := hA a
    simp_all

/-- `pqCheck`: the mask of `p q = n` and'ed into `sMask`, for an odd `n`. -/
theorem cvCheck_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {c : Bool}
    (hc : mword s.mem I.B = mask c) (hN : wv s.mem I.B (slot (wk I.k) aN) (wk I.k) % 2 = 1) :
    WP isa (seqs pqCheck) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mask (c && decide (wv s.mem I.B (slot (wk I.k) aP) (wk I.k) *
        wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) = wv s.mem I.B (slot (wk I.k) aN) (wk I.k))) ∧
      ∀ j, j = aP ∨ j = aQ ∨ j = aD → wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have k1 := L.k1
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have hmw : ∀ {m m' : Mem} {j L' : Nat}, Outside I.B (slot (wk I.k) j) L' m m' → L' ≤ 8 * (wk I.k + 2) →
      mword m' I.B = mword m I.B := fun {_ _ j _} o _ =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega))
      (by omega)
  simp only [pqCheck, List.cons_append, List.nil_append, List.append_assoc]
  -- `[u] := n`, then `divmod`.
  refine WP.seq (WP.mono (zeroA_ok h.ws (by decide)) fun s₁ ⟨_, o₁, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₁.ws (by decide) (by decide) (by decide)) fun s₂ ⟨hU₂, o₂, k₂⟩ => ?_)
  have h₂ := h₁.arr (by decide) (by omega) o₂ k₂ (by decide)
  have g₂ : ∀ j, j < 16 → j ≠ aU → wv s₂.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) :=
    fun j hj hne => by
      rw [outside_arr o₂ (by omega) hne (by omega) hj hZ hn, outside_arr o₁ (Nat.le_refl _) hne (by omega) hj hZ hn]
  rw [outside_arr o₁ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn] at hU₂
  refine WP.seq (WP.mono (divmod_ok h₂.ws.scr h₂.ws.rdi h₂.ws.hw h₂.ws.hS (by have := h₂.ws.w1; omega) h₂.ws.w2 hZ
    (iQ := aU) (iR := aV) (iD := aP) (iT := aT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨_, f₃, k₃, hv₃⟩ => ?_)
  have h₃ := h₂.step f₃ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Mut.ofSlot _ _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> exact h₂.ws.sl (by decide)) k₃ (by decide)
  have g₃ : ∀ j, j < 16 → j ≠ aU → j ≠ aV → j ≠ aT →
      wv s₃.mem I.B (slot (wk I.k) j) (wk I.k) = wv s₂.mem I.B (slot (wk I.k) j) (wk I.k) := fun j hj h1 h2 h3 =>
    f₃.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · have := slot_far (w := wk I.k) h1; omega
      · have := slot_far (w := wk I.k) h2; omega
      · have := slot_far (w := wk I.k) h3; omega) (by have := h.ws.sl hj; omega)
  have hm₃ : mword s₃.mem I.B = mask c := by
    have e : mword s₃.mem I.B = mword s₂.mem I.B := f₃.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · have := hdr_lt_slot (wk I.k) aU (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · have := hdr_lt_slot (wk I.k) aV (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · have := hdr_lt_slot (wk I.k) aT (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega) (by omega)
    exact e.trans ((hmw o₂ (by omega)).trans ((hmw o₁ (Nat.le_refl _)).trans hc))
  rw [hU₂] at hv₃
  rw [g₂ aP (by decide) (by decide)] at hv₃
  -- `rbp = 0` iff `n / p = q`.
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok h₃.ws (a := aU) (b := aQ) (by decide) (by decide))
    fun s₄ ⟨hz₄, m₄, k₄⟩ => ?_)
  have h₄ := h₃.step (rs := []) (by rw [m₄]; exact Frm.refl _ _ _) (by simp) (by simp) k₄ (by decide)
  refine WP.seq (WP.mono (andZero_ok (c := c) h₄.ws (by rw [m₄]; exact hm₃) hz₄) fun s₅ ⟨m₅, k₅⟩ => ?_)
  obtain ⟨h₅, hm₅, a₅⟩ := h₄.mask m₅ k₅ (by decide)
  -- `[c] := 0`, and `rbp = 0` iff `n mod p = 0`.
  refine WP.seq (WP.mono (zeroA_ok h₅.ws (j := aC) (by decide)) fun s₆ ⟨hz₆, o₆, k₆⟩ => ?_)
  have h₆ := h₅.arr (by decide) (Nat.le_refl _) o₆ k₆ (by decide)
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok h₆.ws (a := aV) (b := aC) (by decide) (by decide))
    fun s₇ ⟨hz₇, m₇, k₇⟩ => ?_)
  have h₇ := h₆.step (rs := []) (by rw [m₇]; exact Frm.refl _ _ _) (by simp) (by simp) k₇ (by decide)
  refine WP.seq (WP.mono (andZero_ok (c := c && decide (wv s₃.mem I.B (slot (wk I.k) aU) (wk I.k) =
    wv s₃.mem I.B (slot (wk I.k) aQ) (wk I.k))) h₇.ws (by rw [m₇]; exact (hmw o₆ (Nat.le_refl _)).trans hm₅) hz₇)
    fun s₈ ⟨m₈, k₈⟩ => ?_)
  obtain ⟨h₈, hm₈, a₈⟩ := h₇.mask m₈ k₈ (by decide)
  -- `p` odd.
  simp only [seqs]
  refine WP.mono (andOdd_ok h₈.ws (j := aP) (by decide) hm₈) fun t ⟨mt, kt⟩ => ?_
  obtain ⟨ht, hmt, at'⟩ := h₈.mask mt kt (by decide)
  -- What the arrays hold.
  have wvw : ∀ {m m' : Mem} {j : Nat}, j < 16 →
      wv m' I.B (slot (wk I.k) j) (wk I.k + 2) = wv m I.B (slot (wk I.k) j) (wk I.k + 2) →
      wv m' I.B (slot (wk I.k) j) (wk I.k) = wv m I.B (slot (wk I.k) j) (wk I.k) := fun {m m' j} _ e => by
    have e1 := wv_add m I.B (slot (wk I.k) j) (wk I.k) 2
    have e2 := wv_add m' I.B (slot (wk I.k) j) (wk I.k) 2
    have l1 := wv_lt m I.B (slot (wk I.k) j) (wk I.k)
    have l2 := wv_lt m' I.B (slot (wk I.k) j) (wk I.k)
    rw [e] at e2
    have := congrArg (· % 2 ^ (64 * wk I.k)) (e1.symm.trans e2)
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2] at this
    exact this.symm
  have eP₈ : wv s₈.mem I.B (slot (wk I.k) aP) (wk I.k) = wv s.mem I.B (slot (wk I.k) aP) (wk I.k) := by
    rw [wvw (by decide) (a₈ aP (by decide)), m₇, outside_arr o₆ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn,
      wvw (by decide) (a₅ aP (by decide)), m₄, g₃ aP (by decide) (by decide) (by decide) (by decide),
      g₂ aP (by decide) (by decide)]
  have eC : wv s₆.mem I.B (slot (wk I.k) aC) (wk I.k) = 0 := by
    have := wv_add s₆.mem I.B (slot (wk I.k) aC) (wk I.k) 2; omega
  have eV₆ : wv s₆.mem I.B (slot (wk I.k) aV) (wk I.k) = wv s₃.mem I.B (slot (wk I.k) aV) (wk I.k) := by
    rw [outside_arr o₆ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn, wvw (by decide) (a₅ aV (by decide)), m₄]
  rw [g₃ aQ (by decide) (by decide) (by decide) (by decide), g₂ aQ (by decide) (by decide)] at hz₄
  refine ⟨ht, ?_, fun j hj => ?_⟩
  · rw [hmt, eP₈]
    congr 1
    rw [eV₆, eC, g₃ aQ (by decide) (by decide) (by decide) (by decide), g₂ aQ (by decide) (by decide)]
    apply mask_check
    · intro hp
      have hP0 : 0 < wv s.mem I.B (slot (wk I.k) aP) (wk I.k) := by omega
      obtain ⟨e1, e2⟩ := hv₃ hP0
      have hlt : wv s₃.mem I.B (slot (wk I.k) aV) (wk I.k + 1) < 2 ^ (64 * wk I.k) := by
        rw [e1]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hP0) (Nat.le_of_lt (wv_lt _ _ _ _))
      rw [wv_low_of_lt (Nat.le_succ _) hlt, e1, e2]
      exact pq_iff hN
    · intro hp hpq
      exact hp ((pq_iff hN).mpr hpq).1
  · have hj' : j < 16 := by rcases hj with rfl | rfl | rfl <;> decide
    have e1 : j ≠ aU := by rcases hj with rfl | rfl | rfl <;> decide
    have e2 : j ≠ aV := by rcases hj with rfl | rfl | rfl <;> decide
    have e3 : j ≠ aT := by rcases hj with rfl | rfl | rfl <;> decide
    have e4 : j ≠ aC := by rcases hj with rfl | rfl | rfl <;> decide
    rw [wvw hj' (at' j hj'), wvw hj' (a₈ j hj'), m₇, outside_arr o₆ (Nat.le_refl _) e4 (by omega) hj' hZ hn,
      wvw hj' (a₅ j hj'), m₄, g₃ j hj' e1 e2 e3, g₂ j hj' e1]

end VG.Proof.Rsa.X86_64
