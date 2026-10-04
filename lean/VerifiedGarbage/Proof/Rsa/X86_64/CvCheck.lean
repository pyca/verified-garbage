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
    (k : Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : CvS I m₀ t ∧ mword t.mem I.B = v ∧
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

/-- `invSetup`: `inverse`'s start, `(u, v, x₁, x₂) := (q, p, 1, 0)`, with
the word of `u` above its `w` zero. -/
theorem invSetup_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) :
    WP isa (seqs invSetup) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      Bignum.X86_64.word t.mem I.B (slot (wk I.k) aU + 8 * wk I.k) = 0 ∧
      wv t.mem I.B (slot (wk I.k) aU) (wk I.k) = wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) ∧
      wv t.mem I.B (slot (wk I.k) aV) (wk I.k) = wv t.mem I.B (slot (wk I.k) aP) (wk I.k) ∧
      wv t.mem I.B (slot (wk I.k) aX₁) (wk I.k) = 1 ∧ wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) = 0 ∧
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
  -- The arrays a piece leaves: `ot j` from an `Outside` of another.
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, Outside I.B (slot (wk I.k) j) Ln m m' → Ln ≤ 8 * (wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (slot (wk I.k) i) (wk I.k) = wv m I.B (slot (wk I.k) i) (wk I.k) :=
    fun o hL hij hi => outside_arr o hL hij (by omega) hi hZ hn
  simp only [invSetup, seqs]
  -- `[u] := q`, `[v] := p`, `[x₁] := 1`, `[x₂] := 0`.
  refine WP.seq (WP.mono (zeroA_ok h.ws (j := aU) (by decide)) fun s₁ ⟨z₁, o₁, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₁.ws (o := aU) (a := aQ) (by decide) (by decide) (by decide)) fun s₂ ⟨c₂, o₂, k₂⟩ => ?_)
  have h₂ := h₁.arr (by decide) (by omega) o₂ k₂ (by decide)
  refine WP.seq (WP.mono (zeroA_ok h₂.ws (j := aV) (by decide)) fun s₃ ⟨z₃, o₃, k₃⟩ => ?_)
  have h₃ := h₂.arr (by decide) (Nat.le_refl _) o₃ k₃ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₃.ws (o := aV) (a := aP) (by decide) (by decide) (by decide)) fun s₄ ⟨c₄, o₄, k₄⟩ => ?_)
  have h₄ := h₃.arr (by decide) (by omega) o₄ k₄ (by decide)
  refine WP.seq (WP.mono (zeroA_ok h₄.ws (j := aX₁) (by decide)) fun s₅ ⟨z₅, o₅, k₅⟩ => ?_)
  have h₅ := h₄.arr (by decide) (Nat.le_refl _) o₅ k₅ (by decide)
  refine WP.seq (WP.mono (setOneA_ok h₅.ws (j := aX₁) (by decide)) fun s₆ ⟨m₆, k₆⟩ => ?_)
  have o₆ := writeW_outside s₅.mem I.B (1 : BitVec 64) (d := slot (wk I.k) aX₁) (by have := h.ws.sl (j := aX₁) (by decide); omega)
  rw [← m₆] at o₆
  have h₆ := h₅.arr (by decide) (by omega) o₆ k₆ (by decide)
  refine WP.mono (zeroA_ok h₆.ws (j := aX₂) (by decide)) fun s₇ ⟨z₇, o₇, k₇⟩ => ?_
  have h₇ := h₆.arr (by decide) (Nat.le_refl _) o₇ k₇ (by decide)
  -- The values the inverse starts from.
  have eP : ∀ {m : Mem}, m = s.mem → wv m I.B (slot (wk I.k) aP) (wk I.k) = wv s.mem I.B (slot (wk I.k) aP) (wk I.k) :=
    fun e => by rw [e]
  have vP₇ : wv s₇.mem I.B (slot (wk I.k) aP) (wk I.k) = wv s.mem I.B (slot (wk I.k) aP) (wk I.k) := by
    rw [ot o₇ (Nat.le_refl _) (by decide) (by decide), ot o₆ (by omega) (by decide) (by decide),
      ot o₅ (Nat.le_refl _) (by decide) (by decide), ot o₄ (by omega) (by decide) (by decide),
      ot o₃ (Nat.le_refl _) (by decide) (by decide), ot o₂ (by omega) (by decide) (by decide),
      ot o₁ (Nat.le_refl _) (by decide) (by decide)]
  have vQ₇ : wv s₇.mem I.B (slot (wk I.k) aQ) (wk I.k) = wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) := by
    rw [ot o₇ (Nat.le_refl _) (by decide) (by decide), ot o₆ (by omega) (by decide) (by decide),
      ot o₅ (Nat.le_refl _) (by decide) (by decide), ot o₄ (by omega) (by decide) (by decide),
      ot o₃ (Nat.le_refl _) (by decide) (by decide), ot o₂ (by omega) (by decide) (by decide),
      ot o₁ (Nat.le_refl _) (by decide) (by decide)]
  have vU₇ : wv s₇.mem I.B (slot (wk I.k) aU) (wk I.k) = wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) := by
    rw [ot o₇ (Nat.le_refl _) (by decide) (by decide), ot o₆ (by omega) (by decide) (by decide),
      ot o₅ (Nat.le_refl _) (by decide) (by decide), ot o₄ (by omega) (by decide) (by decide),
      ot o₃ (Nat.le_refl _) (by decide) (by decide), c₂, ot o₁ (Nat.le_refl _) (by decide) (by decide)]
  have vV₇ : wv s₇.mem I.B (slot (wk I.k) aV) (wk I.k) = wv s₇.mem I.B (slot (wk I.k) aP) (wk I.k) := by
    rw [vP₇, ot o₇ (Nat.le_refl _) (by decide) (by decide), ot o₆ (by omega) (by decide) (by decide),
      ot o₅ (Nat.le_refl _) (by decide) (by decide), c₄, ot o₃ (Nat.le_refl _) (by decide) (by decide),
      ot o₂ (by omega) (by decide) (by decide), ot o₁ (Nat.le_refl _) (by decide) (by decide)]
  have vX₂ : wv s₇.mem I.B (slot (wk I.k) aX₂) (wk I.k) = 0 := by
    have := wv_add s₇.mem I.B (slot (wk I.k) aX₂) (wk I.k) 2; omega
  have vX₁ : wv s₇.mem I.B (slot (wk I.k) aX₁) (wk I.k) = 1 := by
    rw [ot o₇ (Nat.le_refl _) (by decide) (by decide), m₆, wv_low (by have := h.ws.w1; omega), word_writeW_self,
      (writeW_outside s₅.mem I.B (1 : BitVec 64) (d := slot (wk I.k) aX₁) (by
        have := h.ws.sl (j := aX₁) (by decide); omega)).wv (Or.inr (by omega)) (by have := h.ws.sl (j := aX₁) (by decide); omega)]
    have hz : ∀ q < wk I.k + 2, Bignum.X86_64.word s₅.mem I.B (slot (wk I.k) aX₁ + 8 * q) = 0 :=
      (wv_eq_zero_iff _ _ _ _).mp z₅
    rw [wv_zero (n := wk I.k - 1) fun q hq => by
      have := hz (1 + q) (by omega)
      rwa [show slot (wk I.k) aX₁ + 8 * (1 + q) = slot (wk I.k) aX₁ + 8 + 8 * q by omega] at this]
    rfl
  have vU0 : Bignum.X86_64.word s₇.mem I.B (slot (wk I.k) aU + 8 * wk I.k) = 0 := by
    have e1 : Bignum.X86_64.word s₂.mem I.B (slot (wk I.k) aU + 8 * wk I.k) = 0 := by
      rw [o₂.word (Or.inr (by omega)) (by have := h.ws.sl (j := aU) (by decide); omega)]
      exact (wv_eq_zero_iff _ _ _ _).mp z₁ (wk I.k) (by omega)
    have r := fun {j Ln : Nat} {m m' : Mem} (o : Outside I.B (slot (wk I.k) j) Ln m m') (hL : Ln ≤ 8 * (wk I.k + 2))
        (hj : j ≠ aU) (hj' : j < 16) =>
      o.word (d := slot (wk I.k) aU + 8 * wk I.k) (by have := slot_far (w := wk I.k) hj; omega)
        (by have := h.ws.sl (j := aU) (by decide); omega)
    rw [r o₇ (Nat.le_refl _) (by decide) (by decide), r o₆ (by omega) (by decide) (by decide),
      r o₅ (Nat.le_refl _) (by decide) (by decide), r o₄ (by omega) (by decide) (by decide),
      r o₃ (Nat.le_refl _) (by decide) (by decide)]
    exact e1
  refine ⟨h₇, (hmw o₇ (Nat.le_refl _)).trans ((hmw o₆ (by omega)).trans ((hmw o₅ (Nat.le_refl _)).trans
    ((hmw o₄ (by omega)).trans ((hmw o₃ (Nat.le_refl _)).trans ((hmw o₂ (by omega)).trans
      (hmw o₁ (Nat.le_refl _))))))), vU0, vU₇, vV₇, vX₁, vX₂, fun j hj => ?_⟩
  rcases hj with rfl | rfl | rfl
  · exact vP₇
  · exact vQ₇
  · rw [ot o₇ (Nat.le_refl _) (by decide) (by decide), ot o₆ (by omega) (by decide) (by decide),
      ot o₅ (Nat.le_refl _) (by decide) (by decide), ot o₄ (by omega) (by decide) (by decide),
      ot o₃ (Nat.le_refl _) (by decide) (by decide), ot o₂ (by omega) (by decide) (by decide),
      ot o₁ (Nat.le_refl _) (by decide) (by decide)]

/-- `invPart`: `qInv` into `aX₂` and `gcd(q, p) = 1` and'ed into `sMask`,
for a mask that is set only if `p` is odd and above 1. -/
theorem cvInv_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {c : Bool}
    (hc : mword s.mem I.B = mask c)
    (hcP : c = true → wv s.mem I.B (slot (wk I.k) aP) (wk I.k) % 2 = 1 ∧ 1 < wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) :
    WP isa (seqs invPart) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mask (c && decide (Nat.gcd (wv s.mem I.B (slot (wk I.k) aQ) (wk I.k))
        (wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) = 1)) ∧
      (c = true → ((wv s.mem I.B (slot (wk I.k) aP) (wk I.k) : Nat) : Int) ∣
          (wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) : Int) * wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) -
            Nat.gcd (wv s.mem I.B (slot (wk I.k) aQ) (wk I.k)) (wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) ∧
        wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) < wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) ∧
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
  -- The arrays a piece leaves: `ot j` from an `Outside` of another.
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, Outside I.B (slot (wk I.k) j) Ln m m' → Ln ≤ 8 * (wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (slot (wk I.k) i) (wk I.k) = wv m I.B (slot (wk I.k) i) (wk I.k) :=
    fun o hL hij hi => outside_arr o hL hij (by omega) hi hZ hn
  simp only [invPart]
  refine wp_seqs_append (by simp [invSetup]) (by simp) (WP.mono (invSetup_ok h L)
    fun s₇ ⟨h₇, m₇, vU0, vU₇, vV₇, vX₁, vX₂, p₇⟩ => ?_)
  have vP₇ := p₇ aP (.inl rfl)
  have vQ₇ := p₇ aQ (.inr (.inl rfl))
  have vD₇ := p₇ aD (.inr (.inr rfl))
  simp only [List.cons_append, List.nil_append]
  -- The inverse.
  refine WP.seq (WP.mono (inverse_ok h₇.ws.scr h₇.ws.rdi h₇.ws.hw h₇.ws.hS (by have := h₇.ws.w1; omega) h₇.ws.w2 hZ
    (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aP) (iT := aT) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) vU0 vV₇ vX₁ vX₂)
    fun s₈ ⟨_, f₈, k₈, hv₈⟩ => ?_)
  have h₈ := h₇.step f₈ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Mut.ofSlot _ _ _
    · exact Mut.ofSlot _ _ _
    · exact Mut.ofSlot _ _ _
    · exact Mut.ofSlot _ _ _
    · exact Mut.ofSlot _ _ _
    · exact Or.inr (Or.inr rfl)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have := h.ws.sl (j := aT) (by decide)
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · have := h.ws.sl (j := aU) (by decide); omega
    · have := h.ws.sl (j := aV) (by decide); omega
    · have := h.ws.sl (j := aX₁) (by decide); omega
    · have := h.ws.sl (j := aX₂) (by decide); omega
    · omega
    · have := hdr_lt_slot (wk I.k) 0 (show sMo < 32 by decide); have := h.ws.sl (j := 0) (by decide)
      unfold sMo sFn at *; omega) k₈ (by decide)
  rw [vU₇, vP₇] at hv₈
  have f8 : ∀ j, j < 16 → j ≠ aU → j ≠ aV → j ≠ aX₁ → j ≠ aX₂ → j ≠ aT →
      wv s₈.mem I.B (slot (wk I.k) j) (wk I.k) = wv s₇.mem I.B (slot (wk I.k) j) (wk I.k) := fun j hj h1 h2 h3 h4 h5 =>
    f₈.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
      · have := slot_far (w := wk I.k) h1; omega
      · have := slot_far (w := wk I.k) h2; omega
      · have := slot_far (w := wk I.k) h3; omega
      · have := slot_far (w := wk I.k) h4; omega
      · have := slot_far (w := wk I.k) h5; omega
      · have := hdr_lt_slot (wk I.k) j (show sMo < 32 by decide); omega) (by have := h.ws.sl hj; omega)
  have hm₈ : mword s₈.mem I.B = mask c := by
    have e8 : mword s₈.mem I.B = mword s₇.mem I.B := f₈.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
      · have := hdr_lt_slot (wk I.k) aU (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · have := hdr_lt_slot (wk I.k) aV (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · have := hdr_lt_slot (wk I.k) aX₁ (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · have := hdr_lt_slot (wk I.k) aX₂ (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · have := hdr_lt_slot (wk I.k) aT (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · simp only [sMo, sFn]; omega) (by omega)
    exact e8.trans (m₇.trans hc)
  -- `[c] := 1`, and the mask of `[v] = 1`.
  refine WP.seq (WP.mono (zeroA_ok h₈.ws (j := aC) (by decide)) fun s₉ ⟨z₉, o₉, k₉⟩ => ?_)
  have h₉ := h₈.arr (by decide) (Nat.le_refl _) o₉ k₉ (by decide)
  refine WP.seq (WP.mono (setOneA_ok h₉.ws (j := aC) (by decide)) fun s₁₀ ⟨m₁₀, k₁₀⟩ => ?_)
  have o₁₀ := writeW_outside s₉.mem I.B (1 : BitVec 64) (d := slot (wk I.k) aC) (by have := h.ws.sl (j := aC) (by decide); omega)
  rw [← m₁₀] at o₁₀
  have h₁₀ := h₉.arr (by decide) (by omega) o₁₀ k₁₀ (by decide)
  have vC : wv s₁₀.mem I.B (slot (wk I.k) aC) (wk I.k) = 1 := by
    rw [m₁₀, wv_low (by have := h.ws.w1; omega), word_writeW_self,
      (writeW_outside s₉.mem I.B (1 : BitVec 64) (d := slot (wk I.k) aC) (by
        have := h.ws.sl (j := aC) (by decide); omega)).wv (Or.inr (by omega)) (by have := h.ws.sl (j := aC) (by decide); omega)]
    have hz : ∀ q < wk I.k + 2, Bignum.X86_64.word s₉.mem I.B (slot (wk I.k) aC + 8 * q) = 0 :=
      (wv_eq_zero_iff _ _ _ _).mp z₉
    rw [wv_zero (n := wk I.k - 1) fun q hq => by
      have := hz (1 + q) (by omega)
      rwa [show slot (wk I.k) aC + 8 * (1 + q) = slot (wk I.k) aC + 8 + 8 * q by omega] at this]
    rfl
  have vV₁₀ : wv s₁₀.mem I.B (slot (wk I.k) aV) (wk I.k) = wv s₈.mem I.B (slot (wk I.k) aV) (wk I.k) := by
    rw [ot o₁₀ (by omega) (by decide) (by decide), ot o₉ (Nat.le_refl _) (by decide) (by decide)]
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok h₁₀.ws (a := aV) (b := aC) (by decide) (by decide))
    fun s₁₁ ⟨hz₁₁, m₁₁, k₁₁⟩ => ?_)
  have h₁₁ := h₁₀.step (rs := []) (by rw [m₁₁]; exact Frm.refl _ _ _) (by simp) (by simp) k₁₁ (by decide)
  rw [vC, vV₁₀] at hz₁₁
  simp only [seqs]
  refine WP.mono (andZero_ok (c := c) h₁₁.ws (by rw [m₁₁]; exact (hmw o₁₀ (by omega)).trans ((hmw o₉ (Nat.le_refl _)).trans hm₈)) hz₁₁)
    fun t ⟨mt, kt⟩ => ?_
  obtain ⟨ht, hmt, at'⟩ := h₁₁.mask mt kt (by decide)
  have tX : ∀ j, j < 16 → j ≠ aC → wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s₈.mem I.B (slot (wk I.k) j) (wk I.k) :=
    fun j hj hne => by
      rw [wvw hj (at' j hj), m₁₁, ot o₁₀ (by omega) hne hj, ot o₉ (Nat.le_refl _) hne hj]
  refine ⟨ht, ?_, fun hcT => ?_, fun j hj => ?_⟩
  · rw [hmt]
    congr 1
    cases c
    · rfl
    · obtain ⟨hp, hp1⟩ := hcP rfl
      rw [(hv₈ hp hp1).1]
  · obtain ⟨hp, hp1⟩ := hcP hcT
    obtain ⟨e1, e2, e3⟩ := hv₈ hp hp1
    rw [tX aX₂ (by decide) (by decide)]
    exact ⟨e1 ▸ e2, e3⟩
  · have hj' : j < 16 := by rcases hj with rfl | rfl | rfl <;> decide
    rw [tX j hj' (by rcases hj with rfl | rfl | rfl <;> decide)]
    rcases hj with rfl | rfl | rfl
    · rw [f8 aP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), vP₇]
    · rw [f8 aQ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), vQ₇]
    · rw [f8 aD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), vD₇]

/-- `decA j`: the low word of `[j]` minus one. -/
theorem decA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 16) :
    WP isa (.block (decA j)) s fun t =>
      t.mem = s.mem.writeW (off B (slot w j)) (Bignum.X86_64.word s.mem B (slot w j) - 1) ∧
        Keep [.r12, .r9, .rbx, .rax] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  unfold decA
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨_, e9, n₁, j₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok j (r := .rbx) (by decide) ((j₁.gpr (by decide)).trans h.rdi) e9)
    fun t₂ ⟨hbx, n₂, j₂⟩ => ?_
  have hs₂ := h.scr.congr (j₁.trans j₂).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B (slot w j))
    (Bignum.X86_64.word s.mem B (slot w j) - 1)) (by
    xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₂.ld (d := slot w j) (by omega), hs₂.st (d := slot w j) (by omega), n₂, n₁]) rfl)
    fun t ⟨mt, j₃⟩ => ⟨mt, ((j₁.trans j₂).trans j₃).mono (by simp)⟩

/-- `divisor j ++ [divmod]`: `[aV] := d mod ([j] - 1)`, for an odd `[j]`. -/
theorem cvDivPart_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {j : Nat} (hj : j = aP ∨ j = aQ) :
    WP isa (seqs (divisor j ++ [divmod aU aV aC aT])) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (wv s.mem I.B (slot (wk I.k) j) (wk I.k) % 2 = 1 → 1 < wv s.mem I.B (slot (wk I.k) j) (wk I.k) →
        wv t.mem I.B (slot (wk I.k) aV) (wk I.k + 1) =
          wv s.mem I.B (slot (wk I.k) aD) (wk I.k) % (wv s.mem I.B (slot (wk I.k) j) (wk I.k) - 1)) ∧
      ∀ i, i = aP ∨ i = aQ ∨ i = aD ∨ i = aX₁ ∨ i = aX₂ →
        wv t.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have k1 := L.k1
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have hj16 : j < 16 := by rcases hj with rfl | rfl <;> decide
  have hjC : j ≠ aC := by rcases hj with rfl | rfl <;> decide
  have hjU : j ≠ aU := by rcases hj with rfl | rfl <;> decide
  have hmw : ∀ {m m' : Mem} {i L' : Nat}, Outside I.B (slot (wk I.k) i) L' m m' → L' ≤ 8 * (wk I.k + 2) →
      mword m' I.B = mword m I.B := fun {_ _ i _} o _ =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) i (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega))
      (by omega)
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, Outside I.B (slot (wk I.k) j) Ln m m' → Ln ≤ 8 * (wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (slot (wk I.k) i) (wk I.k) = wv m I.B (slot (wk I.k) i) (wk I.k) :=
    fun o hL hij hi => outside_arr o hL hij (by omega) hi hZ hn
  simp only [divisor, List.cons_append, List.nil_append]
  -- `[c] := [j]`, minus one.
  refine WP.seq (WP.mono (zeroA_ok h.ws (j := aC) (by decide)) fun s₁ ⟨_, o₁, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₁.ws (o := aC) (a := j) (by decide) hj16 (Ne.symm hjC)) fun s₂ ⟨c₂, o₂, k₂⟩ => ?_)
  have h₂ := h₁.arr (by decide) (by omega) o₂ k₂ (by decide)
  rw [ot o₁ (Nat.le_refl _) hjC hj16] at c₂
  -- The low word.
  have sC := h.ws.sl (j := aC) (by decide)
  refine WP.seq (WP.mono (decA_ok h₂.ws (j := aC) (by decide)) fun s₃ ⟨m₃, k₃⟩ => ?_)
  have o₃ := writeW_outside s₂.mem I.B (Bignum.X86_64.word s₂.mem I.B (slot (wk I.k) aC) - 1)
    (d := slot (wk I.k) aC) (by omega)
  rw [← m₃] at o₃
  have h₃ := h₂.arr (by decide) (by omega) o₃ k₃ (by decide)
  -- `[c] = [j] - 1` for an odd `[j]`.
  have vC₃ : wv s₂.mem I.B (slot (wk I.k) aC) (wk I.k) % 2 = 1 →
      wv s₃.mem I.B (slot (wk I.k) aC) (wk I.k) = wv s₂.mem I.B (slot (wk I.k) aC) (wk I.k) - 1 := by
    have w1 := h.ws.w1
    have e3 := wv_low (m := s₃.mem) (B := I.B) (e := slot (wk I.k) aC) (w := wk I.k) (by omega)
    have e2 := wv_low (m := s₂.mem) (B := I.B) (e := slot (wk I.k) aC) (w := wk I.k) (by omega)
    have hw3 : Bignum.X86_64.word s₃.mem I.B (slot (wk I.k) aC) =
        Bignum.X86_64.word s₂.mem I.B (slot (wk I.k) aC) - 1 := by
      rw [m₃, word_writeW_self]
    have hup : wv s₃.mem I.B (slot (wk I.k) aC + 8) (wk I.k - 1) = wv s₂.mem I.B (slot (wk I.k) aC + 8) (wk I.k - 1) := by
      rw [m₃]; exact (writeW_outside s₂.mem I.B _ (by omega)).wv (Or.inr (by omega)) (by omega)
    intro ho
    rw [e2] at ho ⊢
    have hodd : (Bignum.X86_64.word s₂.mem I.B (slot (wk I.k) aC)).toNat % 2 = 1 := by omega
    have hsub : (Bignum.X86_64.word s₂.mem I.B (slot (wk I.k) aC) - 1).toNat =
        (Bignum.X86_64.word s₂.mem I.B (slot (wk I.k) aC)).toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; rfl
    rw [e3, hup, hw3, hsub]
    omega
  rw [c₂] at vC₃
  -- `[u] := d`.
  refine WP.seq (WP.mono (zeroA_ok h₃.ws (j := aU) (by decide)) fun s₄ ⟨_, o₄, k₄⟩ => ?_)
  have h₄ := h₃.arr (by decide) (Nat.le_refl _) o₄ k₄ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₄.ws (o := aU) (a := aD) (by decide) (by decide) (by decide)) fun s₅ ⟨c₅, o₅, k₅⟩ => ?_)
  have h₅ := h₄.arr (by decide) (by omega) o₅ k₅ (by decide)
  -- `divmod`.
  simp only [seqs]
  refine WP.mono (divmod_ok h₅.ws.scr h₅.ws.rdi h₅.ws.hw h₅.ws.hS (by have := h₅.ws.w1; omega) h₅.ws.w2 hZ
    (iQ := aU) (iR := aV) (iD := aC) (iT := aT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨_, f₆, k₆, hv₆⟩ => ?_
  have ht := h₅.step f₆ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Mut.ofSlot _ _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> exact h.ws.sl (by decide)) k₆ (by decide)
  have f6 : ∀ i, i < 16 → i ≠ aU → i ≠ aV → i ≠ aT →
      wv t.mem I.B (slot (wk I.k) i) (wk I.k) = wv s₅.mem I.B (slot (wk I.k) i) (wk I.k) := fun i hi h1 h2 h3 =>
    f₆.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · have := slot_far (w := wk I.k) h1; omega
      · have := slot_far (w := wk I.k) h2; omega
      · have := slot_far (w := wk I.k) h3; omega) (by have := h.ws.sl hi; omega)
  have back : ∀ i, i < 16 → i ≠ aC → i ≠ aU → wv s₅.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k) :=
    fun i hi h1 h2 => by
      rw [ot o₅ (by omega) h2 hi, ot o₄ (Nat.le_refl _) h2 hi, ot o₃ (by omega) h1 hi, ot o₂ (by omega) h1 hi,
        ot o₁ (Nat.le_refl _) h1 hi]
  refine ⟨ht, ?_, fun ho h1 => ?_, fun i hi => ?_⟩
  · have e6 : mword t.mem I.B = mword s₅.mem I.B := f₆.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · have := hdr_lt_slot (wk I.k) aU (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · have := hdr_lt_slot (wk I.k) aV (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · have := hdr_lt_slot (wk I.k) aT (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega) (by omega)
    exact e6.trans ((hmw o₅ (by omega)).trans ((hmw o₄ (Nat.le_refl _)).trans ((hmw o₃ (by omega)).trans
      ((hmw o₂ (by omega)).trans (hmw o₁ (Nat.le_refl _))))))
  · have hC : wv s₅.mem I.B (slot (wk I.k) aC) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) - 1 := by
      rw [ot o₅ (by omega) (by decide) (by decide), ot o₄ (Nat.le_refl _) (by decide) (by decide)]
      exact vC₃ ho
    have hU : wv s₅.mem I.B (slot (wk I.k) aU) (wk I.k) = wv s.mem I.B (slot (wk I.k) aD) (wk I.k) := by
      rw [c₅, ot o₄ (Nat.le_refl _) (by decide) (by decide), ot o₃ (by omega) (by decide) (by decide),
        ot o₂ (by omega) (by decide) (by decide), ot o₁ (Nat.le_refl _) (by decide) (by decide)]
    have hpos : 0 < wv s₅.mem I.B (slot (wk I.k) aC) (wk I.k) := by
      rw [hC]; omega
    rw [(hv₆ hpos).1, hU, hC]
  · have hi16 : i < 16 := by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [f6 i hi16 (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide),
      back i hi16 (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)]

end VG.Proof.Rsa.X86_64
