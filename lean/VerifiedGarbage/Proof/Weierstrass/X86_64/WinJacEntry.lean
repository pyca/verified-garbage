import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacDbls

/-!
# The Jacobian window method on x86-64: the entry of a digit

Digit `j = rbx` as the comb reads it (`digit_ok`, windows of 5 bits of
`k' = k + offset J`): its magnitude `a = |k'_j - 16|` selects entry `a` of the
table into `T` (`jselect_ok`, zeros for `a = 0`), whose `Y` is negated for a
negative digit (`negY`, as the comb's), so that `T` holds digit `j`'s point
`winPt` with its powers, or `Z = 0` for the digit zero (`jentry_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- The table of bits survives the method. -/
theorem JFrame.bits (hL : JacWinLay K size) {base : Addr} {s₀ s : State} {P : Point C} {k : Nat}
    (hF : JacWinFixed K C base s₀ P k) (hf : JFrame K C base size s₀ s) :
    ∀ t < 5 * K.J, s.mem (off base (K.bits + t)) = if (k + JacWinCfg.offset K.J).testBit t then 1 else 0 := by
  intro t ht
  have hb := hL.bits
  have hn := hf.scr.nowrap
  rw [hf.unch.byte (fun w hw => by have := hL.bits_w w hw; omega) (by omega)]
  exact hF.bits t ht

/-- What `T` holds after the selection and the negation, from `s`: its powers
always (zero for a zero digit), and digit `j`'s point for a nonzero one. -/
structure JEnt (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (k' j : Nat) (s t : State) : Prop where
  fr : JFrame K C base size s₀ t
  unch : Unch base ((List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)) ++
    [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)]) s.mem t.mem
  keep : KeepRegs (clob K.M.n) s t
  lt : ∀ c < 5, wordsVal t.mem base (TS K c) K.M.n < C.p
  z2 : tmv C K.M.n base t (TS K 3) = tmv C K.M.n base t (TS K 2) * tmv C K.M.n base t (TS K 2)
  z3 : tmv C K.M.n base t (TS K 4) = tmv C K.M.n base t (TS K 3) * tmv C K.M.n base t (TS K 2)
  ent : 1 ≤ magH 16 (Window5.nib k' j) → JPt C K.M.n base t (TS K) (Window5.winPt C P k' j)
  zero : magH 16 (Window5.nib k' j) = 0 → tmv C K.M.n base t (TS K 2) = 0

theorem jent_loopW (K : JacWinCfg) : ∀ w ∈ (List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)) ++
    [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)], w ∈ jwLoopW K := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw; exact T_loopW K (List.mem_range.mp hc)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact other_loopW (by jw_mem)
    · exact tmp_loopW

/-- Digit `j`'s entry into `T`, negated for a negative digit. -/
theorem jentry_ok (hL : JacWinLay K size) {base : Addr} {P : Point C} {s₀ : State} {k : Nat}
    (hF : JacWinFixed K C base s₀ P k) {s : State} {j : Nat} (hj : j < K.J)
    (hf : JFrame K C base size s₀ s) (hT : JTblOk K C base P 16 s) (hb : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block (K.tc.digit ++ K.select)) s fun s₂ =>
      WP isa (.block K.tc.negY) s₂ (JEnt K C base size P s₀ (k + JacWinCfg.offset K.J) j s) := by
  have hs := hf.scr
  have hn := hs.nowrap
  have hbl := hL.bits
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) (hF.ro_lt K.P.x (by simp))
  have hbits := hf.bits hL hF
  generalize hk' : k + JacWinCfg.offset K.J = k' at hbits
  have hwj : 5 * j + 5 ≤ 5 * K.J := by omega
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok K.tc hs (k := k') (j := j) (N := 5 * K.J) (by show 1 ≤ 5; decide)
    (by show 5 < 9; decide) hwj (by show K.bits + 5 * K.J ≤ size; omega) hb hbits) fun s₁ ⟨_, r₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hwin : combWin K.tc.w k' j = Window5.nib k' j := Window5.combWin_five k' j
  have hH : K.tc.H = 16 := rfl
  rw [hwin, hH] at r₁
  generalize ha : magH 16 (Window5.nib k' j) = a at r₁
  have ha16 : a ≤ 16 := by rw [← ha]; exact magH_le (by have := Window5.nib_lt k' j; omega)
  refine WP.mono (jselect_ok hL hs₁ r₁ ha16) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  rw [m₁] at e₂
  have U₂ : Unch base (jwLoopW K) s.mem s₂.mem := by
    rw [← m₁]; exact (outside_grid5 (b := 80) O₂).mono fun w hw => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw; exact T_loopW K (List.mem_range.mp hc)
  have F₂ := hf.next hL hs₂ (((Keeps.regs k₁).mono (sub_powClob (by decide))).trans
    (k₂.mono (sub_powClob (by decide)))) U₂ (jwLoopW_sub K)
  -- The negation.
  obtain ⟨tx, ty, tz, t2, t3⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, m2, m3⟩ := hL.T_mem
  have hneg : K.neg ∈ jwSlots K := by jw_mem
  have hzero : K.zero ∈ jwSlots K := by jw_mem
  have hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by rw [F₂.ro hL (by jw_mem)]; exact hF.zero
  have hy₂ : wordsVal s₂.mem base K.E.y K.M.n < C.p := by
    rw [← ty, e₂ 1 (by decide)]
    split
    · exact (hT a (by omega) ha16).lt 1 (by decide)
    · exact hp0
  have hyneg : K.E.y + 8 * K.M.n ≤ K.neg ∨ K.neg + 8 * K.M.n ≤ K.E.y := by
    rw [hL.Ty]; exact (hL.jg_apart (x := K.neg) (by jw_mem) (by decide)).symm
  rw [TCombCfg.negY, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sub_ok hs₂ F₂.mod (o := K.neg) (a := K.zero) (b := K.E.y) (hL.le hneg) (hL.le hzero)
    (hL.le my) (hL.lay.tmp _ hneg) (hL.lay.tmp _ hzero) (hL.lay.tmp _ my) (hL.lay.mo _ hneg)
    (by rw [hz₂]; exact hp0) hy₂) fun s₃ ⟨k₃, e₃⟩ => ?_
  have hs₃ := k₃.scr hs₂
  have hbits₃ : ∀ t < 5 * K.J, s₃.mem (off base (K.bits + t)) = if k'.testBit t then 1 else 0 := by
    intro t ht
    rw [k₃.unch.byte (fun w hw => by
      have hw' : w ∈ jwW K := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact mem_jwW_ws (other_ws (by jw_mem))
        · exact mem_jwW_tmp
      have := hL.bits_w w hw'; omega) (by omega)]
    have := F₂.bits hL hF t ht; rw [hk'] at this; exact this
  rw [WP.block_append_iff]
  refine WP.mono (signMask_ok K.tc hs₃ (k := k') (j := j) (N := 5 * K.J) (by show 1 ≤ 5; decide)
    (by show 5 < 2 ^ 31; decide) hwj (by show K.bits + 5 * K.J ≤ size; omega) (by rw [k₃.gpr _ (rbx_not_clob _), k₂.gpr _ (by decide),
      k₁.1 _ (by decide), hb]) hbits₃) fun s₄ ⟨x₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [hwin] at x₄
  refine WP.mono (sel_ok (decide (Window5.nib k' j < 2 ^ (K.tc.w - 1))) K.M.n hs₄ x₄ (o := K.E.y)
    (a := K.E.y) (b := K.neg) (hL.le my) (hL.le my) (hL.le hneg) (Or.inl (Nat.le_refl _))
    (by omega)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  have b64 : ∀ x ∈ jwSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by have := hL.le hx; omega
  -- `T`'s words: as at `s₂` but `Y`.
  have keepT : ∀ c < 5, c ≠ 1 → wordsVal s₅.mem base (TS K c) K.M.n = wordsVal s₂.mem base (TS K c) K.M.n := by
    intro c hc h1
    have hy : TS K c + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ TS K c := by
      rw [hL.Ty]; exact jg_sep K (by omega)
    rw [O₅.wordsVal hy (b64 _ (jg_mem (by omega))), m₄, k₃.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact (hL.jg_apart (x := K.neg) (by jw_mem) (i := 80 + c) (by omega)).symm
      · exact hL.lay.tmp _ (jg_mem (by omega))) (b64 _ (jg_mem (by omega)))]
  have y₃ : wordsVal s₃.mem base K.E.y K.M.n = wordsVal s₂.mem base K.E.y K.M.n :=
    k₃.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hyneg
      · exact hL.lay.tmp _ my) (b64 _ my)
  have keepY : wordsVal s₅.mem base (TS K 1) K.M.n = if decide (Window5.nib k' j < 2 ^ (K.tc.w - 1)) then
      (0 + C.p - wordsVal s₂.mem base K.E.y K.M.n) % C.p else wordsVal s₂.mem base K.E.y K.M.n := by
    rw [ty, e₅, m₄, e₃, hz₂, y₃]
  have tv : ∀ {x y : Nat}, wordsVal s₅.mem base x K.M.n = wordsVal s₂.mem base y K.M.n →
      tmv C K.M.n base s₅ x = tmv C K.M.n base s₂ y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
  -- `T` at `s₂`: entry `a`, or zeros.
  have e₂' : ∀ c < 5, wordsVal s₂.mem base (TS K c) K.M.n =
      if 1 ≤ a then wordsVal s.mem base (entS K a c) K.M.n else 0 := fun c hc => e₂ c hc
  have T₂z : ∀ c < 5, ¬ 1 ≤ a → tmv C K.M.n base s₂ (TS K c) = 0 := fun c hc h => by
    show toM _ _ _ = _; rw [e₂' c hc, ite_eq_right_of_eq_false _ _ (eq_false h)]; exact toM_zero _ _
  have T₂ : 1 ≤ a → JPt C K.M.n base s₂ (TS K) (mul a P) := fun h =>
    (hT a h ha16).congr fun c hc => by rw [e₂' c hc, ite_eq_left_of_eq_true _ _ (eq_true h)]
  have hU : Unch base ((List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)) ++
      [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)]) s.mem s₅.mem := by
    rw [← m₁]
    refine (((outside_grid5 (b := 80) O₂).trans k₃.unch).trans (m₄ ▸ O₅.unch)).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with (h | h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · rw [h, hL.Ty]; exact Or.inl (List.mem_map.mpr ⟨1, by decide, rfl⟩)
  have hcl : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ clob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [clob]
    · simp [clob]
    · simp [clob]
    · exact r8_mem_clob _
  have kk : KeepRegs (clob K.M.n) s s₅ :=
    ((((Keeps.regs k₁).mono hcl).trans (k₂.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]))).trans
      ((⟨k₃.gpr, k₃.rd, k₃.wr⟩ : KeepRegs (clob K.M.n) s₂ s₃).trans ((Keeps.regs k₄).mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h])))).trans
      (k₅.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]))
  have h16 : (2 : Nat) ^ (K.tc.w - 1) = 16 := rfl
  rw [h16] at keepY
  have lt₂ : ∀ c < 5, wordsVal s₂.mem base (TS K c) K.M.n < C.p := fun c hc => by
    rw [e₂' c hc]; split
    · exact (hT a ‹_› ha16).lt c hc
    · exact hp0
  have tz : ∀ c < 5, c ≠ 1 → tmv C K.M.n base s₅ (TS K c) = tmv C K.M.n base s₂ (TS K c) :=
    fun c hc h1 => tv (keepT c hc h1)
  refine ⟨hf.next hL hs₅ (kk.mono clob_powClob) hU (fun w hw => jwLoopW_sub K w (jent_loopW K w hw)), hU,
    kk, fun c hc => ?_, ?_, ?_, fun h => ?_, fun h => ?_⟩
  · by_cases h1 : c = 1
    · subst h1; rw [keepY]; split
      · exact Nat.mod_lt _ hp0
      · exact hy₂
    · rw [keepT c hc h1]; exact lt₂ c hc
  · rw [tz 3 (by decide) (by decide), tz 2 (by decide) (by decide)]
    by_cases h1 : 1 ≤ a
    · exact (T₂ h1).z2
    · rw [T₂z 3 (by decide) h1, T₂z 2 (by decide) h1]; exact (Lean.Grind.Semiring.mul_zero 0).symm
  · rw [tz 4 (by decide) (by decide), tz 3 (by decide) (by decide), tz 2 (by decide) (by decide)]
    by_cases h1 : 1 ≤ a
    · exact (T₂ h1).z3
    · rw [T₂z 4 (by decide) h1, T₂z 3 (by decide) h1, T₂z 2 (by decide) h1]
      exact (Lean.Grind.Semiring.mul_zero 0).symm
  · rw [ha] at h
    have J₂ := T₂ h
    rw [Window5.winPt_mag, ha]
    by_cases hng : Window5.nib k' j < 16
    · simp only [decide_eq_true hng, ↓reduceIte]
      simp only [decide_eq_true hng, ↓reduceIte] at keepY
      have hy : tmv C K.M.n base s₅ (TS K 1) = -tmv C K.M.n base s₂ (TS K 1) := by
        show toM _ _ _ = -toM _ _ _
        rw [keepY, toM_sub (by omega), toM_zero, ty]
        grind
      refine ⟨fun c hc => ?_, ?_, ?_, ?_, ?_⟩
      · by_cases h1 : c = 1
        · subst h1; rw [keepY]; exact Nat.mod_lt _ hp0
        · rw [keepT c hc h1]; exact lt₂ c hc
      · rw [tz 0 (by decide) (by decide), tz 2 (by decide) (by decide), hy]; exact J₂.jac.negY
      · rw [tz 2 (by decide) (by decide)]; exact J₂.z
      · rw [tz 3 (by decide) (by decide), tz 2 (by decide) (by decide)]; exact J₂.z2
      · rw [tz 4 (by decide) (by decide), tz 3 (by decide) (by decide), tz 2 (by decide) (by decide)]
        exact J₂.z3
    · simp only [decide_eq_false hng, Bool.false_eq_true, ↓reduceIte]
      simp only [decide_eq_false hng, Bool.false_eq_true, ↓reduceIte] at keepY
      rw [← ty] at keepY
      exact J₂.congr fun c hc => by
        by_cases h1 : c = 1
        · subst h1; exact keepY
        · exact keepT c hc h1
  · rw [tz 2 (by decide) (by decide)]
    exact T₂z 2 (by decide) (by rw [ha] at h; omega)

end VG.Proof.Weierstrass.X86_64
