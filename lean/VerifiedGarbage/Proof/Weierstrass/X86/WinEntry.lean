import VerifiedGarbage.Proof.Weierstrass.X86.WinSelect

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

variable {F : Spec.Weierstrass.Mont.Modulus}

theorem combWin_four (k i : Nat) : combWin 4 k i = nib k i := by
  unfold combWin nib; rw [Nat.pow_mul]

/-- After the selection and the negation: `E` represents the point of digit
`i`, and only `E`, `-y` and the temporary area changed. -/
structure EntryPostW (K : WinCfg) (wk : Nat) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (k i : Nat)
    (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs clob s s'
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
    (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n), (wk, 64 * K.M.n), Mont.outW] s.mem s'.mem
  lt : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s'.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s' K.E.x) (tmv C K.M.n base s' K.E.y) (tmv C K.M.n base s' K.E.z)
    (winPt C P k i)

theorem mul_zero_pt' {C : Curve} (P : Point C) : mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; simp

/-- The digit's magnitude, its entry from the table, and its `y` negated for a
negative digit. -/
theorem winEntry_ok {K : WinCfg} {C : Curve} {base : Addr} {size wk k i : Nat} (hL : WinLay K size) (hAcc : WinWk K F C.p size wk)
    (hC : Law C) {P : Point C} (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base) (hi : i < K.J) (hx : s.gpr .esi = BitVec.ofNat 32 i)
    (hbits : ∀ t < 4 * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal s.mem base K.zero K.M.n = 0) (hT : TblOk K C base P 8 s) :
    WP isa (.block ((WinCfg.tc K F).digit ++ WinCfg.select K)) s fun s₂ =>
      WP isa (WinCfg.tc K F).negY s₂ (EntryPostW K wk C base size P k i s) := by
  have hn := hs.nowrap
  have hJ := hL.J
  have h0 := hL.n0
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hone_lt
  obtain ⟨-, -, -, -, exy, exz, eyz, hEo, -, -⟩ := hL.other_ne
  have wE : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x ∈ winWs K := fun x hx => winOther_ws K x (winE_mem x hx)
  have le : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x + 8 * K.M.n ≤ size := fun x hx =>
    hL.lay.le x (winOther_mem (winE_mem x hx))
  have tmp : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x + 8 * K.M.n ≤ K.M.tmp ∨ K.M.tmp + 8 * K.M.n ≤ x :=
    fun x hx => hL.lay.tmp x (winOther_mem (winE_mem x hx))
  have mo : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x + 8 * K.M.n ≤ K.M.mo ∨ K.M.mo + 8 * K.M.n ≤ x :=
    fun x hx => hL.lay.mo x (winOther_mem (winE_mem x hx))
  have neN : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ≠ K.neg := fun x hx e => hEo x hx (by rw [e]; simp)
  have yneg := hL.apart₂ (wE K.E.y (by simp)) (wE K.neg (by simp)) (neN _ (by simp))
  have xneg := hL.apart₂ (wE K.E.x (by simp)) (wE K.neg (by simp)) (neN _ (by simp))
  have zneg := hL.apart₂ (wE K.E.z (by simp)) (wE K.neg (by simp)) (neN _ (by simp))
  have xy := hL.apart₂ (wE K.E.x (by simp)) (wE K.E.y (by simp)) exy
  have xz := hL.apart₂ (wE K.E.x (by simp)) (wE K.E.z (by simp)) exz
  have yz := hL.apart₂ (wE K.E.y (by simp)) (wE K.E.z (by simp)) eyz
  have hbs := hL.bits
  have hEx := le K.E.x (by simp)
  have hEy := le K.E.y (by simp)
  have hEz := le K.E.z (by simp)
  have hneg := le K.neg (by simp)
  have hzs : K.zero ∈ winSlots K := winRo_slots K _ (by simp [winRo])
  have hzl := hL.lay.le K.zero hzs
  have hwi : 4 * i + 4 ≤ 4 * K.J := by omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok (WinCfg.tc K F) hs (k := k) (j := i) (N := 4 * K.J) (by show 1 ≤ 4; decide)
    (by show 4 < 9; decide) hwi
    hL.bits hx hbits) fun s₁ ⟨_, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁.keeps (by decide)
  have hx₁ : s₁.gpr .esi = BitVec.ofNat 32 i := by rw [k₁.1 _ (by decide), hx]
  have hw4 : combWin 4 k i = nib k i := combWin_four k i
  have hmag : magH 8 (nib k i) ≤ 8 := magH_le (by have := nib_lt k i; omega_arith)
  have m₁' : s₁.gpr .ebx = BitVec.ofNat 32 (magH 8 (nib k i)) := by
    rw [m₁, show (WinCfg.tc K F).H = 8 from rfl, show (WinCfg.tc K F).w = 4 from rfl, hw4]
  refine WP.mono (winSelect_ok hL hs₁ (Nat.lt_trans hone_lt hpn) m₁' hmag)
    fun s₂ S₂ => ?_
  obtain ⟨ex₂, ey₂, ez₂, k₂, U₂⟩ := S₂
  change Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s₁.mem s₂.mem at U₂
  rw [k₁.2.1] at ex₂ ey₂ ez₂ U₂
  generalize ha : magH 8 (nib k i) = a at ex₂ ey₂ ez₂ hmag
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have hmoE : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)],
      K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · have := mo K.E.x (by simp); dsimp only; omega_arith
    · have := mo K.E.y (by simp); dsimp only; omega_arith
    · have := mo K.E.z (by simp); dsimp only; omega_arith
  have hM₂ : ModOkW K.M size C.p s₂.mem base := hM.unch U₂ hmoE (by omega_arith)
  have hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by
    have hzW := hL.ro_w (x := K.zero) (by simp [winRo])
    rw [U₂.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;>
        exact hzW _ (List.mem_append_left _ (List.mem_map_of_mem (wE _ (by simp))))) (by omega_arith), hz]
  -- The entry's numbers, below `p`.
  have Ta := fun (h : 1 ≤ a) => hT a h hmag
  have hEy₂ : wordsVal s₂.mem base K.E.y K.M.n < C.p := by
    rw [ey₂]; split
    · exact (Ta ‹_›).1 _ (by simp)
    · exact hone_lt
  -- The negation.
  rw [TCombCfg.negY]
  refine WP.seq (WP.mono (subC_ok hAcc.acc.toCallCfg hs₂ (o := K.neg) (a := K.zero) (b := K.E.y)
    (hAcc.acc.sl _ (winOther_mem (winE_mem _ (by simp)))) (hAcc.acc.sl _ hzs)
    (hAcc.acc.sl _ (winOther_mem (winE_mem _ (by simp))))
    (by rw [hz₂]; exact hp0) hEy₂) fun s₃ ⟨k₃, e₃⟩ => ?_)
  have hs₃ : Scr s₃ base size := k₃.scr hs₂
  have U₃ := k₃.unch
  change Unch base [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n), (wk, 64 * K.M.n), Mont.outW] s₂.mem s₃.mem at U₃
  have hx₃ : s₃.gpr .esi = BitVec.ofNat 32 i := by
    rw [k₃.gpr _ (esi_not_clob), k₂.gpr _ (by decide), hx₁]
  have hbW : ∀ w ∈ winW K, K.bits + 4 * K.J ≤ w.1 ∨ w.1 + w.2 ≤ K.bits := hL.bits_w
  have hbits₃ : ∀ t < 4 * K.J, s₃.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    have hW : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], K.bits + 4 * K.J ≤ x ∨ x + 8 * K.M.n ≤ K.bits := fun x hx =>
      hbW _ (List.mem_append_left _ (List.mem_map_of_mem (wE x hx)))
    have hT' := hbW _ (List.mem_append_right _ (List.mem_singleton_self (K.M.tmp, 8 * K.M.n)))
    rw [U₃.byte (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · have := hW K.neg (by simp); dsimp only; omega_arith
        · dsimp only at hT' ⊢; omega_arith
        · have := hAcc.bits; dsimp only; omega_arith
        · have := hAcc.acc.size; dsimp only [Mont.outW]; omega_arith) (by omega_arith),
      U₂.byte (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · have := hW K.E.x (by simp); dsimp only; omega_arith
        · have := hW K.E.y (by simp); dsimp only; omega_arith
        · have := hW K.E.z (by simp); dsimp only; omega_arith) (by omega_arith)]
    exact hbits t ht
  rw [WP.block_append_iff]
  refine WP.mono (signMask_ok (WinCfg.tc K F) hs₃ (k := k) (j := i) (N := 4 * K.J) (by show 1 ≤ 4; decide)
    (by show 4 < 2 ^ 31; decide) hwi
    hL.bits hx₃ hbits₃) fun s₄ ⟨x₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄.keeps (by decide)
  refine WP.mono (selWords_ok (n := K.M.n) hs₄ (decide (combWin (WinCfg.tc K F).w k i < 2 ^ ((WinCfg.tc K F).w - 1))) x₄
    (o := K.E.y) (a := K.E.y) (b := K.neg) hEy hEy hneg (Or.inl (Nat.le_refl _)) (by omega_arith))
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  rw [show (WinCfg.tc K F).w = 4 from rfl, hw4] at e₅
  -- The values.
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have vx : wordsVal s₅.mem base K.E.x K.M.n = wordsVal s₂.mem base K.E.x K.M.n := by
    rw [O₅.wordsVal (by omega_arith) (by omega_arith), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · dsimp only; omega_arith
      · have := tmp K.E.x (by simp); dsimp only; omega_arith
      · exact Or.inl (hAcc.acc.sl _ (winOther_mem (winE_mem _ (by simp))))
      · have := hAcc.acc.sl _ (winOther_mem (winE_mem K.E.x (by simp))); have := hAcc.wk_le
        exact Or.inl (by dsimp only [Mont.outW]; omega_arith)) (by omega_arith)]
  have vz : wordsVal s₅.mem base K.E.z K.M.n = wordsVal s₂.mem base K.E.z K.M.n := by
    rw [O₅.wordsVal (by omega_arith) (by omega_arith), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · dsimp only; omega_arith
      · have := tmp K.E.z (by simp); dsimp only; omega_arith
      · exact Or.inl (hAcc.acc.sl _ (winOther_mem (winE_mem _ (by simp))))
      · have := hAcc.acc.sl _ (winOther_mem (winE_mem K.E.z (by simp))); have := hAcc.wk_le
        exact Or.inl (by dsimp only [Mont.outW]; omega_arith)) (by omega_arith)]
  have vy₃ : wordsVal s₃.mem base K.E.y K.M.n = wordsVal s₂.mem base K.E.y K.M.n :=
    U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · dsimp only; omega_arith
      · have := tmp K.E.y (by simp); dsimp only; omega_arith
      · exact Or.inl (hAcc.acc.sl _ (winOther_mem (winE_mem _ (by simp))))
      · have := hAcc.acc.sl _ (winOther_mem (winE_mem K.E.y (by simp))); have := hAcc.wk_le
        exact Or.inl (by dsimp only [Mont.outW]; omega_arith)) (by omega_arith)
  have vy : wordsVal s₅.mem base K.E.y K.M.n = if decide (nib k i < 2 ^ (4 - 1)) then
      (0 + C.p - wordsVal s₂.mem base K.E.y K.M.n) % C.p else wordsVal s₂.mem base K.E.y K.M.n := by
    rw [e₅, m₄, e₃, hz₂, vy₃]
  -- The point the selected entry represents: `[a]P` (`O` for `0`).
  have hR : Rep C (tmv C K.M.n base s₂ K.E.x) (tmv C K.M.n base s₂ K.E.y) (tmv C K.M.n base s₂ K.E.z)
      (mul a P) := by
    show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [ex₂, ey₂, ez₂]
    by_cases h1 : 1 ≤ a
    · simp only [h1, ↓reduceIte]
      exact (Ta h1).2
    · have h0 : a = 0 := by omega_arith
      subst h0
      simp only [show ¬ 1 ≤ 0 by omega_arith, ↓reduceIte, toM_zero, hone, mul_zero_pt']
      exact rep_infinity' hC
  have hcl : ∀ r ∈ [Reg.eax, .ecx, .edx, .ebx], r ∈ clob := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [clob]
    · simp [clob]
    · simp [clob]
    · simp [clob]
  refine ⟨hs₄.of_keepRegs k₅ (by decide), ?_, ?_, ?_, ?_⟩
  · exact (((((k₁.keeps).mono hcl).trans (k₂.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))).trans
      ⟨k₃.gpr, k₃.rd, k₃.wr⟩).trans ((k₄.keeps).mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))).trans
      (k₅.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]))
  · refine ((U₂.trans (U₃.trans (m₄ ▸ O₅.unch))).mono ?_)
    intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx, ex₂]; split
      · exact (Ta ‹_›).1 _ (by simp)
      · exact hp0
    · rw [vy]; split
      · exact Nat.mod_lt _ hp0
      · exact hEy₂
    · rw [vz, ez₂]; split
      · exact (Ta ‹_›).1 _ (by simp)
      · exact hp0
  · have ex : tmv C K.M.n base s₅ K.E.x = tmv C K.M.n base s₂ K.E.x := by
      show toM _ _ _ = toM _ _ _; rw [vx]
    have ez : tmv C K.M.n base s₅ K.E.z = tmv C K.M.n base s₂ K.E.z := by
      show toM _ _ _ = toM _ _ _; rw [vz]
    rw [ex, ez]
    unfold winPt
    by_cases h8 : 8 ≤ nib k i
    · have hy : tmv C K.M.n base s₅ K.E.y = tmv C K.M.n base s₂ K.E.y := by
        show toM _ _ _ = toM _ _ _
        rw [vy, decide_eq_false (show ¬ nib k i < 2 ^ (4 - 1) by omega_arith)]; rfl
      rw [hy]
      simp only [h8, ↓reduceIte]
      have : a = nib k i - 8 := by rw [← ha, magH]; simp [h8]
      rw [this] at hR
      exact hR
    · have hy : tmv C K.M.n base s₅ K.E.y = -tmv C K.M.n base s₂ K.E.y := by
        show toM _ _ _ = -toM _ _ _
        rw [vy, decide_eq_true (show nib k i < 2 ^ (4 - 1) by omega_arith)]
        simp only [↓reduceIte]
        rw [toM_sub (by omega_arith), toM_zero]
        grind
      rw [hy]
      simp only [h8, ↓reduceIte]
      have : a = 8 - nib k i := by rw [← ha, magH]; simp [h8]
      rw [this] at hR
      exact Rep.negY hR

end VG.Proof.Weierstrass.X86
