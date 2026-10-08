import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase

/-!
# The window method on AArch64: the entry of a digit

The entry of a digit, selected in constant time, its `y` negated for a negative digit
(`winEntry_ok`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-! ## The entry of a digit -/

theorem tblSlot_eq (K : WinCfg) (c i : Nat) : tblSlot K c i = K.tbl + 8 * K.M.n * (3 * i + c) := by
  unfold tblSlot; grind

theorem tblSlot_pt (K : WinCfg) (a : Nat) :
    tblSlot K 0 (a - 1) = (K.tblPt a).x ∧ tblSlot K 1 (a - 1) = (K.tblPt a).y ∧
      tblSlot K 2 (a - 1) = (K.tblPt a).z := by
  simp only [tblSlot, WinCfg.tblPt]; omega_using []

theorem winSelect_eq (K : WinCfg) : WinCfg.select K =
    (List.range K.M.n).flatMap (WinCfg.selectWord K 0 K.E.x) ++
    ((List.range K.M.n).flatMap (WinCfg.selectWord K 1 K.E.y) ++
    (List.range K.M.n).flatMap (WinCfg.selectWord K 2 K.E.z)) := by
  simp only [WinCfg.select, List.append_assoc]

/-- After the selection and the negation: `E` represents the point of digit
`i`, and only `E`, `-y` and the temporary area changed. -/
structure EntryPostW (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (k i : Nat)
    (s s' : State) : Prop where
  scr : Scr s' base size
  x19 : s'.gpr .x19 = s.gpr .x19
  keep : KeepRegs (combClob K.M.n) s s'
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
    (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)] s.mem s'.mem
  lt : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s'.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s' K.E.x) (tmv C K.M.n base s' K.E.y) (tmv C K.M.n base s' K.E.z)
    (winPt C P k i)

theorem winE_mem {K : WinCfg} : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x ∈ winOther K := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> win_in

theorem mul_zero_pt' {C : Curve} (P : Point C) : mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; simp

/-- The digit's masks, its entry from the table, and its `y` negated for a
negative digit. -/
theorem winEntry_ok {K : WinCfg} {C : Curve} {base : Addr} {size k i : Nat} (hL : WinLay K size)
    (hA : WinA K) (hC : Law C) {P : Point C} (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base) (hi : i < K.J) (hx : s.gpr .x19 = BitVec.ofNat 64 i)
    (hbits : ∀ t < 4 * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal s.mem base K.zero K.M.n = 0) (hT : TblOk K C base P 8 s) :
    WP isa (.block (digit K.bits ++ WinCfg.select K ++ negY K.M K.neg K.zero K.E.y K.bits)) s
      (EntryPostW K C base size P k i s) := by
  have hn := hs.nowrap
  have hJ := hL.J
  have h0 := hL.n0
  have hmag := mag_le (nib_lt k i)
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hone_lt
  obtain ⟨-, -, -, -, exy, exz, eyz, hEo, -, -⟩ := hL.other_ne
  have wE : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x ∈ winWs K := fun x hx => winOther_ws K x (winE_mem x hx)
  have le : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x + 8 * K.M.n ≤ size := fun x hx =>
    hL.lay.le x (winOther_mem (winE_mem x hx))
  have al : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x % 8 = 0 := fun x hx =>
    hA.sl x (winOther_mem (winE_mem x hx))
  have xy := hL.apart₂ (wE K.E.x (by simp)) (wE K.E.y (by simp)) exy
  have xz := hL.apart₂ (wE K.E.x (by simp)) (wE K.E.z (by simp)) exz
  have yz := hL.apart₂ (wE K.E.y (by simp)) (wE K.E.z (by simp)) eyz
  have neN : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ≠ K.neg := fun x hx e => hEo x hx (by rw [e]; simp)
  have xneg := hL.apart₂ (wE K.E.x (by simp)) (wE K.neg (by simp)) (neN _ (by simp))
  have yneg := hL.apart₂ (wE K.E.y (by simp)) (wE K.neg (by simp)) (neN _ (by simp))
  have zneg := hL.apart₂ (wE K.E.z (by simp)) (wE K.neg (by simp)) (neN _ (by simp))
  -- The table's slots, apart from `E`.
  have hslot : ∀ c < 3, ∀ i' < 8, tblSlot K c i' + 8 * K.M.n ≤ size ∧ tblSlot K c i' % 8 = 0 := by
    intro c hc i' hi'
    rw [tblSlot_eq]
    have hm : K.tbl + 8 * K.M.n * (3 * i' + c) ∈ winSlots K := by
      simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K (by omega_using [hc, hi']))
    exact ⟨hL.lay.le _ hm, hA.sl _ hm⟩
  have hsep : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], ∀ c < 3, ∀ i' < 8,
      tblSlot K c i' + 8 * K.M.n ≤ x ∨ x + 8 * K.M.n ≤ tblSlot K c i' := by
    intro x hx c hc i' hi'
    rw [tblSlot_eq]
    exact (hL.tbl_apart (List.mem_append_right _ (winE_mem x hx)) (i := 3 * i' + c) (by omega_using [hc, hi'])).symm
  have sub3 : ∀ o ∈ [K.E.x, K.E.y, K.E.z], o ∈ [K.E.x, K.E.y, K.E.z, K.neg] := by
    intro o ho; simp only [List.mem_cons, List.not_mem_nil, or_false] at ho ⊢
    rcases ho with h | h | h <;> simp [h]
  have hd : ∀ c < 3, ∀ o ∈ [K.E.x, K.E.y, K.E.z], ∀ i' < 8, tblSlot K c i' + 8 * K.M.n ≤ size ∧
      tblSlot K c i' % 8 = 0 ∧ (tblSlot K c i' + 8 * K.M.n ≤ o ∨ o + 8 * K.M.n ≤ tblSlot K c i') :=
    fun c hc o ho i' hi' => ⟨(hslot c hc i' hi').1, (hslot c hc i' hi').2,
      hsep o (sub3 o ho) c hc i' hi'⟩
  -- The digit's masks.
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (digit_ok hs K.bits (k := k) (j := i) (N := 4 * K.J) (by omega_using [hi]) hL.bits hA.bits4 hx
    hbits) fun s₁ ⟨m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : MasksOf s₁ (mag (nib k i)) := m₁
  -- The entry.
  rw [winSelect_eq, List.append_assoc, WP.block_append_iff]
  have W2 := selectCoord_ok hs₁ K hmag hm₁ (c := 0) (o := K.E.x) (al _ (by simp)) (le _ (by simp))
    (hd 0 (by decide) K.E.x (by simp)) (Nat.lt_trans hone_lt hpn)
  refine WP.mono W2 fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  have W3 := selectCoord_ok hs₂ K hmag (hm₁.keepRegs k₂) (c := 1) (o := K.E.y) (al _ (by simp))
    (le _ (by simp)) (hd 1 (by decide) K.E.y (by simp)) (Nat.lt_trans hone_lt hpn)
  refine WP.mono W3 fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  have W4 := selectCoord_ok hs₃ K hmag ((hm₁.keepRegs k₂).keepRegs k₃) (c := 2) (o := K.E.z)
    (al _ (by simp)) (le _ (by simp)) (hd 2 (by decide) K.E.z (by simp)) (Nat.lt_trans hone_lt hpn)
  refine WP.mono W4 fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  -- The table's numbers, unchanged by the selection.
  have tb : ∀ c < 3, ∀ i' < 8, ∀ {m m' : Mem} {o : Nat}, o ∈ [K.E.x, K.E.y, K.E.z] →
      Outside base o (8 * K.M.n) m m' →
      wordsVal m' base (tblSlot K c i') K.M.n = wordsVal m base (tblSlot K c i') K.M.n :=
    fun c hc i' hi' m m' o ho O => O.wordsVal (hsep o (sub3 o ho) c hc i' hi')
      (by have := (hslot c hc i' hi').1; omega_using [hn, this])
  have m₁ : s₁.mem = s.mem := k₁.mem
  -- What `E` holds, from the table at `s`.
  have vx : wordsVal s₄.mem base K.E.x K.M.n = (if mag (nib k i) = 0 then 0 else
      wordsVal s.mem base (tblSlot K 0 (mag (nib k i) - 1)) K.M.n) := by
    rw [O₄.wordsVal xz (by have := le K.E.x (by simp); omega_using [hn, this]),
      O₃.wordsVal xy (by have := le K.E.x (by simp); omega_using [hn, this]), e₂, m₁]
    rfl
  have vy : wordsVal s₄.mem base K.E.y K.M.n = (if mag (nib k i) = 0 then K.one else
      wordsVal s.mem base (tblSlot K 1 (mag (nib k i) - 1)) K.M.n) := by
    rw [O₄.wordsVal yz (by have := le K.E.y (by simp); omega_using [hn, this]), e₃]
    split
    · rfl
    · rw [tb 1 (by decide) _ (by omega_using [hmag]) (o := K.E.x) (by simp) O₂, m₁]
  have vz : wordsVal s₄.mem base K.E.z K.M.n = (if mag (nib k i) = 0 then 0 else
      wordsVal s.mem base (tblSlot K 2 (mag (nib k i) - 1)) K.M.n) := by
    rw [e₄]
    split
    · rfl
    · rw [tb 2 (by decide) _ (by omega_using [hmag]) (o := K.E.y) (by simp) O₃,
        tb 2 (by decide) _ (by omega_using [hmag]) (o := K.E.x) (by simp) O₂, m₁]
  have U₄ : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem s₄.mem := by
    rw [← m₁]; exact (O₂.unch.trans (O₃.unch.trans O₄.unch)).mono (by simp)
  have hEW : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)], w ∈ winW K := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [winW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨_, wE _ (by simp), rfl⟩
    · exact Or.inl ⟨_, wE _ (by simp), rfl⟩
    · exact Or.inl ⟨_, wE _ (by simp), rfl⟩
    · exact Or.inl ⟨_, wE _ (by simp), rfl⟩
    · exact Or.inr rfl
  have U₄' : Unch base (winW K) s.mem s₄.mem := U₄.mono fun w hw => hEW w (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢; rcases hw with h | h | h <;> simp [h])
  have hM₄ : ModOkA K.M size C.p s₄.mem base := hM.unch U₄' (winW_mo hL hM) hn
  have hz₄ : wordsVal s₄.mem base K.zero K.M.n = 0 := by
    rw [hL.ro_val U₄' hn (by simp [winRo]), hz]
  -- The entry's numbers, below `p`.
  have Ta := fun (h : mag (nib k i) ≠ 0) => hT (mag (nib k i)) (by omega_using [h]) hmag
  have hpt := tblSlot_pt K (mag (nib k i))
  have hEy₄ : wordsVal s₄.mem base K.E.y K.M.n < C.p := by
    rw [vy]; split
    · exact hone_lt
    · rename_i h; rw [hpt.2.1]; exact (Ta h).1 _ (by simp)
  -- The negation.
  rw [negY, List.append_assoc, WP.block_append_iff]
  have hneg := le K.neg (by simp)
  have hzl := hL.lay.le K.zero (winRo_slots K _ (by simp [winRo]))
  have W5 := sub_ok hs₄ hM₄ hA.mod (o := K.neg) (a := K.zero) (b := K.E.y) hneg hzl
    (le _ (by simp)) (al _ (by simp)) (hA.sl _ (winRo_slots K _ (by simp [winRo]))) (al _ (by simp))
    (by rw [hz₄]; exact hp0) hEy₄
  refine WP.mono W5 fun s₅ h₅ => ?_
  obtain ⟨k₅, e₅⟩ := h₅
  have hs₅ : Scr s₅ base size := ⟨(k₅.gpr _ (x0_not_clob _)).trans hs₄.x0, k₅.wr ▸ hs₄.wr,
    hs₄.nowrap, hs₄.enc⟩
  have U₅ := k₅.unch
  have U₄₅ : Unch base (winW K) s.mem s₅.mem := (U₄'.trans U₅).mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · exact hEW w (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢; grind)
  have hx₅ : s₅.gpr .x19 = BitVec.ofNat 64 i := by
    rw [k₅.gpr _ (x19_not_clob _), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide),
      k₁.gpr _ (by decide), hx]
  have hbits₅ : ∀ t < 4 * K.J, s₅.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      have := hL.bits
      rw [U₄₅.byte (fun w hw => by have := hL.bits_w w hw; omega_using [ht, this]) (by omega_using [hn, ht, this])]; exact hbits t ht
  rw [WP.block_append_iff]
  have W6 := signMask_ok hs₅ K.bits (k := k) (j := i) (N := 4 * K.J) (by omega_using [hi]) hL.bits hA.bits4 hx₅
    hbits₅
  refine WP.mono W6 fun s₆ h₆ => ?_
  obtain ⟨x₆, k₆⟩ := h₆
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  have W7 := sel_ok (decide (nib k i < 8)) K.M.n hs₆ (by rw [x₆]; rfl) (o := K.E.y) (a := K.E.y)
    (b := K.neg) (le _ (by simp)) (le _ (by simp)) hneg (al _ (by simp)) (al _ (by simp))
    (al _ (by simp)) (Or.inl (Nat.le_refl _)) (by omega_using [yneg])
  refine WP.mono W7 fun s₇ h₇ => ?_
  obtain ⟨e₇, k₇, O₇⟩ := h₇
  have m₆ : s₆.mem = s₅.mem := k₆.mem
  have pt : ∀ x ∈ [(K.E.x, 8 * K.M.n), (K.E.z, 8 * K.M.n)], ∀ w ∈ [(K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)], x.1 + x.2 ≤ w.1 ∨ w.1 + w.2 ≤ x.1 := by
    intro x hx w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hw
    rcases hx with rfl | rfl <;> rcases hw with rfl | rfl <;> dsimp only
    · exact xneg
    · exact hL.lay.tmp _ (winOther_mem (winE_mem _ (by simp)))
    · exact zneg
    · exact hL.lay.tmp _ (winOther_mem (winE_mem _ (by simp)))
  have lx := le K.E.x (by simp)
  have lz := le K.E.z (by simp)
  have ly := le K.E.y (by simp)
  have vx₇ : wordsVal s₇.mem base K.E.x K.M.n = wordsVal s₄.mem base K.E.x K.M.n := by
    rw [O₇.wordsVal (by omega_using [xy]) (by omega_using [hn, lx]), m₆,
      U₅.wordsVal (pt (K.E.x, 8 * K.M.n) (by simp)) (by omega_using [hn, lx])]
  have vz₇ : wordsVal s₇.mem base K.E.z K.M.n = wordsVal s₄.mem base K.E.z K.M.n := by
    rw [O₇.wordsVal (by omega_using [yz]) (by omega_using [hn, lz]), m₆,
      U₅.wordsVal (pt (K.E.z, 8 * K.M.n) (by simp)) (by omega_using [hn, lz])]
  have vy₅ : wordsVal s₅.mem base K.E.y K.M.n = wordsVal s₄.mem base K.E.y K.M.n :=
    U₅.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> dsimp only
      · exact yneg
      · exact hL.lay.tmp _ (winOther_mem (winE_mem _ (by simp)))) (by omega_using [hn, ly])
  have vy₇ : wordsVal s₇.mem base K.E.y K.M.n = if decide (nib k i < 8) then
      (0 + C.p - wordsVal s₄.mem base K.E.y K.M.n) % C.p else wordsVal s₄.mem base K.E.y K.M.n := by
    rw [e₇, m₆, e₅, hz₄, vy₅]
  refine ⟨hs₆.of_keepRegs k₇ (by decide), ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₇.gpr _ (by decide), k₆.gpr _ (by decide), k₅.gpr _ (x19_not_clob _), k₄.gpr _ (by decide),
      k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  · have c1 : ∀ r ∈ clob K.M.n, r ∈ combClob K.M.n := fun r hr =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hr))
    refine (((((((Keeps.regs k₁).mono ?_).trans ((k₂.trans (k₃.trans k₄)).mono ?_)).trans
      ((⟨k₅.gpr, k₅.rd, k₅.wr, k₅.sp⟩ : KeepRegs (clob K.M.n) s₄ s₅).mono c1)).trans
      ((Keeps.regs k₆).mono ?_)).trans (k₇.mono ?_)))
    · intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | rfl | rfl | rfl | hr
      · exact combClob_mem (by simp)
      · exact combClob_mem (by simp)
      · simp [combClob]
      · exact combClob_mem (by simp)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hr))
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [combClob, clob]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [combClob, clob]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [combClob, clob]
  · refine ((U₄.trans (U₅.trans (m₆ ▸ O₇.unch))).mono ?_)
    intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx₇, vx]; split
      · exact hp0
      · rename_i h; rw [hpt.1]; exact (Ta h).1 _ (by simp)
    · rw [vy₇]; split
      · exact Nat.mod_lt _ hp0
      · exact hEy₄
    · rw [vz₇, vz]; split
      · exact hp0
      · rename_i h; rw [hpt.2.2]; exact (Ta h).1 _ (by simp)
  · -- The point: `[|d|]P` (`O` for `0`), reflected for a negative digit.
    have hR : Rep C (toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base K.E.x K.M.n))
        (toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base K.E.y K.M.n))
        (toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base K.E.z K.M.n)) (mul (mag (nib k i)) P) := by
      rw [vx, vy, vz]
      by_cases h : mag (nib k i) = 0
      · simp only [h, ↓reduceIte, toM_zero, hone, mul_zero_pt']
        exact rep_infinity' hC
      · simp only [h, ↓reduceIte]
        rw [hpt.1, hpt.2.1, hpt.2.2]
        exact (Ta h).2
    have ex : tmv C K.M.n base s₇ K.E.x = toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base K.E.x K.M.n) := by
      show toM _ _ _ = _; rw [vx₇]
    have ez : tmv C K.M.n base s₇ K.E.z = toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base K.E.z K.M.n) := by
      show toM _ _ _ = _; rw [vz₇]
    rw [ex, ez]
    unfold winPt
    by_cases h8 : 8 ≤ nib k i
    · have hy : tmv C K.M.n base s₇ K.E.y = toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base K.E.y K.M.n) := by
        show toM _ _ _ = _
        rw [vy₇, decide_eq_false (show ¬ nib k i < 8 by omega_using [h8])]; rfl
      rw [hy]
      simp only [h8, ↓reduceIte]
      have : mag (nib k i) = nib k i - 8 := by simp [mag, h8]
      rw [this] at hR
      exact hR
    · have hy : tmv C K.M.n base s₇ K.E.y = -toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base K.E.y K.M.n) := by
        show toM _ _ _ = _
        rw [vy₇, decide_eq_true (show nib k i < 8 by omega_using [h8])]
        simp only [↓reduceIte]
        rw [toM_sub (by omega_using [hEy₄]), toM_zero]
        grind
      rw [hy]
      simp only [h8, ↓reduceIte]
      have : mag (nib k i) = 8 - nib k i := by simp [mag, h8]
      rw [this] at hR
      exact Rep.negY hR

end VG.Proof.Weierstrass.AArch64
