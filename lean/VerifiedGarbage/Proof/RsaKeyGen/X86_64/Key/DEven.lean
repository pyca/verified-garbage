import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.DOdd

/-!
# An RSA key from its primes on x86-64: `d` for an even `e`

`d = (e mod L)⁻¹ mod L` for an odd `L ≥ 3`, by `inverse` modulo `L` (or
3 otherwise) (`dEven_k`, `inverse_even`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem dEven_eq : dEven = loadEv ++ ([zeroA aM, copyA aM aL] ++ (constA 0 ++ (eqMask aL aC ++
    (([.block [.mov .r15 (.reg .rbp)]] : List (Prog isa)) ++ (constA 1 ++
    (([.block (ws ++ base aM .rbx ++ base aC .r10 ++ ([.mov .rax (.mem (at0 .rbx)), .mov .rdx (.reg .r15),
        .alu .and .rdx (.imm 1), .alu .or .rax (.reg .rdx), .store (at0 .rbx) .rax] : List Instr)),
      zeroA aQt, copyA aQt aE, divmod aQt aR aM aT, zeroA aU, copyA aU aR] : List (Prog isa)) ++ (constA 3 ++ (ltA aL aC ++
    (([.block (([.mov .rcx (.reg .rbp), .alu .xor .rcx (.imm (BitVec.ofInt 32 (-1)))] : List Instr) ++ oddMask aL ++
        ([.alu .and .rax (.reg .rcx), .store (hdr kOk) .rax, .mov .rbp (.reg .rax)] : List Instr)),
      zeroA aM, copyA aM aL] : List (Prog isa)) ++ (selC aM ++ (invFrom aM ++ ([inverse aU aV aX₁ aX₂ aM aT] ++ (gcdIsOne ++
    [zeroA aDd, copyA aDd aX₂]))))))))))))) := by
  simp only [dEven, List.append_assoc]

theorem or_and1_mask (x : BitVec 64) (c : Bool) :
    x ||| (mask c &&& 1) = if c then x ||| 1 else x := by
  cases c
  · simp [mask]
  · simp [mask]

/-- `[j] := [j] | 1` for `[j] = 0` if `c`, else `[j]` unchanged. -/
theorem av_or1 {I : KIn} {m : Mem} {j : Nat} (hw : 1 ≤ I.W) (hj : slot I.W j + 8 * I.W ≤ 2 ^ 64) {c : Bool}
    (hc : c = true → av I m j = 0) :
    av I (m.writeW (off I.B (slot I.W j)) (if c then word m I.B (slot I.W j) ||| 1 else word m I.B (slot I.W j))) j =
      (if c then 1 else av I m j) := by
  have o := writeW_outside m I.B (if c then word m I.B (slot I.W j) ||| 1 else word m I.B (slot I.W j))
    (d := slot I.W j) (by omega)
  dsimp only [av] at hc ⊢
  rw [VG.Proof.Rsa.X86_64.wv_low hw, VG.Proof.Rsa.X86_64.wv_low (m := m) hw, word_writeW_self,
    o.wv (Or.inr (Nat.le_refl _)) (by omega)]
  cases c
  · simp
  · have hz := hc rfl
    rw [VG.Proof.Rsa.X86_64.wv_low (m := m) hw] at hz
    have h0 : (word m I.B (slot I.W j)).toNat = 0 := by omega
    have h1 : wv m I.B (slot I.W j + 8) (I.W - 1) = 0 := by
      rcases Nat.eq_zero_or_pos (wv m I.B (slot I.W j + 8) (I.W - 1)) with h | h
      · exact h
      · have := Nat.le_mul_of_pos_right (2 ^ 64) h; omega
    have : word m I.B (slot I.W j) = 0 := BitVec.eq_of_toNat_eq h0
    simp only [ite_true]
    rw [this, h1]; decide

/-- `dEven`, for an even `e`. -/
theorem dEven_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {e L : Nat} (he64 : e < 2 ^ 64)
    (hee : e % 2 = 0) (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hL : av I s.mem aL = L)
    (hLW : L < 2 ^ (64 * I.W)) :
    WP isa (seqs dEven) s fun t => KS I m₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  have hw2 := h.ws.w2
  rw [dEven_eq]
  -- `[aE] := e`, `[aM] := L`.
  refine wp_seqs_append (by simp [loadEv]) (by simp) (WP.mono (loadEv_k h he64 hev) fun s₁ ⟨h₁, f₁, e₁⟩ => ?_)
  have vE₁ : av I s₁.mem aE = e := av_of_full e₁ (two_le_pow h he64)
  have vL₁ : av I s₁.mem aL = L := by rw [f₁.av (by decide) (by decide) (by decide) hZ, hL]
  refine wp_seqs_append (by simp) (by simp [constA]) (WP.mono (zc_k h₁ (o := aM) (a := aL) (by decide) (by decide)
    (by decide)) fun s₂ ⟨h₂, f₂, v₂, _⟩ => ?_)
  rw [vL₁] at v₂
  -- `r15 := ` the mask of `L = 0`.
  refine wp_seqs_append (by simp [constA]) (by simp [eqMask, eqA]) (WP.mono (constA_k h₂ 0) fun s₃ ⟨h₃, f₃, c₃, _⟩ => ?_)
  have c0 : av I s₃.mem aC = 0 := av_of_full c₃ (Nat.two_pow_pos _)
  have vL₃ : av I s₃.mem aL = L := by
    rw [f₃.av (by decide) (by decide) (by decide) hZ, f₂.av (by decide) (by decide) (by decide) hZ, vL₁]
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) (WP.mono (eqMask_k h₃ (a := aL) (b := aC) (by decide)
    (by decide)) fun s₄ ⟨h₄, m₄, hbp₄, k₄⟩ => ?_)
  rw [vL₃, c0] at hbp₄
  refine wp_seqs_append (by simp) (by simp [constA]) ?_
  simp only [seqs]
  refine WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = mask (decide (L = 0)) ∧ t.mem = s₄.mem)
    (by xrun [hbp₄]) rfl) fun s₅ ⟨⟨h15₅, m₅⟩, k₅⟩ => ?_
  have h₅ := h₄.step (cs := []) (by rw [m₅]; exact KF.refl _ _ _) rfl k₅ (by decide)
  refine wp_seqs_append (by simp [constA]) (by simp) (WP.mono (constA_k h₅ 1) fun s₆ ⟨h₆, f₆, _, k₆⟩ => ?_)
  have h15₆ : s₆.gpr .r15 = mask (decide (L = 0)) := by rw [k₆.gpr (by decide), h15₅]
  have vM₆ : av I s₆.mem aM = L := by
    rw [f₆.av (by decide) (by decide) (by decide) hZ, m₅, m₄, f₃.av (by decide) (by decide) (by decide) hZ, v₂]
  have vE₆ : av I s₆.mem aE = e := by
    rw [f₆.av (by decide) (by decide) (by decide) hZ, m₅, m₄, f₃.av (by decide) (by decide) (by decide) hZ,
      f₂.av (by decide) (by decide) (by decide) hZ, vE₁]
  have vL₆ : av I s₆.mem aL = L := by rw [f₆.av (by decide) (by decide) (by decide) hZ, m₅, m₄, vL₃]
  -- `[aM] := L`, or 1 for `L = 0`.
  have sM := h.ws.sl (j := aM) (by decide)
  refine wp_seqs_append (by simp) (by simp [constA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (Q := fun (t : State) => t.mem = s₆.mem.writeW (off I.B (slot I.W aM))
      (if decide (L = 0) then word s₆.mem I.B (slot I.W aM) ||| 1 else word s₆.mem I.B (slot I.W aM)) ∧
      Keep [.r12, .r9, .rbx, .r10, .rax, .rdx] s₆ t) ?_ fun s₇ ⟨m₇, k₇⟩ => ?_)
  · simp only [List.append_assoc]
    refine WP.block_append_iff.mpr (WP.mono h₆.ws.ws_ok fun u₁ ⟨_, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_)
    have hdi₁ : u₁.gpr .rdi = I.B := (ku₁.gpr (by decide)).trans h₆.ws.rdi
    refine WP.mono (base_ok aM (r := .rbx) (by decide) hdi₁ h9) fun u₂ ⟨hbx, mu₂, ku₂⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok aC (r := .r10) (by decide) ((ku₂.gpr (by decide)).trans hdi₁)
      ((ku₂.gpr (by decide)).trans h9)) fun u₃ ⟨_, mu₃, ku₃⟩ => ?_
    have hs₃ := h₆.ws.scr.congr ((ku₁.trans ku₂).trans ku₃).2.2
    have h15 : u₃.gpr .r15 = mask (decide (L = 0)) := by rw [((ku₁.trans ku₂).trans ku₃).gpr (by decide), h15₆]
    have hmu : u₃.mem = s₆.mem := by rw [mu₃, mu₂, mu₁]
    refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = s₆.mem.writeW (off I.B (slot I.W aM))
      (if decide (L = 0) then word s₆.mem I.B (slot I.W aM) ||| 1 else word s₆.mem I.B (slot I.W aM))) (by
        xrun [State.ea, at0, (ku₃.gpr (by decide)).trans hbx, show BitVec.ofInt 64 0 = 0#64 from rfl,
          BitVec.add_zero, hs₃.ld (d := slot I.W aM) (by omega), hs₃.st (d := slot I.W aM) (by omega), h15, hmu]
        rw [or_and1_mask]) rfl)
      fun t ⟨hm, k⟩ => ⟨hm, (((ku₁.trans ku₂).trans ku₃).trans k).mono (by simp)⟩
  have o₇ := writeW_outside s₆.mem I.B (if decide (L = 0) then word s₆.mem I.B (slot I.W aM) ||| 1 else
    word s₆.mem I.B (slot I.W aM)) (d := slot I.W aM) (by omega)
  rw [← m₇] at o₇
  have f₇ := KF.arr1 (I := I) (j := aM) o₇ (Nat.le_refl _) (by omega)
  have h₇ := h₆.step f₇ (all_mut_arr (by decide)) k₇ (by decide)
  have vM₇ : av I s₇.mem aM = (if decide (L = 0) then 1 else L) := by
    rw [m₇, av_or1 hw1 (by omega) (fun hc => by rw [vM₆]; simpa using hc), vM₆]
  generalize hM₁ : (if decide (L = 0) then 1 else L) = M₁ at vM₇
  have hM₁0 : 0 < M₁ := by
    rw [← hM₁]
    by_cases hL0 : L = 0
    · simp only [hL0, decide_true, ite_true]; decide
    · simp only [hL0, decide_false, Bool.false_eq_true, ite_false]; omega
  -- `[aR] := e mod M₁`, `[aU] := [aR]`.
  refine WP.seq (WP.mono (zeroA_k h₇ (j := aQt) (by decide)) fun s₈ ⟨h₈, f₈, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₈ (o := aQt) (a := aE) (by decide) (by decide) (by decide)) fun s₉ ⟨h₉, f₉, v₉, _, _⟩ =>
      WP.seq (WP.mono (divmod_k h₉ (iQ := aQt) (iR := aR) (iD := aM) (iT := aT) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₁₀ ⟨h₁₀, f₁₀, d₁₀⟩ =>
        WP.seq (WP.mono (zeroA_k h₁₀ (j := aU) (by decide)) fun s₁₁ ⟨h₁₁, f₁₁, z₁₁, _⟩ =>
          WP.mono (copyA_k h₁₁ (o := aU) (a := aR) (by decide) (by decide) (by decide))
            fun s₁₂ ⟨h₁₂, f₁₂, v₁₂, t₁₂, _⟩ => ?_))))
  have vM₉ : av I s₉.mem aM = M₁ := by
    rw [f₉.av (by decide) (by decide) (by decide) hZ, f₈.av (by decide) (by decide) (by decide) hZ, vM₇]
  have vQ₉ : av I s₉.mem aQt = e := by
    rw [v₉, f₈.av (by decide) (by decide) (by decide) hZ, f₇.av (by decide) (by decide) (by decide) hZ, vE₆]
  rw [vM₉, vQ₉] at d₁₀
  have hRlt : e % M₁ < M₁ := Nat.mod_lt _ hM₁0
  have hM₁W : M₁ < 2 ^ (64 * I.W) := by
    rw [← hM₁]
    by_cases hL0 : L = 0
    · simp only [hL0, decide_true, ite_true]; exact Nat.one_lt_two_pow (by omega)
    · simp only [hL0, decide_false, Bool.false_eq_true, ite_false]; exact hLW
  have vR₁₀ : av I s₁₀.mem aR = e % M₁ := by
    rw [← (d₁₀ hM₁0).1]; exact wv_low_of_lt (by omega) (by rw [(d₁₀ hM₁0).1]; omega)
  have hok10 : [Rc.arr aQt, Rc.arr aR, Rc.arr aT].all Rc.ok = true := by decide
  have vU₁₂ : av I s₁₂.mem aU = e % M₁ := by rw [v₁₂, f₁₁.av (by decide) (by decide) (by decide) hZ, vR₁₀]
  have tU₁₂ : atop I s₁₂.mem aU = 0 := by rw [t₁₂]; exact (wv_zero2 z₁₁).2
  have vL₁₂ : av I s₁₂.mem aL = L := by
    rw [f₁₂.av (by decide) (by decide) (by decide) hZ, f₁₁.av (by decide) (by decide) (by decide) hZ,
      f₁₀.av hok10 (by decide) (by decide) hZ, f₉.av (by decide) (by decide) (by decide) hZ,
      f₈.av (by decide) (by decide) (by decide) hZ, f₇.av (by decide) (by decide) (by decide) hZ, vL₆]
  -- `kOk := ` the mask of `L` odd and at least 3.
  refine wp_seqs_append (by simp [constA]) (by simp [ltA]) (WP.mono (constA_k h₁₂ 3) fun s₁₃ ⟨h₁₃, f₁₃, c₁₃, _⟩ => ?_)
  have c3 : av I s₁₃.mem aC = 3 := av_of_full c₁₃ (two_le_pow h (by decide))
  have vL₁₃ : av I s₁₃.mem aL = L := by rw [f₁₃.av (by decide) (by decide) (by decide) hZ, vL₁₂]
  refine wp_seqs_append (by simp [ltA]) (by simp) (WP.mono (ltA_k h₁₃ (a := aL) (b := aC) (by decide) (by decide))
    fun s₁₄ ⟨h₁₄, m₁₄, hbp₁₄, _, _, _, k₁₄⟩ => ?_)
  rw [vL₁₃, c3] at hbp₁₄
  generalize hok0 : (decide (L % 2 = 1) && !decide (L < 3)) = ok0
  refine wp_seqs_append (by simp) (by simp [selC]) ?_
  simp only [seqs]
  have hst := h₁₄.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono (WP.keep [.rcx]
    (Q := fun t => t.gpr .rcx = mask (!decide (L < 3)) ∧ t.mem = s₁₄.mem) (by xrun [hbp₁₄, sxM1, maskNot]) rfl)
    fun s₁₅ ⟨⟨hcx₁₅, m₁₅⟩, k₁₅⟩ => ?_)))
  have h₁₅ := h₁₄.step (cs := []) (by rw [m₁₅]; exact KF.refl _ _ _) rfl k₁₅ (by decide)
  refine WP.mono (oddMask_k h₁₅ (j := aL) (by decide)) fun s₁₆ ⟨m₁₆, hax, _, _, k₁₆⟩ => ?_
  rw [m₁₅, m₁₄, vL₁₃] at hax
  have hcx₁₆ : s₁₆.gpr .rcx = mask (!decide (L < 3)) := by rw [k₁₆.gpr (by decide), hcx₁₅]
  have hdi₁₆ : s₁₆.gpr .rdi = I.B := ((k₁₅.trans k₁₆).gpr (by decide)).trans h₁₄.ws.rdi
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.mem = s₁₆.mem.writeW (off I.B (8 * kOk)) (mask ok0) ∧
    t.gpr .rbp = mask ok0) (by
      have hst₁₆ := (h₁₄.ws.scr.congr (k₁₅.trans k₁₆).2.2).st (d := 8 * kOk)
        (by have := h.ws.h256; unfold kOk sFn; omega)
      xrun [State.ea, hdr, hdi₁₆, hdrOff, hax, hcx₁₆, mask_and', hst₁₆]
      rw [hok0]; exact ⟨rfl, rfl⟩) rfl) fun s₁₇ ⟨⟨m₁₇, hbp₁₇⟩, k₁₇⟩ => ?_
  have h₁₆ := h₁₅.step (cs := []) (by rw [m₁₆]; exact KF.refl _ _ _) rfl k₁₆ (by decide)
  obtain ⟨h₁₇, f₁₇, ok₁₇⟩ := h₁₆.hdrW (i := kOk) (by unfold kOk sFn; omega) m₁₇ k₁₇ (by decide)
  have hm₁₆ : s₁₆.mem = s₁₃.mem := by rw [m₁₆, m₁₅, m₁₄]
  -- `[aM] := L`, then 3 unless `L` is odd and at least 3.
  refine WP.seq (WP.mono (zeroA_k h₁₇ (j := aM) (by decide)) fun s₁₈ ⟨h₁₈, f₁₈, _, k₁₈⟩ =>
    WP.mono (copyA_k h₁₈ (o := aM) (a := aL) (by decide) (by decide) (by decide)) fun s₁₉ ⟨h₁₉, f₁₉, v₁₉, _, k₁₉⟩ => ?_)
  have hokO : [Rc.hdr kOk].all Rc.ok = true := by decide
  have vL₁₇ : av I s₁₇.mem aL = L := by rw [f₁₇.av hokO (by decide) (by decide) hZ, hm₁₆, vL₁₃]
  have vC₁₉ : av I s₁₉.mem aC = 3 := by
    rw [f₁₉.av (by decide) (by decide) (by decide) hZ, f₁₈.av (by decide) (by decide) (by decide) hZ,
      f₁₇.av hokO (by decide) (by decide) hZ, hm₁₆, c3]
  rw [f₁₈.av (by decide) (by decide) (by decide) hZ, vL₁₇] at v₁₉
  refine wp_seqs_append (by simp [selC]) (by simp [invFrom]) (WP.mono (selC_k h₁₉ (j := aM) (by decide) (by decide)
    (c := ok0) (by rw [k₁₉.gpr (by decide), k₁₈.gpr (by decide), hbp₁₇])) fun s₂₀ ⟨h₂₀, f₂₀, v₂₀, _, _⟩ => ?_)
  rw [v₁₉, vC₁₉] at v₂₀
  generalize hM : (if ok0 = true then L else 3) = M at v₂₀
  have hMo : M % 2 = 1 ∧ 1 < M := by
    rw [← hM]; cases ok0
    · simp
    · simp only [ite_true]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hok0
      omega
  -- The inverse modulo `M`.
  refine wp_seqs_append (by simp [invFrom]) (by simp) (WP.mono (invFrom_k h₂₀ (j := aM) (by decide) (by decide))
    fun s₂₁ ⟨h₂₁, f₂₁, vV₂₁, vX₁₂₁, vX₂₂₁⟩ => ?_)
  have hok21 : [Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂].all Rc.ok = true := by decide
  have hokM : [Rc.arr aM].all Rc.ok = true := by decide
  have vM₂₁ : av I s₂₁.mem aM = M := by rw [f₂₁.av hok21 (by decide) (by decide) hZ, v₂₀]
  have presU : ∀ {m m' : Mem} {cs : List Rc}, KF I.B I.W cs m m' → cs.all Rc.ok = true → .arr aU ∉ cs →
      av I m' aU = av I m aU ∧ atop I m' aU = atop I m aU := fun f ok hn =>
    ⟨f.av ok (by decide) hn hZ, f.at ok (by decide) hn hZ⟩
  have pU : av I s₂₁.mem aU = e % M₁ ∧ atop I s₂₁.mem aU = 0 := by
    obtain ⟨a1, b1⟩ := presU f₂₁ hok21 (by decide)
    obtain ⟨a2, b2⟩ := presU f₂₀ hokM (by decide)
    obtain ⟨a3, b3⟩ := presU f₁₉ (by decide) (by decide)
    obtain ⟨a4, b4⟩ := presU f₁₈ (by decide) (by decide)
    obtain ⟨a5, b5⟩ := presU f₁₇ hokO (by decide)
    obtain ⟨a6, b6⟩ := presU f₁₃ (by decide) (by decide)
    rw [hm₁₆] at a5 b5
    exact ⟨by rw [a1, a2, a3, a4, a5, a6, vU₁₂], by rw [b1, b2, b3, b4, b5, b6, tU₁₂]⟩
  refine wp_seqs_append (by simp) (by simp [gcdIsOne, constA]) ?_
  simp only [seqs]
  refine WP.mono (inverse_k h₂₁ (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aM) (iT := aT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) pU.2 (by rw [vV₂₁, v₂₀, vM₂₁]) vX₁₂₁ vX₂₂₁) fun s₂₂ ⟨h₂₂, f₂₂, hinv⟩ => ?_
  rw [vM₂₁, pU.1] at hinv
  obtain ⟨hg₂₂, hdv₂₂, hx₂₂⟩ := hinv hMo.1 hMo.2
  generalize hx : av I s₂₂.mem aX₂ = x at hdv₂₂ hx₂₂
  -- `kOk &= ` the mask of the gcd being 1.
  have hokI : [Rc.arr aU, Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT, Rc.hdr sMo].all Rc.ok = true := by decide
  have ok₂₂ : word s₂₂.mem I.B (8 * kOk) = mask ok0 := by
    rw [f₂₂.word hokI (by decide) (by decide), f₂₁.word hok21 (by decide) (by decide),
      f₂₀.word hokM (by decide) (by decide), f₁₉.word (by decide) (by decide) (by decide),
      f₁₈.word (by decide) (by decide) (by decide), ok₁₇]
  refine wp_seqs_append (by simp [gcdIsOne, constA]) (by simp) (WP.mono (gcdIsOne_k h₂₂ ok₂₂)
    fun s₂₃ ⟨h₂₃, f₂₃, ok₂₃⟩ => ?_)
  rw [hg₂₂] at ok₂₃
  -- `[aDd] := x`.
  refine WP.mono (zc_k h₂₃ (o := aDd) (a := aX₂) (by decide) (by decide) (by decide)) fun t ⟨ht, f₂₄, vD, _⟩ => ?_
  have okt : word t.mem I.B (8 * kOk) = mask (decide (Nat.gcd (e % M₁) M = 1) && ok0) := by
    rw [f₂₄.word (by decide) (by decide) (by decide), ok₂₃]
  have vDt : av I t.mem aDd = x := by
    rw [vD, f₂₃.av (by decide) (by decide) (by decide) hZ, hx]
  have f₁₄₁₆ : KF I.B I.W [] s₁₃.mem s₁₆.mem := by rw [hm₁₆]; exact KF.refl _ _ _
  refine ⟨ht, ?_, ⟨_, okt, ?_, ?_⟩⟩
  · have f₆' : KF I.B I.W [.arr aC] s₃.mem s₆.mem := by rw [← m₄, ← m₅]; exact f₆
    exact (((((((((((((((((((f₁.trans f₂).trans f₃).trans f₆').trans f₇).trans f₈).trans
      f₉).trans f₁₀).trans f₁₁).trans f₁₂).trans f₁₃).trans f₁₄₁₆).trans f₁₇).trans f₁₈).trans f₁₉).trans f₂₀).trans
      f₂₁).trans f₂₂).trans f₂₃).trans f₂₄).mono (by simp)
  · -- The inverse exists iff `L` is odd, at least 3, and the gcd is 1.
    constructor
    · rintro ⟨d, hd⟩
      by_contra hc
      have : ¬ (L % 2 = 1 ∧ 3 ≤ L ∧ Nat.gcd (e % L) L = 1) := fun ⟨h1, h2, h3⟩ => by
        have hok : ok0 = true := by rw [← hok0]; simp [h1]; omega
        have hMe : M = L := by rw [← hM, hok]; rfl
        have hM₁e : M₁ = L := by rw [← hM₁]; simp; omega
        exact hc (by rw [hok, hMe, hM₁e]; simp [h3])
      rw [inverse_even_none hee this] at hd
      cases hd
    · intro hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have hMe : M = L := by rw [← hM, hc.2]; rfl
      have hL3 : 3 ≤ L ∧ L % 2 = 1 := by
        have := hc.2; rw [← hok0] at this
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at this
        omega
      have hM₁e : M₁ = L := by rw [← hM₁]; simp; omega
      have hg1 := hc.1
      rw [hMe, hM₁e] at hg1
      rw [hg₂₂, hMe, hM₁e, hg1] at hdv₂₂
      rw [hMe] at hx₂₂
      exact ⟨x, inverse_even hL3.1 (by exact_mod_cast hdv₂₂) hx₂₂⟩
  · intro d hd
    by_cases hc : L % 2 = 1 ∧ 3 ≤ L ∧ Nat.gcd (e % L) L = 1
    · have hok : ok0 = true := by rw [← hok0]; simp [hc.1]; omega
      have hMe : M = L := by rw [← hM, hok]; rfl
      have hM₁e : M₁ = L := by rw [← hM₁]; simp; omega
      rw [hg₂₂, hMe, hM₁e, hc.2.2] at hdv₂₂
      rw [hMe] at hx₂₂
      rw [inverse_even hc.2.1 (by exact_mod_cast hdv₂₂) hx₂₂] at hd
      cases hd
      exact vDt
    · rw [inverse_even_none hee hc] at hd
      cases hd

end VG.Proof.RsaKeyGen.X86_64.Key
