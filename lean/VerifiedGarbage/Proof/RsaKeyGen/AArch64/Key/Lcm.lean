import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Halve

/-!
# An RSA key from its primes on AArch64: `lcm(p − 1, q − 1)`

The halving's loop (`twos_k`), `gcd(u, v)` after it (`gcdUV_k`), and
`lcmPart` (`lcm_k`): `[aL] := lcm(p − 1, q − 1)` (`lcm_eq`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-! ## The loop -/

theorem lcm_ofNat_shl6 {W : Nat} (hW : W < 2 ^ 24) : BitVec.ofNat 64 W <<< 6 = BitVec.ofNat 64 (64 * W) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show W < 2 ^ 64 by omega), show (2 : Nat) ^ 6 = 64 from rfl, Nat.mul_comm]

/-- `ws` and `x6 := 64 W`. -/
theorem twosInit_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (.block (ws ++ ([.lsl .x .x6 .x12 6] : List Instr))) s fun t =>
      (t.gpr .x6 = BitVec.ofNat 64 (64 * I.W) ∧ t.mem = s.mem) ∧ Keep [.x6, .x11, .x12] s t := by
  have hw2 := h.ws.w2
  rw [WP.block_append_iff]
  refine WP.mono h.ws.ws_ok fun s₁ ⟨⟨h12, _, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (WP.keep [.x6] (Q := fun t => t.gpr .x6 = BitVec.ofNat 64 (64 * I.W) ∧ t.mem = s₁.mem)
    (by brun [h12, lcm_ofNat_shl6 hw2]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h6, m₂⟩, k₂⟩ => ?_
  exact ⟨⟨h6, m₂.trans m₁⟩, (k₁.trans k₂).mono (by decide)⟩

/-- `64 W` steps (`x6 := W << 6`, then `wp_countdown` on `x6`). -/
theorem twos_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) (hU0 : atop I s.mem aU = 0)
    (hV0 : atop I s.mem aV = 0) (hL0 : atop I s.mem aL = 0) :
    WP isa (seqs twos) s fun t => TwoP I s₀ s t ∧
      (av I t.mem aU, av I t.mem aV, av I t.mem aL) =
        halveIter (64 * I.W) (av I s.mem aU, av I s.mem aV, av I s.mem aL) := by
  have hw1 := h.ws.w1
  have hw2 := h.ws.w2
  simp only [twos, seqs]
  refine WP.seq (WP.mono (twosInit_k h) fun s₁ ⟨⟨h6, m₁⟩, k₁⟩ => ?_)
  have h₁ := h.regs m₁ k₁
  refine WP.mono (wp_countdown (N := 64 * I.W) (by omega) (by omega)
    (fun j t => TwoP I s₀ s t ∧
      (av I t.mem aU, av I t.mem aV, av I t.mem aL) = halveIter j (av I s.mem aU, av I s.mem aV, av I s.mem aL))
    (fun j _ t ⟨tp, tv⟩ _ => WP.mono (twoStep_k tp.1 tp.2.2.1 tp.2.2.2.1 tp.2.2.2.2)
      fun t' ⟨tp', h6', tv'⟩ => ⟨⟨tp.trans tp', by rw [tv', tv, halveIter_succ']⟩, h6'⟩)
    ⟨⟨h₁, KF.of_eq m₁, by rw [m₁]; exact hU0, by rw [m₁]; exact hV0, by rw [m₁]; exact hL0⟩, by rw [m₁]; rfl⟩ h6)
    fun t ht => ht

/-! ## `gcd(u, v)` -/

/-- `gcdUV`'s swap: `v` made odd (if it is even, `u` and `v` swapped). -/
theorem gcdSwap_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (seqs [.block (evenMaskOf aV ++ (([mov .x14 .x12] : List Instr) ++ (base aU .x16 ++ base aV .x17))),
      countLoop .x14 cswapBody]) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aU, .arr aV] s.mem t.mem ∧
      av I t.mem aU = (if av I s.mem aV % 2 = 0 then av I s.mem aV else av I s.mem aU) ∧
      av I t.mem aV = (if av I s.mem aV % 2 = 0 then av I s.mem aU else av I s.mem aV) ∧
      atop I t.mem aU = atop I s.mem aU := by
  have hn := h.ws.scr.nowrap
  have sU := h.ws.sl (j := aU) (by decide)
  have sV := h.ws.sl (j := aV) (by decide)
  have sp := slot_sep (w := I.W) (j := aU) (k := aV) (by decide)
  simp only [seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (evenMaskOf_k h (j := aV) (by decide))
    fun s₁ ⟨h₁, m₁, h15, h12, h11, k₁⟩ => WP.block_append_iff.mpr (WP.mono (WP.keep [.x14]
      (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 I.W ∧ t.mem = s₁.mem) (by brun [h12]) (by decide) (by decide)
      (by decide +kernel)) fun s₂ ⟨⟨h14, m₂⟩, k₂⟩ =>
    WP.mono (base2_ok aU aV .x16 .x17 ((k₂.gpr .x0 (by decide)).trans h₁.ws.x0) ((k₂.gpr .x11 (by decide)).trans h11))
      fun s₃ ⟨⟨h16, h17, m₃, _⟩, k₃⟩ => ?_)))
  have k13 := (k₁.trans k₂).trans k₃
  refine WP.mono (cswap_ok (h.ws.scr.congr k13.wr) h16 h17 (((k₂.trans k₃).gpr .x15 (by decide)).trans h15)
    ((k₃.gpr .x14 (by decide)).trans h14) (by have := h.ws.w1; omega) (by have := h.ws.w2; omega) (by omega)
    (by omega) (by omega)) fun t ⟨hX, hY, hf, k₄⟩ => ?_
  have hm : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
  rw [hm] at hX hY hf
  simp only [decide_eq_true_eq] at hX hY
  have f : KF I.B I.W [.arr aU, .arr aV] s.mem t.mem :=
    KF.of_frm hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨.arr aU, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
      · exact ⟨.arr aV, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
  refine ⟨h.step f (all_mut_arrs (js := [aU, aV]) (by decide)) (k13.trans k₄), f, hX, hY, ?_⟩
  exact hf.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega)

/-- `ldh .x15 kOk`. -/
theorem ldOk_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {c : Bool} (hok : word s.mem I.B (8 * kOk) = mask c) :
    WP isa (.block [ldh .x15 kOk]) s fun t => KS I s₀ t ∧ t.mem = s.mem ∧ t.gpr .x15 = mask c ∧
      Keep [.x15] s t := by
  have hld := h.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  refine WP.mono (WP.keep [.x15] (Q := fun t => t.gpr .x15 = mask c ∧ t.mem = s.mem) (by
    brun [h.ws.x0, hdr_enc (show kOk < 32 by decide), hld, hok]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h15, hm⟩, k⟩ => ⟨h.regs hm k, hm, h15, k⟩

/-- `gcdUV`: `v` made odd by a swap (`evenMaskOf_k`), the mask of `v < 2`
into `kOk`, `inverse` modulo `v` (3 if `v < 2`, by `selC_k`), and 1 for
`v < 2`. -/
theorem gcdUV_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) (hU0 : atop I s.mem aU = 0)
    (hodd : let v := if av I s.mem aV % 2 = 0 then av I s.mem aU else av I s.mem aV; 2 ≤ v → v % 2 = 1) :
    WP isa (seqs gcdUV) s fun t => KS I s₀ t ∧
      KF I.B I.W [.arr aU, .arr aV, .arr aC, .arr aM, .arr aX₁, .arr aX₂, .arr aT, .hdr kOk] s.mem t.mem ∧
      av I t.mem aV =
        (let u := if av I s.mem aV % 2 = 0 then av I s.mem aV else av I s.mem aU
         let v := if av I s.mem aV % 2 = 0 then av I s.mem aU else av I s.mem aV
         if v ≤ 1 then 1 else Nat.gcd u v) := by
  have hw1 := h.ws.w1
  have hZ := h.hZ
  unfold gcdUV
  simp only [List.append_assoc]
  -- The swap.
  refine wp_seqs_append (by simp) (by simp [constA]) (WP.mono (gcdSwap_k h) fun s₂ ⟨h₂, f₂, hX, hY, tU⟩ => ?_)
  generalize hu0 : av I s.mem aU = u0 at hodd hX hY
  generalize hv0 : av I s.mem aV = v0 at hodd hX hY
  generalize hu1 : (if v0 % 2 = 0 then v0 else u0) = u1 at hX
  generalize hv1 : (if v0 % 2 = 0 then u0 else v0) = v1 at hodd hY
  dsimp only at hodd ⊢
  have tU₂ : atop I s₂.mem aU = 0 := tU.trans hU0
  -- `kOk := ` the mask of `v < 2`.
  refine wp_seqs_append (by simp [constA]) (by simp [ltA, cmpA]) (WP.mono (constA_k h₂ (x := 2) (by decide))
    fun s₃ ⟨h₃, f₃, c₃, _⟩ => ?_)
  have hokC : [Rc.arr aC].all Rc.ok = true := by decide
  have c2 : av I s₃.mem aC = 2 := av_of_full c₃ (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide)
    (show 2 ≤ 64 * I.W by omega)))
  have vV₃ : av I s₃.mem aV = v1 := by rw [← hY]; exact f₃.av hokC (by decide) (by decide) hZ
  refine wp_seqs_append (by simp [ltA, cmpA]) (by simp) (WP.mono (ltA_k h₃ (a := aV) (b := aC) (by decide)
    (by decide)) fun s₄ ⟨h₄, m₄, h15₄, _, _⟩ => ?_)
  rw [vV₃, c2] at h15₄
  refine wp_seqs_append (by simp) (by simp [constA]) ?_
  simp only [seqs]
  have hst := h₄.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₄.mem.writeW (off I.B (8 * kOk)) (mask (decide (v1 < 2))))
    (by brun [h₄.ws.x0, hdr_enc (show kOk < 32 by decide), hst, h15₄]) rfl rfl rfl) fun s₅ ⟨hm₅, k₅⟩ => ?_
  obtain ⟨h₅, f₅, ok₅⟩ := h₄.hdrW (i := kOk) (by unfold kOk sFn; omega) hm₅ k₅
  have hokO : [Rc.hdr kOk].all Rc.ok = true := by decide
  -- `[aV] := 3` for `v < 2`.
  refine wp_seqs_append (by simp [constA]) (by simp) (WP.mono (constA_k h₅ (x := 3) (by decide))
    fun s₆ ⟨h₆, f₆, c₆, _⟩ => ?_)
  have c3 : av I s₆.mem aC = 3 := av_of_full c₆ (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide)
    (show 2 ≤ 64 * I.W by omega)))
  have vV₆ : av I s₆.mem aV = v1 := by
    rw [← vV₃, f₆.av hokC (by decide) (by decide) hZ, f₅.av hokO (by decide) (by decide) hZ, m₄]
  have ok₆ : word s₆.mem I.B (8 * kOk) = mask (decide (v1 < 2)) := by
    rw [f₆.word hokC (by decide) (by decide), ok₅]
  refine wp_seqs_append (by simp) (by simp [selC]) ?_
  simp only [seqs]
  refine WP.mono (ldOk_k h₆ ok₆) fun s₆' ⟨h₆', m₆', h15₆, _⟩ => ?_
  refine wp_seqs_append (by simp [selC]) (by simp) (WP.mono (selC_k h₆' (j := aV) (by decide) (by decide) h15₆)
    fun s₇ ⟨h₇, f₇, vV₇, _, _⟩ => ?_)
  rw [m₆', vV₆, c3] at vV₇
  generalize hM : (if decide (v1 < 2) = true then 3 else v1) = M at vV₇
  have hMo : M % 2 = 1 ∧ 1 < M := by
    rw [← hM]
    by_cases hv : v1 < 2
    · simp [hv]
    · simp only [hv, decide_false, Bool.false_eq_true, ite_false]; exact ⟨hodd (by omega), by omega⟩
  -- The inverse modulo `M`.
  refine wp_seqs_append (by simp) (by simp [constA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₇ (j := aM) (by decide)) fun s₇' ⟨h₇', f₇', _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₇' (o := aM) (a := aV) (by decide) (by decide) (by decide))
    fun s₈ ⟨h₈, f₈', vM₈, _, _⟩ => WP.seq (WP.mono (zeroA_k h₈ (j := aX₁) (by decide)) fun s₉ ⟨h₉, f₉, z₉, _⟩ =>
      WP.seq (WP.mono (setOne_k h₉ (j := aX₁) (by decide) z₉) fun s₁₀ ⟨h₁₀, f₁₀, o₁₀, _⟩ =>
        WP.seq (WP.mono (zeroA_k h₁₀ (j := aX₂) (by decide)) fun s₁₁ ⟨h₁₁, f₁₁, z₁₁, _⟩ => ?_)))))
  have hokM : [Rc.arr aM].all Rc.ok = true := by decide
  have f₈ : KF I.B I.W [.arr aM] s₇.mem s₈.mem := (f₇'.trans f₈').mono (by simp)
  rw [f₇'.av hokM (j := aV) (by decide) (by decide) hZ] at vM₈
  have hok1 : [Rc.arr aX₁].all Rc.ok = true := by decide
  have hok2 : [Rc.arr aX₂].all Rc.ok = true := by decide
  have pres : ∀ j, j < 16 → j ≠ aM → j ≠ aX₁ → j ≠ aX₂ → av I s₁₁.mem j = av I s₇.mem j := fun j hj h1 h2 h3 => by
    rw [f₁₁.av hok2 hj (by simp [h3]) hZ, f₁₀.av hok1 hj (by simp [h2]) hZ, f₉.av hok1 hj (by simp [h2]) hZ,
      f₈.av hokM hj (by simp [h1]) hZ]
  have vU₁₁ : av I s₁₁.mem aU = u1 := by
    rw [pres aU (by decide) (by decide) (by decide) (by decide), ← hX,
      f₇.av (by decide) (j := aU) (by decide) (by decide) hZ, m₆', f₆.av hokC (by decide) (by decide) hZ,
      f₅.av hokO (by decide) (by decide) hZ, m₄, f₃.av hokC (by decide) (by decide) hZ]
  have vV₁₁ : av I s₁₁.mem aV = M := by rw [pres aV (by decide) (by decide) (by decide) (by decide), vV₇]
  have vM₁₁ : av I s₁₁.mem aM = M := by
    rw [f₁₁.av hok2 (by decide) (by decide) hZ, f₁₀.av hok1 (by decide) (by decide) hZ,
      f₉.av hok1 (by decide) (by decide) hZ, vM₈, vV₇]
  have vX₁ : av I s₁₁.mem aX₁ = 1 := by
    rw [f₁₁.av hok2 (by decide) (by decide) hZ]
    exact av_of_full o₁₀ (Nat.one_lt_two_pow (by omega))
  have vX₂ : av I s₁₁.mem aX₂ = 0 := (wv_zero2 z₁₁).1
  have tU₁₁ : atop I s₁₁.mem aU = 0 := by
    rw [f₁₁.at hok2 (by decide) (by decide) hZ, f₁₀.at hok1 (by decide) (by decide) hZ,
      f₉.at hok1 (by decide) (by decide) hZ, f₈.at hokM (by decide) (by decide) hZ,
      f₇.at (by decide) (j := aU) (by decide) (by decide) hZ, m₆', f₆.at hokC (by decide) (by decide) hZ,
      f₅.at hokO (by decide) (by decide) hZ, m₄, f₃.at hokC (by decide) (by decide) hZ, tU₂]
  refine WP.mono (inverse_k h₁₁ (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aM) (iT := aT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) tU₁₁ (by rw [vV₁₁, vM₁₁]) vX₁ vX₂) fun s₁₂ ⟨h₁₂, f₁₂, hinv⟩ => ?_
  rw [vM₁₁, vU₁₁] at hinv
  have hg := (hinv hMo.1 hMo.2).1
  -- The result 1 for `v < 2`.
  refine wp_seqs_append (by simp [constA]) (by simp) (WP.mono (constA_k h₁₂ (x := 1) (by decide))
    fun s₁₃ ⟨h₁₃, f₁₃, c₁₃, _⟩ => ?_)
  have c1 : av I s₁₃.mem aC = 1 := av_of_full c₁₃ (Nat.one_lt_two_pow (by omega))
  have hokI : [Rc.arr aU, Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT].all Rc.ok = true := by decide
  have ok₁₃ : word s₁₃.mem I.B (8 * kOk) = mask (decide (v1 < 2)) := by
    rw [f₁₃.word hokC (by decide) (by decide), f₁₂.word hokI (by decide) (by decide),
      f₁₁.word hok2 (by decide) (by decide), f₁₀.word hok1 (by decide) (by decide),
      f₉.word hok1 (by decide) (by decide), f₈.word hokM (by decide) (by decide),
      f₇.word (by decide) (by decide) (by decide), m₆', ok₆]
  refine wp_seqs_append (by simp) (by simp [selC]) ?_
  simp only [seqs]
  refine WP.mono (ldOk_k h₁₃ ok₁₃) fun s₁₄ ⟨h₁₄, m₁₄, h15₁₄, _⟩ => ?_
  refine WP.mono (selC_k h₁₄ (j := aV) (by decide) (by decide) h15₁₄) fun t ⟨ht, f₁₅, vV, _, _⟩ => ?_
  have f₅' : KF I.B I.W [.hdr kOk] s₃.mem s₅.mem := by rw [← m₄]; exact f₅
  have f₇'' : KF I.B I.W [.arr aV] s₆.mem s₇.mem := by rw [← m₆']; exact f₇
  have f₁₅' : KF I.B I.W [.arr aV] s₁₃.mem t.mem := by rw [← m₁₄]; exact f₁₅
  refine ⟨ht, ?_, ?_⟩
  · exact (((((((((((f₂.trans f₃).trans f₅').trans f₆).trans f₇'').trans f₈).trans f₉).trans f₁₀).trans f₁₁).trans
      f₁₂).trans f₁₃).trans f₁₅').mono (by simp)
  · rw [vV, m₁₄, c1, f₁₃.av hokC (by decide) (by decide) hZ, hg]
    by_cases hv : v1 < 2
    · simp [hv, show v1 ≤ 1 by omega]
    · simp only [hv, decide_false, Bool.false_eq_true, ite_false, show ¬ v1 ≤ 1 by omega]
      rw [← hM]; simp [hv]

/-! ## The lcm -/

/-- Word `W` of a number of `W + 2` words below `2^(64 W)`. -/
theorem lcm_topZero {m : Mem} {B : Addr} {d W : Nat} (h : wv m B d (W + 2) < 2 ^ (64 * W)) :
    word m B (d + 8 * W) = 0 := by
  have e := wv_add m B d W 2
  have : wv m B (d + 8 * W) 2 = 0 := by
    rcases Nat.eq_zero_or_pos (wv m B (d + 8 * W) 2) with h0 | h0
    · exact h0
    · have := Nat.le_mul_of_pos_right (2 ^ (64 * W)) h0; omega
  have := (wv_eq_zero_iff _ _ _ _).mp this 0 (by decide)
  simpa using this

theorem lcmPart_eq : lcmPart = phi ++ (([zeroA aU, copyA aU aPm, zeroA aV, copyA aV aQm] : List (Prog isa)) ++
    (twos ++ (gcdUV ++ ([divmod aL aR aV aT] : List (Prog isa))))) := by
  simp only [lcmPart, List.append_assoc]

/-- `lcmPart`: `[aL] := lcm(a, b)`. -/
theorem lcm_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {w : Nat} (hW : I.W = 2 * w)
    {a b : Nat} (ha : av I s.mem aPm = a) (hb : av I s.mem aQm = b) (ha' : a < 2 ^ (64 * w))
    (hb' : b < 2 ^ (64 * w)) :
    WP isa (seqs lcmPart) s fun t => KS I s₀ t ∧ KF I.B I.W csL s.mem t.mem ∧ av I t.mem aL = Nat.lcm a b := by
  have hZ := h.hZ
  have hw1 := h.ws.w1
  have hab : a * b < 2 ^ (64 * I.W) := by
    rw [hW, show 64 * (2 * w) = 64 * w + 64 * w by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le ha' (by omega) (Nat.two_pow_pos _)
  rw [lcmPart_eq]
  refine wp_seqs_append (by simp [phi, mulTo]) (by simp) (WP.mono (phi_k h hW ha hb ha' hb') fun s₁ ⟨h₁, f₁, v₁⟩ => ?_)
  have hokL : [Rc.arr aL].all Rc.ok = true := by decide
  have vL₁ : av I s₁.mem aL = a * b := av_of_full v₁ hab
  have tL₁ : atop I s₁.mem aL = 0 := lcm_topZero (by rw [v₁]; exact hab)
  have vP₁ : av I s₁.mem aPm = a := by rw [f₁.av hokL (by decide) (by decide) hZ]; exact ha
  have vQ₁ : av I s₁.mem aQm = b := by rw [f₁.av hokL (by decide) (by decide) hZ]; exact hb
  refine wp_seqs_append (by simp) (by simp [twos]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₁ (j := aU) (by decide)) fun s₂ ⟨h₂, f₂, z₂, _⟩ =>
    WP.seq (WP.mono (copyA_k h₂ (o := aU) (a := aPm) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, v₃, t₃, _⟩ =>
      WP.seq (WP.mono (zeroA_k h₃ (j := aV) (by decide)) fun s₄ ⟨h₄, f₄, z₄, _⟩ =>
        WP.mono (copyA_k h₄ (o := aV) (a := aQm) (by decide) (by decide) (by decide))
          fun s₅ ⟨h₅, f₅, v₅, t₅, _⟩ => ?_)))
  have hU : [Rc.arr aU].all Rc.ok = true := by decide
  have hV : [Rc.arr aV].all Rc.ok = true := by decide
  have vU₅ : av I s₅.mem aU = a := by
    rw [f₅.av hV (by decide) (by decide) hZ, f₄.av hV (by decide) (by decide) hZ, v₃,
      f₂.av hU (by decide) (by decide) hZ, vP₁]
  have vV₅ : av I s₅.mem aV = b := by
    rw [v₅, f₄.av hV (by decide) (by decide) hZ, f₃.av hU (by decide) (by decide) hZ,
      f₂.av hU (by decide) (by decide) hZ, vQ₁]
  have vL₅ : av I s₅.mem aL = a * b := by
    rw [f₅.av hV (by decide) (by decide) hZ, f₄.av hV (by decide) (by decide) hZ,
      f₃.av hU (by decide) (by decide) hZ, f₂.av hU (by decide) (by decide) hZ, vL₁]
  have tU₅ : atop I s₅.mem aU = 0 := by
    rw [f₅.at hV (by decide) (by decide) hZ, f₄.at hV (by decide) (by decide) hZ, t₃]; exact (wv_zero2 z₂).2
  have tV₅ : atop I s₅.mem aV = 0 := by rw [t₅]; exact (wv_zero2 z₄).2
  have tL₅ : atop I s₅.mem aL = 0 := by
    rw [f₅.at hV (by decide) (by decide) hZ, f₄.at hV (by decide) (by decide) hZ,
      f₃.at hU (by decide) (by decide) hZ, f₂.at hU (by decide) (by decide) hZ, tL₁]
  -- The halving.
  refine wp_seqs_append (by simp [twos]) (by simp [gcdUV]) (WP.mono (twos_k h₅ tU₅ tV₅ tL₅)
    fun s₆ ⟨⟨h₆, f₆, tU₆, _, _⟩, hv₆⟩ => ?_)
  rw [vU₅, vV₅, vL₅] at hv₆
  have hK : a < 2 ^ (64 * I.W) ∧ b < 2 ^ (64 * I.W) := by
    rw [hW]; exact ⟨Nat.lt_of_lt_of_le ha' (Nat.pow_le_pow_right (by decide) (by omega)),
      Nat.lt_of_lt_of_le hb' (Nat.pow_le_pow_right (by decide) (by omega))⟩
  have hle := lcm_eq hK.1 hK.2
  dsimp only at hle
  generalize halveIter (64 * I.W) (a, b, a * b) = st at hv₆ hle
  obtain ⟨x, y, f⟩ := st
  simp only [Prod.mk.injEq] at hv₆
  obtain ⟨hx, hy, hf⟩ := hv₆
  dsimp only at hle
  -- `gcd(u, v)`.
  refine wp_seqs_append (by simp [gcdUV]) (by simp) (WP.mono (gcdUV_k h₆ tU₆ (by rw [hx, hy]; exact hle.1))
    fun s₇ ⟨h₇, f₇, vV₇⟩ => ?_)
  rw [hx, hy] at vV₇
  dsimp only at vV₇
  have hokG : [Rc.arr aU, Rc.arr aV, Rc.arr aC, Rc.arr aM, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT,
    Rc.hdr kOk].all Rc.ok = true := by decide
  have vL₇ : av I s₇.mem aL = f := by rw [f₇.av hokG (by decide) (by decide) hZ, hf]
  generalize hg : (if (if y % 2 = 0 then x else y) ≤ 1 then 1 else
    Nat.gcd (if y % 2 = 0 then y else x) (if y % 2 = 0 then x else y)) = g at vV₇ hle
  have hg0 : 0 < g := by
    rw [← hg]
    generalize (if y % 2 = 0 then x else y) = v
    generalize (if y % 2 = 0 then y else x) = u
    by_cases hv : v ≤ 1
    · simp [hv]
    · simp only [hv, ite_false]; exact Nat.gcd_pos_of_pos_right _ (by omega)
  simp only [seqs]
  refine WP.mono (divmod_k h₇ (iQ := aL) (iR := aR) (iD := aV) (iT := aT) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨ht, f₈, hd⟩ => ⟨ht, ?_, ?_⟩
  · have f₂₅ := ((f₂.trans f₃).trans f₄).trans f₅
    exact ((((f₁.trans f₂₅).trans f₆).trans f₇).trans f₈).mono (by simp)
  · rw [vV₇] at hd
    rw [(hd hg0).2, vL₇, hle.2]

end VG.Proof.RsaKeyGen.AArch64.Key
