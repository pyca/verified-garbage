import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Halve

/-!
# An RSA key from its primes on x86-64: `lcm(p − 1, q − 1)`

The halving's loop (`twos_k`), `gcd(u, v)` after it (`gcdUV_k`), and
`lcmPart` (`lcm_k`): `[aL] := lcm(p − 1, q − 1)` (`lcm_eq`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-! ## The loop -/

/-- `divInit t`: `r11 := 64 W`, `r13 := 0`. -/
theorem divInit_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (iT : Nat) :
    WP isa (.block (divInit iT)) s fun t => t.gpr .r11 = BitVec.ofNat 64 (64 * I.W) ∧
      t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s.mem ∧ Keep [.r12, .r9, .r8, .r11, .r13] s t := by
  rw [divInit, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono h.ws.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  refine WP.mono (base_ok iT (r := .r8) (by decide) ((k₁.gpr (by decide)).trans h.ws.rdi) h9) fun s₂ ⟨_, m₂, k₂⟩ => ?_
  have e12 : s₂.gpr .r12 = BitVec.ofNat 64 I.W := (k₂.gpr (by decide)).trans h12
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 I.W ∧ t.mem = s₂.mem)
    (by xrun [e12]) rfl) fun s₃ ⟨⟨h11, m₃⟩, k₃⟩ => ?_
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (64 * I.W) ∧ t.mem = s₃.mem)
    (by
      xrun [h11, ofNat_dbl, List.replicate]
      congr 1; omega) rfl) fun s₄ ⟨⟨h11', m₄⟩, k₄⟩ => ?_
  refine WP.mono (WP.keep [.r13] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s₄.mem)
    (by xrun) rfl) fun t ⟨⟨h13, m₅⟩, k₅⟩ => ?_
  exact ⟨(k₅.gpr (by decide)).trans h11', h13, by rw [m₅, m₄, m₃, m₂, m₁],
    ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by simp)⟩

theorem TwoP.trans {I : KIn} {m₀ : Mem} {s t u : State} (h₁ : TwoP I m₀ s t) (h₂ : TwoP I m₀ t u) :
    TwoP I m₀ s u :=
  ⟨h₂.1, (h₁.2.1.trans h₂.2.1).mono (by simp), h₂.2.2⟩

/-- `twos`: `64 W` steps of the halving. -/
theorem twos_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (hU0 : atop I s.mem aU = 0)
    (hV0 : atop I s.mem aV = 0) (hL0 : atop I s.mem aL = 0) :
    WP isa (seqs twos) s fun t => TwoP I m₀ s t ∧
      (av I t.mem aU, av I t.mem aV, av I t.mem aL) =
        halveIter (64 * I.W) (av I s.mem aU, av I s.mem aV, av I s.mem aL) := by
  have hw1 := h.ws.w1
  have hw2 := h.ws.w2
  simp only [twos, seqs]
  refine WP.seq (WP.mono (divInit_k h aT) fun s₁ ⟨h11, h13, m₁, k₁⟩ => ?_)
  have h₁ := h.step (cs := []) (by rw [m₁]; exact KF.refl _ _ _) rfl k₁ (by decide)
  refine wp_upto (a := 0) (N := 64 * I.W) (by omega)
    (fun j t => t.gpr .r11 = BitVec.ofNat 64 (64 * I.W) ∧ t.gpr .r13 = BitVec.ofNat 64 j ∧ TwoP I m₀ s t ∧
      (av I t.mem aU, av I t.mem aV, av I t.mem aL) = halveIter j (av I s.mem aU, av I s.mem aV, av I s.mem aL))
    (fun j _ hj t ⟨t11, t13, tp, tv⟩ => ?_) (fun t ⟨_, _, tp, tv⟩ => ⟨tp, tv⟩)
    ⟨h11, h13, ⟨h₁, by rw [m₁]; exact (KF.refl _ _ _).mono (by simp), by rw [m₁]; exact hU0, by rw [m₁]; exact hV0,
      by rw [m₁]; exact hL0⟩, by rw [m₁]; rfl⟩
  refine WP.mono (twoStep_k tp.1 tp.2.2.1 tp.2.2.2.1 tp.2.2.2.2 t13 t11 hj) fun t' ⟨hz, h13', h11', tp', tv'⟩ =>
    ⟨hz, h11', h13', tp.trans tp', ?_⟩
  rw [tv', tv, halveIter_succ']

/-! ## `gcd(u, v)` -/

theorem ite_not_odd {α : Sort _} (v : Nat) (a b : α) :
    (if (!decide (v % 2 = 1)) = true then a else b) = (if v % 2 = 0 then a else b) := by
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]

theorem gcdUV_eq : gcdUV = ([.block (oddMask aV ++ ([.mov .r15 (.reg .rax), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))] : List Instr) ++
      base aU .rbx ++ base aV .r10), wordLoop 0 cswapBody] : List (Prog isa)) ++ (constA 2 ++ (ltA aV aC ++
    (([.block [.store (hdr kOk) .rbp, .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]] : List (Prog isa)) ++ (constA 3 ++ (selC aV ++
    ([zeroA aM, copyA aM aV, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂, inverse aU aV aX₁ aX₂ aM aT] ++
    (constA 1 ++ (([.block [.mov .rbp (.mem (hdr kOk)), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]] : List (Prog isa)) ++
      selC aV)))))))) := by
  simp only [gcdUV, List.append_assoc]

/-- `gcdUV`: `v` made odd by a swap, then `[aV] := gcd(u, v)`, or 1 for
`v ≤ 1`, for an odd `v` unless `v ≤ 1`. -/
theorem gcdUV_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (hU0 : atop I s.mem aU = 0)
    (hodd : let v := if av I s.mem aV % 2 = 0 then av I s.mem aU else av I s.mem aV; 2 ≤ v → v % 2 = 1) :
    WP isa (seqs gcdUV) s fun t => KS I m₀ t ∧
      KF I.B I.W [.arr aU, .arr aV, .arr aC, .arr aM, .arr aX₁, .arr aX₂, .arr aT, .hdr sMo, .hdr kOk] s.mem t.mem ∧
      av I t.mem aV =
        (let u := if av I s.mem aV % 2 = 0 then av I s.mem aV else av I s.mem aU
         let v := if av I s.mem aV % 2 = 0 then av I s.mem aU else av I s.mem aV
         if v ≤ 1 then 1 else Nat.gcd u v) := by
  have hn := h.ws.scr.nowrap
  have hw1 := h.ws.w1
  have hw2 := h.ws.w2
  have hZ := h.hZ
  have sU := h.ws.sl (j := aU) (by decide)
  have sV := h.ws.sl (j := aV) (by decide)
  have spUV := slot_far (w := I.W) (i := aU) (j := aV) (by decide)
  generalize hu0 : av I s.mem aU = u0 at hodd
  generalize hv0 : av I s.mem aV = v0 at hodd
  generalize hu1 : (if v0 % 2 = 0 then v0 else u0) = u1
  generalize hv1 : (if v0 % 2 = 0 then u0 else v0) = v1 at hodd
  dsimp only at hodd ⊢
  rw [gcdUV_eq]
  -- The swap.
  have hb : WP isa (.block (oddMask aV ++ [.mov .r15 (.reg .rax), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))] ++
      base aU .rbx ++ base aV .r10)) s fun t => t.mem = s.mem ∧ t.gpr .r15 = mask (!decide (v0 % 2 = 1)) ∧
      t.gpr .rbx = off I.B (slot I.W aU) ∧ t.gpr .r10 = off I.B (slot I.W aV) ∧ t.gpr .r12 = BitVec.ofNat 64 I.W ∧
      Keep [.r12, .r9, .rbx, .rax, .rdx, .r15, .r10] s t := by
    simp only [List.append_assoc]
    refine WP.block_append_iff.mpr (WP.mono (oddMask_k h (j := aV) (by decide)) fun s₁ ⟨m₁, hax, h12, h9, k₁⟩ => ?_)
    rw [hv0] at hax
    refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = mask (!decide (v0 % 2 = 1)) ∧
      t.mem = s₁.mem) (by xrun [hax, sxM1, maskNot]) rfl) fun s₂ ⟨⟨h15, m₂⟩, k₂⟩ => WP.block_append_iff.mpr ?_)
    have hdi₂ : s₂.gpr .rdi = I.B := ((k₁.trans k₂).gpr (by decide)).trans h.ws.rdi
    have h9₂ : s₂.gpr .r9 = BitVec.ofNat 64 (8 * (I.W + 2)) := (k₂.gpr (by decide)).trans h9
    refine WP.mono (base_ok aU (r := .rbx) (by decide) hdi₂ h9₂) fun s₃ ⟨hbx, m₃, k₃⟩ => ?_
    refine WP.mono (base_ok aV (r := .r10) (by decide) ((k₃.gpr (by decide)).trans hdi₂)
      ((k₃.gpr (by decide)).trans h9₂)) fun t ⟨h10, m₄, k₄⟩ => ⟨by rw [m₄, m₃, m₂, m₁],
        ((k₃.trans k₄).gpr (by decide)).trans h15, (k₄.gpr (by decide)).trans hbx, h10,
        (((k₂.trans k₃).trans k₄).gpr (by decide)).trans h12, (((k₁.trans k₂).trans k₃).trans k₄).mono (by simp)⟩
  refine wp_seqs_append (by simp) (by simp [constA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono hb fun s₁ ⟨m₁, h15, hbx, h10, h12, k₁⟩ => ?_)
  refine WP.mono (cswap_ok (h.ws.scr.congr k₁.2.2) hbx h10 h15 h12 (by omega) (by omega) (by omega) (by omega)
    (by omega)) fun s₂ ⟨hX, hY, hf, k₂⟩ => ?_
  have hu0' : wv s.mem I.B (slot I.W aU) I.W = u0 := hu0
  have hv0' : wv s.mem I.B (slot I.W aV) I.W = v0 := hv0
  rw [m₁, hu0', hv0', ite_not_odd, hu1] at hX
  rw [m₁, hu0', hv0', ite_not_odd, hv1] at hY
  have f₂ : KF I.B I.W [.arr aU, .arr aV] s.mem s₂.mem := by
    rw [m₁] at hf
    exact KF.of_frm hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨.arr aU, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
      · exact ⟨.arr aV, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
  have h₂ := h.step f₂ (all_mut_arrs (js := [aU, aV]) (by decide)) (k₁.trans k₂) (by decide)
  have tU₂ : atop I s₂.mem aU = 0 := by
    rw [← hU0]
    dsimp only [atop]
    rw [m₁] at hf
    exact hf.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega)
  -- `kOk := ` the mask of `v ≤ 1`.
  refine wp_seqs_append (by simp [constA]) (by simp [ltA]) (WP.mono (constA_k h₂ 2) fun s₃ ⟨h₃, f₃, c₃, _⟩ => ?_)
  have hokC : [Rc.arr aC].all Rc.ok = true := by decide
  have c2 : av I s₃.mem aC = 2 := av_of_full c₃ (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide)
    (show 2 ≤ 64 * I.W by omega)))
  have vV₃ : av I s₃.mem aV = v1 := by rw [← hY]; exact f₃.av hokC (by decide) (by decide) hZ
  refine wp_seqs_append (by simp [ltA]) (by simp) (WP.mono (ltA_k h₃ (a := aV) (b := aC) (by decide) (by decide))
    fun s₄ ⟨h₄, m₄, hbp, _, _, _, k₄⟩ => ?_)
  rw [vV₃, c2] at hbp
  refine wp_seqs_append (by simp) (by simp [constA]) ?_
  simp only [seqs]
  have hst := h₄.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.mem = s₄.mem.writeW (off I.B (8 * kOk)) (mask (decide (v1 < 2))) ∧
    t.gpr .rbp = mask (!decide (v1 < 2))) (by xrun [State.ea, hdr, h₄.ws.rdi, hdrOff, hst, hbp, sxM1, maskNot]) rfl)
    fun s₅ ⟨⟨hm₅, hbp₅⟩, k₅⟩ => ?_
  obtain ⟨h₅, f₅, ok₅⟩ := h₄.hdrW (i := kOk) (by unfold kOk sFn; omega) hm₅ k₅ (by decide)
  have hokO : [Rc.hdr kOk].all Rc.ok = true := by decide
  -- `[aV] := 3` for `v ≤ 1`.
  refine wp_seqs_append (by simp [constA]) (by simp [selC]) (WP.mono (constA_k h₅ 3) fun s₆ ⟨h₆, f₆, c₆, k₆⟩ => ?_)
  have c3 : av I s₆.mem aC = 3 := av_of_full c₆ (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide)
    (show 2 ≤ 64 * I.W by omega)))
  have vV₆ : av I s₆.mem aV = v1 := by
    rw [← vV₃, f₆.av hokC (by decide) (by decide) hZ, f₅.av hokO (by decide) (by decide) hZ, m₄]
  refine wp_seqs_append (by simp [selC]) (by simp) (WP.mono (selC_k h₆ (j := aV) (by decide) (by decide)
    (c := !decide (v1 < 2)) (by rw [k₆.gpr (by decide), hbp₅])) fun s₇ ⟨h₇, f₇, vV₇, _, _⟩ => ?_)
  rw [vV₆, c3] at vV₇
  generalize hM : (if (!decide (v1 < 2)) = true then v1 else 3) = M at vV₇
  have hMo : M % 2 = 1 ∧ 1 < M := by
    rw [← hM]
    by_cases hv : v1 < 2
    · simp [hv]
    · simp only [hv, decide_false, Bool.not_false, ite_true]; exact ⟨hodd (by omega), by omega⟩
  -- The inverse modulo `M`.
  refine wp_seqs_append (by simp) (by simp [constA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₇ (j := aM) (by decide)) fun s₇' ⟨h₇', f₇', _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₇' (o := aM) (a := aV) (by decide) (by decide) (by decide))
    fun s₈ ⟨h₈, f₈', vM₈, _, _⟩ => WP.seq (WP.mono (zeroA_k h₈ (j := aX₁) (by decide)) fun s₉ ⟨h₉, f₉, z₉, _⟩ =>
      WP.seq (WP.mono (setOne_k h₉ (j := aX₁) (by decide) z₉) fun s₁₀ ⟨h₁₀, f₁₀, o₁₀, _⟩ =>
        WP.seq (WP.mono (zeroA_k h₁₀ (j := aX₂) (by decide)) fun s₁₁ ⟨h₁₁, f₁₁, z₁₁, _⟩ => ?_)))))
  have f₈ : KF I.B I.W [.arr aM] s₇.mem s₈.mem := (f₇'.trans f₈').mono (by simp)
  rw [f₇'.av (by decide) (j := aV) (by decide) (by decide) hZ] at vM₈
  have hokM : [Rc.arr aM].all Rc.ok = true := by decide
  have hok1 : [Rc.arr aX₁].all Rc.ok = true := by decide
  have hok2 : [Rc.arr aX₂].all Rc.ok = true := by decide
  have pres : ∀ j, j < 16 → j ≠ aM → j ≠ aX₁ → j ≠ aX₂ → av I s₁₁.mem j = av I s₇.mem j := fun j hj h1 h2 h3 => by
    rw [f₁₁.av hok2 hj (by simp [h3]) hZ, f₁₀.av hok1 hj (by simp [h2]) hZ, f₉.av hok1 hj (by simp [h2]) hZ,
      f₈.av hokM hj (by simp [h1]) hZ]
  have vU₁₁ : av I s₁₁.mem aU = u1 := by
    rw [pres aU (by decide) (by decide) (by decide) (by decide), ← hX,
      f₇.av (by decide) (j := aU) (by decide) (by decide) hZ, f₆.av hokC (by decide) (by decide) hZ,
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
      f₇.at (by decide) (j := aU) (by decide) (by decide) hZ, f₆.at hokC (by decide) (by decide) hZ,
      f₅.at hokO (by decide) (by decide) hZ, m₄, f₃.at hokC (by decide) (by decide) hZ, tU₂]
  refine WP.mono (inverse_k h₁₁ (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aM) (iT := aT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) tU₁₁ (by rw [vV₁₁, vM₁₁]) vX₁ vX₂) fun s₁₂ ⟨h₁₂, f₁₂, hinv⟩ => ?_
  rw [vM₁₁, vU₁₁] at hinv
  have hg := (hinv hMo.1 hMo.2).1
  -- The result 1 for `v ≤ 1`.
  refine wp_seqs_append (by simp [constA]) (by simp) (WP.mono (constA_k h₁₂ 1) fun s₁₃ ⟨h₁₃, f₁₃, c₁₃, k₁₃⟩ => ?_)
  have c1 : av I s₁₃.mem aC = 1 := av_of_full c₁₃ (Nat.one_lt_two_pow (by omega))
  have hokI : [Rc.arr aU, Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT, Rc.hdr sMo].all Rc.ok = true := by decide
  have ok₁₃ : word s₁₃.mem I.B (8 * kOk) = mask (decide (v1 < 2)) := by
    rw [f₁₃.word hokC (by decide) (by decide), f₁₂.word hokI (by decide) (by decide),
      f₁₁.word hok2 (by decide) (by decide), f₁₀.word hok1 (by decide) (by decide),
      f₉.word hok1 (by decide) (by decide), f₈.word hokM (by decide) (by decide),
      f₇.word (by decide) (by decide) (by decide), f₆.word hokC (by decide) (by decide), ok₅]
  refine wp_seqs_append (by simp) (by simp [selC]) ?_
  simp only [seqs]
  have hl := h₁₃.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask (!decide (v1 < 2)) ∧ t.mem = s₁₃.mem)
    (by xrun [State.ea, hdr, h₁₃.ws.rdi, hdrOff, hl, ok₁₃, sxM1, maskNot]) rfl) fun s₁₄ ⟨⟨hbp₁₄, m₁₄⟩, k₁₄⟩ => ?_
  have h₁₄ := h₁₃.step (cs := []) (by rw [m₁₄]; exact KF.refl _ _ _) rfl k₁₄ (by decide)
  refine WP.mono (selC_k h₁₄ (j := aV) (by decide) (by decide) hbp₁₄) fun t ⟨ht, f₁₅, vV, _, _⟩ => ?_
  have f₅' : KF I.B I.W [.hdr kOk] s₃.mem s₅.mem := by rw [← m₄]; exact f₅
  have f₁₅' : KF I.B I.W [.arr aV] s₁₃.mem t.mem := by rw [← m₁₄]; exact f₁₅
  refine ⟨ht, ?_, ?_⟩
  · exact (((((((((((f₂.trans f₃).trans f₅').trans f₆).trans f₇).trans f₈).trans f₉).trans f₁₀).trans f₁₁).trans
      f₁₂).trans f₁₃).trans f₁₅').mono (by simp)
  · rw [vV, m₁₄, c1, f₁₃.av hokC (by decide) (by decide) hZ, hg]
    by_cases hv : v1 < 2
    · simp [hv, show v1 ≤ 1 by omega]
    · simp only [hv, decide_false, Bool.not_false, ite_true, show ¬ v1 ≤ 1 by omega, ite_false]
      rw [← hM]; simp [hv]

/-! ## The lcm -/

/-- Word `W` of a number of `W + 2` words below `2^(64 W)`. -/
theorem top_zero_of_lt {m : Mem} {B : Addr} {d W : Nat} (h : wv m B d (W + 2) < 2 ^ (64 * W)) :
    word m B (d + 8 * W) = 0 := by
  have e := wv_add m B d W 2
  have : wv m B (d + 8 * W) 2 = 0 := by
    rcases Nat.eq_zero_or_pos (wv m B (d + 8 * W) 2) with h0 | h0
    · exact h0
    · have := Nat.le_mul_of_pos_right (2 ^ (64 * W)) h0; omega
  have := (wv_eq_zero_iff _ _ _ _).mp this 0 (by decide)
  simpa using this

theorem lcmPart_eq : lcmPart = phi ++ ([zeroA aU, copyA aU aPm, zeroA aV, copyA aV aQm] ++ (twos ++ (gcdUV ++
    [divmod aL aR aV aT]))) := by
  simp only [lcmPart, List.append_assoc]

/-- `lcmPart`: `[aL] := lcm(a, b)` for `[aPm] = a` and `[aQm] = b`, below
`2^(64 w)`, `W = 2 w`. -/
theorem lcm_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {w : Nat} (hW : I.W = 2 * w)
    {a b : Nat} (ha : av I s.mem aPm = a) (hb : av I s.mem aQm = b) (ha' : a < 2 ^ (64 * w))
    (hb' : b < 2 ^ (64 * w)) :
    WP isa (seqs lcmPart) s fun t => KS I m₀ t ∧
      KF I.B I.W [.arr aL, .arr aU, .arr aV, .arr aC, .arr aM, .arr aX₁, .arr aX₂, .arr aT, .arr aR, .hdr sMo,
        .hdr kOk] s.mem t.mem ∧ av I t.mem aL = Nat.lcm a b := by
  have hZ := h.hZ
  have hw1 := h.ws.w1
  have hab : a * b < 2 ^ (64 * I.W) := by
    rw [hW, show 64 * (2 * w) = 64 * w + 64 * w by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le ha' (by omega) (Nat.two_pow_pos _)
  rw [lcmPart_eq]
  refine wp_seqs_append (by simp [phi]) (by simp) (WP.mono (phi_k h hW ha hb ha' hb') fun s₁ ⟨h₁, f₁, v₁⟩ => ?_)
  have hokL : [Rc.arr aL].all Rc.ok = true := by decide
  have vL₁ : av I s₁.mem aL = a * b := av_of_full v₁ hab
  have tL₁ : atop I s₁.mem aL = 0 := top_zero_of_lt (by rw [v₁]; exact hab)
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
    fun s₆ ⟨⟨h₆, f₆, tU₆, tV₆, tL₆⟩, hv₆⟩ => ?_)
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
  have hokG : [Rc.arr aU, Rc.arr aV, Rc.arr aC, Rc.arr aM, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT, Rc.hdr sMo,
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

end VG.Proof.RsaKeyGen.X86_64.Key
