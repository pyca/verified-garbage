import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Qinv

/-!
# An RSA key from its primes on x86-64: `dP` and `dQ`

`divisorOf j`: `[aM] := [j]`, or 1 for 0 (`divisorOf_k`); `crtPart`:
`dP = d mod (p − 1)` into `aX₁` and `dQ = d mod (q − 1)` into `aV`
(`crtPart_k`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- A divisor: `x`, or 1 for 0. -/
abbrev dv (x : Nat) : Nat := if x = 0 then 1 else x

theorem divisorOf_eq (j : Nat) : divisorOf j = [zeroA aM, copyA aM j] ++ (constA 0 ++ (eqMask j aC ++
    [.block (ws ++ base aM .rbx ++ [.mov .rax (.mem (at0 .rbx)), .alu .and .rbp (.imm 1), .alu .or .rax (.reg .rbp),
      .store (at0 .rbx) .rax])])) := by
  simp only [divisorOf, List.append_assoc]

/-- `divisorOf j`. -/
theorem divisorOf_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16) (hjM : j ≠ aM)
    (hjC : j ≠ aC) :
    WP isa (seqs (divisorOf j)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aM, .arr aC] s.mem t.mem ∧
      av I t.mem aM = dv (av I s.mem j) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  have sM := h.ws.sl (j := aM) (by decide)
  rw [divisorOf_eq]
  refine wp_seqs_append (by simp) (by simp [constA]) (WP.mono (zc_k h (o := aM) (a := j) (by decide) hj hjM.symm)
    fun s₁ ⟨h₁, f₁, v₁, _⟩ => ?_)
  refine wp_seqs_append (by simp [constA]) (by simp [eqMask, eqA]) (WP.mono (constA_k h₁ 0) fun s₂ ⟨h₂, f₂, c₂, _⟩ => ?_)
  have c0 : av I s₂.mem aC = 0 := av_of_full c₂ (Nat.two_pow_pos _)
  have vj : av I s₂.mem j = av I s.mem j := by
    rw [f₂.av (by decide) hj (by simp [hjC]) hZ, f₁.av (by decide) hj (by simp [hjM]) hZ]
  have vM₂ : av I s₂.mem aM = av I s.mem j := by rw [f₂.av (by decide) (by decide) (by decide) hZ, v₁]
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) (WP.mono (eqMask_k h₂ (a := j) (b := aC) hj (by decide))
    fun s₃ ⟨h₃, m₃, hbp₃, _⟩ => ?_)
  rw [vj, c0] at hbp₃
  simp only [seqs]
  refine WP.mono (Q := fun (t : State) => t.mem = s₃.mem.writeW (off I.B (slot I.W aM))
      (if decide (av I s.mem j = 0) then word s₃.mem I.B (slot I.W aM) ||| 1 else word s₃.mem I.B (slot I.W aM)) ∧
      Keep [.r12, .r9, .rbx, .rax, .rbp] s₃ t) ?_ fun (t : State) ⟨m₄, k₄⟩ => ?_
  · rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono h₃.ws.ws_ok fun u₁ ⟨_, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok aM (r := .rbx) (by decide) ((ku₁.gpr (by decide)).trans h₃.ws.rdi) h9)
      fun u₂ ⟨hbx, mu₂, ku₂⟩ => ?_
    have hs₂ := h₃.ws.scr.congr (ku₁.trans ku₂).2.2
    have hbp : u₂.gpr .rbp = mask (decide (av I s.mem j = 0)) := by rw [(ku₁.trans ku₂).gpr (by decide), hbp₃]
    have hmu : u₂.mem = s₃.mem := by rw [mu₂, mu₁]
    refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.mem = s₃.mem.writeW (off I.B (slot I.W aM))
      (if decide (av I s.mem j = 0) then word s₃.mem I.B (slot I.W aM) ||| 1 else word s₃.mem I.B (slot I.W aM))) (by
        xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
          hs₂.ld (d := slot I.W aM) (by omega), hs₂.st (d := slot I.W aM) (by omega), hbp, hmu]
        rw [or_and1_mask]) rfl) fun t ⟨hm, k⟩ => ⟨hm, ((ku₁.trans ku₂).trans k).mono (by simp)⟩
  have o₄ := writeW_outside s₃.mem I.B (if decide (av I s.mem j = 0) then word s₃.mem I.B (slot I.W aM) ||| 1 else
    word s₃.mem I.B (slot I.W aM)) (d := slot I.W aM) (by omega)
  rw [← m₄] at o₄
  have f₄ := KF.arr1 (I := I) (j := aM) o₄ (Nat.le_refl _) (by omega)
  refine ⟨h₃.step f₄ (all_mut_arr (by decide)) k₄ (by decide), ((f₁.trans f₂).trans (by rw [← m₃]; exact f₄)).mono
    (by simp), ?_⟩
  have vM₃ : av I s₃.mem aM = av I s.mem j := by rw [m₃, vM₂]
  rw [m₄, av_or1 hw1 (by omega) (fun hc => by rw [vM₃]; simpa using hc), vM₃]
  by_cases hz : av I s.mem j = 0 <;> simp [hz, dv]

/-- The parts `crtPart` changes. -/
abbrev csC : List Rc := [.arr aM, .arr aC, .arr aU, .arr aV, .arr aT, .arr aX₁]

/-- `crtPart`: `[aX₁] := d mod dv(P − 1)`, `[aV] := d mod dv(Q − 1)`, for `[aDd] = d`,
`[aPm] = P − 1` and `[aQm] = Q − 1`. -/
theorem crtPart_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {d a b : Nat} (hd : av I s.mem aDd = d)
    (ha : av I s.mem aPm = a) (hb : av I s.mem aQm = b) :
    WP isa (seqs crtPart) s fun t => KS I m₀ t ∧ KF I.B I.W csC s.mem t.mem ∧
      av I t.mem aX₁ = d % dv a ∧ av I t.mem aV = d % dv b := by
  have hZ := h.hZ
  have hdv : ∀ x, 0 < dv x := fun x => by unfold dv; split <;> omega
  have hdW : ∀ {x}, x < 2 ^ (64 * I.W) → dv x < 2 ^ (64 * I.W) := fun hx => by
    unfold dv; split
    · exact Nat.one_lt_two_pow (by have := h.ws.w1; omega)
    · exact hx
  unfold crtPart
  simp only [List.append_assoc]
  -- `dP`.
  refine wp_seqs_append (by simp [divisorOf]) (by simp) (WP.mono (divisorOf_k h (j := aPm) (by decide) (by decide)
    (by decide)) fun s₁ ⟨h₁, f₁, v₁⟩ => ?_)
  rw [ha] at v₁
  have hok1 : [Rc.arr aM, Rc.arr aC].all Rc.ok = true := by decide
  have vD₁ : av I s₁.mem aDd = d := by rw [f₁.av hok1 (by decide) (by decide) hZ, hd]
  refine wp_seqs_append (by simp) (by simp [divisorOf]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₁ (j := aU) (by decide)) fun s₂ ⟨h₂, f₂, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₂ (o := aU) (a := aDd) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, v₃, _, _⟩ =>
      WP.seq (WP.mono (divmod_k h₃ (iQ := aU) (iR := aV) (iD := aM) (iT := aT) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨h₄, f₄, d₄⟩ =>
        WP.seq (WP.mono (zeroA_k h₄ (j := aX₁) (by decide)) fun s₅ ⟨h₅, f₅, _, _⟩ =>
          WP.mono (copyA_k h₅ (o := aX₁) (a := aV) (by decide) (by decide) (by decide))
            fun s₆ ⟨h₆, f₆, v₆, _, _⟩ => ?_))))
  have vM₃ : av I s₃.mem aM = dv a := by
    rw [f₃.av (by decide) (by decide) (by decide) hZ, f₂.av (by decide) (by decide) (by decide) hZ, v₁]
  have vU₃ : av I s₃.mem aU = d := by rw [v₃, f₂.av (by decide) (by decide) (by decide) hZ, vD₁]
  rw [vM₃, vU₃] at d₄
  have hR := (d₄ (hdv a)).1
  have hlt : d % dv a < dv a := Nat.mod_lt _ (hdv a)
  have vM₁W : dv a < 2 ^ (64 * I.W) := by rw [← v₁]; exact wv_lt _ _ _ _
  have vX₆ : av I s₆.mem aX₁ = d % dv a := by
    rw [v₆, f₅.av (by decide) (by decide) (by decide) hZ, ← hR]
    exact wv_low_of_lt (by omega) (by rw [hR]; omega)
  have hok4 : [Rc.arr aU, Rc.arr aV, Rc.arr aT].all Rc.ok = true := by decide
  have pres6 : ∀ j, j < 16 → j ≠ aU → j ≠ aV → j ≠ aT → j ≠ aX₁ → av I s₆.mem j = av I s₁.mem j :=
    fun j hj h1 h2 h3 h4 => by
      rw [f₆.av (by decide) hj (by simp [h4]) hZ, f₅.av (by decide) hj (by simp [h4]) hZ,
        f₄.av hok4 hj (by simp [h1, h2, h3]) hZ, f₃.av (by decide) hj (by simp [h1]) hZ,
        f₂.av (by decide) hj (by simp [h1]) hZ]
  have vQm₆ : av I s₆.mem aQm = b := by
    rw [pres6 aQm (by decide) (by decide) (by decide) (by decide) (by decide), f₁.av hok1 (by decide) (by decide) hZ, hb]
  have vD₆ : av I s₆.mem aDd = d := by
    rw [pres6 aDd (by decide) (by decide) (by decide) (by decide) (by decide), vD₁]
  -- `dQ`.
  refine wp_seqs_append (by simp [divisorOf]) (by simp) (WP.mono (divisorOf_k h₆ (j := aQm) (by decide) (by decide)
    (by decide)) fun s₇ ⟨h₇, f₇, v₇⟩ => ?_)
  rw [vQm₆] at v₇
  have vD₇ : av I s₇.mem aDd = d := by rw [f₇.av hok1 (by decide) (by decide) hZ, vD₆]
  have vX₇ : av I s₇.mem aX₁ = d % dv a := by rw [f₇.av hok1 (by decide) (by decide) hZ, vX₆]
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₇ (j := aU) (by decide)) fun s₈ ⟨h₈, f₈, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₈ (o := aU) (a := aDd) (by decide) (by decide) (by decide)) fun s₉ ⟨h₉, f₉, v₉, _, _⟩ =>
      WP.mono (divmod_k h₉ (iQ := aU) (iR := aV) (iD := aM) (iT := aT) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨ht, f₁₀, d₁₀⟩ => ?_))
  have vM₉ : av I s₉.mem aM = dv b := by
    rw [f₉.av (by decide) (by decide) (by decide) hZ, f₈.av (by decide) (by decide) (by decide) hZ, v₇]
  have vU₉ : av I s₉.mem aU = d := by rw [v₉, f₈.av (by decide) (by decide) (by decide) hZ, vD₇]
  rw [vM₉, vU₉] at d₁₀
  have hR' := (d₁₀ (hdv b)).1
  have vMb : dv b < 2 ^ (64 * I.W) := by rw [← v₇]; exact wv_lt _ _ _ _
  refine ⟨ht, ?_, ?_, ?_⟩
  · exact (((((((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).trans f₆).trans f₇).trans f₈).trans f₉).trans
      f₁₀).mono (by simp)
  · rw [f₁₀.av hok4 (by decide) (by decide) hZ, f₉.av (by decide) (by decide) (by decide) hZ,
      f₈.av (by decide) (by decide) (by decide) hZ, vX₇]
  · rw [← hR']
    exact wv_low_of_lt (by omega) (by rw [hR']; exact Nat.lt_trans (Nat.mod_lt _ (hdv b)) vMb)

end VG.Proof.RsaKeyGen.X86_64.Key
