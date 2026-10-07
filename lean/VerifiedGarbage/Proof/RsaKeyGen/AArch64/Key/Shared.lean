import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Pieces
import VerifiedGarbage.Proof.Bignum.AArch64.CrtRows

/-!
# An RSA key from its primes on AArch64: pieces more than one stage uses

The products `mulTo` (`φ` in `lcmPart`, `n` in `nPart`), `inverse`'s start
`invFrom` and `gcdIsOne` (`dOdd`, `dEven`, `qinvPart`), and `divisorOf`
(`dEven`, `crtPart`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## Products -/

theorem ofNat_shr1 {W : Nat} (hW : W < 2 ^ 64) : BitVec.ofNat 64 W >>> 1 = BitVec.ofNat 64 (W / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, Nat.pow_one]

/-- `mulTo o a b`: `[o] := [a] [b]` (`W + 2` words) for `[a]` and `[b]`
below `2^(64 w)`, `W = 2 w`. -/
theorem mulTo_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {w : Nat} (hW : I.W = 2 * w) {o a b : Nat}
    (ho : o < 16) (ha : a < 16) (hb : b < 16) (hoa : o ≠ a) (hob : o ≠ b)
    {x y : Nat} (hx : av I s.mem a = x) (hy : av I s.mem b = y) (hx' : x < 2 ^ (64 * w)) (hy' : y < 2 ^ (64 * w)) :
    WP isa (seqs (mulTo o a b)) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr o] s.mem t.mem ∧
      wv t.mem I.B (slot I.W o) (I.W + 2) = x * y := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  have hw1 : 1 ≤ w := by have := h.ws.w1; omega
  have hw2 := h.ws.w2
  have so := h.ws.sl ho
  have sa := h.ws.sl ha
  have sb := h.ws.sl hb
  have pa := slot_sep (w := I.W) hoa
  have pb := slot_sep (w := I.W) hob
  simp only [mulTo, seqs]
  refine WP.seq (WP.mono (zeroA_k h ho) fun s₁ ⟨h₁, f₁, hz, _, k₁⟩ => ?_)
  have eX : av I s₁.mem a = x := by rw [f₁.av (by simp [Rc.ok, ho]) ha (by simp [Ne.symm hoa]) hZ, hx]
  have eY : av I s₁.mem b = y := by rw [f₁.av (by simp [Rc.ok, ho]) hb (by simp [Ne.symm hob]) hZ, hy]
  have e : ws ++ base b .x9 ++ base o .x8 ++ base a .x16 ++ ([mov .x11 .x16, .lsr .x .x12 .x12 1, mov .x13 .x12,
      movi .x7 0] : List Instr) = ws ++ ((base b .x9 ++ base o .x8 ++ base a .x16) ++
        ([mov .x11 .x16, .lsr .x .x12 .x12 1, mov .x13 .x12, movi .x7 0] : List Instr)) := by
    simp only [List.append_assoc]
  rw [e]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h₁.ws.ws_ok fun s₂ ⟨⟨h12, h11, m₂, _⟩, k₂⟩ =>
    WP.block_append_iff.mpr (WP.mono (base3_ok b o a .x9 .x8 .x16 ((k₂.gpr .x0 (by decide)).trans h₁.ws.x0) h11)
      fun s₃ ⟨⟨h9, h8, h16, m₃, _⟩, k₃⟩ => ?_)))
  have h12₃ : s₃.gpr .x12 = BitVec.ofNat 64 (2 * w) := by rw [(k₃.gpr .x12 (by decide)).trans h12, hW]
  refine WP.mono (WP.keep [.x11, .x12, .x13, .x7] (Q := fun t => t.gpr .x11 = off I.B (slot I.W a) ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x13 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧ t.mem = s₃.mem) (by
    brun [h16, h12₃, ofNat_shr1 (show 2 * w < 2 ^ 64 by omega), show 2 * w / 2 = w by omega])
    (by decide) (by decide) (by decide +kernel)) fun s₄ ⟨⟨h11₄, h12₄, h13₄, h7₄, m₄⟩, k₄⟩ => ?_
  have k24 := (k₂.trans k₃).trans k₄
  have hm₄ : s₄.mem = s₁.mem := by rw [m₄, m₃, m₂]
  have eX₄ : wv s₄.mem I.B (slot I.W a) w = x := by
    rw [hm₄]; exact (wv_low_of_lt (v := w) (by omega) (show av I s₁.mem a < _ by rw [eX]; exact hx')).trans eX
  have eY₄ : wv s₄.mem I.B (slot I.W b) w = y := by
    rw [hm₄]; exact (wv_low_of_lt (v := w) (by omega) (show av I s₁.mem b < _ by rw [eY]; exact hy')).trans eY
  have eA₄ : wv s₄.mem I.B (slot I.W o) (w + w + 2) = 0 := by
    rw [hm₄, show w + w + 2 = I.W + 2 by omega]; exact hz
  refine WP.mono (mulRows_ok (wa := w) (wb := w) (h₁.ws.scr.congr k24.wr) h11₄ ((k₄.gpr .x9 (by decide)).trans h9)
    h13₄ h12₄ ((k₄.gpr .x8 (by decide)).trans h8) h7₄ hw1 hw1 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by rw [eA₄]; exact Nat.two_pow_pos _)) fun t ⟨hv, o', k₅⟩ => ?_
  rw [hm₄] at o'
  rw [hm₄, show w + w + 2 = I.W + 2 by omega] at hv
  rw [hm₄] at eX₄ eY₄
  have f := KF.arr1 (B := I.B) (W := I.W) (j := o) (o' : Outside I.B (slot I.W o) (8 * (w + w + 2)) s₁.mem t.mem)
    (Nat.le_refl _) (by omega)
  refine ⟨h₁.step f (all_mut_arr ho) (k24.trans k₅) (by decide), (f₁.trans f).mono (by simp), ?_⟩
  rw [hv, hz, eX₄, eY₄, Nat.zero_add]

/-! ## `inverse`'s start and its result -/

/-- `invFrom j`: `v := [j]`, `x₁ := 1`, `x₂ := 0`. -/
theorem invFrom_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {j : Nat} (hj : j < 16) (hjV : j ≠ aV) :
    WP isa (seqs (invFrom j)) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aV, .arr aX₁, .arr aX₂] s.mem t.mem ∧
      av I t.mem aV = av I s.mem j ∧ av I t.mem aX₁ = 1 ∧ av I t.mem aX₂ = 0 := by
  have hZ := h.hZ
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  simp only [invFrom, seqs]
  refine WP.seq (WP.mono (zeroA_k h (j := aV) (by decide)) fun s₁ ⟨h₁, f₁, _, _, _⟩ => ?_)
  refine WP.seq (WP.mono (copyA_k h₁ (o := aV) (a := j) (by decide) hj (Ne.symm hjV)) fun s₂ ⟨h₂, f₂, v₂, _, _⟩ => ?_)
  refine WP.seq (WP.mono (zeroA_k h₂ (j := aX₁) (by decide)) fun s₃ ⟨h₃, f₃, z₃, _, _⟩ => ?_)
  refine WP.seq (WP.mono (setOne_k h₃ (j := aX₁) (by decide) z₃) fun s₄ ⟨h₄, f₄, o₄, _⟩ => ?_)
  refine WP.mono (zeroA_k h₄ (j := aX₂) (by decide)) fun t ⟨ht, f₅, z₅, _, _⟩ => ?_
  refine ⟨ht, ((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).mono (by simp), ?_, ?_, ?_⟩
  · rw [f₅.av (by decide) (by decide) (by decide) hZ, f₄.av (by decide) (by decide) (by decide) hZ,
      f₃.av (by decide) (by decide) (by decide) hZ, v₂, f₁.av (by decide) hj (by simp [hjV]) hZ]
  · rw [f₅.av (by decide) (by decide) (by decide) hZ]
    exact av_of_full o₄ (Nat.one_lt_two_pow (by omega))
  · exact av_of_full z₅ (Nat.two_pow_pos _)

/-- `gcdIsOne`: `kOk &= ` the mask of `[aV] = 1`. -/
theorem gcdIsOne_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {c : Bool}
    (hok : word s.mem I.B (8 * kOk) = mask c) :
    WP isa (seqs gcdIsOne) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aC, .hdr kOk] s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (decide (av I s.mem aV = 1) && c) := by
  have hZ := h.hZ
  unfold gcdIsOne
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [constA]) (by simp [eqMask, eqA]) (WP.mono (constA_k h (x := 1) (by decide))
    fun s₁ ⟨h₁, f₁, c₁, _⟩ => ?_)
  have c1 : av I s₁.mem aC = 1 := av_of_full c₁ (Nat.one_lt_two_pow (by have := h.ws.w1; omega))
  have vV : av I s₁.mem aV = av I s.mem aV := f₁.av (by decide) (by decide) (by decide) hZ
  have hok₁ : word s₁.mem I.B (8 * kOk) = mask c := by rw [f₁.word (by decide) (by decide) (by decide), hok]
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) (WP.mono (eqMask_k h₁ (a := aV) (b := aC) (by decide)
    (by decide)) fun s₂ ⟨h₂, m₂, h15, _, _⟩ => ?_)
  rw [vV, c1] at h15
  simp only [seqs]
  have hst := h₂.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  have hld := h₂.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  have hok₂ : word s₂.mem I.B (8 * kOk) = mask c := by rw [m₂, hok₁]
  refine WP.mono (WP.keep [.x3, .x15] (Q := fun t => t.mem = s₂.mem.writeW (off I.B (8 * kOk))
    (mask (decide (av I s.mem aV = 1) && c))) (by
      brun [h₂.ws.x0, hdr_enc (show kOk < 32 by decide), hst, hld, h15, hok₂, mask_and'])
      (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₃⟩ => ?_
  obtain ⟨ht, f₃, hw⟩ := h₂.hdrW (i := kOk) (by unfold kOk sFn; omega) hm k₃
  exact ⟨ht, (f₁.trans (by rw [← m₂]; exact f₃)).mono (by simp), hw⟩

/-! ## Divisors -/

/-- `x`, or 1 for 0. -/
abbrev dv (x : Nat) : Nat := if x = 0 then 1 else x

theorem or_and1_mask (x : BitVec 64) (c : Bool) :
    x ||| (mask c &&& BitVec.setWidth 64 1#16) = if c then x ||| 1 else x := by
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
  rw [wv_low hw, wv_low (m := m) hw, word_writeW_self, o.wv (Or.inr (Nat.le_refl _)) (by omega)]
  cases c
  · simp
  · have hz := hc rfl
    rw [wv_low (m := m) hw] at hz
    have h0 : (word m I.B (slot I.W j)).toNat = 0 := by omega
    have h1 : wv m I.B (slot I.W j + 8) (I.W - 1) = 0 := by
      rcases Nat.eq_zero_or_pos (wv m I.B (slot I.W j + 8) (I.W - 1)) with h | h
      · exact h
      · have := Nat.le_mul_of_pos_right (2 ^ 64) h; omega
    have : word m I.B (slot I.W j) = 0 := BitVec.eq_of_toNat_eq h0
    simp only [ite_true]
    rw [this, h1]; decide

/-- `divisorOf j`: `[aM] := [j]`, or 1 for `[j] = 0`. -/
theorem divisorOf_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {j : Nat} (hj : j < 16) (hjM : j ≠ aM)
    (hjC : j ≠ aC) :
    WP isa (seqs (divisorOf j)) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aM, .arr aC] s.mem t.mem ∧
      av I t.mem aM = dv (av I s.mem j) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  have sM := h.ws.sl (j := aM) (by decide)
  unfold divisorOf
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [constA]) (WP.mono (zc_k h (o := aM) (a := j) (by decide) hj hjM.symm)
    fun s₁ ⟨h₁, f₁, v₁, _⟩ => ?_)
  refine wp_seqs_append (by simp [constA]) (by simp [eqMask, eqA]) (WP.mono (constA_k h₁ (x := 0) (by decide))
    fun s₂ ⟨h₂, f₂, c₂, _⟩ => ?_)
  have c0 : av I s₂.mem aC = 0 := av_of_full c₂ (Nat.two_pow_pos _)
  have vj : av I s₂.mem j = av I s.mem j := by
    rw [f₂.av (by decide) hj (by simp [hjC]) hZ, f₁.av (by decide) hj (by simp [hjM]) hZ]
  have vM₂ : av I s₂.mem aM = av I s.mem j := by rw [f₂.av (by decide) (by decide) (by decide) hZ, v₁]
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) (WP.mono (eqMask_k h₂ (a := j) (b := aC) hj (by decide))
    fun s₃ ⟨h₃, m₃, h15₃, _, _⟩ => ?_)
  rw [vj, c0] at h15₃
  simp only [seqs]
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (wsBase16_ok h₃ aM) fun s₄ ⟨⟨h16, _, _, m₄⟩, k₄⟩ => ?_
  have hs₄ := h₃.ws.scr.congr k₄.wr
  have h15 : s₄.gpr .x15 = mask (decide (av I s.mem j = 0)) := by rw [k₄.gpr .x15 (by decide), h15₃]
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.mem = s₃.mem.writeW (off I.B (slot I.W aM))
      (if decide (av I s.mem j = 0) then word s₃.mem I.B (slot I.W aM) ||| 1 else word s₃.mem I.B (slot I.W aM))) (by
    brun [h16, hs₄.ld (d := slot I.W aM) (by omega), hs₄.st (d := slot I.W aM) (by omega), h15, m₄, or_and1_mask])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₅⟩ => ?_
  have o₅ := writeW_outside s₃.mem I.B (if decide (av I s.mem j = 0) then word s₃.mem I.B (slot I.W aM) ||| 1 else
    word s₃.mem I.B (slot I.W aM)) (d := slot I.W aM) (by omega)
  rw [← hm] at o₅
  have f₅ := KF.arr1 (B := I.B) (W := I.W) (j := aM) o₅ (Nat.le_refl _) (by omega)
  refine ⟨h₃.step f₅ (all_mut_arr (by decide)) (k₄.trans k₅), ((f₁.trans f₂).trans (by rw [← m₃]; exact f₅)).mono
    (by simp), ?_⟩
  have vM₃ : av I s₃.mem aM = av I s.mem j := by rw [m₃, vM₂]
  rw [hm, av_or1 hw1 (by omega) (fun hc => by rw [vM₃]; simpa using hc), vM₃]
  by_cases hz : av I s.mem j = 0 <;> simp [hz, dv]

end VG.Proof.RsaKeyGen.AArch64.Key
