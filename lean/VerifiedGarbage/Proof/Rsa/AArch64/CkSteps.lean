import VerifiedGarbage.Proof.Rsa.AArch64.CkState

/-!
# `vg_rsa_check_key` on AArch64: the pieces on `CkS`

Each piece of `main` keeps `CkS`; what it does to the arrays' values
(`CkIn.av`, over `W` words) and to the mask, and which arrays it leaves.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The value of array `j` over `W` words. -/
abbrev CkIn.av (I : CkIn) (m : Mem) (j : Nat) : Nat := wv m I.B (slot (wW I.k) j) (wW I.k)

/-- The mask after a piece that changes only array `j`. -/
theorem mword_arr {m m' : Mem} {B : Addr} {W j L : Nat} (o : Outside B (slot W j) L m m') :
    mword m' B = mword m B :=
  o.word (Or.inl (by have := hdr_lt_slot W j (show Public.sMask < 32 by decide); omega))
    (by simp only [Public.sMask, sFn]; omega)

theorem CkS.av_out {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {m m' : Mem} {j L : Nat}
    (o : Outside I.B (slot (wW I.k) j) L m m') (hL : L ≤ 8 * (wW I.k + 2)) {i : Nat} (hi : i < 16) (hij : i ≠ j) :
    I.av m' i = I.av m i :=
  outside_arr o hL hij (by omega) hi h.ws.hZ h.ws.scr.nowrap

/-- `loadA j`: the bytes `bs` into array `j`. -/
theorem ckLoad_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {j sPtr sLen len : Nat} {p : Addr}
    {bs : List Byte} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (hp : word s.mem I.B (8 * sPtr) = p) (hl : word s.mem I.B (8 * sLen) = BitVec.ofNat 64 len)
    (hsrc : Src s I.B I.Z p bs) (hlen : bs.length = len) (hl1 : 1 ≤ len) (hlk : len ≤ I.k) :
    WP isa (seqs (loadA j sPtr sLen)) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧ I.av t.mem j = Spec.Rsa.os2ip bs ∧
      ∀ i < 16, i ≠ j → I.av t.mem i = I.av s.mem i :=
  WP.mono (loadA_ok h.ws hj hP hL hp hl hsrc hlen hl1 (by simp only [wW, wk]; omega)) fun _ ⟨hv, o, _, _, k⟩ =>
    ⟨h.arr hj (Nat.le_refl _) o k (by decide), mword_arr o, hv, fun _ hi hij => h.av_out o (Nat.le_refl _) hi hij⟩

/-- `ltA a b`: the mask of `[a] < [b]`. -/
theorem ckLt_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {a b : Nat} (ha : a < 16) (hb : b < 16)
    {c : Bool} (hm : mword s.mem I.B = mask c) :
    WP isa (seqs (ltA a b)) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mask (decide (I.av s.mem a < I.av s.mem b) && c) ∧
      ∀ i < 16, I.av t.mem i = I.av s.mem i :=
  WP.mono (ltA_ok h.ws ha hb hm) fun _ ⟨hmt, k⟩ =>
    let ⟨ht, hw, hv⟩ := h.mask hmt k (by decide)
    ⟨ht, hw, hv⟩

/-- `eqA a b` and `andZero`: the mask of `[a] = [b]`. -/
theorem ckEq_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {a b : Nat} (ha : a < 16) (hb : b < 16)
    {c : Bool} (hm : mword s.mem I.B = mask c) :
    WP isa (seqs (eqA a b ++ ([.block andZero] : List (Prog isa)))) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mask (decide (I.av s.mem a = I.av s.mem b) && c) ∧
      ∀ i < 16, I.av t.mem i = I.av s.mem i := by
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok h.ws ha hb) fun s₁ ⟨hz, m₁, _, _, k₁⟩ => ?_)
  have h₁ : CkS I m₀ s₁ := h.step (rs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) (by simp) k₁ (by decide)
  simp only [seqs]
  refine WP.mono (andZero_ok (c := c) h₁.ws (by rw [m₁]; exact hm) hz) fun t ⟨⟨hmt, _⟩, k⟩ => ?_
  obtain ⟨ht, hw, hv⟩ := h₁.mask hmt k (by decide)
  exact ⟨ht, hw, fun i hi => by unfold CkIn.av; rw [hv i hi, m₁]⟩

theorem CkLens.w1 {I : CkIn} (L : CkLens I) : 1 ≤ wk I.k := by have := L.k1; simp only [wk]; omega

/-- `mulE`: `[aA] := [aX] e`, `e` the low word of `[aE]`. -/
theorem ckMulE_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) (L : CkLens I)
    (hX : I.av s.mem aX < 2 ^ (64 * wk I.k)) :
    WP isa (seqs mulE) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      I.av t.mem aA = I.av s.mem aX * (word s.mem I.B (slot (wW I.k) aE)).toNat ∧
      ∀ i < 16, i ≠ aA → I.av t.mem i = I.av s.mem i :=
  WP.mono (mulE_ok h.ws L.w1 rfl hX) fun _ ⟨hv, o, k⟩ =>
    ⟨h.arr (by decide) (Nat.le_refl _) o k (by decide), mword_arr o, hv,
      fun _ hi hij => h.av_out o (Nat.le_refl _) hi hij⟩

/-- `mulXR`: `[aA] := [aX] [aR]`. -/
theorem ckMulXR_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) (L : CkLens I)
    (hX : I.av s.mem aX < 2 ^ (64 * wk I.k)) (hR : I.av s.mem aR < 2 ^ (64 * wk I.k)) :
    WP isa (seqs mulXR) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧ I.av t.mem aA = I.av s.mem aX * I.av s.mem aR ∧
      ∀ i < 16, i ≠ aA → I.av t.mem i = I.av s.mem i :=
  WP.mono (mulXR_ok h.ws L.w1 rfl hX rfl hR) fun _ ⟨hv, o, k⟩ =>
    ⟨h.arr (by decide) (Nat.le_refl _) o k (by decide), mword_arr o, hv,
      fun _ hi hij => h.av_out o (Nat.le_refl _) hi hij⟩

/-- `divmod aA aRem aM aT`: the remainder of `[aA]` by `[aM]` into `[aRem]`. -/
theorem ckDivmod_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) :
    WP isa (divmod aA aRem aM aT) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (0 < I.av s.mem aM → I.av t.mem aRem = I.av s.mem aA % I.av s.mem aM) ∧
      ∀ i < 16, i ≠ aA → i ≠ aRem → i ≠ aT → I.av t.mem i = I.av s.mem i := by
  have hn := h.ws.scr.nowrap
  refine WP.mono (divmod_ok h.ws (iQ := aA) (iR := aRem) (iD := aM) (iT := aT) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨_, f, k, hv⟩ => ?_
  have hr : ∀ r ∈ [ar (wW I.k) aA, ar (wW I.k) aRem, ar (wW I.k) aT], ∃ j < 16, r = ar (wW I.k) j := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨aA, by decide, rfl⟩
    · exact ⟨aRem, by decide, rfl⟩
    · exact ⟨aT, by decide, rfl⟩
  refine ⟨h.step f (fun r hr' => by obtain ⟨j, _, rfl⟩ := hr r hr'; exact Mut.ofSlot _ _ _)
    (fun r hr' => by obtain ⟨j, hj, rfl⟩ := hr r hr'; exact h.ws.sl hj) k (by decide), ?_, fun hM => ?_,
    fun i hi h1 h2 h3 => ?_⟩
  · exact f.word_eq (fun r hr' => by
      obtain ⟨j, hj, rfl⟩ := hr r hr'
      have := hdr_lt_slot (wW I.k) j (show Public.sMask < 32 by decide); exact Or.inl (by omega))
      (by simp only [Public.sMask, sFn]; omega)
  · obtain ⟨hr', _⟩ := hv hM
    have hlt : wv t.mem I.B (slot (wW I.k) aRem) (wW I.k + 1) < 2 ^ (64 * wW I.k) := by
      rw [hr']; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hM) (Nat.le_of_lt (wv_lt _ _ _ _))
    unfold CkIn.av
    rw [wv_low_of_lt (v := wW I.k) (w := wW I.k + 1) (by omega) hlt, hr']
  · exact f.wv_eq (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl <;> dsimp only
      · have := slot_sep (w := wW I.k) h1; omega
      · have := slot_sep (w := wW I.k) h2; omega
      · have := slot_sep (w := wW I.k) h3; omega) (by have := h.ws.sl hi; omega)

/-- `decA aM`: `[aM] - 1`, for an odd `[aM]`. -/
theorem ckDec_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) :
    WP isa (.block (decA aM)) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (I.av s.mem aM % 2 = 1 → I.av t.mem aM = I.av s.mem aM - 1) ∧
      ∀ i < 16, i ≠ aM → I.av t.mem i = I.av s.mem i := by
  have hn := h.ws.scr.nowrap
  have sM := h.ws.sl (j := aM) (by decide)
  refine WP.mono (decA_ok h.ws (j := aM) (by decide)) fun t ⟨m, k⟩ => ?_
  have o := writeW_outside s.mem I.B (word s.mem I.B (slot (wW I.k) aM) - 1) (d := slot (wW I.k) aM) (by omega)
  rw [← m] at o
  refine ⟨h.arr (by decide) (by omega) o k (by decide), mword_arr o, fun ho => ?_,
    fun _ hi hij => h.av_out o (by omega) hi hij⟩
  have w1 := h.ws.w1
  have e3 := wv_low (m := t.mem) (B := I.B) (e := slot (wW I.k) aM) (w := wW I.k) (by omega)
  have e2 := wv_low (m := s.mem) (B := I.B) (e := slot (wW I.k) aM) (w := wW I.k) (by omega)
  have hw3 : word t.mem I.B (slot (wW I.k) aM) = word s.mem I.B (slot (wW I.k) aM) - 1 := by
    rw [m, word_writeW_self]
  have hup : wv t.mem I.B (slot (wW I.k) aM + 8) (wW I.k - 1) = wv s.mem I.B (slot (wW I.k) aM + 8) (wW I.k - 1) := by
    rw [m]; exact (writeW_outside s.mem I.B _ (by omega)).wv (Or.inr (by omega)) (by omega)
  unfold CkIn.av at ho ⊢
  rw [e2] at ho ⊢
  have hodd : (word s.mem I.B (slot (wW I.k) aM)).toNat % 2 = 1 := by omega
  have hsub : (word s.mem I.B (slot (wW I.k) aM) - 1).toNat = (word s.mem I.B (slot (wW I.k) aM)).toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; rfl
  rw [e3, hup, hw3, hsub]
  omega

/-- `[aOne] := 1`. -/
theorem ckOne_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) :
    WP isa (seqs [zeroA aOne, .block (setOneA aOne)]) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧ I.av t.mem aOne = 1 ∧
      ∀ i < 16, i ≠ aOne → I.av t.mem i = I.av s.mem i := by
  have hn := h.ws.scr.nowrap
  have sO := h.ws.sl (j := aOne) (by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_ok h.ws (j := aOne) (by decide)) fun s₁ ⟨hz, o₁, _, _, _, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.mono (setOneA_ok h₁.ws (j := aOne) (by decide)) fun t ⟨m, k⟩ => ?_
  have o := writeW_outside s₁.mem I.B (1 : BitVec 64) (d := slot (wW I.k) aOne) (by omega)
  rw [← m] at o
  refine ⟨h₁.arr (by decide) (by omega) o k (by decide), (mword_arr o).trans (mword_arr o₁), ?_,
    fun i hi hij => (h₁.av_out o (by omega) hi hij).trans (h.av_out o₁ (Nat.le_refl _) hi hij)⟩
  have w1 := h.ws.w1
  have hz' : ∀ q < wW I.k + 2, word s₁.mem I.B (slot (wW I.k) aOne + 8 * q) = 0 := (wv_eq_zero_iff _ _ _ _).mp hz
  unfold CkIn.av
  rw [wv_low (by omega), m, word_writeW_self, (writeW_outside s₁.mem I.B _ (by omega)).wv (Or.inr (by omega)) (by omega),
    wv_zero (n := wW I.k - 1) fun q hq => by rw [Nat.add_assoc, ← Nat.mul_one 8, ← Nat.mul_add]; exact hz' _ (by omega)]
  rfl

end VG.Proof.Rsa.AArch64
