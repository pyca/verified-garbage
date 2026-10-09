import VerifiedGarbage.Proof.Rsa.AArch64.CkPhase
import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyTop

/-!
# `vg_rsa_check_crt_key` on AArch64: the phases

`vg_rsa_check_key`'s phases (`Proof/Rsa/AArch64/CkPhase.lean`) without the
checks of `d`, and with `reduceTop` for `divmod`: modulo `X - 1`
(`phModC_ok`) and `qInv` (`phQIC_ok`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.CheckKey (sP sPlen sQ sQlen sQI aX aR aM aA aRem aT aOne aE ltA mulE mulXR)
open VG.Impl.Rsa.AArch64.CheckCrtKey (aQ reduceTop topE topQ modOne modChecks)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- `reduceTop top`: the remainder of `[aA]` by `[aM]` into `[aRem]`, when
the words of `[aA]` from `c` up are below `[aM]`. -/
theorem ckReduceTop_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {top : List Instr} {c : Nat}
    (hT : TopOk top I.B I.Z s.mem c) (hc1 : 1 ≤ c) (hc : c < wW I.k) :
    WP isa (seqs (reduceTop top)) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (I.av s.mem aA / 2 ^ (64 * c) < I.av s.mem aM → I.av t.mem aRem = I.av s.mem aA % I.av s.mem aM) ∧
      ∀ i < 16, i ≠ aRem → i ≠ aQ → i ≠ aT → I.av t.mem i = I.av s.mem i := by
  have hn := h.ws.scr.nowrap
  refine WP.mono (reduceTop_ok h.ws hT hc1 hc) fun t ⟨_, f, k, hv⟩ => ?_
  have hr : ∀ r ∈ [ar (wW I.k) aQ, ar (wW I.k) aRem, ar (wW I.k) aT], ∃ j < 16, r = ar (wW I.k) j := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨aQ, by decide, rfl⟩
    · exact ⟨aRem, by decide, rfl⟩
    · exact ⟨aT, by decide, rfl⟩
  refine ⟨h.step f (fun r hr' => by obtain ⟨j, _, rfl⟩ := hr r hr'; exact Mut.ofSlot _ _ _)
    (fun r hr' => by obtain ⟨j, hj, rfl⟩ := hr r hr'; exact h.ws.sl hj) k (by decide), ?_, fun hlt => ?_,
    fun i hi h1 h2 h3 => ?_⟩
  · exact f.word_eq (fun r hr' => by
      obtain ⟨j, hj, rfl⟩ := hr r hr'
      have := hdr_lt_slot (wW I.k) j (show Public.sMask < 32 by decide); exact Or.inl (by omega))
      (by simp only [Public.sMask, sFn]; omega)
  · have hM : 0 < I.av s.mem aM := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
    have hr' := hv hlt
    have hlt' : wv t.mem I.B (slot (wW I.k) aRem) (wW I.k + 1) < 2 ^ (64 * wW I.k) := by
      rw [hr']; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hM) (Nat.le_of_lt (wv_lt _ _ _ _))
    unfold CkIn.av
    rw [wv_low_of_lt (v := wW I.k) (w := wW I.k + 1) (by omega) hlt', hr']
  · exact f.wv_eq (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl <;> dsimp only
      · have := slot_sep (w := wW I.k) h2; omega
      · have := slot_sep (w := wW I.k) h1; omega
      · have := slot_sep (w := wW I.k) h3; omega) (by have := h.ws.sl hi; omega)

/-- `topE`: `x13 := 1`. -/
theorem topE_ok (B : Addr) (Z : Nat) (m₀ : Mem) : TopOk topE B Z m₀ 1 := fun t _ _ _ =>
  WP.mono (WP.keep [.x13] (Q := fun t' => t'.gpr .x13 = BitVec.ofNat 64 1 ∧ t'.mem = t.mem ∧ t'.c = t.c)
    (by unfold topE; brun) (by decide) (by decide) (by decide +kernel)) fun _ ⟨h, k⟩ => ⟨h, k.mono (by simp)⟩

/-- `topQ`: `x13 := ⌈q_len / 8⌉`, from the header slot of `q_len`. -/
theorem topQ_ok {B : Addr} {Z : Nat} {m₀ : Mem} {ql : Nat} (hq : word m₀ B (8 * sQlen) = BitVec.ofNat 64 ql)
    (hql : ql < 2 ^ 32) (hZ : 8 * 32 ≤ Z) : TopOk topQ B Z m₀ ((ql + 7) / 8) := fun t hs h0 hh => by
  have hl := hs.ld (d := 8 * sQlen) (by simp only [sQlen, sFn]; omega)
  refine WP.mono (WP.keep [.x13] (Q := fun t' => t'.gpr .x13 = BitVec.ofNat 64 ((ql + 7) / 8) ∧ t'.mem = t.mem ∧
    t'.c = t.c) ?_ (by decide) (by decide) (by decide +kernel)) fun _ ⟨h, k⟩ => ⟨h, k.mono (by simp)⟩
  unfold topQ
  brun [h0, hl, hh sQlen (by decide), hq, BitVec.ofNat_add_ofNat, shr_ofNat (show ql + 7 < 2 ^ 64 by omega)]
  rfl

/-- `modOne top`: the mask of `[aA] mod [aM] = 1`, when the words of `[aA]`
from `c` up are below `[aM]`. -/
theorem ckModOneTop_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {c : Bool} (hm : mword s.mem I.B = mask c)
    (hO : I.av s.mem aOne = 1) {top : List Instr} {k : Nat} (hT : TopOk top I.B I.Z s.mem k) (hk1 : 1 ≤ k)
    (hk : k < wW I.k) :
    WP isa (seqs (modOne top)) s fun t => CkS I m₀ t ∧ (∃ r : Nat,
      (I.av s.mem aA / 2 ^ (64 * k) < I.av s.mem aM → r = I.av s.mem aA % I.av s.mem aM) ∧
      mword t.mem I.B = mask (decide (r = 1) && c)) ∧
      ∀ i < 16, i ≠ aRem → i ≠ aQ → i ≠ aT → I.av t.mem i = I.av s.mem i := by
  unfold modOne
  rw [List.append_assoc]
  refine wp_seqs_append (by simp [reduceTop]) (by simp [eqA]) (WP.mono (ckReduceTop_ok h hT hk1 hk)
    fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine WP.mono (ckEq_ok h₁ (a := aRem) (b := aOne) (by decide) (by decide) (m₁.trans hm)) fun t ⟨ht, mt, ot⟩ => ?_
  refine ⟨ht, ⟨I.av s₁.mem aRem, v₁, ?_⟩, fun i hi h1 h2 h3 => by rw [ot i hi, o₁ i hi h1 h2 h3]⟩
  rw [mt, o₁ aOne (by decide) (by decide) (by decide) (by decide), hO]

/-- A product by a number below `2^(64 k)`, shifted down by `64 k` bits, is at
most the other factor. -/
theorem mul_div_top_le {a b k : Nat} (hb : b < 2 ^ (64 * k)) : a * b / 2 ^ (64 * k) ≤ a :=
  Nat.div_le_of_le_mul (by rw [Nat.mul_comm (2 ^ _)]; exact Nat.mul_le_mul_left a (Nat.le_of_lt hb))

theorem ckcModChecks_eq (sX sXlen sDX : Nat) : modChecks sX sXlen sDX =
    loadA aM sX sXlen ++ (([.block (decA aM)] : List (Prog isa)) ++ (loadA aX sDX sXlen ++ (ltA aX aM ++
      (mulE ++ modOne topE)))) := by
  simp only [modChecks, List.append_assoc]

/-- The checks modulo `X - 1` of `vg_rsa_check_crt_key`, for the prime `X`
(the bytes `xb`) and its exponent `dX` (the bytes `dxb`). -/
theorem phModC_ok {I : CkIn} {m₀ : Mem} {s : State} {c : Bool} (h : KS I m₀ c s) (L : CkLens I) (hE64 : I.E < 2 ^ 64)
    {sX sXlen sDX xl : Nat} {pX pDX : Addr} {xb dxb : List Byte} (hsX : sX < 32) (hsL : sXlen < 32)
    (hsD : sDX < 32) (hxl1 : 1 ≤ xl) (hxl2 : xl < I.k) (hxb : xb.length = xl) (hdxb : dxb.length = xl)
    (hA : ∀ t, CkS I m₀ t → word t.mem I.B (8 * sX) = pX ∧ word t.mem I.B (8 * sXlen) = BitVec.ofNat 64 xl ∧
      Src t I.B I.Z pX xb ∧ word t.mem I.B (8 * sDX) = pDX ∧ Src t I.B I.Z pDX dxb) :
    WP isa (seqs (modChecks sX sXlen sDX)) s fun t => ∃ g : Bool, KS I m₀ (g && c) t ∧
      (Spec.Rsa.os2ip xb % 2 = 1 → 1 < Spec.Rsa.os2ip xb →
        g = (decide (Spec.Rsa.os2ip dxb < Spec.Rsa.os2ip xb - 1) &&
          decide (I.E * Spec.Rsa.os2ip dxb % (Spec.Rsa.os2ip xb - 1) = 1))) := by
  obtain ⟨hs, hm, hN, hE, hO⟩ := h
  rw [ckcModChecks_eq]
  -- `[aM] := X - 1`.
  obtain ⟨a1, a2, a3, -, -⟩ := hA s hs
  refine wp_seqs_append (by simp [loadA]) (by simp) (WP.mono (ckLoad_ok hs (j := aM) (by decide) hsX hsL a1 a2 a3
    hxb hxl1 (Nat.le_of_lt hxl2)) fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine wp_seqs_append (a := [.block (decA aM)]) (by simp) (by simp [loadA]) (WP.mono (ckDec_ok h₁)
    fun s₂ ⟨h₂, m₂, v₂, o₂⟩ => ?_)
  rw [v₁] at v₂
  -- `dX < X - 1`.
  obtain ⟨-, b2, -, b4, b5⟩ := hA s₂ h₂
  refine wp_seqs_append (by simp [loadA]) (by simp [ltA]) (WP.mono (ckLoad_ok h₂ (j := aX) (by decide) hsD hsL b4
    b2 b5 hdxb hxl1 (Nat.le_of_lt hxl2)) fun s₃ ⟨h₃, m₃, v₃, o₃⟩ => ?_)
  have M₃ : I.av s₃.mem aM = I.av s₂.mem aM := o₃ aM (by decide) (by decide)
  refine wp_seqs_append (by simp [ltA]) (by simp [mulE]) (WP.mono (ckLt_ok h₃ (a := aX) (b := aM) (by decide)
    (by decide) (m₃.trans (m₂.trans (m₁.trans hm)))) fun s₄ ⟨h₄, m₄, o₄⟩ => ?_)
  rw [v₃, M₃] at m₄
  -- `e dX mod (X - 1) = 1`.
  have E₄ : I.av s₄.mem aE = I.E := by
    rw [o₄ aE (by decide), o₃ aE (by decide) (by decide), o₂ aE (by decide) (by decide),
      o₁ aE (by decide) (by decide), hE]
  have X₄ : I.av s₄.mem aX = Spec.Rsa.os2ip dxb := by rw [o₄ aX (by decide), v₃]
  refine wp_seqs_append (by simp [mulE]) (by simp [modOne]) (WP.mono (ckMulE_ok h₄ L
    (by rw [X₄]; exact lt_w (by rw [hdxb]; exact Nat.le_of_lt hxl2))) fun s₅ ⟨h₅, m₅, v₅, o₅⟩ => ?_)
  rw [X₄, e_word E₄ hE64] at v₅
  have O₅ : I.av s₅.mem aOne = 1 := by
    rw [o₅ aOne (by decide) (by decide), o₄ aOne (by decide), o₃ aOne (by decide) (by decide),
      o₂ aOne (by decide) (by decide), o₁ aOne (by decide) (by decide), hO]
  have hw1 : 1 < wW I.k := by simp only [wW, wk]; omega
  refine WP.mono (ckModOneTop_ok h₅ (m₅.trans m₄) O₅ (topE_ok _ _ _) (Nat.le_refl _) hw1)
    fun t ⟨ht, ⟨r, hr, mt⟩, ot⟩ => ?_
  have M₅ : I.av s₅.mem aM = I.av s₂.mem aM := by
    rw [o₅ aM (by decide) (by decide), o₄ aM (by decide), M₃]
  rw [v₅, M₅] at hr
  have keep : ∀ i, i = 0 ∨ i = aE ∨ i = aOne → I.av t.mem i = I.av s.mem i := by
    intro i hi
    have h16 : i < 16 := by rcases hi with rfl | rfl | rfl <;> decide
    have d1 : i ≠ aM := by rcases hi with rfl | rfl | rfl <;> decide
    have d2 : i ≠ aX := by rcases hi with rfl | rfl | rfl <;> decide
    have d3 : i ≠ aA := by rcases hi with rfl | rfl | rfl <;> decide
    have d4 : i ≠ aRem := by rcases hi with rfl | rfl | rfl <;> decide
    have d5 : i ≠ aT := by rcases hi with rfl | rfl | rfl <;> decide
    have d6 : i ≠ aQ := by rcases hi with rfl | rfl | rfl <;> decide
    rw [ot i h16 d4 d6 d5, o₅ i h16 d3, o₄ i h16, o₃ i h16 d2, o₂ i h16 d1, o₁ i h16 d1]
  refine ⟨decide (Spec.Rsa.os2ip dxb < I.av s₂.mem aM) && decide (r = 1), ⟨ht, ?_,
    by rw [keep 0 (.inl rfl), hN], by rw [keep aE (.inr (.inl rfl)), hE], by rw [keep aOne (.inr (.inr rfl)), hO]⟩,
    fun ho h1 => ?_⟩
  · rw [mt]
    cases decide (r = 1) <;> cases decide (Spec.Rsa.os2ip dxb < I.av s₂.mem aM) <;> cases c <;> rfl
  · have hM : I.av s₂.mem aM = Spec.Rsa.os2ip xb - 1 := v₂ ho
    rw [hM]
    by_cases hlt : Spec.Rsa.os2ip dxb < Spec.Rsa.os2ip xb - 1
    · rw [hr (by rw [hM]; exact Nat.lt_of_le_of_lt (mul_div_top_le (k := 1) (by simpa using hE64)) hlt),
        hM, Nat.mul_comm (Spec.Rsa.os2ip dxb) I.E]
    · simp only [hlt, decide_false, Bool.false_and]

/-- `qInv < p` and `q qInv ≡ 1 (mod p)`, by the shortened remainder. -/
theorem phQIC_ok {I : CkIn} {m₀ : Mem} {s : State} {c : Bool} (h : KS I m₀ c s) (L : CkLens I) :
    WP isa (seqs (loadA aM sP sPlen ++ (loadA aX sQI sPlen ++ (ltA aX aM ++ (loadA aR sQ sQlen ++
      (mulXR ++ modOne topQ)))))) s fun t => ∃ g : Bool, KS I m₀ (g && c) t ∧
      (0 < I.P → g = (decide (I.QI < I.P) && decide (I.Q * I.QI % I.P = 1))) := by
  obtain ⟨hs, hm, hN, hE, hO⟩ := h
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (ckLoad_ok hs (j := aM) (by decide) (by decide)
    (by decide) hs.args.p hs.args.pl hs.p L.pbl L.pl1 (Nat.le_of_lt L.pl2)) fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp [ltA]) (WP.mono (ckLoad_ok h₁ (j := aX) (by decide) (by decide)
    (by decide) h₁.args.qi h₁.args.pl h₁.qi L.qibl L.pl1 (Nat.le_of_lt L.pl2)) fun s₂ ⟨h₂, m₂, v₂, o₂⟩ => ?_)
  have M₂ : I.av s₂.mem aM = I.P := by rw [o₂ aM (by decide) (by decide), v₁]
  refine wp_seqs_append (by simp [ltA]) (by simp [loadA]) (WP.mono (ckLt_ok h₂ (a := aX) (b := aM) (by decide)
    (by decide) (m₂.trans (m₁.trans hm))) fun s₃ ⟨h₃, m₃, o₃⟩ => ?_)
  rw [v₂, M₂] at m₃
  refine wp_seqs_append (by simp [loadA]) (by simp [mulXR]) (WP.mono (ckLoad_ok h₃ (j := aR) (by decide) (by decide)
    (by decide) h₃.args.q h₃.args.ql h₃.q L.qbl L.ql1 (Nat.le_of_lt L.ql2)) fun s₄ ⟨h₄, m₄, v₄, o₄⟩ => ?_)
  have X₄ : I.av s₄.mem aX = I.QI := by rw [o₄ aX (by decide) (by decide), o₃ aX (by decide), v₂]
  refine wp_seqs_append (by simp [mulXR]) (by simp [modOne]) (WP.mono (ckMulXR_ok h₄ L
    (by rw [X₄]; exact lt_w (by rw [L.qibl]; exact Nat.le_of_lt L.pl2))
    (by rw [v₄]; exact lt_w (by rw [L.qbl]; exact Nat.le_of_lt L.ql2))) fun s₅ ⟨h₅, m₅, v₅, o₅⟩ => ?_)
  rw [X₄, v₄] at v₅
  have O₅ : I.av s₅.mem aOne = 1 := by
    rw [o₅ aOne (by decide) (by decide), o₄ aOne (by decide) (by decide), o₃ aOne (by decide),
      o₂ aOne (by decide) (by decide), o₁ aOne (by decide) (by decide), hO]
  -- `c = ⌈q_len / 8⌉` words: `q < 2^(64 c)`.
  have hk1 : 1 ≤ (I.ql + 7) / 8 := by have := L.ql1; omega
  have hk : (I.ql + 7) / 8 < wW I.k := by have := L.ql2; simp only [wW, wk]; omega
  refine WP.mono (ckModOneTop_ok h₅ (m₅.trans (m₄.trans m₃)) O₅ (topQ_ok h₅.args.ql
    (by have := L.ql2; have := L.k2; omega) (by have := h₅.ws.h256; omega)) hk1 hk)
    fun t ⟨ht, ⟨r, hr, mt⟩, ot⟩ => ?_
  have M₅ : I.av s₅.mem aM = I.P := by
    rw [o₅ aM (by decide) (by decide), o₄ aM (by decide) (by decide), o₃ aM (by decide), M₂]
  rw [v₅, M₅] at hr
  have keep : ∀ i, i = 0 ∨ i = aE ∨ i = aOne → I.av t.mem i = I.av s.mem i := by
    intro i hi
    have h16 : i < 16 := by rcases hi with rfl | rfl | rfl <;> decide
    have d1 : i ≠ aM := by rcases hi with rfl | rfl | rfl <;> decide
    have d2 : i ≠ aX := by rcases hi with rfl | rfl | rfl <;> decide
    have d3 : i ≠ aA := by rcases hi with rfl | rfl | rfl <;> decide
    have d4 : i ≠ aRem := by rcases hi with rfl | rfl | rfl <;> decide
    have d5 : i ≠ aT := by rcases hi with rfl | rfl | rfl <;> decide
    have d6 : i ≠ aR := by rcases hi with rfl | rfl | rfl <;> decide
    have d7 : i ≠ aQ := by rcases hi with rfl | rfl | rfl <;> decide
    rw [ot i h16 d4 d7 d5, o₅ i h16 d3, o₄ i h16 d6, o₃ i h16, o₂ i h16 d2, o₁ i h16 d1]
  refine ⟨decide (I.QI < I.P) && decide (r = 1), ⟨ht, ?_, by rw [keep 0 (.inl rfl), hN],
    by rw [keep aE (.inr (.inl rfl)), hE], by rw [keep aOne (.inr (.inr rfl)), hO]⟩, fun hP => ?_⟩
  · rw [mt]
    cases decide (r = 1) <;> cases decide (I.QI < I.P) <;> cases c <;> rfl
  · by_cases hlt : I.QI < I.P
    · have hq : I.Q < 2 ^ (64 * ((I.ql + 7) / 8)) := Nat.lt_of_lt_of_le (os2ip_lt I.qb)
        (by rw [L.qbl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
            exact Nat.pow_le_pow_right (by decide) (by omega))
      rw [hr (Nat.lt_of_le_of_lt (mul_div_top_le hq) hlt), Nat.mul_comm I.QI I.Q]
    · simp only [hlt, decide_false, Bool.false_and]

end VG.Proof.Rsa.AArch64
