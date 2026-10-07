import VerifiedGarbage.Proof.Rsa.AArch64.CkSteps
import VerifiedGarbage.Proof.Rsa.AArch64.CvMain

/-!
# `vg_rsa_check_key` on AArch64: the phases of `main`

`KS c`: `CkS`, the mask `c`, and `n`, `e` and 1 in their arrays. Each phase
of the checks and'es its conditions into the mask (`phDN_ok`, `phPQ_ok`,
`phMod_ok`, `phQI_ok`), exactly when the facts the key's other checks give
hold.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

abbrev CkIn.N (I : CkIn) : Nat := Spec.Rsa.os2ip I.nb
abbrev CkIn.E (I : CkIn) : Nat := Spec.Rsa.os2ip I.eb
abbrev CkIn.D (I : CkIn) : Nat := Spec.Rsa.os2ip I.db
abbrev CkIn.P (I : CkIn) : Nat := Spec.Rsa.os2ip I.pb
abbrev CkIn.Q (I : CkIn) : Nat := Spec.Rsa.os2ip I.qb
abbrev CkIn.DP (I : CkIn) : Nat := Spec.Rsa.os2ip I.dpb
abbrev CkIn.DQ (I : CkIn) : Nat := Spec.Rsa.os2ip I.dqb
abbrev CkIn.QI (I : CkIn) : Nat := Spec.Rsa.os2ip I.qib

theorem wp_seqs_cons {e : Prog isa} {l : List (Prog isa)} (hl : l ≠ []) {s : State} {Q : State → Prop}
    (h : WP isa e s fun t => WP isa (seqs l) t Q) : WP isa (seqs (e :: l)) s Q := by
  obtain ⟨d, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  exact WP.seq h

/-- A number of `len ≤ k` bytes fits in `w` words. -/
theorem lt_w {bs : List Byte} {k : Nat} (hl : bs.length ≤ k) : Spec.Rsa.os2ip bs < 2 ^ (64 * wk k) :=
  Nat.lt_of_lt_of_le (os2ip_lt bs) ((Nat.pow_le_pow_right (by decide) hl).trans
    ((pow256_le_wk k).trans (Nat.pow_le_pow_right (by decide) (by simp only [wk]; omega))))

/-- Between the phases. -/
def KS (I : CkIn) (m₀ : Mem) (c : Bool) (s : State) : Prop :=
  CkS I m₀ s ∧ mword s.mem I.B = mask c ∧ I.av s.mem 0 = I.N ∧ I.av s.mem aE = I.E ∧ I.av s.mem aOne = 1

/-- `d < n`. -/
theorem phDN_ok {I : CkIn} {m₀ : Mem} {s : State} {c : Bool} (h : KS I m₀ c s) (L : CkLens I) :
    WP isa (seqs (loadA aX sD sDlen ++ ltA aX 0)) s (KS I m₀ (decide (I.D < I.N) && c)) := by
  obtain ⟨hs, hm, hN, hE, hO⟩ := h
  refine wp_seqs_append (by simp [loadA]) (by simp [ltA]) (WP.mono (ckLoad_ok hs (j := aX) (by decide) (by decide)
    (by decide) hs.args.d hs.args.dl hs.d L.dbl L.dl1 L.dl2) fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine WP.mono (ckLt_ok h₁ (a := aX) (b := 0) (by decide) (by decide) (m₁.trans hm)) fun t ⟨ht, mt, ot⟩ => ?_
  rw [v₁, o₁ 0 (by decide) (by decide), hN] at mt
  exact ⟨ht, mt, by rw [ot 0 (by decide), o₁ 0 (by decide) (by decide), hN],
    by rw [ot aE (by decide), o₁ aE (by decide) (by decide), hE], by rw [ot aOne (by decide), o₁ aOne (by decide) (by decide), hO]⟩

/-- `p q = n`. -/
theorem phPQ_ok {I : CkIn} {m₀ : Mem} {s : State} {c : Bool} (h : KS I m₀ c s) (L : CkLens I) :
    WP isa (seqs (loadA aX sP sPlen ++ (loadA aR sQ sQlen ++ (mulXR ++ (eqA aA 0 ++ ([.block andZero] : List (Prog isa))))))) s
      (KS I m₀ (decide (I.P * I.Q = I.N) && c)) := by
  obtain ⟨hs, hm, hN, hE, hO⟩ := h
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (ckLoad_ok hs (j := aX) (by decide) (by decide)
    (by decide) hs.args.p hs.args.pl hs.p L.pbl L.pl1 (Nat.le_of_lt L.pl2)) fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp [mulXR]) (WP.mono (ckLoad_ok h₁ (j := aR) (by decide)
    (by decide) (by decide) h₁.args.q h₁.args.ql h₁.q L.qbl L.ql1 (Nat.le_of_lt L.ql2)) fun s₂ ⟨h₂, m₂, v₂, o₂⟩ => ?_)
  have x₂ : I.av s₂.mem aX = I.P := by rw [o₂ aX (by decide) (by decide), v₁]
  refine wp_seqs_append (by simp [mulXR]) (by simp [eqA]) (WP.mono (ckMulXR_ok h₂ L
    (by rw [x₂]; exact lt_w (by rw [L.pbl]; exact Nat.le_of_lt L.pl2))
    (by rw [v₂]; exact lt_w (by rw [L.qbl]; exact Nat.le_of_lt L.ql2))) fun s₃ ⟨h₃, m₃, v₃, o₃⟩ => ?_)
  refine WP.mono (ckEq_ok h₃ (a := aA) (b := 0) (by decide) (by decide) (m₃.trans (m₂.trans (m₁.trans hm))))
    fun t ⟨ht, mt, ot⟩ => ?_
  have k0 : ∀ i < 16, i ≠ aX → i ≠ aR → i ≠ aA → I.av t.mem i = I.av s.mem i := fun i hi h1 h2 h3 => by
    rw [ot i hi, o₃ i hi h3, o₂ i hi h2, o₁ i hi h1]
  rw [v₃, x₂, v₂, o₃ 0 (by decide) (by decide), o₂ 0 (by decide) (by decide), o₁ 0 (by decide) (by decide), hN] at mt
  exact ⟨ht, mt, by rw [k0 0 (by decide) (by decide) (by decide) (by decide), hN],
    by rw [k0 aE (by decide) (by decide) (by decide) (by decide), hE],
    by rw [k0 aOne (by decide) (by decide) (by decide) (by decide), hO]⟩

/-- `modOne`: the mask of `[aA] mod [aM] = 1`. -/
theorem ckModOne_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {c : Bool} (hm : mword s.mem I.B = mask c)
    (hO : I.av s.mem aOne = 1) :
    WP isa (seqs modOne) s fun t => CkS I m₀ t ∧ (∃ r : Nat, (0 < I.av s.mem aM → r = I.av s.mem aA % I.av s.mem aM) ∧
      mword t.mem I.B = mask (decide (r = 1) && c)) ∧
      ∀ i < 16, i ≠ aA → i ≠ aRem → i ≠ aT → I.av t.mem i = I.av s.mem i := by
  unfold modOne
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [eqA]) (WP.mono (ckDivmod_ok h) fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine WP.mono (ckEq_ok h₁ (a := aRem) (b := aOne) (by decide) (by decide) (m₁.trans hm)) fun t ⟨ht, mt, ot⟩ => ?_
  refine ⟨ht, ⟨I.av s₁.mem aRem, v₁, ?_⟩, fun i hi h1 h2 h3 => by rw [ot i hi, o₁ i hi h1 h2 h3]⟩
  rw [mt, o₁ aOne (by decide) (by decide) (by decide) (by decide), hO]

theorem modChecks_eq (sX sXlen sDX : Nat) : modChecks sX sXlen sDX =
    loadA aM sX sXlen ++ (([.block (decA aM)] : List (Prog isa)) ++ (loadA aX sDX sXlen ++ (ltA aX aM ++ (loadA aX sD sDlen ++
      (mulE ++ (modOne ++ (loadA aX sDX sXlen ++ (mulE ++ modOne)))))))) := by
  simp only [modChecks, List.append_assoc]

/-- The low word of `[aE]` is `e`, below `2^64`. -/
theorem e_word {I : CkIn} {m : Mem} (hE : I.av m aE = I.E) (hE64 : I.E < 2 ^ 64) :
    (word m I.B (slot (wW I.k) aE)).toNat = I.E := by
  rw [← wv_mod64 m I.B (slot (wW I.k) aE) (n := wW I.k) (by simp only [wW]; omega), show wv m I.B (slot (wW I.k) aE) (wW I.k) = I.E
    from hE, Nat.mod_eq_of_lt hE64]

/-- The checks modulo `X - 1`, for the prime `X` (the bytes `xb`) and its
exponent `dX` (the bytes `dxb`). -/
theorem phMod_ok {I : CkIn} {m₀ : Mem} {s : State} {c : Bool} (h : KS I m₀ c s) (L : CkLens I) (hE64 : I.E < 2 ^ 64)
    {sX sXlen sDX xl : Nat} {pX pDX : Addr} {xb dxb : List Byte} (hsX : sX < 32) (hsL : sXlen < 32)
    (hsD : sDX < 32) (hxl1 : 1 ≤ xl) (hxl2 : xl < I.k) (hxb : xb.length = xl) (hdxb : dxb.length = xl)
    (hA : ∀ t, CkS I m₀ t → word t.mem I.B (8 * sX) = pX ∧ word t.mem I.B (8 * sXlen) = BitVec.ofNat 64 xl ∧
      Src t I.B I.Z pX xb ∧ word t.mem I.B (8 * sDX) = pDX ∧ Src t I.B I.Z pDX dxb) :
    WP isa (seqs (modChecks sX sXlen sDX)) s fun t => ∃ g : Bool, KS I m₀ (g && c) t ∧
      (Spec.Rsa.os2ip xb % 2 = 1 → 1 < Spec.Rsa.os2ip xb →
        g = (decide (Spec.Rsa.os2ip dxb < Spec.Rsa.os2ip xb - 1) &&
          decide (I.D * I.E % (Spec.Rsa.os2ip xb - 1) = 1) &&
          decide (I.E * Spec.Rsa.os2ip dxb % (Spec.Rsa.os2ip xb - 1) = 1))) := by
  obtain ⟨hs, hm, hN, hE, hO⟩ := h
  rw [modChecks_eq]
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
  refine wp_seqs_append (by simp [ltA]) (by simp [loadA]) (WP.mono (ckLt_ok h₃ (a := aX) (b := aM) (by decide)
    (by decide) (m₃.trans (m₂.trans (m₁.trans hm)))) fun s₄ ⟨h₄, m₄, o₄⟩ => ?_)
  rw [v₃, M₃] at m₄
  -- `d e mod (X - 1) = 1`.
  refine wp_seqs_append (by simp [loadA]) (by simp [mulE]) (WP.mono (ckLoad_ok h₄ (j := aX) (by decide) (by decide)
    (by decide) h₄.args.d h₄.args.dl h₄.d L.dbl L.dl1 L.dl2) fun s₅ ⟨h₅, m₅, v₅, o₅⟩ => ?_)
  have E₅ : I.av s₅.mem aE = I.E := by
    rw [o₅ aE (by decide) (by decide), o₄ aE (by decide), o₃ aE (by decide) (by decide), o₂ aE (by decide) (by decide),
      o₁ aE (by decide) (by decide), hE]
  refine wp_seqs_append (by simp [mulE]) (by simp [modOne]) (WP.mono (ckMulE_ok h₅ L
    (by rw [v₅]; exact lt_w (by rw [L.dbl]; exact L.dl2))) fun s₆ ⟨h₆, m₆, v₆, o₆⟩ => ?_)
  rw [v₅, e_word E₅ hE64] at v₆
  have O₆ : I.av s₆.mem aOne = 1 := by
    rw [o₆ aOne (by decide) (by decide), o₅ aOne (by decide) (by decide), o₄ aOne (by decide),
      o₃ aOne (by decide) (by decide), o₂ aOne (by decide) (by decide), o₁ aOne (by decide) (by decide), hO]
  refine wp_seqs_append (by simp [modOne]) (by simp [loadA]) (WP.mono (ckModOne_ok h₆
    (m₆.trans (m₅.trans m₄)) O₆) fun s₇ ⟨h₇, ⟨r₁, hr₁, m₇⟩, o₇⟩ => ?_)
  have M₆ : I.av s₆.mem aM = I.av s₂.mem aM := by
    rw [o₆ aM (by decide) (by decide), o₅ aM (by decide) (by decide), o₄ aM (by decide), M₃]
  rw [v₆, M₆] at hr₁
  -- `e dX mod (X - 1) = 1`.
  obtain ⟨-, -, -, c4, c5⟩ := hA s₇ h₇
  refine wp_seqs_append (by simp [loadA]) (by simp [mulE]) (WP.mono (ckLoad_ok h₇ (j := aX) (by decide) hsD hsL c4
    ((hA s₇ h₇).2.1) c5 hdxb hxl1 (Nat.le_of_lt hxl2)) fun s₈ ⟨h₈, m₈, v₈, o₈⟩ => ?_)
  have E₈ : I.av s₈.mem aE = I.E := by
    rw [o₈ aE (by decide) (by decide), o₇ aE (by decide) (by decide) (by decide) (by decide), o₆ aE (by decide)
      (by decide), E₅]
  refine wp_seqs_append (by simp [mulE]) (by simp [modOne]) (WP.mono (ckMulE_ok h₈ L
    (by rw [v₈]; exact lt_w (by rw [hdxb]; exact Nat.le_of_lt hxl2))) fun s₉ ⟨h₉, m₉, v₉, o₉⟩ => ?_)
  rw [v₈, e_word E₈ hE64] at v₉
  have O₉ : I.av s₉.mem aOne = 1 := by
    rw [o₉ aOne (by decide) (by decide), o₈ aOne (by decide) (by decide),
      o₇ aOne (by decide) (by decide) (by decide) (by decide), O₆]
  refine WP.mono (ckModOne_ok h₉ (m₉.trans (m₈.trans m₇)) O₉) fun t ⟨ht, ⟨r₂, hr₂, mt⟩, ot⟩ => ?_
  have M₉ : I.av s₉.mem aM = I.av s₂.mem aM := by
    rw [o₉ aM (by decide) (by decide), o₈ aM (by decide) (by decide), o₇ aM (by decide) (by decide) (by decide)
      (by decide), M₆]
  rw [v₉, M₉] at hr₂
  -- What the other arrays keep.
  have keep : ∀ i, i = 0 ∨ i = aE ∨ i = aOne → I.av t.mem i = I.av s.mem i := by
    intro i hi
    have h16 : i < 16 := by rcases hi with rfl | rfl | rfl <;> decide
    have d1 : i ≠ aM := by rcases hi with rfl | rfl | rfl <;> decide
    have d2 : i ≠ aX := by rcases hi with rfl | rfl | rfl <;> decide
    have d3 : i ≠ aA := by rcases hi with rfl | rfl | rfl <;> decide
    have d4 : i ≠ aRem := by rcases hi with rfl | rfl | rfl <;> decide
    have d5 : i ≠ aT := by rcases hi with rfl | rfl | rfl <;> decide
    rw [ot i h16 d3 d4 d5, o₉ i h16 d3, o₈ i h16 d2, o₇ i h16 d3 d4 d5, o₆ i h16 d3, o₅ i h16 d2, o₄ i h16,
      o₃ i h16 d2, o₂ i h16 d1, o₁ i h16 d1]
  refine ⟨decide (Spec.Rsa.os2ip dxb < I.av s₂.mem aM) && decide (r₁ = 1) && decide (r₂ = 1), ⟨ht, ?_,
    by rw [keep 0 (.inl rfl), hN], by rw [keep aE (.inr (.inl rfl)), hE], by rw [keep aOne (.inr (.inr rfl)), hO]⟩,
    fun ho h1 => ?_⟩
  · rw [mt]
    cases decide (r₂ = 1) <;> cases decide (r₁ = 1) <;> cases decide (Spec.Rsa.os2ip dxb < I.av s₂.mem aM) <;>
      cases c <;> rfl
  · have hM : I.av s₂.mem aM = Spec.Rsa.os2ip xb - 1 := v₂ ho
    have hM0 : 0 < I.av s₂.mem aM := by rw [hM]; omega
    rw [hr₁ hM0, hr₂ hM0, hM, Nat.mul_comm (Spec.Rsa.os2ip dxb) I.E]

/-- `qInv < p` and `q qInv ≡ 1 (mod p)`. -/
theorem phQI_ok {I : CkIn} {m₀ : Mem} {s : State} {c : Bool} (h : KS I m₀ c s) (L : CkLens I) :
    WP isa (seqs (loadA aM sP sPlen ++ (loadA aX sQI sPlen ++ (ltA aX aM ++ (loadA aR sQ sQlen ++
      (mulXR ++ modOne)))))) s fun t => ∃ g : Bool, KS I m₀ (g && c) t ∧
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
  refine WP.mono (ckModOne_ok h₅ (m₅.trans (m₄.trans m₃)) O₅) fun t ⟨ht, ⟨r, hr, mt⟩, ot⟩ => ?_
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
    rw [ot i h16 d3 d4 d5, o₅ i h16 d3, o₄ i h16 d6, o₃ i h16, o₂ i h16 d2, o₁ i h16 d1]
  refine ⟨decide (I.QI < I.P) && decide (r = 1), ⟨ht, ?_, by rw [keep 0 (.inl rfl), hN],
    by rw [keep aE (.inr (.inl rfl)), hE], by rw [keep aOne (.inr (.inr rfl)), hO]⟩, fun hP => ?_⟩
  · rw [mt]
    cases decide (r = 1) <;> cases decide (I.QI < I.P) <;> cases c <;> rfl
  · rw [hr hP, Nat.mul_comm I.QI I.Q]

end VG.Proof.Rsa.AArch64
