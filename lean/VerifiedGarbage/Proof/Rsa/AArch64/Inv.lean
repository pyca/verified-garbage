import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.AArch64.Div

/-!
# RSA private keys on AArch64: the binary extended Euclidean algorithm

`invStep`, one step of `inverse`, is `KeyMath.invStep` on the arrays
(`invStepCode_ok`): `u`, `v`, `x₁` and `x₂` (`w` words each), while
`x₁, x₂ < m` and the word `w` of `u` is zero. Its parts: the masks and the
swaps (`invSwap_ok`), the subtractions (`invSubU_ok`, `invSubX_ok`) and the
halvings (`invHalfU_ok`, `invHalfX_ok`). `inverse` is `KeyMath.invIter` for
`128 w` steps from `(a, m, 1, 0)` (`inverse_ok`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem mask_and' (a b : Bool) : mask a &&& mask b = mask (a && b) := by
  cases a <;> cases b <;> rfl

/-- The mask of a word's low bit (`oddMask`). -/
theorem mask_low (x : BitVec 64) : 0 - (x &&& BitVec.setWidth 64 1#16) = mask (decide (x.toNat % 2 = 1)) := by
  have h2 : x &&& BitVec.setWidth 64 1#16 = BitVec.ofNat 64 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (BitVec.setWidth 64 1#16).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
    omega_using []
  rw [h2]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

theorem mask_low' (x : BitVec 64) : BitVec.setWidth 64 0#16 - (x &&& BitVec.setWidth 64 1#16) =
    mask (decide (x.toNat % 2 = 1)) := mask_low x

/-- Three bases. -/
theorem base3_ok {s : State} {B : Addr} {w : Nat} (i j k : Nat) (r₁ r₂ r₃ : Reg) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)))
    (h₁ : r₁ ≠ .x11 := by decide) (h₂ : r₂ ≠ .x11 := by decide) (h₃ : r₃ ≠ .x11 := by decide)
    (h₁₂ : r₂ ≠ r₁ := by decide) (h₁₃ : r₃ ≠ r₁ := by decide) (h₂₃ : r₃ ≠ r₂ := by decide)
    (hr1 : r₁ ≠ .x0 := by decide) (hr2 : r₂ ≠ .x0 := by decide)
    (hc₁ : writesOnly [r₁] (.block [.addImm .x r₁ .x0 hdrBytes]) = true := by decide)
    (hv₁ : Code.allInstrs keepsV (.block [.addImm .x r₁ .x0 hdrBytes] : Prog isa) = true := by decide +kernel)
    (hd₁ : writesOnly [r₁] (.block [.add .x r₁ r₁ .x11]) = true := by decide)
    (hw₁ : Code.allInstrs keepsV (.block [.add .x r₁ r₁ .x11] : Prog isa) = true := by decide +kernel)
    (hc₂ : writesOnly [r₂] (.block [.addImm .x r₂ .x0 hdrBytes]) = true := by decide)
    (hv₂ : Code.allInstrs keepsV (.block [.addImm .x r₂ .x0 hdrBytes] : Prog isa) = true := by decide +kernel)
    (hd₂ : writesOnly [r₂] (.block [.add .x r₂ r₂ .x11]) = true := by decide)
    (hw₂ : Code.allInstrs keepsV (.block [.add .x r₂ r₂ .x11] : Prog isa) = true := by decide +kernel)
    (hc₃ : writesOnly [r₃] (.block [.addImm .x r₃ .x0 hdrBytes]) = true := by decide)
    (hv₃ : Code.allInstrs keepsV (.block [.addImm .x r₃ .x0 hdrBytes] : Prog isa) = true := by decide +kernel)
    (hd₃ : writesOnly [r₃] (.block [.add .x r₃ r₃ .x11]) = true := by decide)
    (hw₃ : Code.allInstrs keepsV (.block [.add .x r₃ r₃ .x11] : Prog isa) = true := by decide +kernel) :
    WP isa (.block (base i r₁ ++ base j r₂ ++ base k r₃)) s fun t =>
      (t.gpr r₁ = off B (slot w i) ∧ t.gpr r₂ = off B (slot w j) ∧ t.gpr r₃ = off B (slot w k) ∧
        t.mem = s.mem ∧ t.c = s.c) ∧ Keep [r₁, r₂, r₃] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (base2_ok i j r₁ r₂ h0 h11 h₁ h₂ h₁₂ hr1 hc₁ hv₁ hd₁ hw₁ hc₂ hv₂ hd₂ hw₂)
    fun t₁ ⟨⟨e₁, e₂, m₁, c₁⟩, k₁⟩ => ?_
  have g : ∀ r, r ≠ r₁ → r ≠ r₂ → t₁.gpr r = s.gpr r := fun r a b => k₁.gpr r (by simp [a, b])
  refine WP.mono (base_ok k r₃ ((g _ (Ne.symm hr1) (Ne.symm hr2)).trans h0) ((g _ (Ne.symm h₁) (Ne.symm h₂)).trans h11)
    h₃ hc₃ hv₃ hd₃ hw₃) fun t ⟨⟨e₃, m₂, c₂⟩, k₂⟩ => ?_
  exact ⟨⟨(k₂.gpr r₁ (by simp [Ne.symm h₁₃])).trans e₁, (k₂.gpr r₂ (by simp [Ne.symm h₂₃])).trans e₂, e₃,
    m₂.trans m₁, c₂.trans c₁⟩, (k₁.trans k₂).mono (by simp)⟩

/-- The masks and the swaps: `(u, v, x₁, x₂)` swapped to `(v, u, x₂, x₁)`
if `u` is odd and below `v`, and the mask of `u` odd in `x9`. -/
theorem invSwap_ok {s : State} {B : Addr} {Z w : Nat} {iU iV iX₁ iX₂ : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (dUV : iU ≠ iV) (dX : iX₁ ≠ iX₂)
    (d₁ : iU ≠ iX₁) (d₂ : iU ≠ iX₂) (d₃ : iV ≠ iX₁) (d₄ : iV ≠ iX₂) {u v x₁ x₂ : Nat} {sw : Bool}
    (hu : wv s.mem B (slot w iU) w = u) (hv : wv s.mem B (slot w iV) w = v)
    (hx₁ : wv s.mem B (slot w iX₁) w = x₁) (hx₂ : wv s.mem B (slot w iX₂) w = x₂)
    (hsw : sw = (decide (u % 2 = 1) && decide (u < v))) :
    WP isa (seqs (invSwapP iU iV iX₁ iX₂)) s fun t =>
      t.gpr .x9 = mask (decide (u % 2 = 1)) ∧ t.gpr .x7 = 0 ∧
      wv t.mem B (slot w iU) w = (if sw then v else u) ∧ wv t.mem B (slot w iV) w = (if sw then u else v) ∧
      wv t.mem B (slot w iX₁) w = (if sw then x₂ else x₁) ∧ wv t.mem B (slot w iX₂) w = (if sw then x₁ else x₂) ∧
      Frm B [(slot w iU, 8 * w), (slot w iV, 8 * w), (slot w iX₁, 8 * w), (slot w iX₂, 8 * w)] s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x7, .x9, .x14, .x15, .x16, .x17] s t := by
  have hn := hs.nowrap
  have sU := Nat.le_trans (slot_lt (w := w) hU) hZ
  have sV := Nat.le_trans (slot_lt (w := w) hV) hZ
  have sX₁ := Nat.le_trans (slot_lt (w := w) hX₁) hZ
  have sX₂ := Nat.le_trans (slot_lt (w := w) hX₂) hZ
  have pUV := slot_sep (w := w) dUV
  have pX := slot_sep (w := w) dX
  have p₁ := slot_sep (w := w) d₁
  have p₂ := slot_sep (w := w) d₂
  have p₃ := slot_sep (w := w) d₃
  have p₄ := slot_sep (w := w) d₄
  simp only [invSwapP, seqs]
  -- `x7 := 0`, `x14 := w`; `x16 := U`, `x17 := V`.
  refine WP.seq (WP.mono (WP.keep [.x7, .x14] (Q := fun t => t.gpr .x7 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧
      t.mem = s.mem) (by brun [h12]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h7₁, h14₁, m₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (base2_ok iU iV .x16 .x17 ((k₁.gpr .x0 (by decide)).trans h0)
    ((k₁.gpr .x11 (by decide)).trans h11)) fun s₂ ⟨⟨h16₂, h17₂, m₂, _⟩, k₂⟩ => ?_)
  have hs₂ := hs.congr (k₁.trans k₂).wr
  -- The mask of `u` odd into `x15` and `x9`; the carry set.
  have e0 : (s₂.mem.readW (off B (slot w iU)) 64).toNat % 2 = u % 2 := by
    rw [m₂, m₁, ← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide), hu]
  refine WP.seq (WP.mono (WP.keep [.x3, .x4, .x9, .x15] (Q := fun t =>
      t.gpr .x9 = mask (decide (u % 2 = 1)) ∧ t.c = true ∧ t.mem = s₂.mem) (by
        brun [h16₂, oddMask, (k₂.gpr .x7 (by decide)).trans h7₁, hs₂.ld (d := slot w iU) (by omega_using [sU]), mask_low, e0])
      (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨⟨h9₃, hc₃, m₃⟩, k₃⟩ => ?_)
  have k13 := (k₁.trans k₂).trans k₃
  have eU : wv s₃.mem B (slot w iU) w = u := by rw [m₃, m₂, m₁, hu]
  have eV : wv s₃.mem B (slot w iV) w = v := by rw [m₃, m₂, m₁, hv]
  -- The carry of `u - v`.
  refine WP.seq (WP.mono (cmpLoop_ok (hs.congr k13.wr) ((k₃.gpr .x16 (by decide)).trans h16₂)
    ((k₃.gpr .x17 (by decide)).trans h17₂) (((k₂.trans k₃).gpr .x14 (by decide)).trans h14₁) hc₃ hw1 (by omega_using [hw])
    (by omega_using [sU]) (by omega_using [sV])) fun s₄ ⟨hc₄, m₄, k₄⟩ => ?_)
  rw [eU, eV] at hc₄
  have k14 := k13.trans k₄
  have e7 : s₄.gpr .x7 = 0 := (((k₂.trans k₃).trans k₄).gpr .x7 (by decide)).trans h7₁
  -- `x15 := ` the swap's mask, `x14 := w`.
  refine WP.seq (WP.mono (WP.keep [.x4, .x14, .x15] (Q := fun t => t.gpr .x15 = mask sw ∧
      t.gpr .x14 = BitVec.ofNat 64 w ∧ t.mem = s₄.mem) (by
    brun [borrowMask, e7, csel_mask_not, hc₄, (k₄.gpr .x9 (by decide)).trans h9₃, mask_and',
      (k14.gpr .x12 (by decide)).trans h12, Bool.not_not]
    rw [hsw, Bool.and_comm]) (by decide) (by decide) (by decide +kernel)) fun s₅ ⟨⟨h15₅, h14₅, m₅⟩, k₅⟩ => ?_)
  have k15 := k14.trans k₅
  refine WP.seq (WP.mono (base2_ok iU iV .x16 .x17 ((k15.gpr .x0 (by decide)).trans h0)
    ((k15.gpr .x11 (by decide)).trans h11)) fun s₆ ⟨⟨h16₆, h17₆, m₆, _⟩, k₆⟩ => ?_)
  have k16 := k15.trans k₆
  -- The swap of `U` and `V`.
  refine WP.seq (WP.mono (cswap_ok (hs.congr k16.wr) h16₆ h17₆ ((k₆.gpr .x15 (by decide)).trans h15₅)
    ((k₆.gpr .x14 (by decide)).trans h14₅) hw1 (by omega_using [hw]) (by omega_using [sU]) (by omega_using [sV]) (by omega_using [pUV]))
    fun s₇ ⟨hU₇, hV₇, f₇, k₇⟩ => ?_)
  have k17 := k16.trans k₇
  rw [m₆, m₅, m₄, eU, eV] at hU₇ hV₇
  -- `x14 := w`; the bases of `X₁` and `X₂`.
  refine WP.seq (WP.mono (WP.keep [.x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.mem = s₇.mem)
    (by brun [(k17.gpr .x12 (by decide)).trans h12]) (by decide) (by decide) (by decide +kernel))
    fun s₈ ⟨⟨h14₈, m₈⟩, k₈⟩ => ?_)
  have k18 := k17.trans k₈
  refine WP.seq (WP.mono (base2_ok iX₁ iX₂ .x16 .x17 ((k18.gpr .x0 (by decide)).trans h0)
    ((k18.gpr .x11 (by decide)).trans h11)) fun s₉ ⟨⟨h16₉, h17₉, m₉, _⟩, k₉⟩ => ?_)
  have k19 := k18.trans k₉
  -- The swap of `X₁` and `X₂`.
  refine WP.mono (cswap_ok (hs.congr k19.wr) h16₉ h17₉ ((k₇.trans k₈ |>.trans k₉ |>.gpr .x15 (by decide)).trans
    ((k₆.gpr .x15 (by decide)).trans h15₅)) ((k₉.gpr .x14 (by decide)).trans h14₈) hw1 (by omega_using [hw]) (by omega_using [sX₁])
    (by omega_using [sX₂]) (by omega_using [pX])) fun t ⟨hX₁t, hX₂t, f₁₀, k₁₀⟩ => ?_
  rw [m₉, m₈] at hX₁t hX₂t f₁₀
  -- What the swap of `U` and `V` left of `X₁` and `X₂`.
  have fx : ∀ i, i = iX₁ ∨ i = iX₂ → wv s₇.mem B (slot w i) w = wv s.mem B (slot w i) w := by
    intro i hi
    have hi' : i < 16 := by rcases hi with rfl | rfl <;> with_reducible assumption
    have hsep : ∀ r ∈ [(slot w iU, 8 * w), (slot w iV, 8 * w)], slot w i + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w i := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> rcases hi with rfl | rfl <;> omega_using [p₁, p₂, p₃, p₄]
    rw [f₇.wv_eq hsep (by have := Nat.le_trans (slot_lt (w := w) hi') hZ; omega_using [hn, this]), m₆, m₅, m₄, m₃, m₂, m₁]
  have hUt : ∀ i, i = iU ∨ i = iV → wv t.mem B (slot w i) w = wv s₇.mem B (slot w i) w := by
    intro i hi
    have hi' : i < 16 := by rcases hi with rfl | rfl <;> with_reducible assumption
    exact f₁₀.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> rcases hi with rfl | rfl <;> omega_using [p₁, p₃, p₂, p₄])
      (by have := Nat.le_trans (slot_lt (w := w) hi') hZ; omega_using [hn, this])
  have k3t := ((((((k₄.trans k₅).trans k₆).trans k₇).trans k₈).trans k₉).trans k₁₀)
  refine ⟨(k3t.gpr .x9 (by decide)).trans h9₃,
    (k3t.gpr .x7 (by decide)).trans ((k₃.gpr .x7 (by decide)).trans ((k₂.gpr .x7 (by decide)).trans h7₁)),
    by rw [hUt iU (.inl rfl)]; exact hU₇, by rw [hUt iV (.inr rfl)]; exact hV₇,
    by rw [hX₁t, fx iX₁ (.inl rfl), fx iX₂ (.inr rfl), hx₁, hx₂],
    by rw [hX₂t, fx iX₁ (.inl rfl), fx iX₂ (.inr rfl), hx₁, hx₂], ?_, (k19.trans k₁₀).mono (by decide)⟩
  intro x hx
  have a := hx (slot w iU, 8 * w) (by simp)
  have b := hx (slot w iV, 8 * w) (by simp)
  have c := hx (slot w iX₁, 8 * w) (by simp)
  have d := hx (slot w iX₂, 8 * w) (by simp)
  dsimp only at a b c d
  rw [f₁₀ x (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> with_reducible assumption),
    f₇ x (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> with_reducible assumption),
    m₆, m₅, m₄, m₃, m₂, m₁]

/-- `countLoop .x14 addMBody` over `N` words, from the carry clear:
`O + 2^(64 N) C = (c ? M : 0) + A` for `M` at `x10`, `A` at `x8`, `O` at `x5`. -/
theorem addM_ok {s : State} {B : Addr} {Z N eo eN eA : Nat} {c : Bool} (hs : Scr s B Z)
    (h10 : s.gpr .x10 = off B eN) (h8 : s.gpr .x8 = off B eA) (h5 : s.gpr .x5 = off B eo)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 N) (h15 : s.gpr .x15 = mask c) (hc : s.c = false)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (ho : eo + 8 * N ≤ Z) (hM : eN + 8 * N ≤ Z) (hA : eA + 8 * N ≤ Z)
    (sN : eN + 8 * N ≤ eo ∨ eo + 8 * N ≤ eN) (sA : eA + 8 * N ≤ eo ∨ eo + 8 * N ≤ eA) :
    WP isa (countLoop .x14 addMBody) s fun t =>
      wv t.mem B eo N + 2 ^ (64 * N) * t.c.toNat = (if c then wv s.mem B eN N else 0) + wv s.mem B eA N ∧
      t.gpr .x5 = off B (eo + 8 * N) ∧ Outside B eo (8 * N) s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x8, .x10, .x14] s t := by
  have h0 : MaInv s B Z eo eN eA c 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h10]; rfl, by rw [h8]; rfl, by rw [h5]; rfl, Outside.refl _ _ _ _,
      by rw [hc]; cases c <;> rfl⟩
  refine WP.mono (wp_countdown (N := N) (by omega_using [hN']) (by omega_using [hN]) (MaInv s B Z eo eN eA c)
    (fun j hj t hI _ => maStep_ok h15 ho hM hA sN sA hj hI) h0 h14) fun t hI => ⟨hI.val, hI.x5, hI.out, hI.keep⟩

/-- `u -= v` if `u` is odd (the mask in `x9`), leaving the mask in `x15`. -/
theorem invSubU_ok {s : State} {B : Addr} {Z w : Nat} {iU iV : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) (hU : iU < 16) (hV : iV < 16) (dUV : iU ≠ iV)
    {odd : Bool} (h9 : s.gpr .x9 = mask odd) :
    WP isa (seqs (invSubUP iU iV)) s fun t =>
      wv t.mem B (slot w iU) w + (if odd then wv s.mem B (slot w iV) w else 0) =
        wv s.mem B (slot w iU) w + 2 ^ (64 * w) * (if odd ∧ wv s.mem B (slot w iU) w < wv s.mem B (slot w iV) w
          then 1 else 0) ∧
      t.gpr .x15 = mask odd ∧ t.gpr .x7 = 0 ∧ Outside B (slot w iU) (8 * w) s.mem t.mem ∧
      Keep [.x3, .x4, .x7, .x8, .x14, .x15, .x16, .x17] s t := by
  have hn := hs.nowrap
  have sU := Nat.le_trans (slot_lt (w := w) hU) hZ
  have sV := Nat.le_trans (slot_lt (w := w) hV) hZ
  have p1 := slot_sep (w := w) dUV
  simp only [invSubUP, seqs]
  refine WP.seq (WP.mono (WP.keep [.x3, .x7, .x14, .x15] (Q := fun t => t.gpr .x15 = mask odd ∧ t.gpr .x7 = 0 ∧
      t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = true ∧ t.mem = s.mem) (by brun [h9, h12])
      (by decide) (by decide) (by decide +kernel))
    fun s₀ ⟨⟨h15₀, h7₀, h14₀, hc₀, m₀⟩, k₀⟩ => ?_)
  refine WP.seq (WP.mono (base3_ok iU iV iU .x16 .x17 .x8 ((k₀.gpr .x0 (by decide)).trans h0)
    ((k₀.gpr .x11 (by decide)).trans h11)) fun s₁ ⟨⟨h16, h17, h8, m₁, c₁⟩, k₁⟩ => ?_)
  have k01 := k₀.trans k₁
  refine WP.mono (subM_ok (hs.congr k01.wr) h16 h17 h8 ((k₁.gpr .x14 (by decide)).trans h14₀)
    ((k₁.gpr .x15 (by decide)).trans h15₀) (by rw [c₁, hc₀]) hw1 (by omega_using [hw]) (by omega_using [sU])
        (by omega_using [sU]) (by omega_using [sV])
    (Or.inl rfl) (by omega_using [p1])) fun t ⟨hv, o, k₂⟩ => ?_
  rw [m₁, m₀] at hv o
  have u2 := wv_lt t.mem B (slot w iU) w
  have v0 := wv_lt s.mem B (slot w iV) w
  have u0 := wv_lt s.mem B (slot w iU) w
  have hb1 := Bool.toNat_le (!t.c)
  refine ⟨?_, (k₂.gpr .x15 (by decide)).trans ((k₁.gpr .x15 (by decide)).trans h15₀),
    (k₂.gpr .x7 (by decide)).trans ((k₁.gpr .x7 (by decide)).trans h7₀), o, (k01.trans k₂).mono (by decide)⟩
  generalize (!t.c) = b₁ at hv hb1
  cases odd <;> simp only [Bool.false_eq_true, ite_false, ite_true, false_and, true_and] at hv ⊢
  · cases b₁ <;> simp only [Bool.toNat_false, Bool.toNat_true] at hv <;> omega_using [hv, u2]
  · split <;> rename_i h <;> cases b₁ <;> simp only [Bool.toNat_false, Bool.toNat_true] at hv <;> omega_using [h, hv, u2]

/-- `x₁ := x₁ - x₂ mod m` if `u` is odd (the mask in `x9`). -/
theorem invSubX_ok {s : State} {B : Addr} {Z w : Nat} {iX₁ iX₂ iM iT : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)))
    (h7 : s.gpr .x7 = 0) (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z)
    (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT)
    {odd : Bool} (h9 : s.gpr .x9 = mask odd) :
    WP isa (seqs (invSubXP iX₁ iX₂ iM iT)) s fun t =>
      (wv s.mem B (slot w iX₁) w < wv s.mem B (slot w iM) w → wv s.mem B (slot w iX₂) w < wv s.mem B (slot w iM) w →
        wv t.mem B (slot w iX₁) w = if odd then
          subMod (wv s.mem B (slot w iM) w) (wv s.mem B (slot w iX₁) w) (wv s.mem B (slot w iX₂) w)
          else wv s.mem B (slot w iX₁) w) ∧
      Frm B [(slot w iX₁, 8 * w), (slot w iT, 8 * w)] s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x8, .x10, .x14, .x15, .x16, .x17] s t := by
  have hn := hs.nowrap
  have sX₁ := Nat.le_trans (slot_lt (w := w) hX₁) hZ
  have sX₂ := Nat.le_trans (slot_lt (w := w) hX₂) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have sT := Nat.le_trans (slot_lt (w := w) hT) hZ
  have p9 := slot_sep (w := w) dX
  have p10 := slot_sep (w := w) dX₁M
  have p11 := slot_sep (w := w) dX₁T
  have p12 := slot_sep (w := w) dX₂T
  have p13 := slot_sep (w := w) dMT
  simp only [invSubXP, seqs]
  refine WP.seq (WP.mono (WP.keep [.x3, .x14, .x15] (Q := fun t => t.gpr .x15 = mask odd ∧
      t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = true ∧ t.mem = s.mem) (by brun [h9, h12, h7])
      (by decide) (by decide) (by decide +kernel))
    fun s₀ ⟨⟨h15₀, h14₀, hc₀, m₀⟩, k₀⟩ => ?_)
  refine WP.seq (WP.mono (base3_ok iX₁ iX₂ iT .x16 .x17 .x8 ((k₀.gpr .x0 (by decide)).trans h0)
    ((k₀.gpr .x11 (by decide)).trans h11)) fun s₁ ⟨⟨h16, h17, h8, m₁, c₁⟩, k₁⟩ => ?_)
  have k01 := k₀.trans k₁
  refine WP.seq (WP.mono (subM_ok (hs.congr k01.wr) h16 h17 h8 ((k₁.gpr .x14 (by decide)).trans h14₀)
    ((k₁.gpr .x15 (by decide)).trans h15₀) (by rw [c₁, hc₀]) hw1 (by omega_using [hw]) (by omega_using [sT])
        (by omega_using [sX₁]) (by omega_using [sX₂])
    (by omega_using [p11]) (by omega_using [p12])) fun s₂ ⟨hv₂, o₂, k₂⟩ => ?_)
  rw [m₁, m₀] at hv₂ o₂
  have k02 := k01.trans k₂
  have e7 : s₂.gpr .x7 = 0 := (k02.gpr .x7 (by decide)).trans h7
  refine WP.seq (WP.mono (WP.keep [.x3, .x4, .x14, .x15] (Q := fun t => t.gpr .x15 = mask (!s₂.c) ∧
      t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = false ∧ t.mem = s₂.mem)
      (by brun [borrowMask, e7, csel_mask_not, (k02.gpr .x12 (by decide)).trans h12])
      (by decide) (by decide) (by decide +kernel))
    fun s₃ ⟨⟨h15₃, h14₃, hc₃, m₃⟩, k₃⟩ => ?_)
  have k03 := k02.trans k₃
  refine WP.seq (WP.mono (base3_ok iM iT iX₁ .x10 .x8 .x5 ((k03.gpr .x0 (by decide)).trans h0)
    ((k03.gpr .x11 (by decide)).trans h11)) fun s₄ ⟨⟨h10₄, h8₄, h5₄, m₄, c₄⟩, k₄⟩ => ?_)
  have k04 := k03.trans k₄
  have hT₄ : wv s₄.mem B (slot w iT) w = wv s₂.mem B (slot w iT) w := by rw [m₄, m₃]
  have hM₄ : wv s₄.mem B (slot w iM) w = wv s.mem B (slot w iM) w := by
    rw [m₄, m₃]; exact o₂.wv (by omega_using [p13]) (by omega_using [hn, sM])
  refine WP.mono (addM_ok (hs.congr k04.wr) h10₄ h8₄ h5₄ ((k₄.gpr .x14 (by decide)).trans h14₃)
    ((k₄.gpr .x15 (by decide)).trans h15₃) (by rw [c₄, hc₃]) hw1 (by omega_using [hw]) (by omega_using [sX₁])
        (by omega_using [sM]) (by omega_using [sT])
    (by omega_using [p10]) (by omega_using [p11])) fun t ⟨hvt, _, ot, kt⟩ => ?_
  rw [hT₄, hM₄] at hvt
  have x1 := wv_lt t.mem B (slot w iX₁) w
  have t5 := wv_lt s₂.mem B (slot w iT) w
  have x10 := wv_lt s.mem B (slot w iX₁) w
  have hb2 := Bool.toNat_le (!s₂.c)
  have hc := Bool.toNat_le t.c
  refine ⟨fun h1 h2 => ?_, ?_, (k04.trans kt).mono (by decide)⟩
  · clear hn sX₁ sX₂ sM sT p9 p10 p11 p12 p13
    unfold subMod
    generalize (!s₂.c) = b₂ at hv₂ hvt hb2
    generalize t.c = c at hvt hc
    cases odd <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hv₂ ⊢
    · cases b₂ <;> cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, ite_false,
        ite_true, Bool.false_eq_true, Nat.zero_add, Nat.add_zero] at hv₂ hvt <;> omega_using [hv₂, hvt, x10, t5]
    · split <;> cases b₂ <;> cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one,
        ite_false, ite_true, Bool.false_eq_true, Nat.zero_add, Nat.add_zero] at hv₂ hvt <;> omega_arith
  · intro x hx
    have b := hx (slot w iX₁, 8 * w) (by simp)
    have d := hx (slot w iT, 8 * w) (by simp)
    dsimp only at b d
    rw [ot x (by omega_using [b]), m₄, m₃, o₂ x (by omega_using [d])]

/-- `u /= 2`, if the word `w` of `u` is zero. -/
theorem invHalfU_ok {s : State} {B : Addr} {Z w : Nat} {iU : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) (hU : iU < 16)
    (hU0 : word s.mem B (slot w iU + 8 * w) = 0) :
    WP isa (seqs (invHalfUP iU)) s fun t =>
      wv t.mem B (slot w iU) w = wv s.mem B (slot w iU) w / 2 ∧ Outside B (slot w iU) (8 * w) s.mem t.mem ∧
      Keep [.x3, .x4, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  have sU := Nat.le_trans (slot_lt (w := w) hU) hZ
  simp only [invHalfUP, seqs]
  refine WP.seq (WP.mono (WP.keep [.x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.mem = s.mem)
    (by brun [h12]) (by decide) (by decide) (by decide +kernel)) fun s₀ ⟨⟨h14₀, m₀⟩, k₀⟩ => ?_)
  refine WP.seq (WP.mono (base2_ok iU iU .x16 .x17 ((k₀.gpr .x0 (by decide)).trans h0)
    ((k₀.gpr .x11 (by decide)).trans h11)) fun s₁ ⟨⟨h16, h17, m₁, _⟩, k₁⟩ => ?_)
  refine WP.mono (shr_ok (hs.congr (k₀.trans k₁).wr) h16 h17 ((k₁.gpr .x14 (by decide)).trans h14₀) hw1 (by omega_using [hw])
    (by omega_using [sU]) (by omega_using [sU]) (Or.inl rfl)) fun t ⟨hv, _, o, k₂⟩ => ?_
  rw [m₁, m₀, hU0, ← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide)] at hv
  rw [m₁, m₀] at o
  refine ⟨?_, o, ((k₀.trans k₁).trans k₂).mono (by decide)⟩
  simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_mod, Nat.mul_zero, Nat.add_zero] at hv
  omega_using [hv]

/-- `x₁ := x₁ / 2 (mod m)`. -/
theorem invHalfX_ok {s : State} {B : Addr} {Z w : Nat} {iX₁ iM iT : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)))
    (h7 : s.gpr .x7 = 0) (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) (hX₁ : iX₁ < 16) (hM : iM < 16)
    (hT : iT < 16) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT) (dMT : iM ≠ iT) :
    WP isa (seqs (invHalfXP iX₁ iM iT)) s fun t =>
      wv t.mem B (slot w iX₁) w = halfMod (wv s.mem B (slot w iM) w) (wv s.mem B (slot w iX₁) w) ∧
      Frm B [(slot w iX₁, 8 * w), ar w iT] s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x8, .x10, .x14, .x15, .x16, .x17] s t := by
  have hn := hs.nowrap
  have sX₁ := Nat.le_trans (slot_lt (w := w) hX₁) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have sT := Nat.le_trans (slot_lt (w := w) hT) hZ
  have p10 := slot_sep (w := w) dX₁M
  have p11 := slot_sep (w := w) dX₁T
  have p13 := slot_sep (w := w) dMT
  simp only [invHalfXP, seqs]
  -- `x8 := X₁`, `x15 := ` the mask of `x₁` odd, `x14 := w`, the carry clear.
  refine WP.seq (WP.mono (base_ok iX₁ .x8 h0 h11) fun s₁ ⟨⟨h8, m₁, _⟩, k₁⟩ => ?_)
  have e0 : (s₁.mem.readW (off B (slot w iX₁)) 64).toNat % 2 = wv s.mem B (slot w iX₁) w % 2 := by
    rw [m₁, ← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide)]
  refine WP.seq (WP.mono (WP.keep [.x3, .x4, .x14, .x15] (Q := fun t =>
      t.gpr .x15 = mask (decide (wv s.mem B (slot w iX₁) w % 2 = 1)) ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧
      t.c = false ∧ t.mem = s₁.mem) (by
        brun [h8, oddMask, (k₁.gpr .x7 (by decide)).trans h7, (k₁.gpr .x12 (by decide)).trans h12,
          (hs.congr k₁.wr).ld (d := slot w iX₁) (by omega_using [sX₁]), mask_low, e0])
      (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨⟨h15, h14, hc₂, m₂⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.seq (WP.mono (base2_ok iM iT .x10 .x5 ((k12.gpr .x0 (by decide)).trans h0)
    ((k12.gpr .x11 (by decide)).trans h11)) fun s₃ ⟨⟨h10, h5, m₃, c₃⟩, k₃⟩ => ?_)
  have k03 := k12.trans k₃
  -- `T := (M & mask) + X₁`.
  refine WP.seq (WP.mono (addM_ok (hs.congr k03.wr) h10 ((k₂.trans k₃).gpr .x8 (by decide) |>.trans h8) h5
    ((k₃.gpr .x14 (by decide)).trans h14) ((k₃.gpr .x15 (by decide)).trans h15) (by rw [c₃, hc₂]) hw1
    (by omega_using [hw]) (by omega_using [sT]) (by omega_using [sM]) (by omega_using [sX₁]) (by omega_using [p13])
        (by omega_using [p11])) fun s₄ ⟨hv₄, h5₄, o₄, k₄⟩ => ?_)
  rw [m₃, m₂, m₁] at hv₄ o₄
  have k04 := k03.trans k₄
  have hs₄ := hs.congr k04.wr
  -- `T_w := C`, `x14 := w`.
  refine WP.seq (WP.mono (WP.keep [.x3, .x14] (Q := fun t =>
      t.mem = s₄.mem.writeW (off B (slot w iT + 8 * w)) (BitVec.ofNat 64 s₄.c.toNat) ∧
      t.gpr .x14 = BitVec.ofNat 64 w) (by
      brun [h5₄, (k04.gpr .x7 (by decide)).trans h7, (k04.gpr .x12 (by decide)).trans h12,
        hs₄.st (d := slot w iT + 8 * w) (by omega_using [sT])]
      cases s₄.c <;> rfl) (by decide) (by decide) (by decide +kernel))
    fun s₅ ⟨⟨m₅, h14₅⟩, k₅⟩ => ?_)
  have k05 := k04.trans k₅
  refine WP.seq (WP.mono (base2_ok iT iX₁ .x16 .x17 ((k05.gpr .x0 (by decide)).trans h0)
    ((k05.gpr .x11 (by decide)).trans h11)) fun s₆ ⟨⟨h16₆, h17₆, m₆, _⟩, k₆⟩ => ?_)
  have k06 := k05.trans k₆
  -- `X₁ := T / 2`.
  refine WP.mono (shr_ok (hs.congr k06.wr) h16₆ h17₆ ((k₆.gpr .x14 (by decide)).trans h14₅) hw1 (by omega_using [hw])
    (by omega_using [sX₁]) (by omega_using [sT]) (by omega_using [p11])) fun t ⟨hv, _, o, k₇⟩ => ?_
  have hT₆ : wv s₆.mem B (slot w iT) w = wv s₄.mem B (slot w iT) w := by
    rw [m₆, m₅]
    exact (writeW_outside s₄.mem B (d := slot w iT + 8 * w) _ (by omega_using [hn, sT])).wv (Or.inl (Nat.le_refl _))
        (by omega_using [hn, sT])
  have hTw : word s₆.mem B (slot w iT + 8 * w) = BitVec.ofNat 64 s₄.c.toNat := by rw [m₆, m₅, word_writeW_self]
  have hT0 : (word s₆.mem B (slot w iT)).toNat % 2 = wv s₄.mem B (slot w iT) w % 2 := by
    rw [← hT₆, ← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide)]
  have hcl := Bool.toNat_le s₄.c
  rw [hT₆, hTw, hT0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show s₄.c.toNat < 2 ^ 64 by omega_using [hcl]),
    Nat.mod_eq_of_lt (show s₄.c.toNat < 2 by omega_using [hcl])] at hv
  refine ⟨?_, ?_, (k06.trans k₇).mono (by decide)⟩
  · unfold halfMod
    rcases Nat.mod_two_eq_zero_or_one (wv s.mem B (slot w iX₁) w) with h | h
    · rw [show decide (wv s.mem B (slot w iX₁) w % 2 = 1) = false by simp [h]] at hv₄
      simp only [Bool.false_eq_true, ite_false] at hv₄
      simp only [h, ite_true]; omega_using [hv, hv₄]
    · rw [show decide (wv s.mem B (slot w iX₁) w % 2 = 1) = true by simp [h]] at hv₄
      simp only [ite_true] at hv₄
      simp only [show ¬ (wv s.mem B (slot w iX₁) w % 2 = 0) by omega_using [h], ite_false]; omega_using [hv, hv₄]
  · intro x hx
    have a := hx (slot w iX₁, 8 * w) (by simp)
    have b := hx (ar w iT) (by simp)
    dsimp only at a b
    rw [o x (by omega_using [a]), m₆, m₅, writeW_outside s₄.mem B _ (by omega_using [hn, sT]) x (by omega_using [b]),
        o₄ x (by omega_using [b])]

/-- What the swaps and the subtractions leave: `(u', v', x₁', x₂')`. -/
def subState (m : Nat) (st : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  let (u, v, x₁, x₂) := st
  if u % 2 = 1 then
    if u < v then (v - u, u, subMod m x₂ x₁, x₁) else (u - v, v, subMod m x₁ x₂, x₂)
  else (u, v, x₁, x₂)

/-- The ranges a step of `inverse` changes. -/
abbrev invRanges (w iU iV iX₁ iX₂ iT : Nat) : List (Nat × Nat) :=
  [(slot w iU, 8 * w), (slot w iV, 8 * w), (slot w iX₁, 8 * w), (slot w iX₂, 8 * w), ar w iT]

/-- The swaps and the subtractions of a step of `inverse`. -/
theorem invFirst_ok {s : State} {B : Addr} {Z w : Nat} {iU iV iX₁ iX₂ iM iT : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT) :
    WP isa (seqs (invSwapP iU iV iX₁ iX₂ ++ invSubP iU iV iX₁ iX₂ iM iT)) s fun t =>
      (wv s.mem B (slot w iX₁) w < wv s.mem B (slot w iM) w → wv s.mem B (slot w iX₂) w < wv s.mem B (slot w iM) w →
        (wv t.mem B (slot w iU) w, wv t.mem B (slot w iV) w, wv t.mem B (slot w iX₁) w, wv t.mem B (slot w iX₂) w) =
          subState (wv s.mem B (slot w iM) w) (wv s.mem B (slot w iU) w, wv s.mem B (slot w iV) w,
            wv s.mem B (slot w iX₁) w, wv s.mem B (slot w iX₂) w)) ∧
      t.gpr .x7 = 0 ∧
      Frm B [(slot w iU, 8 * w), (slot w iV, 8 * w), (slot w iX₁, 8 * w), (slot w iX₂, 8 * w), (slot w iT, 8 * w)]
        s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x7, .x8, .x9, .x10, .x14, .x15, .x16, .x17] s t := by
  have hn := hs.nowrap
  have sU := Nat.le_trans (slot_lt (w := w) hU) hZ
  have sV := Nat.le_trans (slot_lt (w := w) hV) hZ
  have sX₁ := Nat.le_trans (slot_lt (w := w) hX₁) hZ
  have sX₂ := Nat.le_trans (slot_lt (w := w) hX₂) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have sT := Nat.le_trans (slot_lt (w := w) hT) hZ
  rw [invSubP]
  refine wp_seqs_append (by simp [invSwapP]) (by simp [invSubUP]) (WP.mono (invSwap_ok hs h0 h12 h11 hw1 hw hZ hU hV
    hX₁ hX₂ dUV dX dUX₁ dUX₂ dVX₁ dVX₂ rfl rfl rfl rfl rfl) fun s₁ ⟨h9₁, _, hU₁, hV₁, hX₁₁, hX₂₁, f₁, k₁⟩ => ?_)
  refine wp_seqs_append (by simp [invSubUP]) (by simp [invSubXP]) (WP.mono (invSubU_ok (hs.congr k₁.wr)
    ((k₁.gpr .x0 (by decide)).trans h0) ((k₁.gpr .x12 (by decide)).trans h12) ((k₁.gpr .x11 (by decide)).trans h11)
    hw1 hw hZ hU hV dUV h9₁) fun s₂ ⟨hU₂, _, h7₂, o₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.mono (invSubX_ok (hs.congr k12.wr) ((k12.gpr .x0 (by decide)).trans h0)
    ((k12.gpr .x12 (by decide)).trans h12) ((k12.gpr .x11 (by decide)).trans h11) h7₂ hw1 hw hZ hX₁ hX₂ hM hT dX
    dX₁M dX₁T dX₂T dMT ((k₂.gpr .x9 (by decide)).trans h9₁)) fun t ⟨hX₁t, f₃, k₃⟩ => ?_
  -- What each part leaves of the others.
  have eM₁ : wv s₁.mem B (slot w iM) w = wv s.mem B (slot w iM) w := f₁.wv_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only
    · have := slot_sep (w := w) dUM; omega_using [this]
    · have := slot_sep (w := w) dVM; omega_using [this]
    · have := slot_sep (w := w) dX₁M; omega_using [this]
    · have := slot_sep (w := w) dX₂M; omega_using [this]) (by omega_using [hn, sM])
  have eV₂ : wv s₂.mem B (slot w iV) w = wv s₁.mem B (slot w iV) w :=
    o₂.wv (by have := slot_sep (w := w) dUV; omega_using [this]) (by omega_using [hn, sV])
  have eX₁₂ : wv s₂.mem B (slot w iX₁) w = wv s₁.mem B (slot w iX₁) w :=
    o₂.wv (by have := slot_sep (w := w) dUX₁; omega_using [this]) (by omega_using [hn, sX₁])
  have eX₂₂ : wv s₂.mem B (slot w iX₂) w = wv s₁.mem B (slot w iX₂) w :=
    o₂.wv (by have := slot_sep (w := w) dUX₂; omega_using [this]) (by omega_using [hn, sX₂])
  have eM₂ : wv s₂.mem B (slot w iM) w = wv s₁.mem B (slot w iM) w :=
    o₂.wv (by have := slot_sep (w := w) dUM; omega_using [this]) (by omega_using [hn, sM])
  have eU₃ : wv t.mem B (slot w iU) w = wv s₂.mem B (slot w iU) w := f₃.wv_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only
    · have := slot_sep (w := w) dUX₁; omega_using [this]
    · have := slot_sep (w := w) dUT; omega_using [this]) (by omega_using [hn, sU])
  have eV₃ : wv t.mem B (slot w iV) w = wv s₂.mem B (slot w iV) w := f₃.wv_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only
    · have := slot_sep (w := w) dVX₁; omega_using [this]
    · have := slot_sep (w := w) dVT; omega_using [this]) (by omega_using [hn, sV])
  have eX₂₃ : wv t.mem B (slot w iX₂) w = wv s₂.mem B (slot w iX₂) w := f₃.wv_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only
    · have := slot_sep (w := w) dX; omega_using [this]
    · have := slot_sep (w := w) dX₂T; omega_using [this]) (by omega_using [hn, sX₂])
  rw [eX₁₂, eX₂₂, eM₂, eM₁, hX₁₁, hX₂₁] at hX₁t
  rw [hV₁, hU₁] at hU₂
  refine ⟨fun hx₁ hx₂ => ?_, (k₃.gpr .x7 (by decide)).trans h7₂, ?_, ((k12.trans k₃)).mono (by decide)⟩
  · rw [eU₃, eV₃, eX₂₃, eV₂, eX₂₂, hV₁, hX₂₁]
    have := hX₁t (by split <;> omega_using [hx₂, hx₁]) (by split <;> omega_using [hx₁, hx₂])
    rw [this]
    have hu := wv_lt s₂.mem B (slot w iU) w
    unfold subState
    dsimp only
    generalize wv s.mem B (slot w iU) w = u at hU₂ ⊢
    generalize wv s.mem B (slot w iV) w = v at hU₂ ⊢
    generalize wv s₂.mem B (slot w iU) w = u' at hU₂ hu ⊢
    rcases Nat.mod_two_eq_zero_or_one u with ho | ho
    · simp only [ho, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, false_and, Nat.mul_zero,
        Nat.add_zero, show (0 : Nat) ≠ 1 by decide] at hU₂ ⊢
      rw [hU₂]
    · by_cases hlt : u < v
      · simp only [ho, hlt, decide_true, Bool.and_self, ite_true, show ¬ v < u by omega_using [hlt], and_false, ite_false,
          Nat.mul_zero, Nat.add_zero] at hU₂ ⊢
        refine Prod.ext (by dsimp only; omega_using [hU₂]) rfl
      · simp only [ho, hlt, decide_true, decide_false, Bool.and_false, Bool.false_eq_true, ite_true, ite_false,
          and_false, Nat.mul_zero, Nat.add_zero] at hU₂ ⊢
        refine Prod.ext (by dsimp only; omega_using [hU₂]) rfl
  · intro x hx
    have a := hx (slot w iU, 8 * w) (by simp)
    have b := hx (slot w iV, 8 * w) (by simp)
    have c := hx (slot w iX₁, 8 * w) (by simp)
    have d := hx (slot w iX₂, 8 * w) (by simp)
    have e := hx (slot w iT, 8 * w) (by simp)
    dsimp only at a b c d e
    have h3 : ∀ r ∈ [(slot w iX₁, 8 * w), (slot w iT, 8 * w)], ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> with_reducible assumption
    have h1 : ∀ r ∈ [(slot w iU, 8 * w), (slot w iV, 8 * w), (slot w iX₁, 8 * w), (slot w iX₂, 8 * w)],
        ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl) <;> with_reducible assumption
    rw [f₃ x h3, o₂ x a, f₁ x h1]

/-- `KeyMath.invStep` is the subtraction, then the halvings. -/
theorem invStep_eq (m : Nat) (st : Nat × Nat × Nat × Nat) :
    VG.Proof.Rsa.invStep m st = ((subState m st).1 / 2, (subState m st).2.1, halfMod m (subState m st).2.2.1,
      (subState m st).2.2.2) := by
  obtain ⟨u, v, x₁, x₂⟩ := st
  unfold VG.Proof.Rsa.invStep subState
  dsimp only
  split
  · split <;> rfl
  · rfl

/-- One step of `inverse`: `KeyMath.invStep`, while `x₁, x₂ < m` and the
word `w` of `u` is zero, and the step counter `x6` counted down. -/
theorem invStepCode_ok {s : State} {B : Addr} {Z w : Nat} {iU iV iX₁ iX₂ iM iT : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT) (hU0 : word s.mem B (slot w iU + 8 * w) = 0) :
    WP isa (VG.Impl.Rsa.AArch64.Keys.invStep iU iV iX₁ iX₂ iM iT) s fun t =>
      t.gpr .x6 = s.gpr .x6 - BitVec.ofNat 64 1 ∧
      Frm B (invRanges w iU iV iX₁ iX₂ iT) s.mem t.mem ∧ Keep stepRegs s t ∧
      (wv s.mem B (slot w iX₁) w < wv s.mem B (slot w iM) w → wv s.mem B (slot w iX₂) w < wv s.mem B (slot w iM) w →
        (wv t.mem B (slot w iU) w, wv t.mem B (slot w iV) w, wv t.mem B (slot w iX₁) w, wv t.mem B (slot w iX₂) w) =
          VG.Proof.Rsa.invStep (wv s.mem B (slot w iM) w) (wv s.mem B (slot w iU) w, wv s.mem B (slot w iV) w,
            wv s.mem B (slot w iX₁) w, wv s.mem B (slot w iX₂) w)) := by
  have hn := hs.nowrap
  have sU := Nat.le_trans (slot_lt (w := w) hU) hZ
  have sV := Nat.le_trans (slot_lt (w := w) hV) hZ
  have sX₁ := Nat.le_trans (slot_lt (w := w) hX₁) hZ
  have sX₂ := Nat.le_trans (slot_lt (w := w) hX₂) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have sT := Nat.le_trans (slot_lt (w := w) hT) hZ
  unfold VG.Impl.Rsa.AArch64.Keys.invStep
  rw [show invSwapP iU iV iX₁ iX₂ ++ (invSubP iU iV iX₁ iX₂ iM iT ++ (invHalfP iU iX₁ iM iT ++
      [.block [.subImm .x .x6 .x6 1]])) =
    (invSwapP iU iV iX₁ iX₂ ++ invSubP iU iV iX₁ iX₂ iM iT) ++ (invHalfUP iU ++ (invHalfXP iX₁ iM iT ++
      [.block [.subImm .x .x6 .x6 1]])) by simp [invHalfP]]
  refine wp_seqs_append (by simp [invSwapP]) (by simp [invHalfUP]) (WP.mono (invFirst_ok hs h0 h12 h11 hw1 hw hZ hU hV
    hX₁ hX₂ hM hT dUV dUX₁ dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T dX₂M dX₂T dMT) fun s₁ ⟨hv₁, h7₁, f₁, k₁⟩ => ?_)
  have hU0₁ : word s₁.mem B (slot w iU + 8 * w) = 0 := by
    rw [f₁.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> dsimp only
      · omega_using []
      · have := slot_sep (w := w) dUV; omega_using [this]
      · have := slot_sep (w := w) dUX₁; omega_using [this]
      · have := slot_sep (w := w) dUX₂; omega_using [this]
      · have := slot_sep (w := w) dUT; omega_using [this]) (by omega_using [hn, sU])]
    exact hU0
  refine wp_seqs_append (by simp [invHalfUP]) (by simp [invHalfXP]) (WP.mono (invHalfU_ok (hs.congr k₁.wr)
    ((k₁.gpr .x0 (by decide)).trans h0) ((k₁.gpr .x12 (by decide)).trans h12) ((k₁.gpr .x11 (by decide)).trans h11)
    hw1 hw hZ hU hU0₁) fun s₂ ⟨hU₂, o₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine wp_seqs_append (by simp [invHalfXP]) (by simp) (WP.mono (invHalfX_ok (hs.congr k12.wr)
    ((k12.gpr .x0 (by decide)).trans h0) ((k12.gpr .x12 (by decide)).trans h12) ((k12.gpr .x11 (by decide)).trans h11)
    ((k₂.gpr .x7 (by decide)).trans h7₁) hw1 hw hZ hX₁ hM hT dX₁M dX₁T dMT) fun s₃ ⟨hX₃, f₃, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  simp only [seqs]
  refine WP.mono (dec_ok s₃ .x6) fun t ⟨⟨h6t, mt, _⟩, k₄⟩ =>
    ⟨by rw [h6t, k13.gpr .x6 (by decide)], ?_, (k13.trans k₄).mono (by simp [stepRegs]), fun hx₁ hx₂ => ?_⟩
  · intro x hx
    have a := hx (slot w iU, 8 * w) (by simp)
    have b := hx (slot w iV, 8 * w) (by simp)
    have c := hx (slot w iX₁, 8 * w) (by simp)
    have d := hx (slot w iX₂, 8 * w) (by simp)
    have e := hx (ar w iT) (by simp)
    dsimp only at a b c d e
    have h3 : ∀ r ∈ [(slot w iX₁, 8 * w), ar w iT], ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> with_reducible assumption
    have h1 : ∀ r ∈ [(slot w iU, 8 * w), (slot w iV, 8 * w), (slot w iX₁, 8 * w), (slot w iX₂, 8 * w),
        (slot w iT, 8 * w)], ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl) <;> first | with_reducible assumption | (dsimp only; omega_using [e])
    rw [mt, f₃ x h3, o₂ x a, f₁ x h1]
  · have e := hv₁ hx₁ hx₂
    rw [invStep_eq, ← e]
    have eM₁ : wv s₁.mem B (slot w iM) w = wv s.mem B (slot w iM) w := f₁.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> dsimp only
      · have := slot_sep (w := w) dUM; omega_using [this]
      · have := slot_sep (w := w) dVM; omega_using [this]
      · have := slot_sep (w := w) dX₁M; omega_using [this]
      · have := slot_sep (w := w) dX₂M; omega_using [this]
      · have := slot_sep (w := w) dMT; omega_using [this]) (by omega_using [hn, sM])
    have eM₂ : wv s₂.mem B (slot w iM) w = wv s₁.mem B (slot w iM) w :=
      o₂.wv (by have := slot_sep (w := w) dUM; omega_using [this]) (by omega_using [hn, sM])
    have eX₂ : wv s₂.mem B (slot w iX₁) w = wv s₁.mem B (slot w iX₁) w :=
      o₂.wv (by have := slot_sep (w := w) dUX₁; omega_using [this]) (by omega_using [hn, sX₁])
    have f3 : ∀ i, i ≠ iX₁ → i ≠ iT → i < 16 → wv t.mem B (slot w i) w = wv s₂.mem B (slot w i) w := by
      intro i h1 h2 hi
      rw [mt]
      exact f₃.wv_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only
        · have := slot_sep (w := w) h1; omega_using [this]
        · have := slot_sep (w := w) h2; omega_using [this]) (by have := Nat.le_trans (slot_lt (w := w) hi) hZ; omega_using [hn, this])
    have o2 : ∀ i, i ≠ iU → i < 16 → wv s₂.mem B (slot w i) w = wv s₁.mem B (slot w i) w := by
      intro i h1 hi
      exact o₂.wv (by have := slot_sep (w := w) h1; omega_using [this])
          (by have := Nat.le_trans (slot_lt (w := w) hi) hZ; omega_using [hn, this])
    rw [f3 iU dUX₁ dUT hU, hU₂, f3 iV dVX₁ dVT hV, o2 iV (Ne.symm dUV) hV, f3 iX₂ (Ne.symm dX) dX₂T hX₂,
      o2 iX₂ (Ne.symm dUX₂) hX₂, mt, hX₃, eM₂, eM₁, eX₂]

/-- The invariant of `inverse`'s loop after `j` steps from `s`. -/
structure InvInv (s : State) (B : Addr) (Z w iU iV iX₁ iX₂ iT a m : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  x0 : t.gpr .x0 = B
  x12 : t.gpr .x12 = BitVec.ofNat 64 w
  x11 : t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))
  frm : Frm B (invRanges w iU iV iX₁ iX₂ iT) s.mem t.mem
  keep : Keep (.x11 :: .x12 :: stepRegs) s t
  u0 : word t.mem B (slot w iU + 8 * w) = 0
  val : m % 2 = 1 → 1 < m → (wv t.mem B (slot w iU) w, wv t.mem B (slot w iV) w, wv t.mem B (slot w iX₁) w,
    wv t.mem B (slot w iX₂) w) = invIter m j (a, m, 1, 0)

/-- `inverse`: from `(a, m, 1, 0)` in `[u], [v], [x₁], [x₂]` (the word `w`
of `[u]` zero), `[m]` odd and above 1: `[v] = gcd(a, m)` and
`[x₂] a ≡ [v] (mod m)`, `[x₂] < m`. -/
theorem inverse_ok {s : State} {B : Addr} {Z w : Nat} {iU iV iX₁ iX₂ iM iT : Nat} (h : Ws s B Z w)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT) (hU0 : word s.mem B (slot w iU + 8 * w) = 0)
    (hVM : wv s.mem B (slot w iV) w = wv s.mem B (slot w iM) w) (hX1 : wv s.mem B (slot w iX₁) w = 1)
    (hX2 : wv s.mem B (slot w iX₂) w = 0) :
    WP isa (inverse iU iV iX₁ iX₂ iM iT) s fun t =>
      t.gpr .x0 = B ∧ Frm B (invRanges w iU iV iX₁ iX₂ iT) s.mem t.mem ∧ Keep (.x11 :: .x12 :: stepRegs) s t ∧
      (wv s.mem B (slot w iM) w % 2 = 1 → 1 < wv s.mem B (slot w iM) w →
        wv t.mem B (slot w iV) w = Nat.gcd (wv s.mem B (slot w iU) w) (wv s.mem B (slot w iM) w) ∧
        ((wv s.mem B (slot w iM) w : Nat) : Int) ∣
          (wv t.mem B (slot w iX₂) w : Int) * wv s.mem B (slot w iU) w - wv t.mem B (slot w iV) w ∧
        wv t.mem B (slot w iX₂) w < wv s.mem B (slot w iM) w) := by
  have hs := h.scr
  have hn := hs.nowrap
  have hZ := h.hZ
  have hw1 : 1 ≤ w := by have := h.w1; omega_using [this]
  have hw := h.w2
  have sU := Nat.le_trans (slot_lt (w := w) hU) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  unfold inverse invInit
  -- The registers.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12₁, h11₁, m₁, _⟩, k₁⟩ =>
    WP.mono (WP.keep [.x6] (Q := fun t => t.gpr .x6 = BitVec.ofNat 64 (128 * w) ∧ t.mem = s₁.mem)
      (by brun [h12₁, shl_ofNat (show w * 2 ^ 7 < 2 ^ 64 by omega_using [hw])]; congr 1; omega_using [])
      (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨⟨h6₂, m₂⟩, k₂⟩ => ?_))
  have k12 := k₁.trans k₂
  have fM : ∀ {t : State}, Frm B (invRanges w iU iV iX₁ iX₂ iT) s.mem t.mem →
      wv t.mem B (slot w iM) w = wv s.mem B (slot w iM) w := fun f =>
    f.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> dsimp only
      · have := slot_sep (w := w) dUM; omega_using [this]
      · have := slot_sep (w := w) dVM; omega_using [this]
      · have := slot_sep (w := w) dX₁M; omega_using [this]
      · have := slot_sep (w := w) dX₂M; omega_using [this]
      · have := slot_sep (w := w) dMT; omega_using [this]) (by omega_using [hn, sM])
  refine WP.mono (wp_countdown (N := 128 * w) (by omega_using [hw]) (by omega_using [hw1])
    (InvInv s B Z w iU iV iX₁ iX₂ iT (wv s.mem B (slot w iU) w) (wv s.mem B (slot w iM) w))
    (fun j hj t hI _ => ?_)
    ⟨hs.congr k12.wr, (k12.gpr .x0 (by decide)).trans h.x0, (k₂.gpr .x12 (by decide)).trans h12₁,
      (k₂.gpr .x11 (by decide)).trans h11₁, by rw [m₂, m₁]; exact Frm.refl _ _ _, k12.mono (by simp [stepRegs]),
      by rw [m₂, m₁]; exact hU0, fun _ _ => by rw [m₂, m₁, hVM, hX1, hX2]; rfl⟩ h6₂)
    fun t hI => ⟨hI.x0, hI.frm, hI.keep, fun hodd h1 => ?_⟩
  · refine WP.mono (invStepCode_ok hI.scr hI.x0 hI.x12 hI.x11 hw1 hw hZ hU hV hX₁ hX₂ hM hT dUV dUX₁
      dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T dX₂M dX₂T dMT hI.u0) fun t' ⟨h6', f', k', hv'⟩ =>
      ⟨⟨hI.scr.congr k'.wr, (k'.gpr .x0 (by decide)).trans hI.x0, (k'.gpr .x12 (by decide)).trans hI.x12,
        (k'.gpr .x11 (by decide)).trans hI.x11, hI.frm.trans f', (hI.keep.trans k').mono (by simp [stepRegs]), ?_,
        fun hodd h1 => ?_⟩, h6'⟩
    · rw [f'.word_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> dsimp only
        · omega_using []
        · have := slot_sep (w := w) dUV; omega_using [this]
        · have := slot_sep (w := w) dUX₁; omega_using [this]
        · have := slot_sep (w := w) dUX₂; omega_using [this]
        · have := slot_sep (w := w) dUT; omega_using [this]) (by omega_using [hn, sU])]
      exact hI.u0
    · have hv := hI.val hodd h1
      have hinv := invIter_inv hodd (invI_start (a := wv s.mem B (slot w iU) w) hodd h1) j
      rw [← hv] at hinv
      rw [fM hI.frm] at hv'
      rw [hv' hinv.x₁_lt hinv.x₂_lt, hv]
      rfl
  · have hv := hI.val hodd h1
    have hd := invIter_done (a := wv s.mem B (slot w iU) w) (K := 128 * w) hodd (by
      have := wv_lt s.mem B (slot w iU) w
      have := wv_lt s.mem B (slot w iM) w
      rw [show 128 * w = 64 * w + 64 * w by omega_using [], Nat.pow_add]
      exact Nat.mul_lt_mul'' (by omega_arith) (by omega_using [this]))
    rw [Nat.mod_eq_of_lt h1, ← hv] at hd
    exact ⟨hd.2.1, hd.2.2.1, hd.2.2.2⟩

end VG.Proof.Rsa.AArch64
