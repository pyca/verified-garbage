import VerifiedGarbage.Proof.Bignum.AArch64.Store

/-!
# Multiword arithmetic on AArch64: setting up

`minv`: `-m₀⁻¹ mod 2⁶⁴` for an odd `m₀` (`minv_ok`), by five steps of
Newton's iteration from `x = m₀`, which is right modulo 8. `setBases`: the
arrays' bases into the header (`setBases_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum (newton_step emod_pow_weaken odd_sq neg_inv)

/-- A Newton step computed on words is the step on integers, modulo `2⁶⁴`. -/
theorem newton_val (a x : BitVec 64) :
    (((x * (BitVec.ofNat 64 2 - a * x)).toNat : Int) - x.toNat * (2 - a.toNat * x.toNat)) % 2 ^ 64 = 0 := by
  have hx := x.isLt; have ha := a.isLt
  have hR : (x * (BitVec.ofNat 64 2 - a * x)).toNat = x.toNat * (BitVec.ofNat 64 2 - a * x).toNat % 2 ^ 64 :=
    BitVec.toNat_mul _ _
  have hD : (BitVec.ofNat 64 2 - a * x).toNat = (2 ^ 64 - a.toNat * x.toNat % 2 ^ 64 + 2) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat]
  generalize (BitVec.ofNat 64 2 - a * x).toNat = D at hR hD
  generalize (x * (BitVec.ofNat 64 2 - a * x)).toNat = R at hR ⊢
  generalize x.toNat = X at *
  generalize a.toNat = A at *
  -- `D = 2 - A X + 2⁶⁴ j`.
  have hDj : (D : Int) = 2 - (A * X : Nat) + 2 ^ 64 * (((D : Int) - 2 + (A * X : Nat)) / 2 ^ 64) := by
    have : ((A * X : Nat) : Int) % 2 ^ 64 = ((A * X % 2 ^ 64 : Nat) : Int) := by omega
    omega
  generalize (((D : Int) - 2 + (A * X : Nat)) / 2 ^ 64) = j at hDj
  have hXD : ((X * D : Nat) : Int) = 2 * X - (X : Int) * (A * X : Nat) + 2 ^ 64 * (X * j) := by
    rw [Int.natCast_mul, hDj, Int.mul_add, Int.mul_sub, Int.mul_left_comm (X : Int) (2 ^ 64) j]
    omega
  have e : (X : Int) * (2 - (A : Int) * X) = 2 * X - (X : Int) * (A * X : Nat) := by
    rw [Int.mul_sub, Int.natCast_mul, Int.mul_comm (X : Int) 2]
  rw [e]
  have : ((X * D % 2 ^ 64 : Nat) : Int) = ((X * D : Nat) : Int) % 2 ^ 64 := by omega
  rw [hR, this, hXD]
  omega

theorem newton_ok (t : State) :
    WP isa (.block newton) t fun t' =>
      ((((t'.gpr .x4).toNat : Int) - (t.gpr .x4).toNat * (2 - (t.gpr .x3).toNat * (t.gpr .x4).toNat)) %
        (2 ^ 64 : Int) = 0 ∧ t'.gpr .x3 = t.gpr .x3 ∧ t'.mem = t.mem) ∧ Keep [.x4, .x5, .x6] t t' := by
  refine WP.keep [.x4, .x5, .x6] ?_ (by decide) (by decide) (by decide +kernel)
  unfold newton
  brun
  exact newton_val _ _

/-- A Newton step on the state: `a x' ≡ 1 (mod 2^(2j))` from `a x ≡ 1 (mod 2^j)`. -/
theorem newton_step_ok (t : State) {j : Nat} (hj : 2 * j ≤ 64)
    (h : (((t.gpr .x3).toNat : Int) * (t.gpr .x4).toNat - 1) % (2 ^ j : Int) = 0) :
    WP isa (.block newton) t fun t' =>
      ((((t'.gpr .x3).toNat : Int) * (t'.gpr .x4).toNat - 1) % (2 ^ (2 * j) : Int) = 0 ∧
      t'.gpr .x3 = t.gpr .x3 ∧ t'.mem = t.mem) ∧ Keep [.x4, .x5, .x6] t t' :=
  WP.mono (newton_ok t) fun t' ⟨⟨hv, hb, hm⟩, k⟩ => ⟨⟨by rw [hb]; exact newton_step hj h hv, hb, hm⟩, k⟩

/-- `minv`: `-m₀⁻¹ mod 2⁶⁴` into `x15`, for the odd `m₀` in `x3`. -/
theorem minv_ok (s : State) (hodd : (s.gpr .x3).toNat % 2 = 1) :
    WP isa (.block minv) s fun t =>
      ((s.gpr .x3).toNat * (t.gpr .x15).toNat + 1) % 2 ^ 64 = 0 ∧
      Keep [.x4, .x5, .x6, .x15] s t ∧ t.mem = s.mem := by
  unfold minv
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x4] (c := .block [mov .x4 .x3]) (Q := fun t =>
    t.gpr .x4 = s.gpr .x3 ∧ t.mem = s.mem) (by brun) (by decide) rfl (by decide +kernel))
    fun t₀ ⟨⟨h₀, hm₀⟩, k₀⟩ => ?_
  have hb₀ : t₀.gpr .x3 = s.gpr .x3 := k₀.gpr .x3 (by decide)
  have e₀ : (((t₀.gpr .x3).toNat : Int) * (t₀.gpr .x4).toNat - 1) % (2 ^ 3 : Int) = 0 := by
    rw [hb₀, h₀]
    have h1 := odd_sq _ hodd
    have h2 : (((s.gpr .x3).toNat : Int) * (s.gpr .x3).toNat) % 8 = 1 := by
      simpa only [Int.natCast_mul, Int.natCast_emod, show ((8 : Nat) : Int) = 8 from rfl,
        show ((1 : Nat) : Int) = 1 from rfl] using congrArg (fun n : Nat => (n : Int)) h1
    show (((s.gpr .x3).toNat : Int) * (s.gpr .x3).toNat - 1) % 8 = 0
    omega
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₀ (j := 3) (by decide) e₀) fun t₁ ⟨⟨e₁, hb₁, hm₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₁ (j := 6) (by decide) e₁) fun t₂ ⟨⟨e₂, hb₂, hm₂⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₂ (j := 12) (by decide) e₂) fun t₃ ⟨⟨e₃, hb₃, hm₃⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₃ (j := 24) (by decide) e₃) fun t₄ ⟨⟨e₄, hb₄, hm₄⟩, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₄ (j := 32) (by decide) (emod_pow_weaken (by decide) e₄))
    fun t₅ ⟨⟨e₅, hb₅, hm₅⟩, k₅⟩ => ?_
  have hb : t₅.gpr .x3 = s.gpr .x3 := hb₅.trans (hb₄.trans (hb₃.trans (hb₂.trans (hb₁.trans hb₀))))
  have kk := ((((k₀.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅
  rw [hb] at e₅
  refine WP.mono (WP.keep [.x6, .x15] (Q := fun t => t.gpr .x15 = 0 - t₅.gpr .x4 ∧ t.mem = t₅.mem)
    (by brun; rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h15, hm⟩, k⟩ =>
    ⟨?_, (kk.trans k).mono (by decide), ?_⟩
  · rw [h15, BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl]
    exact neg_inv (t₅.gpr .x4).isLt e₅
  · rw [hm, hm₅, hm₄, hm₃, hm₂, hm₁, hm₀]

/-! ## The arrays' bases -/

theorem setBase_ok {t : State} {B : Addr} {Z w j : Nat} (hs : Scr t B Z) (h0 : t.gpr .x0 = B)
    (hj : j < 8) (hZ : 8 * sArr 8 ≤ Z) (h4 : t.gpr .x4 = off B (slot w j))
    (h3 : t.gpr .x3 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block (setBase j)) t fun t' =>
      (t'.mem = t.mem.writeW (off B (8 * sArr j)) (off B (slot w j)) ∧
      t'.gpr .x4 = off B (slot w (j + 1))) ∧ Keep [.x4] t t' := by
  have h8 : 8 * sArr j + 8 ≤ 8 * sArr 8 := by unfold sArr; omega
  have hst : InRegions t.wr (off B (8 * sArr j)) 8 := hs.st (by omega)
  have hsa : sArr j < 32 := by unfold sArr; omega
  refine WP.keep [.x4] ?_ rfl rfl rfl
  unfold setBase
  brun [h0, h4, h3, hdr_enc hsa, hst]
  rw [show slot w (j + 1) = slot w j + 8 * (w + 2) by unfold slot; rw [Nat.add_mul, Nat.one_mul]; omega]

theorem setBasesN_ok {B : Addr} {Z w : Nat} (hZ : 8 * sArr 8 ≤ Z) :
    ∀ n ≤ 8, ∀ t : State, Scr t B Z → t.gpr .x0 = B → t.gpr .x4 = off B (slot w 0) →
      t.gpr .x3 = BitVec.ofNat 64 (8 * (w + 2)) →
      WP isa (.block ((List.range n).flatMap setBase)) t fun t' =>
        (∀ j < n, word t'.mem B (8 * sArr j) = off B (slot w j)) ∧ t'.gpr .x4 = off B (slot w n) ∧
        Outside B (8 * sArr 0) (8 * n) t.mem t'.mem ∧ Keep [.x4] t t' := by
  intro n
  induction n with
  | zero =>
    intro _ t _ _ h4 _
    exact WP.block_nil ⟨fun j hj => absurd hj (by omega), h4, Outside.refl _ _ _ _, Keep.refl _ _⟩
  | succ n ih =>
    intro hn t hs h0 h4 h3
    have hnZ := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega) t hs h0 h4 h3) fun t₁ ⟨hw₁, h4₁, ho₁, k₁⟩ => ?_
    refine WP.mono (setBase_ok (hs.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans h0) (by omega) hZ h4₁
      ((k₁.gpr .x3 (by decide)).trans h3)) fun t' ⟨⟨hm, h4'⟩, k'⟩ =>
        ⟨?_, h4', ?_, (k₁.trans k').mono (by decide)⟩
    · intro j hj
      rw [hm]
      by_cases hjn : j = n
      · subst hjn; exact word_writeW_self _ _ _ _
      · rw [(writeW_outside t₁.mem B _ (by unfold sArr at *; omega)).word
          (by unfold sArr; omega) (by unfold sArr; omega)]
        exact hw₁ j (by omega)
    · rw [hm]
      intro x hx
      rw [writeW_outside t₁.mem B _ (by unfold sArr; omega) x (by unfold sArr at *; omega)]
      exact ho₁ x (by omega)

/-- `setBases`: the arrays' bases into the header, for `w` in `x12`. -/
theorem setBases_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (hZ : 8 * sArr 8 ≤ Z) :
    WP isa (.block setBases) s fun t =>
      (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot w j)) ∧
      Outside B (8 * sArr 0) 64 s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  unfold setBases
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (8 * (w + 2)) ∧
      t.gpr .x4 = off B (slot w 0) ∧ t.mem = s.mem) ?_ (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h3, h4, hm⟩, k⟩ => ?_
  · brun [h12, h0]
    refine ⟨?_, by simp [off, slot, hdrBytes]⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  refine WP.mono (setBasesN_ok hZ 8 (by omega) t (hs.congr k.wr) ((k.gpr .x0 (by decide)).trans h0) h4 h3)
    fun t' ⟨hw', _, ho, k'⟩ => ⟨hw', by rw [← hm]; exact ho, (k.trans k').mono (by decide)⟩

end VG.Proof.Bignum.AArch64
