import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Wp
import VerifiedGarbage.Proof.Sha3.X86_64.X4.Loop

/-!
# Keccak-f[1600] four times at once, in registers: one round

One round (`round`) of the four states held in the registers `lreg i`
(`Regs4`), lane by lane (`Proof.Sha3.out`) in each of the four elements:
θ's columns (`columns_ok`) and `D` (`dcols_ok`), ρ and π along `piChain`
(`rhoPi_ok`), χ plane by plane (`chis_ok`) and ι (`iota_ok`).
-/

namespace VG.Proof.Sha3.X86_64.X4R

open VG VG.X86_64 VG.Impl.Sha3.X86_64.X4R
open VG.Proof.Sha3 (C D B out rotl outState)
open VG.Impl.Sha3 (piSrc rhoOff)
open VG.Proof.Sha3.X86_64.X4 (KState Lane la la_eq not_eq_xor)
open VG.Proof.Sha3.X86_64 (wp_nil)
open VG.Impl.Sha3.X86_64 (at_)

/-- The four states are held in the registers: lane `i` of state `k` is
element `k` of `lreg i`. -/
def Regs4 (s : State) (A : Nat → KState) : Prop := ∀ i < 25, ∀ k < 4, qy s (lreg i) k = (A k)[i]!

/-! ## Registers -/

theorem vreg_inj : ∀ i < 31, ∀ j < 31, vreg i = vreg j → i = j := by decide

theorem lreg_ne {i j : Nat} (hi : i < 25) (hj : j < 25) (h : i ≠ j) : lreg i ≠ lreg j :=
  fun e => h (vreg_inj i (by omega) j (by omega) e)

theorem creg_ne {x x' : Nat} (hx : x < 5) (hx' : x' < 5) (h : x ≠ x') : creg x ≠ creg x' :=
  fun e => h (by have := vreg_inj (25 + x) (by omega) (25 + x') (by omega) e; omega)

theorem lreg_creg {i x : Nat} (hi : i < 25) (hx : x < 5) : lreg i ≠ creg x :=
  fun e => by have := vreg_inj i (by omega) (25 + x) (by omega) e; omega

theorem lreg_T {i : Nat} (hi : i < 25) : lreg i ≠ T :=
  fun e => by have := vreg_inj i (by omega) 30 (by omega) e; omega

theorem creg_T {x : Nat} (hx : x < 5) : creg x ≠ T :=
  fun e => by have := vreg_inj (25 + x) (by omega) 30 (by omega) e; omega

/-! ## Vector code -/

theorem ite_t {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by simp [h]
theorem ite_f {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b := by simp [h]

/-- `s'` agrees with `s` but for the vector registers and the flags. -/
structure Same (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Same.refl (s : State) : Same s s := ⟨rfl, rfl, rfl, rfl⟩

theorem Same.trans {s₁ s₂ s₃ : State} (h₁ : Same s₁ s₂) (h₂ : Same s₂ s₃) : Same s₁ s₃ :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem YUpd.same {s s' : State} {d : VReg} {v : Nat → BitVec 64} (h : YUpd s s' d v) : Same s s' :=
  ⟨h.gpr, h.mem, h.rd, h.wr⟩

/-- Running `f 0, …, f (n - 1)`, one instruction each. -/
theorem wp_range_map {f : Nat → Instr} {N : Nat} (Inv : Nat → State → Prop)
    (hstep : ∀ k s, k < N → Inv k s → WP isa (.block [f k]) s (Inv (k + 1))) (s : State) (hs : Inv 0 s) :
    WP isa (.block ((List.range N).map f)) s (Inv N) := by
  rw [List.map_eq_flatMap]
  exact wp_range_flatMap (M := isa) Inv hstep N (Nat.le_refl _) s hs

/-! ## θ: the columns -/

theorem column_ok (x : Nat) (hx : x < 5) (s : State) (A : Nat → KState) (hA : Regs4 s A) :
    WP isa (.block (column x)) s fun s' =>
      Same s s' ∧ (∀ r, r ≠ creg x → ∀ k < 4, qy s' r k = qy s r k) ∧ ∀ k < 4, qy s' (creg x) k = C (A k) x := by
  unfold column
  refine wp_exor fun s₁ u₁ => wp_tern96 fun s₂ u₂ => wp_exor fun s₃ u₃ => wp_nil
    ⟨(u₁.same.trans u₂.same).trans u₃.same, fun r hr k hk => by rw [u₃.other r hr k hk, u₂.other r hr k hk,
      u₁.other r hr k hk], fun k hk => ?_⟩
  have o : ∀ i < 25, ∀ t : State, ∀ t' : State, ∀ v, YUpd t t' (creg x) v → qy t' (lreg i) k = qy t (lreg i) k :=
    fun i hi t t' v u => u.other _ (lreg_creg hi hx) k hk
  rw [u₃.val k hk, u₂.val k hk, u₁.val k hk, o _ (by omega) _ _ _ u₂, o _ (by omega) _ _ _ u₁,
    o _ (by omega) _ _ _ u₁, o _ (by omega) _ _ _ u₁, hA x (by omega) k hk, hA (x + 5) (by omega) k hk, hA (x + 10) (by omega) k hk,
    hA (x + 15) (by omega) k hk, hA (x + 20) (by omega) k hk]
  rfl

/-- After the first `n` columns. -/
def ColInv (s₀ : State) (A : Nat → KState) (n : Nat) (s : State) : Prop :=
  Same s₀ s ∧ Regs4 s A ∧ ∀ x < n, ∀ k < 4, qy s (creg x) k = C (A k) x

theorem columns_ok (s₀ : State) (A : Nat → KState) (hA : Regs4 s₀ A) :
    WP isa (.block ((List.range 5).flatMap column)) s₀ (ColInv s₀ A 5) := by
  refine wp_range_flatMap (M := isa) (ColInv s₀ A) (fun x s hx ⟨hw, hr, hc⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Same.refl _, hA, fun _ h => absurd h (by omega)⟩
  refine WP.mono (column_ok x hx s A hr) fun s' ⟨h, ho, hv⟩ => ⟨hw.trans h, fun i hi k hk => ?_, fun x' hx' k hk => ?_⟩
  · rw [ho _ (lreg_creg hi hx) k hk, hr i hi k hk]
  · by_cases e : x' = x
    · subst e; exact hv k hk
    · rw [ho _ (creg_ne (by omega) hx e) k hk, hc x' (by omega) k hk]

/-! ## θ: `D` -/

/-- Lane `i` after θ. -/
def Th (A : KState) (i : Nat) : Lane := A[i]! ^^^ D A (i % 5)

theorem xor_D (a c r : Lane) : a ^^^ c ^^^ r = a ^^^ (r ^^^ c) := by
  rw [BitVec.xor_assoc, BitVec.xor_comm c r]

/-- The lanes of column `x` with the first `n` updated. -/
def DyInv (s₀ : State) (A : Nat → KState) (x n : Nat) (s : State) : Prop :=
  Same s₀ s ∧ (∀ x' < 5, ∀ k < 4, qy s (creg x') k = qy s₀ (creg x') k) ∧
    (∀ k < 4, qy s T k = (C (A k) ((x + 1) % 5)).rotateRight 63) ∧
    ∀ i < 25, ∀ k < 4, qy s (lreg i) k = if i % 5 = x ∧ i / 5 < n then Th (A k) i else qy s₀ (lreg i) k

theorem dcol_ok (x : Nat) (hx : x < 5) (s : State) (A : Nat → KState)
    (hc : ∀ x' < 5, ∀ k < 4, qy s (creg x') k = C (A k) x')
    (hl : ∀ i < 25, ∀ k < 4, i % 5 = x → qy s (lreg i) k = (A k)[i]!) :
    WP isa (.block (dcol x)) s fun s' =>
      Same s s' ∧ (∀ x' < 5, ∀ k < 4, qy s' (creg x') k = qy s (creg x') k) ∧
      ∀ i < 25, ∀ k < 4, qy s' (lreg i) k = if i % 5 = x then Th (A k) i else qy s (lreg i) k := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h4 : (x + 4) % 5 < 5 := Nat.mod_lt _ (by omega)
  unfold dcol
  refine wp_eror (by decide) fun s₁ u₁ => ?_
  refine WP.mono (wp_range_map (DyInv s₁ A x) (fun y t hy ⟨hw, hcs, hT, hls⟩ => ?_) s₁
    ⟨Same.refl _, fun _ _ _ _ => rfl, fun k hk => by rw [u₁.val k hk, hc _ h1 k hk],
      fun i _ k _ => by simp only [Nat.not_lt_zero, and_false, ite_false]⟩) fun s' ⟨hw, hcs, _, hls⟩ => ?_
  · have hi : x + 5 * y < 25 := by omega
    refine wp_tern96 fun t' u => wp_nil ⟨hw.trans u.same, fun x' hx' k hk => by
        rw [u.other _ (lreg_creg hi hx').symm k hk, hcs x' hx' k hk],
      fun k hk => by rw [u.other _ (lreg_T hi).symm k hk, hT k hk], fun i hi' k hk => ?_⟩
    by_cases e : i = x + 5 * y
    · subst e
      have e1 : (x + 5 * y) % 5 = x := by omega
      have e2 : ¬((x + 5 * y) % 5 = x ∧ (x + 5 * y) / 5 < y) := by omega
      have e3 : (x + 5 * y) % 5 = x ∧ (x + 5 * y) / 5 < y + 1 := by omega
      rw [u.val k hk, hls _ hi k hk, hT k hk, hcs _ h4 k hk, u₁.other _ (creg_T h4) k hk, hc _ h4 k hk,
        ite_f e2, ite_t e3, u₁.other _ (lreg_T hi) k hk, hl _ hi k hk e1, Th, e1, D, xor_D]
    · rw [u.other _ (lreg_ne hi' hi e) k hk, hls i hi' k hk]
      congr 1
      apply propext; constructor
      · intro ⟨a, b⟩; exact ⟨a, by omega⟩
      · intro ⟨a, b⟩; exact ⟨a, by omega⟩
  · refine ⟨u₁.same.trans hw, fun x' hx' k hk => by rw [hcs x' hx' k hk, u₁.other _ (creg_T hx') k hk],
      fun i hi k hk => ?_⟩
    rw [hls i hi k hk, u₁.other _ (lreg_T hi) k hk]
    congr 1
    apply propext; constructor
    · intro ⟨a, _⟩; exact a
    · intro a; exact ⟨a, by omega⟩

/-- After the first `n` columns' `D`. -/
def DInv (s₀ : State) (A : Nat → KState) (n : Nat) (s : State) : Prop :=
  Same s₀ s ∧ (∀ x < 5, ∀ k < 4, qy s (creg x) k = C (A k) x) ∧
    ∀ i < 25, ∀ k < 4, qy s (lreg i) k = if i % 5 < n then Th (A k) i else (A k)[i]!

theorem dcols_ok (s₀ : State) (A : Nat → KState) (hA : Regs4 s₀ A)
    (hc : ∀ x < 5, ∀ k < 4, qy s₀ (creg x) k = C (A k) x) :
    WP isa (.block ((List.range 5).flatMap dcol)) s₀ (DInv s₀ A 5) := by
  refine wp_range_flatMap (M := isa) (DInv s₀ A) (fun x s hx ⟨hw, hcs, hl⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Same.refl _, hc, fun i hi k hk => by simp only [Nat.not_lt_zero, ite_false]; exact hA i hi k hk⟩
  refine WP.mono (dcol_ok x hx s A hcs fun i hi k hk e => by
      rw [hl i hi k hk, ite_f (show ¬ i % 5 < x by omega)])
    fun s' ⟨h, hc', hl'⟩ => ⟨hw.trans h, fun x' hx' k hk => by rw [hc' x' hx' k hk, hcs x' hx' k hk],
      fun i hi k hk => ?_⟩
  rw [hl' i hi k hk]
  by_cases e : i % 5 = x
  · rw [ite_t e, ite_t (show i % 5 < x + 1 by omega)]
  · rw [ite_f e, hl i hi k hk]
    by_cases e' : i % 5 < x
    · rw [ite_t e', ite_t (show i % 5 < x + 1 by omega)]
    · rw [ite_f e', ite_f (show ¬ i % 5 < x + 1 by omega)]

/-! ## ρ and π -/

theorem chain_len : piChain.length = 24 := rfl

/-- The facts about `piChain` the proof uses, each for the 24 lanes. -/
theorem chain_lt : ∀ j < 24, piChain.getD j 0 < 25 ∧ piChain.getD j 0 ≠ 0 := by decide
theorem chain_inj : ∀ j < 24, ∀ j' < 24, piChain.getD j 0 = piChain.getD j' 0 → j = j' := by decide
theorem chain_src : ∀ j < 23,
    piSrc (piChain.getD j 0 % 5) (piChain.getD j 0 / 5) = piChain.getD (j + 1) 0 := by decide
theorem chain_last : piSrc (piChain.getD 23 0 % 5) (piChain.getD 23 0 / 5) = piChain.getD 0 0 := by decide
theorem chain_all : ∀ p < 25, p ≠ 0 → ∃ j < 24, piChain.getD j 0 = p := by decide
theorem chain_rho : ∀ j < 24, 0 < rhoOff (piChain.getD j 0) ∧ rhoOff (piChain.getD j 0) < 64 := by decide
theorem piSrc_lt : ∀ p < 25, piSrc (p % 5) (p / 5) < 25 := by decide
theorem piSrc_zero : piSrc (0 % 5) (0 / 5) = 0 := rfl
theorem rhoOff_zero : rhoOff 0 = 0 := rfl
theorem piSrc_mod (x y : Nat) : piSrc x y % 5 = (x + 3 * y) % 5 := by
  simp only [piSrc]; omega

/-- Lane `p` after ρ and π: `B` at it. -/
def Bp (A : KState) (p : Nat) : Lane := B A (p % 5) (p / 5)

theorem Bp_eq (A : KState) (p : Nat) :
    Bp A p = rotl (Th A (piSrc (p % 5) (p / 5))) (rhoOff (piSrc (p % 5) (p / 5))) := by
  rw [Bp, B, Th, piSrc_mod]

/-- After the first `n` steps of the chain. -/
def ChInv (s₀ : State) (A : Nat → KState) (n : Nat) (s : State) : Prop :=
  Same s₀ s ∧ (∀ x < 5, ∀ k < 4, qy s (creg x) k = qy s₀ (creg x) k) ∧
    (∀ k < 4, qy s T k = Th (A k) (piChain.getD 0 0)) ∧
    ∀ i < 25, ∀ k < 4, qy s (lreg i) k = if ∃ j < n, piChain.getD j 0 = i then Bp (A k) i else Th (A k) i

theorem rotl_ror (v : Lane) {r : Nat} (h₁ : 0 < r) (h₂ : r < 64) : v.rotateRight (64 - r) = rotl v r := by
  rw [rotl, ite_f (show ¬ r = 0 by omega)]

theorem rhoPi_ok (s₀ : State) (A : Nat → KState) (hT : ∀ i < 25, ∀ k < 4, qy s₀ (lreg i) k = Th (A k) i) :
    WP isa (.block rhoPi) s₀ fun s =>
      Same s₀ s ∧ (∀ x < 5, ∀ k < 4, qy s (creg x) k = qy s₀ (creg x) k) ∧
      ∀ p < 25, ∀ k < 4, qy s (lreg p) k = Bp (A k) p := by
  unfold rhoPi
  refine wp_ecopy fun s₁ u₁ => ?_
  rw [List.append_eq, WP.block_append_iff]
  refine WP.mono (wp_range_map (ChInv s₀ A) (fun j t hj ⟨hw, hcs, hTt, hls⟩ => ?_) s₁
    ⟨u₁.same, fun x hx k hk => u₁.other _ (creg_T hx) k hk, fun k hk => by rw [u₁.val k hk]; exact hT 1 (by omega) k hk,
      fun i hi k hk => by
        rw [u₁.other _ (lreg_T hi) k hk, hT i hi k hk,
          ite_f (show ¬ ∃ j < 0, piChain.getD j 0 = i from fun ⟨_, h, _⟩ => absurd h (by omega))]⟩)
    fun s₂ ⟨hw, hcs, hTt, hls⟩ => ?_
  · have ⟨hc₀, _⟩ := chain_lt j (by omega)
    have ⟨hc₁, _⟩ := chain_lt (j + 1) (by omega)
    have ⟨r₀, r₁⟩ := chain_rho (j + 1) (by omega)
    refine wp_eror (by unfold rhoR; omega) fun t' u => wp_nil ⟨hw.trans u.same,
      fun x hx k hk => by rw [u.other _ (lreg_creg hc₀ hx).symm k hk, hcs x hx k hk],
      fun k hk => by rw [u.other _ (lreg_T hc₀).symm k hk, hTt k hk], fun i hi k hk => ?_⟩
    by_cases e : i = piChain.getD j 0
    · subst e
      have nf : ¬ ∃ j' < j, piChain.getD j' 0 = piChain.getD (j + 1) 0 := by
        rintro ⟨j', hj', e'⟩
        have := chain_inj j' (by omega) (j + 1) (by omega) e'
        omega
      have tt : ∃ j' < j + 1, piChain.getD j' 0 = piChain.getD j 0 := ⟨j, by omega, rfl⟩
      rw [u.val k hk, hls _ hc₁ k hk, ite_f nf, ite_t tt, Bp_eq, chain_src j hj, rhoR]
      exact rotl_ror _ r₀ r₁
    · rw [u.other _ (lreg_ne hi hc₀ e) k hk, hls i hi k hk]
      congr 1
      apply propext; constructor
      · rintro ⟨j', hj', e'⟩; exact ⟨j', by omega, e'⟩
      · rintro ⟨j', hj', e'⟩
        refine ⟨j', ?_, e'⟩
        by_contra h
        exact e (by rw [← e', show j' = j by omega])
  · have c23 : piChain.getD 23 0 = 10 := rfl
    have c0 : piChain.getD 0 0 = 1 := rfl
    refine wp_eror (show rhoR 1 < 64 by decide) fun s₃ u => wp_nil ⟨hw.trans u.same,
      fun x hx k hk => by rw [u.other _ (lreg_creg (by decide) hx).symm k hk, hcs x hx k hk],
      fun p hp k hk => ?_⟩
    by_cases e : p = 10
    · subst e
      rw [u.val k hk, hTt k hk, Bp_eq, ← c23, chain_last, c0, rhoR]
      exact rotl_ror _ (by decide) (by decide)
    · rw [u.other _ (lreg_ne hp (by decide) e) k hk, hls p hp k hk]
      by_cases e0 : p = 0
      · subst e0
        have nf : ¬ ∃ j' < 23, piChain.getD j' 0 = 0 := fun ⟨j', hj', e'⟩ => (chain_lt j' (by omega)).2 e'
        rw [ite_f nf, Bp_eq, piSrc_zero, rhoOff_zero, rotl, ite_t rfl]
      · obtain ⟨j', hj', e'⟩ := chain_all p hp e0
        have tt : ∃ j'' < 23, piChain.getD j'' 0 = p := ⟨j', by
          by_contra h
          exact e (by rw [← e', show j' = 23 by omega]; rfl), e'⟩
        rw [ite_t tt]
/-! ## χ -/

/-- Lane `p` of the output of χ, before ι. -/
def Xp (A : KState) (p : Nat) : Lane := out A 0 (p % 5) (p / 5)

theorem out_t (A : KState) (rc : Lane) (x y : Nat) (h : ¬(x = 0 ∧ y = 0)) : out A rc x y = out A 0 x y := by
  simp only [out, h, ite_false]

theorem chi_val (A : KState) (x y : Nat) :
    (B A ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& B A ((x + 2) % 5) y ^^^ B A x y = out A 0 x y := by
  simp only [out]; split <;> simp

/-- After the first `n` planes of χ. -/
def ChiInv (s₀ : State) (A : Nat → KState) (n : Nat) (s : State) : Prop :=
  Same s₀ s ∧ ∀ i < 25, ∀ k < 4, qy s (lreg i) k = if i / 5 < n then Xp (A k) i else Bp (A k) i

/-- χ on five lanes `b₀, …, b₄` in the distinct registers `a₀, …, a₄`, with
the copies in `t₀` and `t₁`. -/
theorem chi5_ok (s : State) (a₀ a₁ a₂ a₃ a₄ t₀ t₁ : VReg) (b : Nat → Nat → Lane)
    (n01 : a₀ ≠ a₁) (n02 : a₀ ≠ a₂) (n03 : a₀ ≠ a₃) (n04 : a₀ ≠ a₄) (n12 : a₁ ≠ a₂) (n13 : a₁ ≠ a₃)
    (n14 : a₁ ≠ a₄) (n23 : a₂ ≠ a₃) (n24 : a₂ ≠ a₄) (n34 : a₃ ≠ a₄) (m0 : t₀ ≠ t₁)
    (p0 : ∀ a ∈ [a₀, a₁, a₂, a₃, a₄], a ≠ t₀) (p1 : ∀ a ∈ [a₀, a₁, a₂, a₃, a₄], a ≠ t₁)
    (h0 : ∀ k < 4, qy s a₀ k = b 0 k) (h1 : ∀ k < 4, qy s a₁ k = b 1 k) (h2 : ∀ k < 4, qy s a₂ k = b 2 k)
    (h3 : ∀ k < 4, qy s a₃ k = b 3 k) (h4 : ∀ k < 4, qy s a₄ k = b 4 k) :
    WP isa (.block [copy t₀ a₀, copy t₁ a₁, tern a₀ a₁ a₂ 0xD2, tern a₁ a₂ a₃ 0xD2, tern a₂ a₃ a₄ 0xD2,
      tern a₃ a₄ t₀ 0xD2, tern a₄ t₀ t₁ 0xD2]) s fun s' =>
      Same s s' ∧ (∀ r, r ∉ [a₀, a₁, a₂, a₃, a₄, t₀, t₁] → ∀ k < 4, qy s' r k = qy s r k) ∧
      ∀ x < 5, ∀ k < 4, qy s' ([a₀, a₁, a₂, a₃, a₄].getD x a₀) k =
        (b ((x + 1) % 5) k ^^^ 0xffffffffffffffff) &&& b ((x + 2) % 5) k ^^^ b x k := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at p0 p1
  obtain ⟨q0, q1, q2, q3, q4⟩ := p0
  obtain ⟨r0, r1, r2, r3, r4⟩ := p1
  refine wp_ecopy fun s₁ u₁ => wp_ecopy fun s₂ u₂ => wp_ternD2 fun s₃ u₃ => wp_ternD2 fun s₄ u₄ =>
    wp_ternD2 fun s₅ u₅ => wp_ternD2 fun s₆ u₆ => wp_ternD2 fun s₇ u₇ => wp_nil
      ⟨(((((u₁.same.trans u₂.same).trans u₃.same).trans u₄.same).trans u₅.same).trans u₆.same).trans u₇.same,
        fun r hr k hk => ?_, fun x hx k hk => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := hr
    rw [u₇.other _ e4 k hk, u₆.other _ e3 k hk, u₅.other _ e2 k hk, u₄.other _ e1 k hk, u₃.other _ e0 k hk,
      u₂.other _ e6 k hk, u₁.other _ e5 k hk]
  · -- Each register before its write.
    have z0 : qy s₂ a₀ k = b 0 k := by rw [u₂.other _ r0 k hk, u₁.other _ q0 k hk, h0 k hk]
    have z1 : qy s₂ a₁ k = b 1 k := by rw [u₂.other _ r1 k hk, u₁.other _ q1 k hk, h1 k hk]
    have z2 : qy s₂ a₂ k = b 2 k := by rw [u₂.other _ r2 k hk, u₁.other _ q2 k hk, h2 k hk]
    have z3 : qy s₂ a₃ k = b 3 k := by rw [u₂.other _ r3 k hk, u₁.other _ q3 k hk, h3 k hk]
    have z4 : qy s₂ a₄ k = b 4 k := by rw [u₂.other _ r4 k hk, u₁.other _ q4 k hk, h4 k hk]
    have zt0 : qy s₂ t₀ k = b 0 k := by rw [u₂.other _ m0 k hk, u₁.val k hk, h0 k hk]
    have zt1 : qy s₂ t₁ k = b 1 k := by rw [u₂.val k hk, u₁.other _ q1 k hk, h1 k hk]
    rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd, Nat.reduceMod]
    · rw [u₇.other _ n04 k hk, u₆.other _ n03 k hk, u₅.other _ n02 k hk, u₄.other _ n01 k hk, u₃.val k hk, z0, z1, z2]
    · rw [u₇.other _ n14 k hk, u₆.other _ n13 k hk, u₅.other _ n12 k hk, u₄.val k hk, u₃.other _ n02.symm k hk,
        u₃.other _ n03.symm k hk, u₃.other _ n01.symm k hk, z1, z2, z3]
    · rw [u₇.other _ n24 k hk, u₆.other _ n23 k hk, u₅.val k hk, u₄.other _ n13.symm k hk, u₄.other _ n14.symm k hk,
        u₄.other _ n12.symm k hk, u₃.other _ n03.symm k hk, u₃.other _ n04.symm k hk, u₃.other _ n02.symm k hk,
        z2, z3, z4]
    · rw [u₇.other _ n34 k hk, u₆.val k hk, u₅.other _ n24.symm k hk, u₅.other _ q2.symm k hk,
        u₅.other _ n23.symm k hk, u₄.other _ n14.symm k hk, u₄.other _ q1.symm k hk, u₄.other _ n13.symm k hk,
        u₃.other _ n04.symm k hk, u₃.other _ q0.symm k hk, u₃.other _ n03.symm k hk, z4, zt0, z3]
    · rw [u₇.val k hk, u₆.other _ q3.symm k hk, u₆.other _ r3.symm k hk, u₆.other _ n34.symm k hk,
        u₅.other _ q2.symm k hk, u₅.other _ r2.symm k hk, u₅.other _ n24.symm k hk,
        u₄.other _ q1.symm k hk, u₄.other _ r1.symm k hk, u₄.other _ n14.symm k hk,
        u₃.other _ q0.symm k hk, u₃.other _ r0.symm k hk, u₃.other _ n04.symm k hk, zt0, zt1, z4]


/-- χ on plane `y`. -/
theorem chi_ok (y : Nat) (hy : y < 5) (s : State) (A : Nat → KState)
    (hb : ∀ x < 5, ∀ k < 4, qy s (lreg (5 * y + x)) k = Bp (A k) (5 * y + x)) :
    WP isa (.block (chi y)) s fun s' =>
      Same s s' ∧ (∀ i < 25, i / 5 ≠ y → ∀ k < 4, qy s' (lreg i) k = qy s (lreg i) k) ∧
      ∀ x < 5, ∀ k < 4, qy s' (lreg (5 * y + x)) k = Xp (A k) (5 * y + x) := by
  have l : ∀ x < 5, 5 * y + x < 25 := fun x hx => by omega
  have ne : ∀ x < 5, ∀ x' < 5, x ≠ x' → lreg (5 * y + x) ≠ lreg (5 * y + x') :=
    fun x hx x' hx' h => lreg_ne (l x hx) (l x' hx') (by omega)
  have lc : ∀ x < 5, ∀ c < 5, lreg (5 * y + x) ≠ creg c := fun x hx c hc => lreg_creg (l x hx) hc
  refine WP.mono (chi5_ok s (lreg (5 * y + 0)) (lreg (5 * y + 1)) (lreg (5 * y + 2)) (lreg (5 * y + 3))
    (lreg (5 * y + 4)) (creg 0) (creg 1) (fun x k => Bp (A k) (5 * y + x))
    (ne 0 (by omega) 1 (by omega) (by omega)) (ne 0 (by omega) 2 (by omega) (by omega))
    (ne 0 (by omega) 3 (by omega) (by omega)) (ne 0 (by omega) 4 (by omega) (by omega))
    (ne 1 (by omega) 2 (by omega) (by omega)) (ne 1 (by omega) 3 (by omega) (by omega))
    (ne 1 (by omega) 4 (by omega) (by omega)) (ne 2 (by omega) 3 (by omega) (by omega))
    (ne 2 (by omega) 4 (by omega) (by omega)) (ne 3 (by omega) 4 (by omega) (by omega))
    (creg_ne (by omega) (by omega) (by omega))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨lc 0 (by omega) 0 (by omega), lc 1 (by omega) 0 (by omega), lc 2 (by omega) 0 (by omega),
          lc 3 (by omega) 0 (by omega), lc 4 (by omega) 0 (by omega)⟩)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨lc 0 (by omega) 1 (by omega), lc 1 (by omega) 1 (by omega), lc 2 (by omega) 1 (by omega),
          lc 3 (by omega) 1 (by omega), lc 4 (by omega) 1 (by omega)⟩)
    (hb 0 (by omega)) (hb 1 (by omega)) (hb 2 (by omega)) (hb 3 (by omega)) (hb 4 (by omega)))
    fun s' ⟨hs, ho, hv⟩ => ⟨hs, fun i hi hiy k hk => ho _ ?_ k hk, fun x hx k hk => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨lreg_ne hi (l 0 (by omega)) (by omega), lreg_ne hi (l 1 (by omega)) (by omega),
      lreg_ne hi (l 2 (by omega)) (by omega), lreg_ne hi (l 3 (by omega)) (by omega),
      lreg_ne hi (l 4 (by omega)) (by omega), lreg_creg hi (by omega), lreg_creg hi (by omega)⟩
  · have e := hv x hx k hk
    have g : [lreg (5 * y + 0), lreg (5 * y + 1), lreg (5 * y + 2), lreg (5 * y + 3), lreg (5 * y + 4)].getD x
        (lreg (5 * y + 0)) = lreg (5 * y + x) := by
      rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [g] at e
    rw [e, Xp, show (5 * y + x) % 5 = x by omega, show (5 * y + x) / 5 = y by omega, ← chi_val]
    simp only [Bp]
    rw [show (5 * y + (x + 1) % 5) % 5 = (x + 1) % 5 by omega, show (5 * y + (x + 1) % 5) / 5 = y by omega,
      show (5 * y + (x + 2) % 5) % 5 = (x + 2) % 5 by omega, show (5 * y + (x + 2) % 5) / 5 = y by omega,
      show (5 * y + x) % 5 = x by omega, show (5 * y + x) / 5 = y by omega]

theorem chis_ok (s₀ : State) (A : Nat → KState) (hb : ∀ p < 25, ∀ k < 4, qy s₀ (lreg p) k = Bp (A k) p) :
    WP isa (.block ((List.range 5).flatMap chi)) s₀ (ChiInv s₀ A 5) := by
  refine wp_range_flatMap (M := isa) (ChiInv s₀ A) (fun y s hy ⟨hw, hl⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Same.refl _, fun i hi k hk => by rw [ite_f (show ¬ i / 5 < 0 by omega)]; exact hb i hi k hk⟩
  refine WP.mono (chi_ok y hy s A fun x hx k hk => by
      rw [hl _ (by omega) k hk, ite_f (show ¬ (5 * y + x) / 5 < y by omega)])
    fun s' ⟨h, ho, hv⟩ => ⟨hw.trans h, fun i hi k hk => ?_⟩
  by_cases e : i / 5 = y
  · rw [ite_t (show i / 5 < y + 1 by omega), show i = 5 * y + i % 5 by omega]
    exact hv _ (Nat.mod_lt _ (by omega)) k hk
  · rw [ho i hi e k hk, hl i hi k hk]
    by_cases e' : i / 5 < y
    · rw [ite_t e', ite_t (show i / 5 < y + 1 by omega)]
    · rw [ite_f e', ite_f (show ¬ i / 5 < y + 1 by omega)]

/-! ## ι, and the next round constant -/

theorem iota_ok (s : State) (rcp : Addr) (rc : Lane) (hrdx : s.gpr .rdx = rcp)
    (hin : InRegions (s.rd ++ s.wr) rcp 32) (hrc : ∀ k < 4, s.mem.readW (la rcp 0 k) 64 = rc) :
    WP isa (.block iota) s fun s' =>
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ k < 4, qy s' (lreg 0) k = qy s (lreg 0) k ^^^ rc) ∧
      (∀ i < 25, i ≠ 0 → ∀ k < 4, qy s' (lreg i) k = qy s (lreg i) k) ∧
      s'.gpr .rdx = rcp + 32 ∧ (∀ g, g ≠ .rdx → s'.gpr g = s.gpr g) ∧
      s'.zf = some (rcp + 32 - s.gpr .rcx == 0) := by
  have ha : s.ea (at_ .rdx 0) = rcp := by rw [VG.Proof.Sha3.X86_64.ea_at, hrdx]; exact BitVec.add_zero _
  unfold iota
  refine wp_evld ha hin fun s₁ u₁ => wp_exor fun s₂ u₂ => WP.cons rfl (WP.cons rfl (wp_nil ?_))
  have g : s₂.gpr = s.gpr := u₂.gpr.trans u₁.gpr
  refine ⟨u₂.mem.trans u₁.mem, u₂.rd.trans u₁.rd, u₂.wr.trans u₁.wr, fun k hk => ?_, fun i hi h0 k hk => ?_, ?_, ?_, ?_⟩
  · show qy s₂ (lreg 0) k = _
    rw [u₂.val k hk, u₁.other _ (lreg_T (by decide)) k hk, u₁.val k hk, ← hrc k hk]
    simp only [la, Nat.mul_zero, Nat.zero_add]
  · show qy s₂ (lreg i) k = _
    rw [u₂.other _ (lreg_ne hi (by decide) h0) k hk, u₁.other _ (lreg_T hi) k hk]
  · simp [State.setReg, g, hrdx]
  · intro r hr; simp [State.setReg, g, hr]
  · simp [State.setReg, g, hrdx]

end VG.Proof.Sha3.X86_64.X4R
