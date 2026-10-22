module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightTriStep
public import VerifiedGarbage.Proof.Bignum.Square
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMath

/-! # The row-wise triangle of an eight-limb square: a carry chain of products

`n` steps `R i := R i + half(x · Y i) + c`, each forming its product in the
temporary just before its addition, add the halves' number to the
registers' number, with the carry in and out. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64.SquareEight

/-- The number in the registers `R 0, …, R (n - 1)`, least significant first. -/
def regVal (s : State) (R : Nat → Reg) (n : Nat) : Nat :=
  Square.value (2 ^ 64) (fun i => (s.gpr (R i)).toNat) n

/-- The number of the halves of `x · Y 0, …, x · Y (n - 1)`. -/
def halfVal (s : State) (hi : Bool) (x : Reg) (Y : Nat → Reg) (n : Nat) : Nat :=
  Square.value (2 ^ 64) (fun i => (half hi (s.gpr x) (s.gpr (Y i))).toNat) n

/-- The carry out of a chain of `n` steps: none of an empty one. -/
def carryOf (n : Nat) (s : State) : Nat := if n = 0 then 0 else s.c.toNat

/-- The registers a chain writes, with the temporary. -/
abbrev work : List Reg := tmp :: accs

theorem regVal_congr {s t : State} {R : Nat → Reg} {n : Nat}
    (h : ∀ i < n, t.gpr (R i) = s.gpr (R i)) : regVal t R n = regVal s R n :=
  BlockedRedc.value_congr fun i hi => congrArg BitVec.toNat (h i hi)

theorem halfVal_congr {s t : State} {hi : Bool} {x : Reg} {Y : Nat → Reg} {n : Nat}
    (hx : t.gpr x = s.gpr x) (h : ∀ i < n, t.gpr (Y i) = s.gpr (Y i)) :
    halfVal t hi x Y n = halfVal s hi x Y n :=
  BlockedRedc.value_congr fun i hi => by rw [hx, h i hi]

theorem prod_eq (hi : Bool) (x y : Reg) :
    (if hi then Instr.umulh tmp x y else Instr.mul .x tmp x y) = prod hi x y := rfl

private theorem chain_arith {V V' H C C' S R' h P s' : Nat}
    (ih : V + P * C = S + H) (hr : R' + 2 ^ 64 * C' = s' + h + C)
    (hv : V' = V + R' * P) : V' + P * 2 ^ 64 * C' = S + s' * P + (H + h * P) := by
  subst hv; grind

theorem chain_ok (hi : Bool) (x : Reg) (Y R S : Nat → Reg) (n : Nat) (s : State)
    (hw : ∀ i < n, R i ∈ accs) (hx : x ∉ work) (hY : ∀ k < n, Y k ∉ work)
    (hRR : ∀ i < n, ∀ k < n, R i = R k → i = k)
    (hS : ∀ i < n, S i ≠ tmp ∧ ∀ k < i, R k ≠ S i) :
    WP isa (.block (VG.Impl.Bignum.AArch64.SquareEight.chain hi x Y R S n)) s fun t =>
      (regVal t R n + 2 ^ (64 * n) * carryOf n t = regVal s S n + halfVal s hi x Y n ∧
        (∀ r, r ≠ tmp → (∀ i < n, R i ≠ r) → t.gpr r = s.gpr r) ∧ t.mem = s.mem) ∧
      Keep work s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨⟨by simp [regVal, halfVal, carryOf, Square.value], fun _ _ _ => rfl, rfl⟩,
      Keep.refl _ _⟩
  | succ n ih =>
    have hRt : R n ≠ tmp := fun h => by
      have := hw n (by omega); rw [h] at this; exact absurd this (by decide)
    simp only [VG.Impl.Bignum.AArch64.SquareEight.chain, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, prod_eq]
    apply WP.block_append
    refine WP.mono (ih s (fun i h => hw i (by omega)) (fun k h => hY k (by omega))
      (fun i h k h' => hRR i (by omega) k (by omega)) (fun i h => hS i (by omega)))
      fun a ⟨⟨ha, hak, ham⟩, ka⟩ => ?_
    have hSn : a.gpr (S n) = s.gpr (S n) :=
      hak _ (hS n (by omega)).1 fun i hi => (hS n (by omega)).2 i hi
    have hxa : a.gpr x = s.gpr x := ka.gpr x hx
    have hYa : a.gpr (Y n) = s.gpr (Y n) := ka.gpr _ (hY n (by omega))
    have hStep : WP isa (.block [prod hi x (Y n), (if n = 0 then Instr.adds else Instr.adcs) .x (R n) (S n) tmp]) a
        fun t => (t.gpr (R n) = addCarry (a.gpr (S n)) (half hi (a.gpr x) (a.gpr (Y n)))
            (if n = 0 then false else a.c) ∧
          t.c = carryOut (a.gpr (S n)) (half hi (a.gpr x) (a.gpr (Y n))) (if n = 0 then false else a.c) ∧
          t.mem = a.mem) ∧ Keep [tmp, R n] a t := by
      by_cases h0 : n = 0
      · simp only [h0, ↓reduceIte]
        exact prod_adds_ok a hi (R 0) (S 0) x (Y 0) (h0 ▸ hRt) (h0 ▸ (hS n (by omega)).1)
      · simp only [h0, ↓reduceIte]
        exact prod_adcs_ok a hi (R n) (S n) x (Y n) hRt (hS n (by omega)).1
    refine WP.mono hStep fun t ⟨⟨htr, htc, htm⟩, kt⟩ => ?_
    have tKeep : ∀ r, r ≠ tmp → r ≠ R n → t.gpr r = a.gpr r := fun r h1 h2 =>
      kt.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2⟩)
    have hlow : regVal t R n = regVal a R n := regVal_congr fun i hi =>
      tKeep _ (fun h => by have := hw i (by omega); rw [h] at this; exact absurd this (by decide))
        fun h => absurd (hRR i (by omega) n (by omega) h) (by omega)
    have hv := addCarry_value (a.gpr (S n)) (half hi (a.gpr x) (a.gpr (Y n))) (if n = 0 then false else a.c)
    rw [← htr, ← htc, hSn, hxa, hYa] at hv
    have hcin : (if n = 0 then false else a.c).toNat = carryOf n a := by
      by_cases h0 : n = 0 <;> simp [h0, carryOf]
    rw [hcin] at hv
    refine ⟨⟨?_, ?_, htm.trans ham⟩, (ka.trans kt).mono ?_⟩
    · have e1 : regVal t R (n + 1) = regVal t R n + (t.gpr (R n)).toNat * (2 ^ 64) ^ n := rfl
      have e2 : regVal s S (n + 1) = regVal s S n + (s.gpr (S n)).toNat * (2 ^ 64) ^ n := rfl
      have e3 : halfVal s hi x Y (n + 1) = halfVal s hi x Y n +
          (half hi (s.gpr x) (s.gpr (Y n))).toNat * (2 ^ 64) ^ n := rfl
      have e4 : carryOf (n + 1) t = t.c.toNat := rfl
      rw [e1, e2, e3, e4, hlow, show 2 ^ (64 * (n + 1)) = (2 ^ 64) ^ n * 2 ^ 64 by
        rw [Nat.mul_succ, Nat.pow_add, Nat.pow_mul]]
      rw [show 2 ^ (64 * n) = (2 ^ 64) ^ n by rw [Nat.pow_mul]] at ha
      exact chain_arith ha hv rfl
    · intro r h1 h2
      exact (tKeep r h1 (fun h => h2 n (by omega) h.symm)).trans
        (hak r h1 fun i hi => h2 i (by omega))
    · intro r hr
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h
      · exact h
      · exact Or.inl h
      · exact Or.inr (h ▸ hw n (by omega))

end VG.Proof.Bignum.AArch64.SquareEight
