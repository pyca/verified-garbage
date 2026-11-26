module

public import VerifiedGarbage.Proof.Bignum.Amm52

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

variable {w : Nat}

def carryBit (g p : BitVec w) : Nat → Bool
  | 0 => false
  | i + 1 => g.getLsbD i || (p.getLsbD i && carryBit g p i)

private theorem shifted_succ (g : BitVec w) {i : Nat} (hi : i + 1 < w) :
    (g <<< 1).getLsbD (i + 1) = g.getLsbD i := by
  have h : ¬ i + 1 < 1 := by omega
  simp only [BitVec.getLsbD_shiftLeft, hi, h, decide_true, decide_false, Bool.not_false,
    Bool.true_and, Nat.add_sub_cancel]

private theorem addCarry (g p : BitVec w) {i : Nat} (hi : i < w)
    (disjoint : ∀ j < i, (g.getLsbD j && p.getLsbD j) = false) :
    (((g <<< 1).getLsbD i && BitVec.carry i p (g <<< 1) false) = false) ∧
    ((g <<< 1).getLsbD i || BitVec.carry i p (g <<< 1) false) = carryBit g p i := by
  induction i with
  | zero => simp [carryBit]
  | succ i ih =>
    obtain ⟨h, e⟩ := ih (Nat.lt_trans (Nat.lt_succ_self _) hi) (fun j hj => disjoint j (by omega))
    rw [shifted_succ g hi, BitVec.carry_succ, carryBit, ← e]
    have key : ∀ g p b c : Bool, (b && c) = false → (g && p) = false →
        ((g && Bool.atLeastTwo p b c) = false) ∧ (g || Bool.atLeastTwo p b c) = (g || (p && (b || c))) := by decide
    exact key _ _ _ _ h (disjoint i (Nat.lt_succ_self i))

theorem getLsbD_carryMask (g p : BitVec w) {i : Nat} (hi : i < w)
    (disjoint : ∀ j < i, (g.getLsbD j && p.getLsbD j) = false) :
    ((p + (g <<< 1)) ^^^ p).getLsbD i = carryBit g p i := by
  obtain ⟨h, e⟩ := addCarry g p hi disjoint
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_add hi, ← e]
  have key : ∀ p b c : Bool, (b && c) = false → ((p ^^ (b ^^ c)) ^^ p) = (b || c) := by decide
  exact key _ _ _ h

open VG.Proof.Bignum.Amm52

/-- The preceding limb's high bits, or zero at the first limb. -/
def priorHigh (L : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => L j / 2 ^ 52

/-- Add each high part to the following low part, in parallel. -/
def provisional (L : Nat → Nat) (j : Nat) : Nat := L j % 2 ^ 52 + priorHigh L j

/-- One-bit carries of the provisional limbs. -/
def extraCarry (L : Nat → Nat) : Nat → Bool
  | 0 => false
  | j + 1 => decide (2 ^ 52 ≤ provisional L j) ||
      (decide (provisional L j = 2 ^ 52 - 1) && extraCarry L j)

theorem carryIn_eq_high_add (L : Nat → Nat) (j : Nat) (hL : ∀ i < j, L i < 2 ^ 63) :
    carryIn L j = priorHigh L j + (extraCarry L j).toNat := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [carryIn, ih (fun i hi => hL i (by omega)), priorHigh, extraCarry]
    have hp : priorHigh L j < 2048 := by
      cases j with
      | zero => simp [priorHigh]
      | succ j =>
        change L j / 4503599627370496 < 2048
        have h := hL j (by omega)
        omega
    have hm := Nat.mod_lt (L j) (show 0 < 2 ^ 52 by decide)
    have h := Nat.mod_add_div (L j) (2 ^ 52)
    simp only [provisional]
    cases hc : extraCarry L j <;> by_cases hg : 2 ^ 52 ≤ L j % 2 ^ 52 + priorHigh L j <;>
      by_cases he : L j % 2 ^ 52 + priorHigh L j = 2 ^ 52 - 1 <;>
      simp [hg, he] <;> omega

theorem carried_eq_provisional (L : Nat → Nat) (j : Nat) (hL : ∀ i < j, L i < 2 ^ 63) :
    carried L j = (provisional L j + (extraCarry L j).toNat) % 2 ^ 52 := by
  rw [carried, carryIn_eq_high_add L j hL]
  simp only [provisional]
  omega

/-- Use the generate and propagate masks to recover the one-bit carry
into any represented limb. -/
theorem carryMask_eq_extraCarry (L : Nat → Nat) (g p : BitVec w) {i : Nat} (hi : i < w)
    (hg : ∀ j < i, g.getLsbD j = decide (2 ^ 52 ≤ provisional L j))
    (hp : ∀ j < i, p.getLsbD j = decide (provisional L j = 2 ^ 52 - 1)) :
    ((p + (g <<< 1)) ^^^ p).getLsbD i = extraCarry L i := by
  have hd : ∀ j < i, (g.getLsbD j && p.getLsbD j) = false := by
    intro j hj
    rw [hg j hj, hp j hj]
    by_cases h : provisional L j = 2 ^ 52 - 1 <;> simp [h]
  rw [getLsbD_carryMask g p hi hd]
  clear hd
  induction i with
  | zero => rfl
  | succ j ih =>
    have hj : j < w := by omega
    rw [carryBit, extraCarry, hg j (by omega), hp j (by omega), ih hj
      (fun k hk => hg k (by omega)) (fun k hk => hp k (by omega))]

private theorem carryMaskByte_test (i : Nat) (hi : i < 64) :
    (0x01010101 : BitVec 64).getLsbD i = decide (i = 0 ∨ i = 8 ∨ i = 16 ∨ i = 24) := by
  exact (show ∀ j : Fin 64, (0x01010101 : BitVec 64).getLsbD j.val =
    decide (j.val = 0 ∨ j.val = 8 ∨ j.val = 16 ∨ j.val = 24) from by decide) ⟨i, hi⟩

/-- Extract the four bits one byte apart and pack them into the low nibble. -/
theorem compactCarryBits_bit (x : BitVec 64) {j : Nat} (hj : j < 4) :
    (((((x &&& 0x01010101) * 0x01020408) >>> 24) &&& 15).getLsbD j) = x.getLsbD (8 * j) := by
  let a0 := x.getLsbD 0
  let a1 := x.getLsbD 8
  let a2 := x.getLsbD 16
  let a3 := x.getLsbD 24
  let placed := fun (b0 b1 b2 b3 : Bool) =>
    BitVec.ofNat 64 (b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat)
  have hb : ∀ (b0 b1 b2 b3 : Bool) (i : Fin 64),
      (placed b0 b1 b2 b3).getLsbD i.val =
        (if i.val = 0 then b0 else if i.val = 8 then b1 else if i.val = 16 then b2
          else if i.val = 24 then b3 else false) := by decide +kernel
  have hp : x &&& 0x01010101 = placed a0 a1 a2 a3 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, carryMaskByte_test i hi, hb _ _ _ _ ⟨i, hi⟩]
    by_cases h0 : i = 0
    · subst h0; exact Bool.and_true _
    by_cases h1 : i = 8
    · subst h1; exact Bool.and_true _
    by_cases h2 : i = 16
    · subst h2; exact Bool.and_true _
    by_cases h3 : i = 24
    · subst h3; exact Bool.and_true _
    simp only [h0, h1, h2, h3, or_false, decide_false, Bool.and_false, ↓reduceIte]
  have hc : ∀ (b0 b1 b2 b3 : Bool) (i : Fin 4),
      (((((placed b0 b1 b2 b3) * 0x01020408) >>> 24) &&& 15).getLsbD i.val) =
        (if i.val = 0 then b0 else if i.val = 1 then b1 else if i.val = 2 then b2 else b3) := by decide +kernel
  rw [hp, hc _ _ _ _ ⟨j, hj⟩]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

/-- The spread row occupies bits `row + 8 * lane` and no others. -/
theorem spreadCarryMask_shifted (x : BitVec 32) (hx : x.toNat < 16)
    {row i : Nat} (hr : row < 8) (hi : i < 32) :
    ((((x * 0x00204081) &&& 0x01010101) <<< row).getLsbD i) =
      (decide (i % 8 = row) && x.getLsbD (i / 8)) := by
  have h : ∀ (a : Fin 16) (r : Fin 8) (k : Fin 32),
      ((((BitVec.ofNat 32 a.val * 0x00204081) &&& 0x01010101) <<< r.val).getLsbD k.val) =
        (decide (k.val % 8 = r.val) && (BitVec.ofNat 32 a.val).getLsbD (k.val / 8)) := by
    decide +kernel
  have e : BitVec.ofNat 32 x.toNat = x := by simp
  simpa only [e] using h ⟨x.toNat, hx⟩ ⟨row, hr⟩ ⟨i, hi⟩

/-- A carry out of the final limb is one bit. Disjoint masks and
zero bits above the 32 limbs exclude a second carry at bit 33. -/
theorem carryMask_high_word (g p : BitVec 64)
    (hg : ∀ i ≥ 32, g.getLsbD i = false) (hp : ∀ i ≥ 32, p.getLsbD i = false)
    (hd : ∀ i < 32, (g.getLsbD i && p.getLsbD i) = false) :
    (((p + (g <<< 1)) ^^^ p) >>> 32) =
      (BitVec.ofBool (((p + (g <<< 1)) ^^^ p).getLsbD 32)).setWidth 64 := by
  have hh := (addCarry g p (i := 32) (by decide) hd).1
  have hg' (i : Nat) (hi : 33 ≤ i) : (g <<< 1).getLsbD i = false := by
    simp only [BitVec.getLsbD_shiftLeft, hg (i - 1) (by omega), Bool.and_false]
  have h33 : BitVec.carry 33 p (g <<< 1) false = false := by
    rw [show 33 = 32 + 1 by decide, BitVec.carry_succ, hp 32 (by decide)]
    simpa only [Bool.atLeastTwo_false_left] using hh
  have hz (i : Nat) : BitVec.carry (i + 33) p (g <<< 1) false = false := by
    induction i with
    | zero => exact h33
    | succ i ih =>
      rw [show i + 1 + 33 = (i + 33) + 1 by omega, BitVec.carry_succ,
        hp _ (by omega), hg' _ (by omega), ih]
      rfl
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h0 : i = 0
  · subst i
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBool, Nat.add_zero,
      Nat.reduceLT, decide_true, Bool.true_and]
  · have hz' : BitVec.carry (32 + i) p (g <<< 1) false = false := by
      rw [show 32 + i = (i - 1) + 33 by omega]
      exact hz _
    have hb : ((p + (g <<< 1)) ^^^ p).getLsbD (32 + i) = false := by
      by_cases hj : 32 + i < 64
      · rw [BitVec.getLsbD_xor, BitVec.getLsbD_add hj, hp _ (by omega), hg' _ (by omega), hz']
        rfl
      · exact BitVec.getLsbD_of_ge _ _ (by omega)
    simp only [BitVec.getLsbD_ushiftRight, hb, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBool, h0,
      decide_false, Bool.false_and, Bool.and_false]

end VG.Proof.Bignum.X86_64.Ifma
