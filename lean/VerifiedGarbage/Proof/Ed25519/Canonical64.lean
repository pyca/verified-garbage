import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.X25519.Bytes

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Word64`. -/
section

/-! Target-independent unsigned word arithmetic for the Ed25519 ports. -/
namespace VG.Proof.Ed25519.Word64

abbrev Word := BitVec 64

def addCarry (a b : VG.Proof.Ed25519.Word64.Word) (c : Bool) : VG.Proof.Ed25519.Word64.Word := a + b + BitVec.ofNat 64 c.toNat
def carryOut (a b : VG.Proof.Ed25519.Word64.Word) (c : Bool) : Bool := decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)

abbrev val4 (a b c d : VG.Proof.Ed25519.Word64.Word) : Nat :=
  a.toNat + 2 ^ 64 * b.toNat + 2 ^ 128 * c.toNat + 2 ^ 192 * d.toNat

theorem val4_lt (a b c d : VG.Proof.Ed25519.Word64.Word) : VG.Proof.Ed25519.Word64.val4 a b c d < 2 ^ 256 := by
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [VG.Proof.Ed25519.Word64.val4]
  omega

theorem low_le_val4 (a b c d : VG.Proof.Ed25519.Word64.Word) : a.toNat ≤ VG.Proof.Ed25519.Word64.val4 a b c d := by
  simp only [VG.Proof.Ed25519.Word64.val4]
  omega

theorem carryWord (c : Bool) : (BitVec.ofNat 64 c.toNat).toNat = c.toNat := by
  cases c <;> rfl

theorem carry38_value (c : Bool) : (VG.Proof.Ed25519.Word64.addCarry 0 0 c * 38).toNat = 38 * c.toNat := by
  cases c <;> decide

theorem borrow_mask (c : Bool) : VG.Proof.Ed25519.Word64.addCarry 0 (~~~0) c = if c then 0 else -1 := by
  cases c <;> decide

theorem borrow38_value (c : Bool) :
    (VG.Proof.Ed25519.Word64.addCarry 0 (~~~0) c &&& 38).toNat = 38 * (1 - c.toNat) := by
  cases c <;> decide

theorem addCarry_value (a b : VG.Proof.Ed25519.Word64.Word) (c : Bool) :
    (VG.Proof.Ed25519.Word64.addCarry a b c).toNat + 2 ^ 64 * (VG.Proof.Ed25519.Word64.carryOut a b c).toNat =
      a.toNat + b.toNat + c.toNat := by
  have := a.isLt; have := b.isLt; have := Bool.toNat_le c
  simp only [VG.Proof.Ed25519.Word64.addCarry, BitVec.toNat_add, VG.Proof.Ed25519.Word64.carryWord, VG.Proof.Ed25519.Word64.carryOut]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- Complemented addition implements subtraction with C as *no borrow*. -/
theorem subCarry_value (a b : VG.Proof.Ed25519.Word64.Word) (c : Bool) :
    (VG.Proof.Ed25519.Word64.addCarry a (~~~b) c).toNat + b.toNat + (1 - c.toNat) =
      a.toNat + 2 ^ 64 * (1 - (VG.Proof.Ed25519.Word64.carryOut a (~~~b) c).toNat) := by
  have h := VG.Proof.Ed25519.Word64.addCarry_value a (~~~b) c
  have hb := b.isLt
  have hc := Bool.toNat_le c
  have hd := Bool.toNat_le (VG.Proof.Ed25519.Word64.carryOut a (~~~b) c)
  simp only [BitVec.toNat_not] at h
  omega

theorem addCarry_false (a b : VG.Proof.Ed25519.Word64.Word) : VG.Proof.Ed25519.Word64.addCarry a b false = a + b := by
  change a + b + 0 = a + b
  exact BitVec.add_zero _

theorem carryOut_false (a b : VG.Proof.Ed25519.Word64.Word) :
    VG.Proof.Ed25519.Word64.carryOut a b false = decide (2 ^ 64 ≤ a.toNat + b.toNat) := by
  simp only [VG.Proof.Ed25519.Word64.carryOut, Bool.toNat_false, Nat.add_zero]

theorem addCarry_sub (a b : VG.Proof.Ed25519.Word64.Word) (c : Bool) :
    VG.Proof.Ed25519.Word64.addCarry a (~~~b) c = a - b - BitVec.ofNat 64 (1 - c.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := b.isLt; have := Bool.toNat_le c
  simp only [VG.Proof.Ed25519.Word64.addCarry, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_not,
    BitVec.toNat_ofNat]
  omega

/-- Four limbs, including a carry into the low limb and out of the high limb. -/
theorem add4_value (a0 a1 a2 a3 b0 b1 b2 b3 : VG.Proof.Ed25519.Word64.Word) (c : Bool) :
    let c0 := VG.Proof.Ed25519.Word64.carryOut a0 b0 c
    let c1 := VG.Proof.Ed25519.Word64.carryOut a1 b1 c0
    let c2 := VG.Proof.Ed25519.Word64.carryOut a2 b2 c1
    let c3 := VG.Proof.Ed25519.Word64.carryOut a3 b3 c2
    VG.Proof.Ed25519.Word64.val4 (VG.Proof.Ed25519.Word64.addCarry a0 b0 c) (VG.Proof.Ed25519.Word64.addCarry a1 b1 c0) (VG.Proof.Ed25519.Word64.addCarry a2 b2 c1) (VG.Proof.Ed25519.Word64.addCarry a3 b3 c2) +
        2 ^ 256 * c3.toNat = VG.Proof.Ed25519.Word64.val4 a0 a1 a2 a3 + VG.Proof.Ed25519.Word64.val4 b0 b1 b2 b3 + c.toNat := by
  intro c0 c1 c2 c3
  have e0 := VG.Proof.Ed25519.Word64.addCarry_value a0 b0 c
  have e1 := VG.Proof.Ed25519.Word64.addCarry_value a1 b1 c0
  have e2 := VG.Proof.Ed25519.Word64.addCarry_value a2 b2 c1
  have e3 := VG.Proof.Ed25519.Word64.addCarry_value a3 b3 c2
  dsimp only [c0, c1, c2, c3] at *
  simp only [VG.Proof.Ed25519.Word64.val4]
  omega

theorem sub4_value (a0 a1 a2 a3 b0 b1 b2 b3 : VG.Proof.Ed25519.Word64.Word) (c : Bool) :
    let c0 := VG.Proof.Ed25519.Word64.carryOut a0 (~~~b0) c
    let c1 := VG.Proof.Ed25519.Word64.carryOut a1 (~~~b1) c0
    let c2 := VG.Proof.Ed25519.Word64.carryOut a2 (~~~b2) c1
    let c3 := VG.Proof.Ed25519.Word64.carryOut a3 (~~~b3) c2
    VG.Proof.Ed25519.Word64.val4 (VG.Proof.Ed25519.Word64.addCarry a0 (~~~b0) c) (VG.Proof.Ed25519.Word64.addCarry a1 (~~~b1) c0)
        (VG.Proof.Ed25519.Word64.addCarry a2 (~~~b2) c1) (VG.Proof.Ed25519.Word64.addCarry a3 (~~~b3) c2) +
        VG.Proof.Ed25519.Word64.val4 b0 b1 b2 b3 + (1 - c.toNat) =
      VG.Proof.Ed25519.Word64.val4 a0 a1 a2 a3 + 2 ^ 256 * (1 - c3.toNat) := by
  intro c0 c1 c2 c3
  have e0 := VG.Proof.Ed25519.Word64.subCarry_value a0 b0 c
  have e1 := VG.Proof.Ed25519.Word64.subCarry_value a1 b1 c0
  have e2 := VG.Proof.Ed25519.Word64.subCarry_value a2 b2 c1
  have e3 := VG.Proof.Ed25519.Word64.subCarry_value a3 b3 c2
  dsimp only [c0, c1, c2, c3] at *
  simp only [VG.Proof.Ed25519.Word64.val4]
  omega

/-- A full 64-by-64 product, plus two words, fits in two words. -/
theorem multiply_accumulate (a b c t : VG.Proof.Ed25519.Word64.Word) :
    let lo := a * b
    let hi := BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)
    let r := VG.Proof.Ed25519.Word64.addCarry lo c false
    let d := VG.Proof.Ed25519.Word64.addCarry hi 0 (VG.Proof.Ed25519.Word64.carryOut lo c false)
    (VG.Proof.Ed25519.Word64.addCarry t r false).toNat +
        2 ^ 64 * (VG.Proof.Ed25519.Word64.addCarry d 0 (VG.Proof.Ed25519.Word64.carryOut t r false)).toNat =
      t.toNat + c.toNat + a.toNat * b.toNat := by
  intro lo hi r d
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have ht := t.isLt
  have hp : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hlo : lo.toNat = a.toNat * b.toNat % 2 ^ 64 := BitVec.toNat_mul _ _
  have hhi : hi.toNat = a.toNat * b.toNat / 2 ^ 64 := by
    simp only [hi, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hz : (0 : VG.Proof.Ed25519.Word64.Word).toNat = 0 := rfl
  simp only [r, d, VG.Proof.Ed25519.Word64.addCarry, VG.Proof.Ed25519.Word64.carryOut, BitVec.toNat_add, VG.Proof.Ed25519.Word64.carryWord,
    Bool.toNat_false, BitVec.add_zero, hz, Nat.add_zero, hlo, hhi]
  by_cases h1 : 2 ^ 64 ≤ a.toNat * b.toNat % 2 ^ 64 + c.toNat
  all_goals simp only [h1, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false]
  all_goals by_cases h2 : 2 ^ 64 ≤ t.toNat + (a.toNat * b.toNat % 2 ^ 64 + c.toNat) % 2 ^ 64
  all_goals simp only [h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false]
  all_goals omega

/-- A doubled bounded value cannot carry out of its four limbs. -/
theorem bounded_double {v a c b : Nat} (e : v + 2 ^ 256 * c = a + a + b)
    (h : 2 * a + b < 2 ^ 256) : v = 2 * a + b := by omega

end VG.Proof.Ed25519.Word64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Field64`. -/
section

/-! Target-independent facts for folding carries modulo 2^255 - 19. -/
namespace VG.Proof.Ed25519.Word64
open VG.Proof.X25519

/-- After adding a small word to a four-word number, folding a final
carry back as 38 cannot overflow the low word. -/
theorem foldCarry_low (r0 r1 r2 r3 : VG.Proof.Ed25519.Word64.Word) (c : Bool) {a v : Nat}
    (ha : a < 2 ^ 256) (hv : v < 2 ^ 58)
    (h : VG.Proof.Ed25519.Word64.val4 r0 r1 r2 r3 + 2 ^ 256 * c.toNat = a + v) :
    (r0 + BitVec.ofNat 64 (38 * c.toNat)).toNat = r0.toNat + 38 * c.toNat := by
  have hl := VG.Proof.Ed25519.Word64.low_le_val4 r0 r1 r2 r3
  cases c with
  | false =>
    change (r0 + 0).toNat = r0.toNat + 0
    exact congrArg BitVec.toNat (BitVec.add_zero r0)
  | true =>
    have hb : r0.toNat + 38 < 2 ^ 64 := by
      simp only [Bool.toNat_true, Nat.mul_one] at h
      omega
    change (r0 + 38).toNat = r0.toNat + 38
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt hb

theorem foldCarry_field (r0 r1 r2 r3 : VG.Proof.Ed25519.Word64.Word) (c : Bool) {a v : Nat}
    (ha : a < 2 ^ 256) (hv : v < 2 ^ 58)
    (h : VG.Proof.Ed25519.Word64.val4 r0 r1 r2 r3 + 2 ^ 256 * c.toNat = a + v) :
    toFe (VG.Proof.Ed25519.Word64.val4 (r0 + BitVec.ofNat 64 (38 * c.toNat)) r1 r2 r3) = toFe (a + v) := by
  have hn : VG.Proof.Ed25519.Word64.val4 (r0 + BitVec.ofNat 64 (38 * c.toNat)) r1 r2 r3 =
      VG.Proof.Ed25519.Word64.val4 r0 r1 r2 r3 + 38 * c.toNat := by
    simp only [VG.Proof.Ed25519.Word64.val4]
    rw [VG.Proof.Ed25519.Word64.foldCarry_low r0 r1 r2 r3 c ha hv h]
    omega
  apply toFe_congr
  rw [hn, ← h]
  exact (fold256 _ _).symm

end VG.Proof.Ed25519.Word64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Canonical64`. -/
section

/-! Target-independent canonicalization of four field limbs. -/
namespace VG.Proof.Ed25519.Word64
open VG.Spec.X25519 (P)

def mask (sw : Bool) : VG.Proof.Ed25519.Word64.Word := if sw then BitVec.allOnes 64 else 0

theorem xor_sel (sw : Bool) (a b : VG.Proof.Ed25519.Word64.Word) :
    a ^^^ ((a ^^^ b) &&& VG.Proof.Ed25519.Word64.mask sw) = (if sw then b else a) ∧
      b ^^^ ((a ^^^ b) &&& VG.Proof.Ed25519.Word64.mask sw) = (if sw then a else b) := by
  cases sw
  · simp only [VG.Proof.Ed25519.Word64.mask, Bool.false_eq_true, ite_false]
    constructor <;> (apply BitVec.eq_of_toNat_eq; simp)
  · simp only [VG.Proof.Ed25519.Word64.mask, ite_true, BitVec.and_allOnes]
    constructor
    · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem xor_sel' (sw : Bool) (a b : VG.Proof.Ed25519.Word64.Word) :
    a ^^^ ((b ^^^ a) &&& VG.Proof.Ed25519.Word64.mask sw) = if sw then b else a := by
  rw [BitVec.xor_comm b a]
  exact (VG.Proof.Ed25519.Word64.xor_sel sw a b).1

theorem and_low63 (x : VG.Proof.Ed25519.Word64.Word) : (x &&& 0x7fffffffffffffff).toNat = x.toNat % 2 ^ 63 := by
  rw [BitVec.toNat_and, show (0x7fffffffffffffff : VG.Proof.Ed25519.Word64.Word).toNat = 2 ^ 63 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem fold_top (a0 a1 a2 a3 a3' m : VG.Proof.Ed25519.Word64.Word) (hm : m.toNat = 19 * (a3.toNat / 2 ^ 63))
    (hl : a3'.toNat = a3.toNat % 2 ^ 63) :
    let c0 := VG.Proof.Ed25519.Word64.carryOut a0 m false
    let c1 := VG.Proof.Ed25519.Word64.carryOut a1 0 c0
    let c2 := VG.Proof.Ed25519.Word64.carryOut a2 0 c1
    let v := VG.Proof.Ed25519.Word64.val4 (VG.Proof.Ed25519.Word64.addCarry a0 m false) (VG.Proof.Ed25519.Word64.addCarry a1 0 c0)
      (VG.Proof.Ed25519.Word64.addCarry a2 0 c1) (VG.Proof.Ed25519.Word64.addCarry a3' 0 c2)
    v % P = VG.Proof.Ed25519.Word64.val4 a0 a1 a2 a3 % P ∧ v < 2 ^ 255 + 19 := by
  intro c0 c1 c2 v
  have e := VG.Proof.Ed25519.Word64.add4_value a0 a1 a2 a3' m 0 0 0 false
  change v + 2 ^ 256 * _ = _ at e
  clear_value v c2 c1 c0
  have h0 := a0.isLt; have h1 := a1.isLt; have h2 := a2.isLt; have h3 := a3.isLt
  have hz : (0 : VG.Proof.Ed25519.Word64.Word).toNat = 0 := rfl
  simp only [VG.Proof.Ed25519.Word64.val4, hz, Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e
  have hv : VG.Proof.Ed25519.Word64.val4 a0 a1 a2 a3 = v + P * (a3.toNat / 2 ^ 63) := by
    simp only [VG.Proof.Ed25519.Word64.val4, P]
    omega
  exact ⟨by rw [hv, Nat.add_mul_mod_self_left], by omega⟩

theorem add19_top (a0 a1 a2 a3 : VG.Proof.Ed25519.Word64.Word) (hx : VG.Proof.Ed25519.Word64.val4 a0 a1 a2 a3 < 2 ^ 255 + 19) :
    let c0 := VG.Proof.Ed25519.Word64.carryOut a0 19 false
    let c1 := VG.Proof.Ed25519.Word64.carryOut a1 0 c0
    let c2 := VG.Proof.Ed25519.Word64.carryOut a2 0 c1
    let w3 := VG.Proof.Ed25519.Word64.addCarry a3 0 c2
    0 - w3 >>> 63 = VG.Proof.Ed25519.Word64.mask (decide (P ≤ VG.Proof.Ed25519.Word64.val4 a0 a1 a2 a3)) ∧
    (P ≤ VG.Proof.Ed25519.Word64.val4 a0 a1 a2 a3 → VG.Proof.Ed25519.Word64.val4 (VG.Proof.Ed25519.Word64.addCarry a0 19 false) (VG.Proof.Ed25519.Word64.addCarry a1 0 c0)
      (VG.Proof.Ed25519.Word64.addCarry a2 0 c1) (w3 &&& 0x7fffffffffffffff) = VG.Proof.Ed25519.Word64.val4 a0 a1 a2 a3 - P) := by
  intro c0 c1 c2 w3
  have e := VG.Proof.Ed25519.Word64.add4_value a0 a1 a2 a3 19 0 0 0 false
  change VG.Proof.Ed25519.Word64.val4 _ _ _ w3 + 2 ^ 256 * _ = _ at e
  clear_value w3 c2
  generalize VG.Proof.Ed25519.Word64.addCarry a0 19 false = w0 at e ⊢
  generalize VG.Proof.Ed25519.Word64.addCarry a1 0 c0 = w1 at e ⊢
  generalize VG.Proof.Ed25519.Word64.addCarry a2 0 c1 = w2 at e ⊢
  have hb : (19 : VG.Proof.Ed25519.Word64.Word).toNat = 19 := rfl
  have hz : (0 : VG.Proof.Ed25519.Word64.Word).toNat = 0 := rfl
  have h0 := w0.isLt; have h1 := w1.isLt; have h2 := w2.isLt; have h3 := w3.isLt
  simp only [VG.Proof.Ed25519.Word64.val4, hb, hz, Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e hx ⊢
  have ht : (w3 >>> 63).toNat = w3.toNat / 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hl := VG.Proof.Ed25519.Word64.and_low63 w3
  by_cases h : P ≤ a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat
  · have h1' : w3.toNat / 2 ^ 63 = 1 := by simp only [P] at h; omega
    rw [BitVec.eq_of_toNat_eq (show (w3 >>> 63).toNat = (1 : VG.Proof.Ed25519.Word64.Word).toNat by rw [ht, h1']; rfl),
      decide_eq_true h]
    refine ⟨by decide, fun _ => ?_⟩
    rw [hl]
    simp only [P] at h ⊢
    omega
  · have h0' : w3.toNat / 2 ^ 63 = 0 := by simp only [P] at h; omega
    rw [BitVec.eq_of_toNat_eq (show (w3 >>> 63).toNat = (0 : VG.Proof.Ed25519.Word64.Word).toNat by rw [ht, h0']; rfl),
      decide_eq_false h]
    exact ⟨by decide, fun h' => absurd h' h⟩

end VG.Proof.Ed25519.Word64

end
