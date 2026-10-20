module

public import VerifiedGarbage.Proof.RsaKeyGen.Trial32
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The carried whole-word trial reduction computes the mathematical quotient -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Trial
open VG

def carry (a b : BitVec 32) : Bool := decide (2 ^ 32 ≤ a.toNat + b.toNat)

def carryWord (b : Bool) : BitVec 32 := (BitVec.ofBool b).setWidth 32

def quotient (h acc prime inv : BitVec 32) : BitVec 32 :=
  let lo := h + acc
  let q := BitVec.ofNat 32 (lo.toNat * inv.toNat)
  let prod := q.toNat * prime.toNat
  BitVec.ofNat 32 (prod / 2 ^ 32) + carryWord (carry h acc) +
    carryWord (carry (BitVec.ofNat 32 prod) lo)

theorem carryWord_toNat (b : Bool) : (carryWord b).toNat = b.toNat := by
  cases b <;> decide

theorem carry_toNat (a b : BitVec 32) : (carry a b).toNat = (a.toNat + b.toNat) / 2 ^ 32 := by
  have := a.isLt
  have := b.isLt
  unfold carry
  by_cases full : 2 ^ 32 ≤ a.toNat + b.toNat
  · rw [decide_eq_true full]
    change 1 = _
    omega
  · rw [decide_eq_false full]
    change 0 = _
    omega

theorem quotient_correct (h acc prime inv : BitVec 32)
    (primeLow : 3 ≤ prime.toNat) (primeHigh : prime.toNat ≤ 8161)
    (accBound : acc.toNat < 2 * prime.toNat)
    (inverse : (prime.toNat * inv.toNat + 1) % 2 ^ 32 = 0) :
    (quotient h acc prime inv).toNat =
      ((h.toNat + acc.toNat) + (h.toNat + acc.toNat) * inv.toNat % 2 ^ 32 * prime.toNat) / 2 ^ 32 := by
  have inputBound : h.toNat + acc.toNat < prime.toNat * 2 ^ 32 := by
    have := h.isLt
    omega
  have math := VG.Proof.RsaKeyGen.redc32_math inverse inputBound
  have qEq : (BitVec.ofNat 32 ((h + acc).toNat * inv.toNat)).toNat =
      (h.toNat + acc.toNat) * inv.toNat % 2 ^ 32 := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_add, Nat.mod_mul_mod]
  have lowBound : (BitVec.ofNat 32 ((h + acc).toNat * inv.toNat)).toNat * prime.toNat % 2 ^ 32 < 2 ^ 32 :=
    Nat.mod_lt _ (by decide)
  have highLow := Nat.div_add_mod
    ((BitVec.ofNat 32 ((h + acc).toNat * inv.toNat)).toNat * prime.toNat) (2 ^ 32)
  have input := Nat.div_add_mod (h.toNat + acc.toNat) (2 ^ 32)
  have addition := Nat.div_add_mod
    (((BitVec.ofNat 32 ((h + acc).toNat * inv.toNat)).toNat * prime.toNat) % 2 ^ 32 +
      (h.toNat + acc.toNat) % 2 ^ 32) (2 ^ 32)
  unfold quotient
  rw [BitVec.toNat_add, BitVec.toNat_add, carryWord_toNat, carryWord_toNat,
    carry_toNat, carry_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_add]
  rw [qEq] at highLow lowBound addition
  simp only [BitVec.toNat_ofNat, Nat.mod_mul_mod]
  simp only [Nat.mod_mul_mod] at highLow lowBound addition
  omega

end VG.Proof.RsaKeyGen.X86.Trial
