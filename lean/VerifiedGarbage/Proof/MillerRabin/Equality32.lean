module

public import VerifiedGarbage.Proof.Mont.Words32

/-! # Native-word XOR accumulation is equality of the represented integers -/

@[expose] public section
namespace VG.Proof.MillerRabin
open VG VG.Proof.Mont

def xorWords (m : Mem) (W : Addr) (a b : Nat) : Nat → BitVec 32
  | 0 => 0#32
  | n + 1 => (m.readW (off W a) 32 ^^^ m.readW (off W b) 32) ||| xorWords m W (a + 4) (b + 4) n

theorem val32_cons_eq (m : Mem) (W : Addr) (a b n : Nat) :
    val32 m W a (n + 1) = val32 m W b (n + 1) ↔
      w32 m W a = w32 m W b ∧ val32 m W (a + 4) n = val32 m W (b + 4) n := by
  have lowA : w32 m W a < 2 ^ 32 := (m.readW (off W a) 32).isLt
  have lowB : w32 m W b < 2 ^ 32 := (m.readW (off W b) 32).isLt
  change w32 m W a + 2 ^ 32 * val32 m W (a + 4) n =
    w32 m W b + 2 ^ 32 * val32 m W (b + 4) n ↔ _
  omega

theorem xorWords_zero (m : Mem) (W : Addr) (a b n : Nat) :
    xorWords m W a b n = 0#32 ↔ val32 m W a n = val32 m W b n := by
  induction n generalizing a b with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ n ih =>
    rw [xorWords, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, ih, val32_cons_eq]
    constructor
    · rintro ⟨H, V⟩
      exact ⟨congrArg BitVec.toNat H, V⟩
    · rintro ⟨H, V⟩
      exact ⟨BitVec.eq_of_toNat_eq H, V⟩

theorem xorWords_succ (m : Mem) (W : Addr) (a b n : Nat) :
    xorWords m W a b (n + 1) = xorWords m W a b n |||
      (m.readW (off W (a + 4 * n)) 32 ^^^ m.readW (off W (b + 4 * n)) 32) := by
  induction n generalizing a b with
  | zero => simp only [xorWords, Nat.mul_zero, Nat.add_zero, BitVec.or_zero, BitVec.zero_or]
  | succ n ih =>
    change (m.readW (off W a) 32 ^^^ m.readW (off W b) 32) |||
      xorWords m W (a + 4) (b + 4) (n + 1) =
      ((m.readW (off W a) 32 ^^^ m.readW (off W b) 32) ||| xorWords m W (a + 4) (b + 4) n) |||
        (m.readW (off W (a + 4 * (n + 1))) 32 ^^^ m.readW (off W (b + 4 * (n + 1))) 32)
    rw [ih (a + 4) (b + 4), BitVec.or_assoc]
    rw [show a + 4 + 4 * n = a + 4 * (n + 1) by omega,
      show b + 4 + 4 * n = b + 4 * (n + 1) by omega]

end VG.Proof.MillerRabin
