module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Shift
import VerifiedGarbage.Proof.RsaKeyGen.Shift32

/-! # The fixed native-word reduction consumes the input's high-to-low bits -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64

def shifted (x i : Nat) : Nat := (x % 2 ^ (32 - i)) * 2 ^ i
def consumed (x i : Nat) : Nat := x / 2 ^ (32 - i)

theorem word_step (x i : Nat) (index : i < 32) (word : BitVec 32) (value : word.toNat = shifted x i) :
    (word + word).toNat = shifted x (i + 1) ∧
      consumed x i * 2 + (incoming word).toNat = consumed x (i + 1) := by
  have H := VG.Proof.RsaKeyGen.shift_step32 x (31 - i) i (by omega)
  rw [show 31 - i + 1 = 32 - i by omega, show 31 - i = 32 - (i + 1) by omega] at H
  have bitValue : (incoming word).toNat = x / 2 ^ (32 - (i + 1)) % 2 := by
    unfold incoming
    rw [value]
    exact H.2.1
  refine ⟨?_, ?_⟩
  · rw [BitVec.toNat_add, value]
    exact H.2.2.1
  · rw [bitValue]
    exact H.2.2.2

theorem consumed_mod_step (r x i exponent bit : Nat) (advance : consumed x i * 2 + bit = consumed x (i + 1)) :
    (2 * ((r * 2 ^ i + consumed x i) % exponent) + bit) % exponent =
      (r * 2 ^ (i + 1) + consumed x (i + 1)) % exponent := by
  rw [Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
  congr 1
  rw [Nat.pow_succ]
  grind

end VG.Proof.RsaKeyGen.X86.Mod64
