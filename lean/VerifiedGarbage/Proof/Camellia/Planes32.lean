module

public import VerifiedGarbage.Impl.Camellia.Planes32
public import VerifiedGarbage.Proof.Camellia.Bitsliced32
import VerifiedGarbage.Proof.Camellia.Bitsliced

/-!
# Planes of Camellia's 64-bit constants, on 32-bit targets

`sigma_rel`: the planes `keyPlane32` of a constant hold it in every lane,
as the bitsliced rounds read a table entry (`W32.HalfRel`).
-/

@[expose] public section

namespace VG.Proof.Camellia

open VG.Impl.Camellia (planeBits32 keyPlane32)

theorem testBit_planeBits32 (x : BitVec 64) (w j n p : Nat) :
    (planeBits32 x w j n).testBit p = (decide (p < n) && x.getLsbD (56 - 8 * (4 * w + p / 8) + j)) := by
  induction n with
  | zero => simp [planeBits32]
  | succ n ih =>
    rw [planeBits32, Nat.testBit_or, ih]
    have hlt : (decide (p < n + 1)) = (decide (p < n) || decide (p = n)) := by
      by_cases h : p < n <;> by_cases h' : p = n <;> simp [h, h'] <;> omega
    rw [hlt]
    by_cases hpn : p = n
    · subst hpn; split <;> simp_all
    · split <;> simp [hpn, Ne.symm hpn]

theorem keyPlane32_bit (x : BitVec 64) (w j : Nat) {p : Nat} (hp : p < 32) :
    (keyPlane32 x w j).getLsbD p = x.getLsbD (56 - 8 * (4 * w + p / 8) + j) := by
  rw [keyPlane32, BitVec.getLsbD_ofNat, testBit_planeBits32]
  simp [hp]

/-- The planes of a constant hold it in every lane. -/
theorem sigma_rel (x : BitVec 64) : W32.HalfRel (fun k => keyPlane32 x (k / 8) (k % 8)) fun _ => x := by
  intro b hb c hc j hj
  rw [keyPlane32_bit _ _ _ (by omega), getLsbD_byteOf _ hc hj, show (8 * (c / 4) + j) / 8 = c / 4 by omega,
    show (8 * (c / 4) + j) % 8 = j by omega, show (8 * (c % 4) + b) / 8 = c % 4 by omega,
    show 4 * (c / 4) + c % 4 = c by omega]

end VG.Proof.Camellia
