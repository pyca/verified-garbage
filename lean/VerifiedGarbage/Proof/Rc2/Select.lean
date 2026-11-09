module

public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.Mem
meta import Lean.Elab.Tactic.Omega.Frontend
import Std.Data.DTreeMap.Internal.Operations
import VerifiedGarbage.Proof.Framework.Omega

/-! # Arithmetic selection lemmas for RC2's constant-time lookups -/

@[expose] public section

namespace VG.Proof.Rc2

theorem maskByte (x : BitVec 64) : x &&& 255 = (x.setWidth 8).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change x.toNat &&& (2 ^ 8 - 1) = x.toNat % 256 % 18446744073709551616
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem joinBytes (lo hi : Byte) :
    lo.setWidth 64 ||| (hi.setWidth 64).rotateRight 56 =
      (lo.setWidth 16 ||| hi.setWidth 16 <<< 8).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_shiftLeft]
  by_cases h8 : j < 8
  · simp (disch := omega) [h8, show j < 16 by omega,
      BitVec.getLsbD_of_ge]
  · by_cases h16 : j < 16
    · simp (disch := omega) [h8, h16, hj, show j - 8 < 64 by omega,
        show j - 8 < 16 by omega, BitVec.getLsbD_of_ge]
    · simp (disch := omega) [h8, h16,
        BitVec.getLsbD_of_ge]

end VG.Proof.Rc2
