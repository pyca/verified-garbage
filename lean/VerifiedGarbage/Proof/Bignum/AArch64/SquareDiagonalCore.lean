module

import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonal
public import VerifiedGarbage.Impl.Bignum.AArch64.Square
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Register arithmetic of one doubled cross-product pair plus a diagonal. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem carry3_nat (a b c : Bool) :
    (BitVec.ofNat 64 a.toNat + BitVec.ofNat 64 b.toNat + BitVec.ofNat 64 c.toNat).toNat =
      a.toNat + b.toNat + c.toNat := by
  have ha := Bool.toNat_le a; have hb := Bool.toNat_le b; have hc := Bool.toNat_le c
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_arith

theorem carry3_bound (a b c : Bool) : a.toNat + b.toNat + c.toNat ≤ 3 := by
  have ha := Bool.toNat_le a; have hb := Bool.toNat_le b; have hc := Bool.toNat_le c
  omega

theorem diagonalCore_ok (s : State) (h7 : s.gpr .x7 = 0) :
    WP isa (.block VG.Impl.Bignum.AArch64.Square.diagonalCore) s fun t =>
      ((t.gpr .x3).toNat + 2 ^ 64*(t.gpr .x4).toNat + 2 ^ 128*(t.gpr .x5).toNat =
        2*((s.gpr .x3).toNat + 2 ^ 64*(s.gpr .x4).toNat) +
          (s.gpr .x2).toNat + 2 ^ 64*(s.gpr .x1).toNat + (s.gpr .x5).toNat ∧
        (t.gpr .x5).toNat ≤ 3 ∧ t.mem = s.mem) ∧ Keep [.x3, .x4, .x5, .x6] s t := by
  refine WP.keep [.x3, .x4, .x5, .x6] ?_ rfl rfl rfl
  unfold VG.Impl.Bignum.AArch64.Square.diagonalCore
  brun [h7]
  simp only [Bool.toNat_false, Nat.add_zero, add_ofNat0, add_zero64, zero_add64, show (0 : BitVec 64).toNat = 0 from rfl]
  constructor
  · rw [carry3_nat]
    simpa only [off, BitVec.ofNat_add, BitVec.add_assoc] using
      (diagonal_pair_val (s.gpr .x2) (s.gpr .x1) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5))
  · rw [carry3_nat]
    exact carry3_bound _ _ _

end VG.Proof.Bignum.AArch64.Square
