module
public import VerifiedGarbage.Impl.Bignum.Arm.R2
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block

/-! # The one and two needed by R-squared precomputation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem r2Constants_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) :
    WP isa r2Constants s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 4 = 1 ∧ w32 t.mem (State.addr base) (arrAt w 7) = 2 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [r2Constants, WP.seq_iff]
  refine WP.mono (smallConst_ok s (o := 4) 1 h (by decide) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨ready, one, _, keeps1, frame1, rest1⟩
  refine WP.mono (smallConst_ok u (o := 7) 2 ready (by decide) (by decide) (by decide) (by decide)) ?_
  rintro t ⟨next, _, two, keeps2, frame2, rest2⟩
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have oldOne := keeps_array_num keeps2 fits op4 (by decide)
  have oldM1 := keeps_array_num keeps1 fits op0 (by decide)
  have oldM2 := keeps_array_num keeps2 fits op0 (by decide)
  exact ⟨next, oldOne.trans one, two, oldM2.trans oldM1, frame1.trans frame2, rest1.trans rest2⟩

end VG.Proof.Bignum.Arm
