module
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Rsa.MontContract

import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.TCB.Arm.Isa

/-! # Integer import preserves the RSA layout and the modulus parity -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt wOf Layout)

theorem numAt_low_odd (mem : Mem) (base : Addr) {w o : Nat} (hw : 0 < w)
    (odd : numAt mem base w o % 2 = 1) :
    (VG.Proof.Mont.word mem base (arrAt w o)).toNat % 2 = 1 := by
  have split : numAt mem base w o = (VG.Proof.Mont.word mem base (arrAt w o)).toNat +
      2 ^ 64 * VG.Proof.Mont.wordsVal mem base (arrAt w o + 8) (w - 1) := by
    unfold numAt
    rw [read_eq_wordsVal]
    exact congrArg (fun n => VG.Proof.Mont.wordsVal mem base (arrAt w o) n)
      (show w = (w - 1) + 1 by omega)
  rw [split] at odd
  omega

theorem array_outside_layout {m m' : Mem} {base : Addr} {len w o : Nat}
    (outside : VG.Proof.Mont.Outside base (arrAt w o) (8 * w) m m')
    (layout : Layout m base len) : wOf m' base = wOf m base ∧ Layout m' base len := by
  have start : 256 ≤ arrAt w o := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega
  have width : wOf m' base = wOf m base :=
    congrArg BitVec.toNat (outside.word (d := 48) (by omega) (by decide))
  refine ⟨width, ?_⟩
  unfold Layout
  rw [width]
  refine ⟨layout.1, layout.2.1, layout.2.2.1, ?_⟩
  intro j hj
  change VG.Proof.Mont.word m' base (8 * (8 + j)) = _
  rw [outside.word (by omega) (by omega)]
  exact layout.2.2.2 j hj

end VG.Proof.Bignum.Arm
