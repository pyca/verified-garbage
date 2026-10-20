module
public import VerifiedGarbage.Impl.Bignum.Arm.ModulusCheck
public import VerifiedGarbage.Proof.X25519.Arm.Instr

import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckBounds
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckFinish
import VerifiedGarbage.Proof.Bignum.ModulusCheckMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckMath

/-! # Functional validity predicate computed by ARMv7 instructions -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem modulusCheckCalc_ok (s : State) (hf : (s.gpr .r1).toNat < 256)
    (hk : 64 ≤ (s.gpr .r6).toNat) (hk' : (s.gpr .r6).toNat ≤ 1024) :
    WP isa (.block modulusCheckCalc) s fun t =>
      t.z = !(decide ((s.gpr .r1).toNat < 1) || decide ((s.gpr .r2).toNat % 2 < 1) ||
        decide (((s.gpr .r6).toNat - 64) * 256 + (s.gpr .r1).toNat < 128)) ∧
      t.mem = s.mem ∧ Rest [.r2, .r7, .r9] s t := by
  rw [modulusCheckCalc, WP.block_append_iff]
  refine WP.mono (modulusCheckBounds_ok s) ?_
  rintro u ⟨low, top, mem, rest⟩
  refine WP.mono (modulusCheckFinish_ok u) ?_
  rintro t ⟨zero, memT, keep⟩
  rw [low, top, rest.gpr .r2 (by simp), modulusCheck_value _ _ _ hf hk hk'] at zero
  exact ⟨zero, memT.trans mem, (rest.mono (by simp)).trans (keep.mono (by simp))⟩

end VG.Proof.Bignum.Arm
