module

import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncMath
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec16
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Lanes
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Bytes
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.AArch64.Isa

/-! # ML-KEM encoding eight coefficients at a time -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Codec16 (encMath maskVec)
open VG.Proof.Rc4.AArch64

theorem low_byte (v : BitVec 128) {j : Nat} (hj : j<8) :
    (v.extractLsb' 0 64).extractLsb' (8*j) 8 = vbyte v j := by
  rw [BitVec.extractLsb'_extractLsb'_of_le (by omega_using [hj])]
  rfl

theorem high_byte (v : BitVec 128) {j : Nat} (hj : j<4) :
    ((v.extractLsb' 64 64).setWidth 32).extractLsb' (8*j) 8 = vbyte v (8+j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vbyte,BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,hi,decide_true,
    Bool.true_and,show 8*j+i<32 by omega_using [hj, hi],show 8*j+i<64 by omega_using [hj, hi]]
  exact congrArg _ (by omega_using [])


theorem encMask_value : encMask = 0xffffffff0e0d0c0a0908060504020100#128 := by
  apply vbyte_ext
  exact (by decide +kernel : ∀ e<16, vbyte encMask e = vbyte 0xffffffff0e0d0c0a0908060504020100#128 e)

end VG.Proof.MlKem.AArch64.Codec16
