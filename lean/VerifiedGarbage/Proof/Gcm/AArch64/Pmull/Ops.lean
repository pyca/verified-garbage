module

import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Impl.Gcm.AArch64.Pmull
public import VerifiedGarbage.Proof.Gcm.Clmul.Ops -- shake: keep (exports the existing PMULL value interface)
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# GHASH with PMULL: the values

What the instructions of `Impl.Gcm.AArch64.Pmull` compute, as bits: the
doublewords of a vector, `ext #8`, the products `acc` accumulates and the
block `reduce` computes from them, and `rev64 .16b`. Their classes in the ring
of `Proof/Gcm/Poly.lean` are in `Arith.lean`; this module needs no algebra.
-/

@[expose] public section

local notation "vdword" => VG.Proof.Gcm.Clmul.vdword

namespace VG.Proof.Gcm.AArch64.Pmull

open VG.AArch64
open VG.Impl.Gcm.AArch64.Pmull (poly xInv2Hi)

export VG.Proof.Gcm.Clmul (vdwords vdword_append_0 vdword_append_1 vdword_xor ext8 ext8_eq vdword_ext8_0 vdword_ext8_1 ext8_ext8 Prod reduce xInv2 getLsbD_append_block getLsbD_ofVBytes)

namespace Prod
export VG.Proof.Gcm.Clmul.Prod (acc zero)
end Prod

/-- `rev64 .16b` reverses the bytes of each doubleword. -/
theorem vdword_rev64b (v : BitVec 128) {e : Nat} (he : e < 2) :
    vdword (VRevOp.eval .rev64b v) e = rev64 (vdword v e) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hr : rev64 (vdword v e) = byteRev64 (vdword v e) := rfl
  rw [hr, getLsbD_byteRev64 _ _ hi]
  simp only [VG.Proof.Gcm.Clmul.vdword, VRevOp.eval, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    show 8 * (7 - i / 8) + i % 8 < 64 by omega]
  rw [show 64 * e + i = 8 * (8 * e + i / 8) + i % 8 by omega,
    getLsbD_ofVBytes _ (by omega) (Nat.mod_lt _ (by decide)), vbyte, BitVec.getLsbD_extractLsb',
    decide_eq_true (Nat.mod_lt _ (by decide)), Bool.true_and]
  exact congrArg _ (by omega)

theorem rev64b_rev64b (v : BitVec 128) : VRevOp.eval .rev64b (VRevOp.eval .rev64b v) = v := by
  have h : ∀ a : BitVec 64, rev64 (rev64 a) = a := byteRev64_byteRev64
  rw [vdwords (VRevOp.eval .rev64b _), vdword_rev64b _ (by decide), vdword_rev64b _ (by decide),
    vdword_rev64b _ (by decide), vdword_rev64b _ (by decide), h, h, ← vdwords]

end VG.Proof.Gcm.AArch64.Pmull
