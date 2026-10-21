module
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # Exact SIMD horizontal sum used for the rejection mask -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.Ntt16

def sum8 (x : BitVec 128) : BitVec 16 :=
  vhalf x 0 + vhalf x 1 + vhalf x 2 + vhalf x 3 +
  vhalf x 4 + vhalf x 5 + vhalf x 6 + vhalf x 7

theorem laneSum_h8 (x : BitVec 128) :
    VArr.h8.laneSum x = (vhalf x 0).toNat + (vhalf x 1).toNat + (vhalf x 2).toNat + (vhalf x 3).toNat +
      (vhalf x 4).toNat + (vhalf x 5).toNat + (vhalf x 6).toNat + (vhalf x 7).toNat := by
  simp [VArr.laneSum, VArr.lanes, vhalf, BitVec.toNat_setWidth]
  omega

/-- Lane 0 of `addv h, v.8h` is the sum of the eight halfwords. -/
theorem addv_half (x : BitVec 128) :
    vhalf (BitVec.ofNat 128 (VArr.h8.laneSum x % 2 ^ 16)) 0 = sum8 x := by
  apply BitVec.eq_of_toNat_eq
  rw [laneSum_h8]
  simp only [vhalf, sum8, BitVec.toNat_add, BitVec.toNat_extractLsb', BitVec.toNat_ofNat]
  omega

/-- The horizontal sum before UMOV: `addv h1, v1.8h`. -/
def sumCode : List Instr := [.vop (.addv .h8 .v1 .v1)]

theorem sumCode_ok (s : State) :
    WP isa (.block sumCode) s fun t => VChg [.v1] s t ∧ vhalf (t.v .v1) 0 = sum8 (s.v .v1) := by
  refine wp_vop (d := .v1) rfl fun t ht => wp_nil ?_
  refine ⟨ht.chg, ?_⟩
  rw [ht.v]
  exact addv_half _

end VG.Proof.MlKem.AArch64.Rej8
