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
  have h : ∀ i, (BitVec.setWidth 128 (vhalf x i)).toNat = (vhalf x i).toNat := fun i => by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (vhalf x i).isLt (by decide))]
  rw [VArr.laneSum, VArr.lanes, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h]
  omega

theorem sum8_toNat (x : BitVec 128) : (sum8 x).toNat = ((vhalf x 0).toNat + (vhalf x 1).toNat + (vhalf x 2).toNat +
    (vhalf x 3).toNat + (vhalf x 4).toNat + (vhalf x 5).toNat + (vhalf x 6).toNat + (vhalf x 7).toNat) % 2 ^ 16 := by
  simp only [sum8, BitVec.toNat_add, Nat.mod_add_mod]

theorem addv_half (x : BitVec 128) :
    vhalf (BitVec.ofNat 128 (VArr.h8.laneSum x % 2 ^ 16)) 0 = sum8 x := by
  apply BitVec.eq_of_toNat_eq
  rw [sum8_toNat, ← laneSum_h8, vhalf, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mul_zero, Nat.shiftRight_zero,
    Nat.mod_eq_of_lt (show VArr.h8.laneSum x % 2 ^ 16 < 2 ^ 128 from Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)),
    Nat.mod_mod]

/-- The horizontal sum before UMOV: `addv h1, v1.8h`. -/
def sumCode : List Instr := [.vop (.addv .h8 .v1 .v1)]

theorem sumCode_ok (s : State) :
    WP isa (.block sumCode) s fun t => VChg [.v1] s t ∧ vhalf (t.v .v1) 0 = sum8 (s.v .v1) := by
  refine wp_vop (d := .v1) rfl fun t ht => wp_nil ?_
  refine ⟨ht.chg, ?_⟩
  rw [ht.v]
  exact addv_half _

end VG.Proof.MlKem.AArch64.Rej8
