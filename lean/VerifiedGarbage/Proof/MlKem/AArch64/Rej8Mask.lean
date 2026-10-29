module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Value
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec

import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
/-! # Connecting acceptance predicates to the packed table index and count -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Rej8Sum.lean`, which only this module imported.
section

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
end

end

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Impl.MlKem.AArch64.Rej8

def mask8 (a b c d e f g h : Bool) : Nat :=
  (if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0) +
  (if d then 8 else 0) + (if e then 16 else 0) + (if f then 32 else 0) +
  (if g then 64 else 0) + (if h then 128 else 0)

def weight8 (a b c d e f g h : Bool) : BitVec 16 :=
  (if a then BitVec.ofNat 16 257 else 0) + (if b then BitVec.ofNat 16 258 else 0) + (if c then BitVec.ofNat 16 260 else 0) +
  (if d then BitVec.ofNat 16 264 else 0) + (if e then BitVec.ofNat 16 272 else 0) + (if f then BitVec.ofNat 16 288 else 0) +
  (if g then BitVec.ofNat 16 320 else 0) + (if h then BitVec.ofNat 16 384 else 0)

theorem mask8_bound : ∀ a b c d e f g h, mask8 a b c d e f g h < 256 := by decide +kernel

theorem mask8_bits : ∀ a b c d e f g h, ∀ i < 8,
    ((mask8 a b c d e f g h / 2^i)%2 == 1) = [a,b,c,d,e,f,g,h].getD i false := by decide +kernel

theorem weight8_exact : ∀ a b c d e f g h,
    weight8 a b c d e f g h = BitVec.ofNat 16 (packedCount (mask8 a b c d e f g h)) := by decide +kernel

/-- Acceptance mask of eight decoded candidates. -/
def acceptanceMask (x : BitVec 128) : Nat :=
  mask8 (decide ((vhalf x 0).toNat < 3329)) (decide ((vhalf x 1).toNat < 3329))
    (decide ((vhalf x 2).toNat < 3329)) (decide ((vhalf x 3).toNat < 3329))
    (decide ((vhalf x 4).toNat < 3329)) (decide ((vhalf x 5).toNat < 3329))
    (decide ((vhalf x 6).toNat < 3329)) (decide ((vhalf x 7).toNat < 3329))

theorem acceptanceMask_bound (x : BitVec 128) : acceptanceMask x < 256 := mask8_bound ..

theorem acceptanceMask_bits (x : BitVec 128) {i : Nat} (hi : i < 8) :
    ((acceptanceMask x / 2^i)%2 == 1) = decide ((vhalf x i).toNat < 3329) := by
  rw [acceptanceMask,mask8_bits _ _ _ _ _ _ _ _ i hi]
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

/-- The horizontal sum really is the table index and accepted count for
these candidates, without modular overflow in the halfword lanes. -/
theorem accepted_sum {x y : BitVec 128}
    (hy : ∀ i < 8, vhalf y i = if (vhalf x i).toNat < 3329 then BitVec.ofNat 16 (256+2^i) else 0) :
    sum8 y = BitVec.ofNat 16 (packedCount (acceptanceMask x)) := by
  rw [sum8,hy 0 (by decide),hy 1 (by decide),hy 2 (by decide),hy 3 (by decide),
    hy 4 (by decide),hy 5 (by decide),hy 6 (by decide),hy 7 (by decide)]
  simpa only [weight8, decide_eq_true_eq, Nat.reducePow, Nat.reduceAdd, acceptanceMask] using
    weight8_exact (decide ((vhalf x 0).toNat < 3329)) (decide ((vhalf x 1).toNat < 3329))
      (decide ((vhalf x 2).toNat < 3329)) (decide ((vhalf x 3).toNat < 3329))
      (decide ((vhalf x 4).toNat < 3329)) (decide ((vhalf x 5).toNat < 3329))
      (decide ((vhalf x 6).toNat < 3329)) (decide ((vhalf x 7).toNat < 3329))

end VG.Proof.MlKem.AArch64.Rej8
