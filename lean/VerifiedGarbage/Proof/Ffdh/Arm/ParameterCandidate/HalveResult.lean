module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Halve
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResidueBytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Output framing and final parity of the native byte-halving loop. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Ffdh.ParameterCandidate (carryAt carryAt_le halfByte_val)

theorem HalfInv.frame {s0 s : State} {dst : BitVec 32} {bs : List Byte} {i : Nat}
    (inv : HalfInv s0 dst bs i s) (fit : dst.toNat + bs.length ≤ 2 ^ 32) :
    Frame [⟨State.addr dst, bs.length⟩] s0.mem s.mem := by
  intro a ha
  apply inv.outside a
  intro j hj equal
  apply ha ⟨State.addr dst, bs.length⟩ (by simp)
  rw [equal, VG.Arm.addr_add (by have := inv.index; omega)]
  exact Offset.contains_base _ (by have := inv.index; omega) (by have := inv.index; omega)

theorem HalfInv.parity {s0 s : State} {dst : BitVec 32} {bs : List Byte}
    (inv : HalfInv s0 dst bs bs.length s) (positive : 0 < bs.length)
    (fits : dst.toNat + bs.length ≤ 2 ^ 32) :
    (s.gpr .r1).toNat % 2 = (Spec.Rsa.os2ip bs / 2) % 2 := by
  have last := inv.last (bs.length - 1) (by omega)
  have byte := inv.shifted (bs.length - 1) (by omega)
  rw [VG.Arm.addr_add (by omega : dst.toNat + (bs.length - 1) < 2 ^ 32)] at byte
  have carry := carryAt_le (by decide : 0 ≤ 1) bs (bs.length - 1)
  have byteBound := (bs[bs.length - 1]?.getD 0).isLt
  have value : (s.gpr .r1).toNat =
      (bs[bs.length - 1]?.getD 0).toNat / 2 + 128 * carryAt 0 bs (bs.length - 1) := by
    rw [last, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega :
      (bs[bs.length - 1]?.getD 0).toNat / 2 + 128 * carryAt 0 bs (bs.length - 1) < 2 ^ 32)]
  have residue := candidate_mod8_last s.mem (State.addr dst) positive
  rw [inv.value fits, byte, halfByte_val carry] at residue
  omega

end VG.Proof.Ffdh.Arm.ParameterCandidate
