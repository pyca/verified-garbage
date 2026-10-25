module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Locate the occupied native witness word and its exact bit count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem witness_geometry {bits w : Nat} (positive : 0 < bits) (bound : bits ≤ 64 * w) :
    (bits - 1) / 32 < 2 * w ∧ (bits - 1) % 32 + 1 ≤ 32 ∧
      32 * ((bits - 1) / 32) + ((bits - 1) % 32 + 1) = bits ∧
      8 * ((bits + 7) / 8) ≤ 32 * ((bits - 1) / 32 + 1) := by omega

private theorem nativeIndex {bits : Nat} (bound : bits ≤ 8192) :
    BitVec.ofNat 32 (bits - 1) >>> 5 = BitVec.ofNat 32 ((bits - 1) / 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : bits - 1 < 2 ^ 32),
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : (bits - 1) / 32 < 2 ^ 32)]

private theorem nativeCount {bits : Nat} (bound : bits ≤ 8192) :
    (BitVec.ofNat 32 (bits - 1) &&& 31) + 1 = BitVec.ofNat 32 ((bits - 1) % 32 + 1) := by
  have mask : BitVec.ofNat 32 (bits - 1) &&& 31 = BitVec.ofNat 32 ((bits - 1) % 32) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : bits - 1 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : (bits - 1) % 32 < 2 ^ 32)]
    change (bits - 1) &&& (2 ^ 5 - 1) = _
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  rw [mask]
  change BitVec.ofNat 32 ((bits - 1) % 32) + BitVec.ofNat 32 1 = _
  exact BitVec.ofNat_add_ofNat _ _

theorem witnessMaskHead_ok {s : State} {bits : Nat} (stack : Workspace s s.sp 72)
    (positive : 0 < bits) (bound : bits ≤ 8192)
    (saved : s.mem.readW (State.addr (s.sp + 44#32)) 32 = BitVec.ofNat 32 bits) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskHead) s fun t =>
      (t.gpr .r5 = BitVec.ofNat 32 ((bits - 1) / 32) ∧
        t.gpr .r6 = BitVec.ofNat 32 ((bits - 1) % 32 + 1) ∧ t.mem = s.mem) ∧ Rest [.r5, .r6] s t := by
  have read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 44#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.read (by decide)
  have sub : BitVec.ofNat 32 bits - 1 = BitVec.ofNat 32 (bits - 1) := by
    change BitVec.ofNat 32 bits - BitVec.ofNat 32 1 = _
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive
  refine withRest_all [.r5, .r6] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskHead
  ffrun [BitVec.add_zero, read, saved, sub, nativeIndex bound, nativeCount bound]

end VG.Proof.Ffdh.Arm.ParameterCandidate
