module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.HalveOctets
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Native byte halving implements the shared safe-prime encoding recurrence. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem halfByte_ok (s : State)
    (read : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0)) 1)
    (write : InRegions s.wr (State.addr (s.gpr .r0)) 1) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.halfByte) s fun t =>
      (t.gpr .r0 = s.gpr .r0 + 1 ∧
        t.gpr .r1 = (s.mem (State.addr (s.gpr .r0))).setWidth 32 >>> 1 ||| s.gpr .r2 ∧
        t.gpr .r2 = ((s.mem (State.addr (s.gpr .r0))).setWidth 32 &&& 1) <<< 7 ∧
        t.gpr .lr = s.gpr .lr - 1 ∧ t.z = (s.gpr .lr - 1 == 0) ∧
        t.mem = s.mem.writeW (State.addr (s.gpr .r0))
          (((s.mem (State.addr (s.gpr .r0))).setWidth 32 >>> 1 ||| s.gpr .r2).setWidth 8)) ∧
        Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  refine withRest_all [.r0, .r1, .r2, .r3, .lr] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.halfByte
  ffrun [BitVec.add_zero, read, write]

theorem halfByte_value (b : Byte) {carry : Nat} (bound : carry ≤ 1) :
    ((b.setWidth 32 >>> 1) ||| BitVec.ofNat 32 (128 * carry)) =
      BitVec.ofNat 32 (b.toNat / 2 + 128 * carry) := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 128 * carry < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : b.toNat / 2 + 128 * carry < 2 ^ 32)]
  rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt (by omega : b.toNat / 2 < 2 ^ 7) carry]
  omega

theorem halfByte_encoding (b : Byte) {carry : Nat} (bound : carry ≤ 1) :
    (((b.setWidth 32 >>> 1) ||| BitVec.ofNat 32 (128 * carry)).setWidth 8) =
      VG.Proof.Ffdh.ParameterCandidate.halfByte carry b := by
  rw [halfByte_value b bound]
  simp only [VG.Proof.Ffdh.ParameterCandidate.halfByte, BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 32)]

theorem halfByte_carry (b : Byte) :
    ((b.setWidth 32 &&& 1) <<< 7) = BitVec.ofNat 32 (128 * (b.toNat % 2)) := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 32), Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  change ((b.toNat &&& (2 ^ 1 - 1)) * 2 ^ 7) % 2 ^ 32 = (128 * (b.toNat % 2)) % 2 ^ 32
  rw [Nat.and_two_pow_sub_one_eq_mod]
  congr 1
  omega

end VG.Proof.Ffdh.Arm.ParameterCandidate
