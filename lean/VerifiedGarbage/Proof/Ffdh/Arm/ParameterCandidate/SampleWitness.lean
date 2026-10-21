module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundData
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMask
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMaskHead
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperand
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Import a witness at its phase's byte width, then cut it to the exact
bit width, while preserving the shared-round constants. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Spec.Rsa.Mont (numAt Keeps)

theorem sampleWitness_ok {s : State} {base src : BitVec 32} {capacity w n bits : Nat}
    (ready : ArithmeticReady base capacity w s) (data : RoundData base capacity w n s.mem)
    (stack : Workspace s s.sp 72)
    (stackSep : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (positive : 0 < bits) (bound : bits ≤ 8192) (fitsBits : bits ≤ 64 * w)
    (saved : s.mem.readW (State.addr (s.sp + 44#32)) 32 = BitVec.ofNat 32 bits)
    (sourceFit : src.toNat + (bits + 7) / 8 ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) ((bits + 7) / 8))
    (sep : (⟨State.addr src, (bits + 7) / 8⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (source : s.gpr .r4 = src) (count : s.gpr .r6 = BitVec.ofNat 32 ((bits + 7) / 8)) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.sampleWitness s fun t =>
      ArithmeticReady base capacity w t ∧ RoundData base capacity w n t.mem ∧
      numAt t.mem (State.addr base) w 1 =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) ((bits + 7) / 8)) % 2 ^ bits ∧
      Keeps (State.addr base) capacity w 1 s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * capacity⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.sampleWitness, WP.seq_iff]
  refine WP.mono (importOperand_ok s ready (o := 1) (by decide) (by decide)
    (by omega) (by omega) sourceFit read sep source count) ?_
  rintro u ⟨readyU, valueU, keepsU, frameU, restU⟩
  have stackU : Workspace u u.sp 72 := by rw [restU.sp]; exact stack.congr restU.wr
  have savedU : u.mem.readW (State.addr (u.sp + 44#32)) 32 = BitVec.ofNat 32 bits := by
    have separate : (⟨State.addr (s.sp + 44#32), 4⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩ := by
      rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
      exact stackSep.sub_left (Offset.sub_base _ (by decide : 44 + 4 ≤ 72))
    rw [restU.sp, frameU.readW (r := ⟨State.addr (s.sp + 44#32), 4⟩) (Region.contains_self _ _)
      (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact separate) (by decide)]
    exact saved
  have rawBound := VG.Proof.Bignum.os2ip_lt
    (Spec.Rsa.bytesAt s.mem (State.addr src) ((bits + 7) / 8))
  rw [VG.Proof.Bignum.bytesAt_length, show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] at rawBound
  have small : numAt u.mem (State.addr base) w 1 < 2 ^ (32 * ((bits - 1) / 32 + 1)) := by
    rw [valueU]
    exact Nat.lt_of_lt_of_le rawBound (Nat.pow_le_pow_right (by decide : 0 < 2)
      (witness_geometry positive fitsBits).2.2.2)
  refine WP.mono (witnessMask_ok readyU stackU positive bound fitsBits savedU small) ?_
  rintro t ⟨readyT, valueT, keepsT, frameT, restT⟩
  rw [valueU] at valueT
  have keeps : Keeps (State.addr base) capacity w 1 s.mem t.mem := fun i hi outside =>
    (keepsT i hi outside).trans (keepsU i hi outside)
  exact ⟨readyT, data.after_operand (by decide) (by decide) (by decide) keeps,
    valueT, keeps, frameU.trans frameT, restU.trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
