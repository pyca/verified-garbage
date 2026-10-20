module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Branch on an already computed FFDH status and return a native status. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

theorem ret_ok (s : State) (n : BitVec 32) (enc : encodable n = true) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.ret n) s fun t =>
      (t.gpr .r0 = n ∧ t.mem = s.mem) ∧ Rest [.r0] s t := by
  refine withRest [.r0] ?_ (by
    intro r hr i hi
    simp only [instrs, VG.Impl.Ffdh.Arm.Domain.ret, List.mem_singleton] at hi
    subst i
    simp only [List.mem_singleton] at hr
    simp [clobbers, dstOf, Ne.symm hr]) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.ret
  ffrun [enc]

theorem testFlag_ok (s : State) :
    WP isa VG.Impl.Ffdh.Arm.Domain.testFlag s fun t =>
      (t.z = (s.gpr .r11 == 0) ∧ t.mem = s.mem) ∧ Rest [] s t := by
  refine withRest [] ?_ (by
    intro r _ i hi
    simp only [instrs, VG.Impl.Ffdh.Arm.Domain.testFlag, List.mem_singleton] at hi
    subst i
    rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.testFlag
  ffrun []
  change (s.gpr .r11 - 0#32 == 0#32) = (s.gpr .r11 == 0#32)
  rw [BitVec.sub_zero]

theorem finishFlag_ok (s : State) :
    WP isa VG.Impl.Ffdh.Arm.Domain.finishFlag s fun t =>
      (t.gpr .r0 = s.gpr .r11 ∧ t.mem = s.mem) ∧ Rest [.r0] s t := by
  refine withRest [.r0] ?_ (by
    intro r hr i hi
    simp only [instrs, VG.Impl.Ffdh.Arm.Domain.finishFlag, List.mem_singleton] at hi
    subst i
    simp only [List.mem_singleton] at hr
    simp [clobbers, dstOf, Ne.symm hr]) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.finishFlag
  ffrun []

end VG.Proof.Ffdh.Arm
