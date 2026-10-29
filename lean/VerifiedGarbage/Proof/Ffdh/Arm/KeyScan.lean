module

public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScanStep
public import VerifiedGarbage.Proof.Ffdh.Lead
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
public import VerifiedGarbage.TCB.Arm.Isa

/-! The native public-bound scan terminates at the first nonzero byte or the final byte. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

theorem keyScan_ok (s : State) {base src : BitVec 32} {len : Nat} {bs : List Byte}
    (source : Octets base src len bs s) (positive : 0 < bs.length) (fits : bs.length < 2 ^ 32)
    (ptr : s.gpr .r4 = src) (count : s.gpr .r6 = BitVec.ofNat 32 bs.length) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.scan s fun t =>
      t.gpr .r4 = src + BitVec.ofNat 32 (VG.Proof.Ffdh.lead bs) ∧
      t.gpr .r6 = BitVec.ofNat 32 (bs.length - VG.Proof.Ffdh.lead bs) ∧
      t.gpr .r3 = (bs.getD (VG.Proof.Ffdh.lead bs) 0).setWidth 32 ∧
      t.mem = s.mem ∧ Rest [.r3, .r4, .r6, .r11] s t := by
  induction bs generalizing src s with
  | nil => simp at positive
  | cons b tail ih =>
    obtain ⟨trace, u, run, ⟨byte, memU, result⟩, restU⟩ := scanStep_ok s source positive fits ptr count
    change u.gpr .r3 = b.setWidth 32 at byte
    change (if b = 0 ∧ 1 < (b :: tail).length then
      u.gpr .r4 = src + 1 ∧ u.gpr .r6 = BitVec.ofNat 32 ((b :: tail).length - 1) ∧ u.z = false
      else u.gpr .r4 = src ∧ u.gpr .r6 = BitVec.ofNat 32 (b :: tail).length ∧ u.z = true) at result
    by_cases go : b = 0 ∧ 1 < (b :: tail).length
    · rw [ite_eq_left go] at result
      obtain ⟨ptrU, countU, zeroU⟩ := result
      have tailPositive : 0 < tail.length := by have := go.2; simp only [List.length_cons] at this; omega
      have leadAdd : VG.Proof.Ffdh.lead (b :: tail) = VG.Proof.Ffdh.lead tail + 1 := by
        cases tail with
        | nil => simp at tailPositive
        | cons c rest => simp only [VG.Proof.Ffdh.lead, go.1, ite_true]
      have frame : Frame [] s.mem u.mem := by rw [memU]; exact Frame.refl _ _
      have sourceU := source.after_frame frame restU (by simp)
      have sourceTail : Octets base (src + 1) len tail u := by
        rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl]
        simpa only [List.drop_succ_cons, List.drop_zero, List.take_length] using
          sourceU.slice (d := 1) (k := tail.length) tailPositive (by simp only [List.length_cons]; omega)
      have countTail : u.gpr .r6 = BitVec.ofNat 32 tail.length := by
        simpa only [List.length_cons, Nat.add_sub_cancel] using countU
      obtain ⟨traceT, t, runT, ptrT, countT, byteT, memT, restT⟩ :=
        ih u sourceTail tailPositive (by simp only [List.length_cons] at fits; omega) ptrU countTail
      refine ⟨_, t, Exec.loopNext run (by simp only [eval, zeroU, Bool.not_false]) runT, ?_, ?_, ?_, memT.trans memU, restU.trans restT⟩
      · rw [ptrT, leadAdd, BitVec.add_assoc]
        change src + (BitVec.ofNat 32 1 + BitVec.ofNat 32 (VG.Proof.Ffdh.lead tail)) = _
        rw [← BitVec.ofNat_add, Nat.add_comm 1]
      · rw [countT, leadAdd]
        apply congrArg (BitVec.ofNat 32)
        simp only [List.length_cons]
        omega
      · rw [byteT, leadAdd]
        rfl
    · rw [ite_eq_right go] at result
      obtain ⟨ptrU, countU, zeroU⟩ := result
      have leadZero : VG.Proof.Ffdh.lead (b :: tail) = 0 := by
        cases tail with
        | nil => rfl
        | cons c rest =>
          have nonzero : b ≠ 0 := by intro zero; exact go ⟨zero, by simp⟩
          simp only [VG.Proof.Ffdh.lead, ite_eq_right nonzero]
      refine ⟨_, u, Exec.loopExit run (by simp only [eval, zeroU, Bool.not_true]), ?_, ?_, ?_, memU, restU⟩
      · rw [leadZero, BitVec.add_zero]; exact ptrU
      · rw [leadZero, Nat.sub_zero]; exact countU
      · rw [leadZero]; exact byte

end VG.Proof.Ffdh.Arm
