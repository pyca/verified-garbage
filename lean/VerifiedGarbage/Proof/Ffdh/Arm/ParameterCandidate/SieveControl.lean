module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveContext
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SaveWord
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The sieve's local flag and bounded loop controls. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem sieveInitTail_ok (s : State) (stack : Workspace s s.sp 72) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInitTail) s fun t =>
      (t.gpr .r10 = s.gpr .r11 ∧ t.gpr .r11 = 53#32 ∧
        t.mem = s.mem.writeW (State.addr (s.sp + 64#32)) (0#32)) ∧ Rest [.r1, .r10, .r11, .r12] s t := by
  have write : InRegions s.wr (State.addr (s.sp + 64#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.write (by decide)
  refine withRest [.r1, .r10, .r11, .r12] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInitTail : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInitTail VG.Impl.Ffdh.Arm.ParameterCandidate.save
  ffrun [List.cons_append, List.nil_append, BitVec.add_zero, write]
  rfl

theorem sieveCount_ok {s : State} {count : Nat} (positive : 0 < count) (bound : count ≤ 53)
    (saved : s.gpr .r11 = BitVec.ofNat 32 count) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveCount) s fun t =>
      (t.gpr .r11 = BitVec.ofNat 32 (count - 1) ∧ t.z = decide (count = 1) ∧ t.mem = s.mem) ∧ Rest [.r11] s t := by
  have subtract : BitVec.ofNat 32 count - (1 : BitVec 32) = BitVec.ofNat 32 (count - 1) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive
  have zero : (BitVec.ofNat 32 (count - 1) == (0 : BitVec 32)) = decide (count = 1) := by
    rw [ofNat_beq_zero (by omega : count - 1 < 2 ^ 32)]
    exact decide_eq_decide.mpr (by omega)
  refine withRest [.r11] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveCount : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.sieveCount
  ffrun [saved, subtract, zero]

theorem sieveFlag_ok {s : State} {bad : Bool} (stack : Workspace s s.sp 72)
    (saved : s.mem.readW (State.addr (s.sp + 64#32)) 32 = if bad then 1 else 0) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFlag s fun t =>
      t.mem.readW (State.addr (t.sp + 64#32)) 32 = (if bad || s.z then 1 else 0) ∧
      Frame [sieveLocal s.sp] s.mem t.mem ∧ Rest [.r1, .r12] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFlag
  cases flag : s.z with
  | false =>
    refine WP.ite false (by change some s.z = some false; rw [flag]) (by intro h; cases h) ?_
    intro _
    exact WP.block_nil ⟨by simpa only [flag, Bool.or_false] using saved, Frame.refl _ _, Rest.refl _ _⟩
  | true =>
    refine WP.ite true (by change some s.z = some true; rw [flag]) ?_ (by intro h; cases h)
    intro _
    refine WP.mono (saveWord_ok stack (d := 64) (by decide) 1 (by decide)) ?_
    rintro t ⟨memory, rest⟩
    refine ⟨?_, ?_, rest⟩
    · rw [rest.sp, memory, Mem.readW_writeW_self32, Bool.or_true]
      rfl
    · rw [memory]
      exact sieveLocal_frame s 1

theorem sieveFinish_ok {s : State} {bad : Bool} (stack : Workspace s s.sp 72)
    (saved : s.mem.readW (State.addr (s.sp + 64#32)) 32 = if bad then 1 else 0) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFinish) s fun t =>
      (t.z = !bad ∧ t.mem = s.mem) ∧ Rest [.r1] s t := by
  have read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 64#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.read (by decide)
  refine withRest [.r1] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFinish : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFinish
  cases bad <;> ffrun [BitVec.add_zero, read, saved] <;> rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
