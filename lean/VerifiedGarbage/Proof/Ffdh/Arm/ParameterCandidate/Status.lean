module

public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialFlag
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Native status values use Z only to request another witness iteration. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

theorem setStatus_ok (s : State) (status : Nat) (bound : status ≤ 4) :
    WP isa (.block [.mov .r3 (.imm (BitVec.ofNat 32 status)), .cmp .r3 (.imm 4)]) s fun t =>
      (t.gpr .r3 = BitVec.ofNat 32 status ∧ t.z = decide (status = 4) ∧ t.mem = s.mem) ∧ Rest [.r3] s t := by
  have enc : encodable (BitVec.ofNat 32 status) = true :=
    encodable_byte (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : status < 2 ^ 32)]; omega)
  have zero : (BitVec.ofNat 32 status - (4 : BitVec 32) == (0 : BitVec 32)) = decide (status = 4) :=
    (sub_beq_zero _ _).trans (ofNat_beq_eq (by omega) (by decide))
  refine withRest [.r3] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block [.mov .r3 (.imm (BitVec.ofNat 32 status)), .cmp .r3 (.imm 4)] : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  ffrun [enc, zero]

theorem cmpWord_ok (r : Reg) {s : State} {result : Bool}
    (value : (s.gpr r).toNat = if result then 1 else 0) :
    WP isa (.block [.cmp r (.imm 0)]) s fun t =>
      (t.z = !result ∧ t.mem = s.mem) ∧ Rest [] s t := by
  have expected : (s.gpr r - (0 : BitVec 32) == (0 : BitVec 32)) = !result := by
    cases result with
    | false =>
      have word : s.gpr r = (0 : BitVec 32) := BitVec.eq_of_toNat_eq value
      rw [word]
      rfl
    | true =>
      have word : s.gpr r = (1 : BitVec 32) := BitVec.eq_of_toNat_eq value
      rw [word]
      rfl
  refine wp_cmp (op2_imm (by decide)) fun t flags zero => WP.block_nil ?_
  exact ⟨⟨zero.trans expected, flags.mem⟩, flags.rest []⟩

theorem cmpResult_ok {s : State} {result : Bool}
    (value : (s.gpr .r0).toNat = if result then 1 else 0) :
    WP isa (.block [.cmp .r0 (.imm 0)]) s fun t =>
      (t.z = !result ∧ t.mem = s.mem) ∧ Rest [] s t := cmpWord_ok .r0 value

theorem cmpStatus_ok {s : State} (value compare : Nat) (valueBound : value ≤ 4) (compareBound : compare ≤ 4)
    (word : s.gpr .r3 = BitVec.ofNat 32 value) :
    WP isa (.block [.cmp .r3 (.imm (BitVec.ofNat 32 compare))]) s fun t =>
      (t.z = decide (value = compare) ∧ t.mem = s.mem) ∧ Rest [] s t := by
  have enc : encodable (BitVec.ofNat 32 compare) = true := encodable_byte (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : compare < 2 ^ 32)]
    omega)
  have expected : (s.gpr .r3 - BitVec.ofNat 32 compare == (0 : BitVec 32)) = decide (value = compare) := by
    rw [word, sub_beq_zero]
    exact ofNat_beq_eq (by omega) (by omega)
  refine wp_cmp (op2_imm enc) fun t flags zero => WP.block_nil ?_
  exact ⟨⟨zero.trans expected, flags.mem⟩, flags.rest []⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
