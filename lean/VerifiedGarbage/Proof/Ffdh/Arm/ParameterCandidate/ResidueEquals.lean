module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialFlag
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Short public residue tests after the shared RSA radix-2^16 reducer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm

theorem residueEquals_ok (s : State) (first : Nat) (rest : List Nat)
    (bounds : ∀ v ∈ first :: rest, v < 256) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.residueEquals (first :: rest)) s fun t =>
      t.z = (first :: rest).any (fun v => s.gpr .r2 == BitVec.ofNat 32 v) ∧ t.mem = s.mem ∧ Rest [] s t := by
  induction rest generalizing first s with
  | nil =>
    simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.residueEquals]
    refine wp_cmp (op2_imm (encodable_byte (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := bounds first (by simp); omega)]
      exact bounds first (by simp)))) fun t changed flag => WP.block_nil ?_
    refine ⟨?_, changed.mem, changed.rest []⟩
    rw [flag, sub_beq_zero]
    simp only [List.any_cons, List.any_nil, Bool.or_false]
  | cons next rest ih =>
    simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.residueEquals]
    refine WP.seq (wp_cmp (op2_imm (encodable_byte (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := bounds first (by simp); omega)]
      exact bounds first (by simp)))) fun u changed flag => WP.block_nil ?_)
    have zero : u.z = (s.gpr .r2 == BitVec.ofNat 32 first) := by rw [flag, sub_beq_zero]
    by_cases same : (s.gpr .r2 == BitVec.ofNat 32 first) = true
    · refine WP.ite true (by change some u.z = some true; rw [zero, same]) ?_ (by intro h; cases h)
      intro _
      exact WP.block_nil ⟨by simp only [List.any_cons, same, Bool.true_or]; exact zero.trans same,
        changed.mem, changed.rest []⟩
    · have different : (s.gpr .r2 == BitVec.ofNat 32 first) = false := by
        cases h : (s.gpr .r2 == BitVec.ofNat 32 first) <;> simp_all
      refine WP.ite false (by change some u.z = some false; rw [zero, different]) (by intro h; cases h) ?_
      intro _
      refine WP.mono (ih u next (by intro v hv; exact bounds v (by simp only [List.mem_cons] at hv ⊢; exact .inr hv))) ?_
      rintro t ⟨last, memory, restT⟩
      refine ⟨?_, memory.trans changed.mem, (changed.rest []).trans restT⟩
      rw [List.any_cons, different, Bool.false_or]
      simpa only [changed.gpr] using last

end VG.Proof.Ffdh.Arm.ParameterCandidate
