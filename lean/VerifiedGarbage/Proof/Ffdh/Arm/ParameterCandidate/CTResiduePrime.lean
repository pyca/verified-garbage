module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTTrialSmall
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! Public generator congruences reuse the same native RSA small-prime reducer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

def TrialBuffers (p : TrialData) (s : State) : Prop :=
  ReadContext p.dst p.n s ∧
  ∀ i < p.n, s.mem (State.addr (p.dst + BitVec.ofNat 32 p.n - BitVec.ofNat 32 (i + 1))) = p.values[i]?.getD 0

theorem residuePrime_ct (prime : Nat) (values : List Nat) (enc : encodable (BitVec.ofNat 32 prime) = true)
    (cert : CandidateCert [.r2] (VG.Impl.Ffdh.Arm.ParameterCandidate.residueEquals values)) :
    RelCT isa (Two fun p s => TrialBuffers p s ∧ p.prime = BitVec.ofNat 32 prime)
      (VG.Impl.Ffdh.Arm.ParameterCandidate.residuePrime prime values) (fun _ _ => True) := by
  have load : RelCT isa (Two fun p s => TrialBuffers p s ∧ p.prime = BitVec.ofNat 32 prime)
      (.block [.mov .r7 (.imm (BitVec.ofNat 32 prime))]) (Two TrialState) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine wp_mov (op2_imm enc) fun t moved => WP.block_nil ?_
      have rest := moved.rest (by simp : Reg.r7 ∈ [Reg.r7])
      exact ⟨h.1.1.after_memory moved.mem rest, moved.gpr.trans h.2.symm,
        by rw [moved.mem]; exact h.1.2⟩)
  obtain ⟨hint, checked⟩ := cert
  have test : RelCT isa (fun s t => s.gpr .r2 = t.gpr .r2)
      (VG.Impl.Ffdh.Arm.ParameterCandidate.residueEquals values) (fun _ _ => True) := by
    refine RelCT.taint (A := taint) (Taint.ofRegs [.r2]) ?_ checked
    intro s t h
    refine Taint.agree_ofRegs ?_
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h
  exact load.seq (trialSmall_ct.seq (test.seq (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
