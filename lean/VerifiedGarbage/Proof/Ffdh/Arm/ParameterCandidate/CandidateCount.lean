module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SaveWord
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Account for the candidate's fixed-width entropy prefix before any early rejection. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem candidateCount_ok {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) (enough : p.length ≤ p.bytes.length) :
    WP isa (.block ([.ldrSp .r1 12] ++ VG.Impl.Ffdh.Arm.ParameterCandidate.save .r1 40)) s fun t =>
      CandidateContext p p.length t ∧
      Frame [⟨State.addr (s.sp + 40#32), 4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.block_append_iff]
  refine wp_loadStack (a := State.addr (s.sp + 12#32)) (by decide) rfl (h.saved.read (by decide)) fun u loaded => WP.block_nil ?_
  have value : u.gpr .r1 = BitVec.ofNat 32 p.length := loaded.gpr.trans (h.saved.saved 12 (by decide))
  have restU : Rest [.r1] s u := loaded.rest (by simp)
  have ctx := h.after_memory loaded.mem restU
  refine WP.mono (saveR1_ok ctx.saved.space (d := 40) (by decide)) ?_
  rintro t ⟨memory, restT⟩
  rw [value, loaded.mem, restU.sp] at memory
  have rest : Rest [.r1, .r12] s t := (restU.mono (by simp)).trans (restT.mono (by simp))
  have changed : Frame [⟨State.addr (s.sp + 40#32), 4⟩] s.mem t.mem := by
    rw [memory]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  exact ⟨h.store_consumed enough memory rest, changed, rest.mono (by simp [roundClobbers])⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
