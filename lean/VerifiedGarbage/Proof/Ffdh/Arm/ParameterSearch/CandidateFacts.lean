module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPost
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Result
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallParams
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Packed
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The candidate's public result supplies the exact native consumption field and classification. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (lowWord)

theorem CandidatePost.consumed_low {p : SearchParams} {used : Nat} {s : State}
    (post : CandidatePost p used s) : lowWord s.mem p.control 14 = BitVec.ofNat 32 (candidateUsed p used) := by
  have result := post.consumed
  change [s.mem.readW (State.addr (p.control + 112#32) + 0#64) 64] =
    [BitVec.ofNat 64 (candidateUsed p used)] at result
  rw [BitVec.add_zero, List.singleton_inj, p.used_addr] at result
  exact packedLow s.mem p.control 14 (candidateUsed p used)
    (by have := candidateUsed_bound p used; have := p.c.tapeCount; omega) result

theorem CandidatePost.after_read {p : SearchParams} {used : Nat} {s t : State} {rs : List Reg}
    (post : CandidatePost p used s) (mem : t.mem = s.mem) (rest : Rest rs s t) (kept : .r0 ∉ rs) :
    CandidatePost p used t :=
  ⟨by rw [rest.gpr .r0 kept]; exact post.status, by rw [mem]; exact post.output,
    by rw [mem]; exact post.consumed⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
