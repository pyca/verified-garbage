module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPost
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Exit
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Result
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.LiveGuards
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! An incomplete candidate either requests more entropy or exhausts its native entropy budget. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm

theorem SearchLive.short {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) (positive : 0 < remaining)
    (candidate : candidateResult p used = none)
    (zero : Spec.Rsa.bytesAt s.mem (State.addr p.c.out) p.c.length = List.replicate p.c.length 0) :
    WP isa VG.Impl.Ffdh.Arm.ParameterSearch.short s fun t =>
      SearchDone p (p.tail used remaining) t ∧ Rest searchClobbers s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.short
  refine WP.seq (WP.mono h.entropy_guard fun u ⟨⟨live, flag, mem⟩, restU⟩ => ?_)
  refine WP.ite _ (by change some u.z = _; rw [flag]) ?_ ?_
  · intro short
    have short' := of_decide_eq_true short
    have zeroU : Spec.Rsa.bytesAt u.mem (State.addr p.c.out) p.c.length = List.replicate p.c.length 0 := by
      rw [mem]; exact zero
    refine WP.mono (live.request_done zeroU) ?_
    rintro t ⟨done, restT⟩
    rw [p.tail_short positive candidate, ite_eq_right (by omega)]
    exact ⟨done, (restU.mono (by simp [searchClobbers])).trans restT⟩
  · intro full
    have full' := of_decide_eq_false full
    refine WP.mono live.exhausted ?_
    rintro t ⟨done, restT⟩
    rw [p.tail_short positive candidate, ite_eq_left (by omega)]
    exact ⟨done, (restU.mono (by simp [searchClobbers])).trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
