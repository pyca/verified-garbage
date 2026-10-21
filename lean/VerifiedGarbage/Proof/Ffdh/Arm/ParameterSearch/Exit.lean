module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.LivePolicy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Done
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Outputs
import VerifiedGarbage.Proof.Framework.Block

/-! Exhaustion and entropy requests return the exact shared search results. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (lowWord)

def requestResult (p : SearchParams) (used remaining : Nat) : Spec.Ffdh.ParameterSearchResult :=
  .entropy remaining (Spec.Ffdh.parameterRequest p.c.bits (p.c.bytes.length - used)) used

theorem SearchLive.exhausted {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterSearch.exhausted s fun t =>
      SearchDone p (.exhausted used) t ∧ Rest searchClobbers s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.exhausted
  refine WP.seq (WP.mono (h.terminal (Or.inr rfl)) fun u ⟨live, status, request, _, restU⟩ => ?_)
  refine WP.mono live.zero_output ?_
  rintro t ⟨finished, bytes, frame, restT⟩
  have statusT : lowWord t.mem p.control 13 = 3#32 := by
    unfold lowWord
    rw [output_control_word frame (by decide : 8 * 13 + 32 / 8 ≤ 128)]
    exact status
  have requestT : t.mem.readW (off (State.addr p.control) 24) 64 = 0 :=
    (output_control_word frame (by decide : 24 + 64 / 8 ≤ 128)).trans request
  exact ⟨finished.done statusT requestT bytes,
    (restU.mono (by simp [searchClobbers])).trans (restT.mono (by simp [searchClobbers]))⟩

theorem SearchLive.request_done {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s)
    (zero : Spec.Rsa.bytesAt s.mem (State.addr p.c.out) p.c.length = List.replicate p.c.length 0) :
    WP isa VG.Impl.Ffdh.Arm.ParameterSearch.request s fun t =>
      SearchDone p (requestResult p used remaining) t ∧ Rest searchClobbers s t := by
  refine WP.mono h.request ?_
  rintro t ⟨live, status, request, frame, rest⟩
  exact ⟨live.done status request (control_output zero frame), rest.mono (by simp [searchClobbers])⟩

theorem SearchLive.short_request {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) :
    WP isa (.seq VG.Impl.Ffdh.Arm.ParameterSearch.zeroOut VG.Impl.Ffdh.Arm.ParameterSearch.request) s fun t =>
      SearchDone p (requestResult p used remaining) t ∧ Rest searchClobbers s t := by
  refine WP.seq (WP.mono h.zero_output fun u ⟨live, zero, _, restU⟩ => ?_)
  refine WP.mono (live.request_done zero) ?_
  rintro t ⟨done, restT⟩
  exact ⟨done, (restU.mono (by simp [searchClobbers])).trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
