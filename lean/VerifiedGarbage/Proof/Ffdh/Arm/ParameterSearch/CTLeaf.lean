module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTState
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.ZeroOutput
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Outputs
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Live
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.LivePolicy
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Native output clearing and terminal updates disclose only public controller addresses and lengths. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins two_piece two_taint two_post)

def ZeroCT (p : SearchParams) (s : State) : Prop :=
  AnyCT p s ∧ s.gpr .r0 = p.c.out ∧ s.gpr .lr = BitVec.ofNat 32 p.c.length

private theorem zero_header (p : SearchParams) (s : State) (h : AnyCT p s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r0 5,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .lr 1, .mov .r2 (.imm 0)]) s (ZeroCT p) := by
  obtain ⟨used, remaining, live⟩ := h
  have pointer := live.saved 5 (by simp [searchSlots])
  have length := live.saved 1 (by simp [searchSlots])
  simp only [searchValues] at pointer length
  refine WP.mono (zeroOutArgs_ok s live.buffers.controller (by decide : 5 < 16) pointer length) ?_
  rintro t ⟨⟨ptr, count, _, mem⟩, rest⟩
  exact ⟨⟨used, remaining, live.after_read (by decide) mem rest⟩, ptr, count⟩

theorem zero_ct : RelCT isa (Two AnyCT) VG.Impl.Ffdh.Arm.ParameterSearch.zeroOut (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.zeroOut
  refine RelCT.seq (two_piece [.r4] any_pins (by taint_decide) zero_header) ?_
  exact two_taint [.r0, .lr] (fun _ _ _ hs ht r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.2.2.trans ht.2.2.symm) (by taint_decide)

private theorem terminal_ready (p : SearchParams) (s : State) (h : AnyCT p s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterSearch.terminal 3)) s (AnyCT p) := by
  obtain ⟨used, remaining, live⟩ := h
  exact WP.mono (live.terminal (Or.inr rfl)) fun _ ⟨ready, _⟩ => ⟨used, 0, ready⟩

theorem exhausted_ct : RelCT isa (Two AnyCT) VG.Impl.Ffdh.Arm.ParameterSearch.exhausted (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.exhausted
  exact RelCT.seq (two_piece [.r4] any_pins (by taint_decide) terminal_ready) zero_ct

theorem accepted_ct : RelCT isa (Two AnyCT) (.block VG.Impl.Ffdh.Arm.ParameterSearch.accept) (fun _ _ => True) :=
  two_taint [.r4] any_pins (by taint_decide)

theorem rejected_ct : RelCT isa (Two AnyCT) (.block VG.Impl.Ffdh.Arm.ParameterSearch.reject) (fun _ _ => True) :=
  two_taint [.r4] any_pins (by taint_decide)

end VG.Proof.Ffdh.Arm.ParameterSearch
