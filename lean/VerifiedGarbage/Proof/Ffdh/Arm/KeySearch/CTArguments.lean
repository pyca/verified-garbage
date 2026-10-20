module

public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Live
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTAttemptState
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Allocated
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Allocated
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ArgumentBlocks
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ArgumentBlocks
meta import VerifiedGarbage.Proof.Framework.Arm.Call

/-! Native argument setup uses only the public controller and stack
addresses, even when loading secret scalar/output registers afterward. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Bignum.Arm

def ArgumentPins (q : KeyPoint sampling) (s : State) : Prop :=
  s.gpr .r4 = q.inputs.control ∧ s.gpr .r12 = callSp q.inputs

private theorem head_ready (q : KeyPoint sampling) (u : State) (h : KeyAllocated q u) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 5, VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 2,
      VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 6, VG.Impl.Ffdh.Arm.KeySearch.ldf .r3 2, .addSp .r12 0]) u (ArgumentPins q) := by
  obtain ⟨s, ⟨⟨_, live, _⟩, _⟩, rfl⟩ := h
  refine WP.mono (argumentHead_ok (allocated (GenerationPolicy.argumentBytes sampling) s) (x := q.inputs.xp) (y := q.inputs.yp) (n := q.inputs.len) live.allocated_data.1
    (live.header (by simp [KeyPublic.headers])) (live.header (by simp [KeyPublic.headers]))
    (live.header (by simp [KeyPublic.headers]))) ?_
  rintro t ⟨⟨_, _, _, _, pointer, _⟩, rest⟩
  exact ⟨(rest.gpr .r4 (by simp)).trans live.pointer, pointer.trans live.call_sp⟩

private theorem head_ct :
    RelCT isa (Two (KeyAllocated (sampling := sampling))) (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 5,
      VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 2, VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 6,
      VG.Impl.Ffdh.Arm.KeySearch.ldf .r3 2, .addSp .r12 0]) (fun _ _ => True) := by
  change RelCT isa _ (.block ([VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 5,
    VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 2, VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 6,
    VG.Impl.Ffdh.Arm.KeySearch.ldf .r3 2] ++ [.addSp .r12 0])) _
  refine RelCT.block_append (RelCT.seq
    (relCT_keep_sp (two_taint [.r4] key_allocated_pins (by taint_decide)) (fun _ _ ⟨_, _, _, sp⟩ => sp)) ?_)
  exact VG.Proof.Ffdh.Arm.stackAddr_ct.mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem arguments_ct : RelCT isa (Two (KeyAllocated (sampling := sampling)))
    (.block (VG.Impl.Ffdh.Arm.KeySearch.argumentsFor sampling.cachedContext)) (fun _ _ => True) := by
  cases sampling <;>
    change RelCT isa _ (.block ([VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 5,
      VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 2, VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 6,
      VG.Impl.Ffdh.Arm.KeySearch.ldf .r3 2, .addSp .r12 0] ++ _)) _
  all_goals refine RelCT.block_append (RelCT.seq (two_post head_ct head_ready) ?_)
  all_goals exact two_taint [.r4, .r12] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁.1.trans h₂.1.symm
    · exact h₁.2.trans h₂.2.symm) (by taint_decide)

end VG.Proof.Ffdh.Arm.KeySearch
