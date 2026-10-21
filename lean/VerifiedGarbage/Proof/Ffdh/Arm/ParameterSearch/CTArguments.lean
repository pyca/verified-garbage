module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTCallState
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.ArgumentHead
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Candidate argument construction uses only the public controller pointer and stack pointer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller Two two_taint)

private def ArgumentPins (a : SearchPoint × BitVec 32) (s : State) : Prop :=
  s.gpr .r4 = a.1.inputs.control ∧ s.gpr .r12 = a.2

private theorem head_ct : RelCT isa (Two AllocatedCT)
    (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r0 5, VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r1 1,
      .dp .add .r2 .r4 (.imm 112), VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r3 7, .addSp .r12 0]) (fun _ _ => True) := by
  change RelCT isa _ (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r0 5,
    VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r1 1, .dp .add .r2 .r4 (.imm 112),
    VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r3 7] ++ [.addSp .r12 0])) _
  refine RelCT.block_append (RelCT.seq
    (relCT_keep_sp (two_taint [.r4] allocated_pins (by taint_decide)) (fun _ _ ⟨_, _, _, sp⟩ => sp)) ?_)
  exact VG.Proof.Ffdh.Arm.stackAddr_ct.mono (fun _ _ h => h) (fun _ _ _ => trivial)

private theorem head_ready (a : SearchPoint × BitVec 32) (s : State)
    (h : AllocatedCT a.1 s ∧ s.sp = a.2) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r0 5, VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r1 1,
      .dp .add .r2 .r4 (.imm 112), VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r3 7, .addSp .r12 0]) s (ArgumentPins a) := by
  obtain ⟨⟨original, ⟨live, room⟩, rfl⟩, sp⟩ := h
  have control : Controller a.1.inputs.control (allocated 24 original) :=
    ⟨⟨a.1.inputs.controlFits, List.mem_cons_of_mem _ live.buffers.controller.space.2⟩, live.buffers.controller.ptr⟩
  have stack : Workspace (allocated 24 original) (allocated 24 original).sp 24 :=
    ⟨callArguments_fits live.buffers.below, List.mem_cons_self⟩
  have separate : (⟨State.addr a.1.inputs.control, 128⟩ : Region).Disjoint
      ⟨State.addr (allocated 24 original).sp, 24⟩ :=
    ((live.buffers.stackSeparate _ (by simp)).2.sub_left (callArguments_sub live.buffers.below)).symm
  refine WP.mono (argumentHead_ok (allocated 24 original) control stack separate live.saved) ?_
  rintro t ⟨⟨context, _⟩, rest⟩
  exact ⟨context.controller.ptr, context.pointer.trans (rest.sp.trans sp)⟩

theorem arguments_ct : RelCT isa (Two AllocatedCT) (.block VG.Impl.Ffdh.Arm.ParameterSearch.arguments) (fun _ _ => True) := by
  have checked : RelCT isa (Two (fun (a : SearchPoint × BitVec 32) s => AllocatedCT a.1 s ∧ s.sp = a.2))
      (.block VG.Impl.Ffdh.Arm.ParameterSearch.arguments) (fun _ _ => True) := by
    change RelCT isa _ (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r0 5,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r1 1, .dp .add .r2 .r4 (.imm 112),
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r3 7, .addSp .r12 0] ++ _)) _
    refine RelCT.block_append (RelCT.seq (VG.Proof.Ffdh.Arm.KeySearch.two_post
      (head_ct.mono (fun _ _ ⟨a, hs, ht, sp⟩ => ⟨a.1, hs.1, ht.1, sp⟩) (fun _ _ h => h)) head_ready) ?_)
    exact two_taint [.r4, .r12] (fun _ _ _ hs ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.trans ht.2.symm) (by taint_decide)
  exact checked.mono (fun s t ⟨q, hs, ht, sp⟩ => ⟨(q, s.sp), ⟨hs, rfl⟩, ⟨ht, sp.symm⟩, sp⟩) (fun _ _ h => h)

theorem arguments_ready (q : SearchPoint) (s : State) (h : AllocatedCT q s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.arguments) s (CallCT q) := by
  obtain ⟨original, ⟨live, room⟩, rfl⟩ := h
  have control : Controller q.inputs.control (allocated 24 original) :=
    ⟨⟨q.inputs.controlFits, List.mem_cons_of_mem _ live.buffers.controller.space.2⟩, live.buffers.controller.ptr⟩
  have stack : Workspace (allocated 24 original) (allocated 24 original).sp 24 :=
    ⟨callArguments_fits live.buffers.below, List.mem_cons_self⟩
  have separate : (⟨State.addr q.inputs.control, 128⟩ : Region).Disjoint
      ⟨State.addr (allocated 24 original).sp, 24⟩ :=
    ((live.buffers.stackSeparate _ (by simp)).2.sub_left (callArguments_sub live.buffers.below)).symm
  refine WP.mono (arguments_ok (allocated 24 original) control stack separate live.saved) ?_
  rintro t ⟨⟨args, mem⟩, rest⟩
  exact ⟨original, live, room, args, mem, rest⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
