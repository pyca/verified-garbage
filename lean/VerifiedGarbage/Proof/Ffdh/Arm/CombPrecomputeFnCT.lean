module

public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInput
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCTState
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeEntry

/-! The public precompute frame and fixed argument stores preserve its timing policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem combPrecomputeFn_ct (backend : MontBackend) {p : Inputs}
    (mainTiming : ∀ {sp : BitVec 32},
      RelCT isa (fun s t=>CombBuilder.EnterInput p sp s ∧ CombBuilder.EnterInput p sp t ∧
        VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
        (VG.Impl.Ffdh.Arm.CombPrecompute.main
          (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code) (fun _ _=>True)) :
    RelCT isa (fun s t => CombPrecomputeFnInput p s ∧ CombPrecomputeFnInput p t ∧
      VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.CombPrecompute.code
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code) (fun _ _=>True) := by
  let P := fun a : State => ∃s,CombPrecomputeFnInput p s ∧ a=entered s
  let Q := fun a : State => ∃sp,CombBuilder.EnterInput p sp a
  have wp (a : State) (h : P a) : WP isa (.block VG.Impl.Ffdh.Arm.CombPrecompute.entry) a Q := by
    obtain ⟨s,input,rfl⟩ := h
    refine WP.mono_syms (withAllRest (combEntry_ok (entered s) input.args input.incomingCount input.incomingBase
      input.outputReg input.domainReg input.domainLengthReg)) ?_
    rintro u ⟨⟨ctx,frame⟩,rest⟩ syms
    have context : Context p CombBuilder.slots u :=
      ⟨⟨ctx.workspace,ctx.locals,ctx.domain,ctx.domainStack,fun d hd=>
        ctx.saved d (by simp only [CombBuilder.slots,List.mem_cons,List.not_mem_nil,or_false] at hd ⊢; omega)⟩,ctx.ptr⟩
    have environment := VettedGroups.environment.stable input.environment
      (frame.mono (by simp [keyCallWrites,keyWrites])) rest syms
    exact ⟨(entered s).sp,context,environment,input.calls.after rest,input.output.after rest,
      input.workspaceSeparate,input.domainSeparate,input.localSeparate,input.callSeparate,rest.sp,input.valid⟩
  have entry : RelCT isa (fun s t=>P s ∧ P t ∧ VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
      (.block VG.Impl.Ffdh.Arm.CombPrecompute.entry)
      (fun s t=>VettedGroups.environment.publicRel s t ∧ s.sp=t.sp) := by
    intro s t tr1 tr2 u v h e1 e2
    have ct := relCT_keep_sp (combEntry_ct.mono (P' :=fun (s t : State)=>P s ∧ P t ∧ VettedGroups.environment.publicRel s t ∧ s.sp=t.sp) (fun _ _ k=>k.2.2.2) (fun _ _ _=>trivial))
      (fun _ _ k=>k.2.2.2)
    refine ⟨(ct s t tr1 tr2 u v h e1 e2).1,?_,(ct s t tr1 tr2 u v h e1 e2).2⟩
    change u.syms VG.Impl.Ffdh.Arm.VettedGroups.tableSym=v.syms VG.Impl.Ffdh.Arm.VettedGroups.tableSym
    rw [VG.Arm.Exec.syms e1,VG.Arm.Exec.syms e2]
    exact h.2.2.1
  have body : RelCT isa (fun s t=>P s ∧ P t ∧ VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
      (.seq (.block VG.Impl.Ffdh.Arm.CombPrecompute.entry)
        (VG.Impl.Ffdh.Arm.CombPrecompute.main
          (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code)) (fun _ _=>True) := by
    refine (entry.wp (fun s t h=>⟨wp s h.1,wp t h.2.1⟩)).seq ?_
    intro s t tr1 tr2 u v ⟨⟨pubEq,sp⟩,⟨sp1,h1⟩,⟨sp2,h2⟩⟩ e1 e2
    have eq : sp1=sp2 := h1.fixed.symm.trans (sp.trans h2.fixed)
    subst sp2
    exact mainTiming s t tr1 tr2 u v ⟨h1,h2,pubEq,sp⟩ e1 e2
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.code
  apply framed_ct (fun _ _ h=>⟨by have := h.1.stackFits; omega,by have := h.2.1.stackFits; omega⟩)
    (fun _ _ h=>h.2.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s,t,related,rfl,rfl⟩ := h
  exact body _ _ _ _ _ _ ⟨⟨s,related.1,rfl⟩,⟨t,related.2.1,rfl⟩,related.2.2.1,
    by rw [entered_sp,entered_sp,related.2.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm
