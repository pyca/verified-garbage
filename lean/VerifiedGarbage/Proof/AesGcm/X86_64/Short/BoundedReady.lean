module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedDescriptor
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Short
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Impl.AesGcm.X86_64.BoundedGather

/-! Both public gather runs read only the public descriptor geometry before the shared seal. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather.Layout
open VG VG.X86_64 Gather Short
open VG.Impl.AesGcm.X86_64.DirectGather VG.Impl.AesGcm.X86_64.Short
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
variable {s t u : State} {M : CtxMode}

theorem args_rel (p : Layout M s) (q : Layout M t) (pb : Pub s t) (c : Cnt s=1 ∨ Cnt s=2) :
    RelCT isa (fun a b => Initial s a ∧ Initial t b) gatherArgs fun _ _ => True := by
  have c' : Cnt t=1 ∨ Cnt t=2 := pb.cnt ▸ c
  refine RelCT.seq (rel_next (rel_taint [.rsp] (fun _ _ h r hr => by
    rw [List.mem_singleton.mp hr,h.1.rsp,h.2.rsp]; exact pb.rsp.symm) ⟨_,by taint_decide⟩)
    (fun _ e => p.headReady e) (fun _ e => q.headReady e)) ?_
  refine RelCT.seq (rel_next (rel_taint [.rax,.rsp] (fun _ _ h r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · rw [h.1.2,h.2.2,pb.src]
    · rw [h.1.1.rsp,h.2.1.rsp]; exact pb.rsp.symm) ⟨_,by taint_decide⟩)
    (fun _ e => p.dataReady c e) (fun _ e => q.dataReady c' e)) ?_
  refine rel_ite_e (fun _ _ h => by rw [h.1.2.2.2,h.2.2.2.2,pb.cnt])
    (rel_taint [.rax] (fun _ _ h r hr => by
      rw [List.mem_singleton.mp hr,h.1.1.1.2,h.1.2.1.2,pb.src]) ⟨_,by taint_decide⟩)
    (rel_taint [] (by simp) ⟨_,by taint_decide⟩)

theorem publicSecond (pb : Pub s t) (c : Cnt s=1 ∨ Cnt s=2) : secondSrc t = secondSrc s := by
  unfold secondSrc; rw [pb.cnt]; split
  · exact pb.sb (by omega)
  · exact pb.sb (by omega)

abbrev Small (s : State) := IsShort (NL s) (AL s).toNat (L s)

theorem fullExt (p : Layout (CtxMode.flaggedT 48) s) :
    CtxExt CtxMode.prepared (K s) (W s+16#64) (W s) (SP s) (Dst s) (L s) s :=
  { p.preparedExt (by decide) with ok := p.ok.2.2 p.ok.1 }

theorem runDescriptor (p : Layout (CtxMode.flaggedT 48) s) (hf : ShortFacts)
    (c : Cnt s=1 ∨ Cnt s=2) (sh : Small s) (u : State) (hu : ArgsReady s u) : CallRun u (BodyDone (CtxMode.flaggedT 48) s) :=
  (run_cut hf (p.oneCtx (CtxMode.flaggedT 48).ge) p.fullExt powOk_powersP hu.1 (p.boundedGeo c) rfl rfl rfl sh hu.2).mono
    (fun _ post => p.boundedDone c post)

theorem gather_wp (p : Layout (CtxMode.flaggedT 48) s) (hf : ShortFacts) (c : Cnt s=1 ∨ Cnt s=2)
    (sh : Small s) (e : Initial s u) : WP isa boundedGather u (BodyDone (CtxMode.flaggedT 48) s) :=
  WP.seq (WP.mono (p.argsReady c e) fun v hv => (p.runDescriptor hf c sh v hv).wp)

theorem gather_rel (p : Layout (CtxMode.flaggedT 48) s) (q : Layout (CtxMode.flaggedT 48) t) (hf : ShortFacts)
    (pb : Pub s t) (c : Cnt s=1 ∨ Cnt s=2) (sh : Small s) :
    RelCT isa (fun a b => Initial s a ∧ Initial t b) boundedGather fun _ _ => True := by
  have c' : Cnt t=1 ∨ Cnt t=2 := pb.cnt ▸ c
  have sh' : Small t := by simpa only [Small,NL,AL,pb.eL,pb.rcx,pb.r9] using sh
  have ct := rel_next (p.args_rel q pb c) (fun _ e => p.argsReady c e) (fun _ e => q.argsReady c' e)
  refine RelCT.seq ct (CallRun.rel (fun a b h =>
    ⟨(p.runDescriptor hf c sh a h.1).mono (fun _ _ => trivial),
     (q.runDescriptor hf c' sh' b h.2).mono (fun _ _ => trivial)⟩)
    (fun _ _ h => h.1.1.rsp.trans (pb.rsp.symm.trans h.2.1.rsp.symm)) ?_)
  have nz : 0<Cnt s := by omega
  have cx := q.oneCtx (CtxMode.flaggedT 48).ge
  have ext := (powOk_powersP q.fullExt).choose_spec
  have geo := q.boundedGeo c'
  simp only [K,Nn,Ad,SP,NL,AL,pb.rdi,pb.rdx,pb.r8,pb.rsp,pb.rcx,pb.r9,pb.eL,pb.w,pb.dst] at cx
  simp only [K,SP,pb.rdi,pb.rsp,pb.w,pb.eL,pb.dst] at ext
  simp only [SP,pb.rsp,pb.w,pb.dst,pb.eL,pb.sb nz,pb.sl nz,publicSecond pb c] at geo
  have rel := bounded_rel powersP_ct (p.oneCtx (CtxMode.flaggedT 48).ge) cx
    (powOk_powersP p.fullExt).choose_spec ext (p.boundedGeo c) geo rfl rfl rfl rfl
    pb.rdx (congrArg BitVec.toNat pb.rcx) (congrArg BitVec.toNat pb.r9) (congrArg BitVec.toNat pb.rsi) sh
  refine rel.mono (fun _ _ h => ⟨h.1,?_⟩) (fun _ _ _ => trivial)
  simpa only [ArgsReady,Initial,K,SP,Ad,pb.rdi,pb.r8,pb.rsp,pb.w,pb.dst,pb.eL,pb.sb nz,pb.sl nz,publicSecond pb c] using h.2

end VG.Proof.AesGcm.X86_64.DirectGather.Layout
