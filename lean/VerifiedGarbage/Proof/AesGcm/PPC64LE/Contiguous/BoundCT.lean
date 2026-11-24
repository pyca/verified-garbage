module

-- separate module: Keep the two-run timing certificates separate from the functional correctness and scrub proofs.

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Framed
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.PayloadCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Framed
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-! # Same-trace composition for the public contiguous POWER entry -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_seq)

abbrev prepRegs : List Reg := [.r18,.r21,.r22,.r24,.r25,.r29,.r30,.r31]
abbrev closeRegs : List Reg := [.r20,.r31]

theorem prepare_rel {s t : State} (sp : s.sp=t.sp) (pub : ∀ r∈prepRegs,s.gpr r=t.gpr r) : RelCT isa (Eq2 s t) nonceAad TT := by
  refine RelCT.taint (A := vectorTaint) (Taint.ofRegs prepRegs)
    (fun _ _ ⟨rfl,rfl⟩ => ⟨sp,fun r hr => pub r (Taint.mem_ofRegs.mp hr)⟩) (by taint_decide)

theorem close_rel {s t : State} (sp : s.sp=t.sp) (pub : ∀ r∈closeRegs,s.gpr r=t.gpr r) :
    RelCT isa (Eq2 s t) (.seq (.block tagOut) (.block restore)) TT := by
  refine RelCT.taint (A := vectorTaint) (Taint.ofRegs closeRegs)
    (fun _ _ ⟨rfl,rfl⟩ => ⟨sp,fun r hr => pub r (Taint.mem_ofRegs.mp hr)⟩) (by taint_decide)

structure CallPublic (s d : State) : Prop where
  sp : s.sp=d.sp
  key : s.gpr .r3=d.gpr .r3
  rounds : s.gpr .r4=d.gpr .r4
  nonce : s.gpr .r5=d.gpr .r5
  nonceLen : s.gpr .r6=d.gpr .r6
  aad : s.gpr .r7=d.gpr .r7
  aadLen : s.gpr .r8=d.gpr .r8
  src : s.gpr .r9=d.gpr .r9
  dst : s.gpr .r10=d.gpr .r10
  len : stackArg s 0=stackArg d 0
  tag : stackArg s 1=stackArg d 1

theorem public_args {s d : State} (h : contract.pub s d) : CallPublic s d := by
  sig_pub [contract,Spec.Gcm.sealContiguousContract,Spec.Gcm.sealContiguousSig,VG.PPC64LE.abi,VG.PPC64LE.argRegs,List.getD,List.range,List.range.loop] at h
  obtain ⟨sp,c,r,n,nl,a,al,src,dst,len,tag⟩ := h
  exact ⟨sp,c,r,n,nl,a,al,src,dst,len,tag⟩

private theorem work_eq {s d : State} (pub : CallPublic s d) : work s=work d :=
  congrArg (fun p => p-1280+128) pub.sp

theorem prep_agree {s d e f t v : State} (pub : CallPublic s d)
    (p : Args s e) (q : Args d f) (a : Started e (work s) t) (b : Started f (work d) v) :
    ∀ r∈prepRegs,t.gpr r=v.gpr r := by
  have reg (r : Reg) (ra : r≠.r0) (rb : r≠.r12) (eq : s.gpr r=d.gpr r) : e.gpr r=f.gpr r :=
    (p.regs r ra rb).trans (eq.trans (q.regs r ra rb).symm)
  have wk := work_eq pub
  simp only [prepRegs,List.forall_mem_cons]
  exact ⟨a.nonceLenSaved.trans ((reg _ (by decide) (by decide) pub.nonceLen).trans b.nonceLenSaved.symm),
    a.aad.trans ((reg _ (by decide) (by decide) pub.aad).trans b.aad.symm),
    a.aadLen.trans ((reg _ (by decide) (by decide) pub.aadLen).trans b.aadLen.symm),
    a.nonce.trans ((reg _ (by decide) (by decide) pub.nonce).trans b.nonce.symm),
    a.nonceLen.trans ((reg _ (by decide) (by decide) pub.nonceLen).trans b.nonceLen.symm),
    a.key.trans ((reg _ (by decide) (by decide) pub.key).trans b.key.symm),
    a.stream.trans ((congrArg (·+16) wk).trans b.stream.symm),a.scratch.trans (wk.trans b.scratch.symm),List.forall_mem_nil _⟩

theorem payload_agree {s d u v : State} (pub : CallPublic s d) (a : Positions s u) (b : Positions d v) :
    ∀ r∈sealRegs,u.gpr r=v.gpr r := by
  simp only [sealRegs,List.forall_mem_cons]
  have wk := work_eq pub
  exact ⟨a.src.trans (pub.src.trans b.src.symm),a.aadLen.trans (pub.aadLen.trans b.aadLen.symm),
    a.len.trans (pub.len.trans b.len.symm),a.dst.trans (pub.dst.trans b.dst.symm),a.rounds.trans (pub.rounds.trans b.rounds.symm),
    a.key.trans (pub.key.trans b.key.symm),a.stream.trans ((congrArg (·+16) wk).trans b.stream.symm),
    a.work.trans (wk.trans b.work.symm),List.forall_mem_nil _⟩

theorem fromReady_rel [Proof.Gcm.PPC64LE.GhashLaw] [Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {s d e f ta tb u v : State} (pub : CallPublic s d) (h : CallLayout s) (k : CallLayout d)
    (p : Args s e) (q : Args d f) (a : Positions s u) (b : Positions d v)
    (oa : ReadyData s e ta u) (ob : ReadyData d f tb v) :
    RelCT isa (Eq2 u v) (.seq VG.Impl.AesGcm.PPC64LE.Contiguous.payload (.seq (.block tagOut) (.block restore))) TT := by
  have sp : u.sp=v.sp := oa.env.sp.trans (p.sp.trans ((congrArg (·-1280) pub.sp).trans (q.sp.symm.trans ob.env.sp.symm)))
  have pa := a.space h (by rw [oa.env.r29,oa.env.r30,oa.env.r31];exact oa.env.perm)
  have pb := b.space k (by rw [ob.env.r29,ob.env.r30,ob.env.r31];exact ob.env.perm)
  have ca := pa.core (by rw [roundsOf,a.rounds];exact h.rounds)
  have cb := pb.core (by rw [roundsOf,b.rounds];exact k.rounds)
  refine rel_seq (payload_rel sp (payload_agree pub a b) ca.access ca.read ca.write cb.access cb.read cb.write)
    (bound_wp h a oa) (bound_wp k b ob) fun x y z w => ?_
  refine close_rel (z.sp.trans (sp.trans w.sp.symm)) ?_
  simp only [closeRegs,List.forall_mem_cons]
  exact ⟨(z.regs .r20 (by decide)).trans (a.tag.trans (pub.tag.trans (b.tag.symm.trans (w.regs .r20 (by decide)).symm))),
    (z.regs .r31 (by decide)).trans (a.work.trans ((work_eq pub).trans (b.work.symm.trans (w.regs .r31 (by decide)).symm))),List.forall_mem_nil _⟩

theorem body_rel [Proof.Gcm.PPC64LE.GhashLaw] [Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] {s d e f : State}
    (pub : CallPublic s d) (h : CallLayout s) (k : CallLayout d) (p : Args s e) (q : Args d f) :
    RelCT isa (Eq2 e f) VG.Impl.AesGcm.PPC64LE.Contiguous.body TT := by
  have sp := p.sp.trans ((congrArg (·-1280) pub.sp).trans q.sp.symm)
  refine rel_seq (entry_rel p.arguments ((work_eq pub).symm ▸ q.arguments) sp) (entry_wp p.arguments) (entry_wp q.arguments) fun x y ax ay => ?_
  apply RelCT.assoc
  refine rel_seq (prepare_rel (ax.entered.keeps.sp.trans (sp.trans ay.entered.keeps.sp.symm)) (prep_agree pub p q ax ay))
    (WP.with_rdwr (prepare_wp h p ax)) (WP.with_rdwr (prepare_wp k q ay)) fun u v ⟨oa,rd,wr,_⟩ ⟨ob,re,we,_⟩ => ?_
  exact fromReady_rel pub h k p q (positions p ax oa rd wr) (positions q ay ob re we) oa ob

open VG.Impl.StackScratch.PPC64LE

theorem timing [Proof.Gcm.PPC64LE.GhashLaw] [Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    ConstantTime isa contract.pre contract.pub framed := by
  refine VG.Proof.Gather.PPC64LE.ct_of fun s d hs hd hp => ?_
  have h := layout_of_pre hs
  have k := layout_of_pre hd
  have pub := public_args hp
  have bs : base s=base d := congrArg (·-1280) pub.sp
  refine (RelCT.alloc (bytes:=1280) (body:=.seq (.block (setArgsAt 1280 2 128)) VG.Impl.AesGcm.PPC64LE.Contiguous.body)
    (P:=Eq2 s d) (R:=TT) (fun a b ⟨rfl,rfl⟩ => pub.sp)
    ((?_ : RelCT isa (Eq2 (allocated 1280 s) (allocated 1280 d)) _ TT).mono
      (fun a b ⟨s',d',⟨hs,hd⟩,ha,hb⟩ => by subst s' d'; exact ⟨ha,hb⟩) fun _ _ h => h)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  obtain ⟨one,ea⟩ := args_run h
  obtain ⟨two,eb⟩ := args_run k
  refine rel_seq ?_ (WP.block ⟨_,one,ea⟩) (WP.block ⟨_,two,eb⟩) (fun _ _ p q => body_rel pub h k p q)
  rintro _ _ ta tb sa sb ⟨rfl,rfl⟩ ra rb
  rw [Exec.block_iff,one] at ra
  rw [Exec.block_iff,two] at rb
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj ra)
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj rb)
  exact ⟨congrArg (fun ptr => setArgsTrace 1280 ptr 2) bs,trivial⟩

end VG.Proof.AesGcm.PPC64LE.Contiguous
