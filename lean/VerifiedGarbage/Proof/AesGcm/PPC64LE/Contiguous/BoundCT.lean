module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Framed
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.PayloadCT
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
  obtain ⟨c,r,n,nl,a,al,src,dst,len,tag,sp,_⟩ := h
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

end VG.Proof.AesGcm.PPC64LE.Contiguous
