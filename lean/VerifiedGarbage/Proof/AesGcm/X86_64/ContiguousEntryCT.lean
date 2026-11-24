module
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousRecord
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.X86_64.Seal
import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousRunCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Impl.AesGcm.X86_64

/-! The contiguous record ABI passes the original source and destination as
separate words. Preserve the return address, callee-saved registers and tag. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith)
open VG.Spec.Aes (bytesAt)
open Short (SpanLayout)

abbrev K (s : State) := s.gpr .rdi
abbrev SP (s : State) := s.gpr .rsp
abbrev S (s : State) := stackArg s 0
abbrev D (s : State) := stackArg s 1
abbrev N (s : State) := (stackArg s 2).toNat
abbrev T (s : State) := stackArg s 3
abbrev W (s : State) := stackArg s 4

structure EntryPre (M : CtxMode) (s : State) : Prop where
  ctx : OneCtx s 5 (K s) (W s) (SP s) (s.gpr .rdx) (s.gpr .r8) (D s) (s.gpr .rcx).toNat (s.gpr .r9).toNat (N s)
  ext : CtxExt M (K s) (W s+16#64) (W s) (SP s) (D s) (N s) s
  geo : SpanLayout s (S s) (S s) (D s) (W s) (SP s) (N s) (N s)
  nowrap : (S s).toNat+N s≤2^64
  tw : Covers [⟨T s,16⟩] s.wr
  td : (⟨T s,16⟩ : Region).Disjoint ⟨D s,N s⟩
  tW : (⟨T s,16⟩ : Region).Disjoint ⟨W s,2560⟩
  rt : (⟨SP s,8⟩ : Region).Disjoint ⟨T s,16⟩

/-- Ordinary one-shot layout, extended by the two possible source/destination
geometries. Incoming ABI permissions provide read coverage for the source in
either the readable list or the writable destination. -/
theorem EntryPre.ofLayout {M : CtxMode} {s : State} (lay : Proof.AesGcm.oneLay M.len 4 5 s 1 2)
    (ctx : Covers [⟨K s,M.len⟩] (s.rd++s.wr)) (nonce : Covers [⟨s.gpr .rdx,(s.gpr .rcx).toNat⟩] (s.rd++s.wr))
    (aad : Covers [⟨s.gpr .r8,(s.gpr .r9).toNat⟩] (s.rd++s.wr)) (args : Covers [⟨SP s+8#64,40⟩] (s.rd++s.wr))
    (dst : Covers [⟨D s,N s⟩] s.wr) (work : Covers [⟨W s,2560⟩] s.wr) (ok : M.ok s.mem (K s))
    (src : Covers [⟨S s,N s⟩] (s.rd++s.wr)) (alias : S s=D s ∨ (⟨S s,N s⟩ : Region).Disjoint ⟨D s,N s⟩)
    (sw : (⟨S s,N s⟩ : Region).Disjoint ⟨W s,2560⟩) (ss : (⟨S s,N s⟩ : Region).Disjoint (below (SP s) 24))
    (wrap : (S s).toNat+N s≤2^64) (tag : Covers [⟨T s,16⟩] s.wr)
    (td : (⟨T s,16⟩ : Region).Disjoint ⟨D s,N s⟩) (tw : (⟨T s,16⟩ : Region).Disjoint ⟨W s,2560⟩)
    (rt : (⟨SP s,8⟩ : Region).Disjoint ⟨T s,16⟩) : EntryPre M s := by
  refine ⟨OneCtx.ofAt lay M.ge ctx nonce aad args dst work,?_,?_,wrap,tag,td,tw,rt⟩
  · obtain ⟨cd,cw,_,_,_,_,_,_,_,_,_,ct,_,_,_,_,ww,_⟩ := lay
    exact ⟨ww,cw.sub_right (Lay.wSub (by decide)),cw,cd,ct,ctx,ok⟩
  · exact ⟨Nat.le_refl _,src,alias,sw,ss,fun h => (Nat.lt_irrefl _ h).elim,fun h => (Nat.lt_irrefl _ h).elim,
      fun h => (Nat.lt_irrefl _ h).elim,fun h => (Nat.lt_irrefl _ h).elim⟩

def EntryPost (s t : State) : Prop :=
  encryptWith (ctxCiph s.mem (K s) (s.gpr .rsi).toNat) (ctxH s.mem (K s)) 16
    (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (S s) (N s))
    (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) = (bytesAt t.mem (D s) (N s),bytesAt t.mem (T s) 16)

theorem entry_ok {M : CtxMode} {body : Prog isa} (h : RecordOk M body) {s : State} (p : EntryPre M s) :
    WP isa (.seq (.block (oneEntry 40 16 24)) (.seq body (.seq (.block (tagOut (at_ .rsp 32))) (.block restore)))) s
      fun t => gprPreserved s t ∧ EntryPost s t := by
  have C := p.ctx
  refine WP.seq ((oneEntryAt_okL (id:=1) (il:=2) (wo:=40) (by decide) (by decide) C rfl rfl rfl rfl rfl rfl
    (C.args 4 (by decide))).mono fun u ⟨E,_⟩ => ?_)
  refine WP.seq ((h C p.ext p.geo p.nowrap rfl rfl E rfl rfl rfl).mono fun v ⟨env,rd,wr,saved,frame,ct,tag⟩ => WP.seq ?_)
  have sub : Region.Sub ⟨SP s+32#64,8⟩ ⟨SP s+8#64,8*5⟩ := by
    rw [show 32#64 = (BitVec.ofNat 64 (8+24)) from rfl,← add_ofNat_assoc]; exact Offset.sub_base _ (by decide)
  have slot : v.mem.readW (v.gpr .rsp+32#64) 64=T s := by
    rw [env.rsp,frame.readW (Region.contains_self _ _) (fun b hb => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl|rfl
      · exact C.dA.sub_left sub
      · exact C.dAD.sub_left sub
      · exact Offset.disjoint_below _ (n:=24) (d:=32) (k:=8) (by decide)) (by decide)]; rfl
  obtain ⟨z,run,tagOut,fr,g,zr,zw⟩ := tagOut_ok (b:=.rsp) (d:=32) env.r15 slot
    (by rw [env.rsp,rd,wr]; exact C.args 3 (by decide)) env.perm.w (wr ▸ p.tw)
  refine WP.of_runBlock ⟨z,run,?_⟩
  have ez := env.keep (fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact g _ (by decide) (by decide) (by decide)) zr zw
  have sz : SavedAt z.mem (W s) s := saved.frame fr fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact (p.tW.sub_right (Lay.wSub (by decide))).symm
  have ret : z.mem.readW (SP s) 64 = s.mem.readW (SP s) 64 := by
    rw [ret_kept fr (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact p.rt),
        ret_kept frame (fun r hr => by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl|rfl|rfl
          · exact C.rW
          · exact C.rD
          · exact Offset.base_disjoint_below _ (n:=24) (k:=8) (by decide))]
  refine (exit_ok ez.r15 ez.rsp (covers_left ez.perm.w) sz ret).mono fun t ⟨regs,mem,_⟩ => ⟨regs,?_⟩
  have dst : bytesAt z.mem (D s) (N s) = bytesAt v.mem (D s) (N s) :=
    bytesAt_frame fr (fun b hb => by obtain rfl := List.mem_singleton.mp hb; exact p.td.symm) (by have := C.data.ok.lt; omega_arith)
  unfold EntryPost
  rw [Spec.Gcm.encryptWith,mem,tagOut,tag,dst,ct,Proof.Gcm.fullTag_eq,Proof.Gcm.length_gctr,length_bytesAt,length_bytesAt]
  simp only [Prod.mk.injEq,true_and]
  rw [List.take_of_length_le (by rw [Cmac.toBytes_length])]

end VG.Proof.AesGcm.X86_64.ContiguousSeal

/-! Leakage across the ten-argument ABI and its caller-provided scratch. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open Short (rel_next)

def EntryPublic (s t : State) : Prop :=
  (∀ r ∈ [Reg.rdi,.rsi,.rdx,.rcx,.r8,.r9,.rsp], s.gpr r=t.gpr r) ∧ ∀ i, i<5 → stackArg s i=stackArg t i

theorem entry_start {M : CtxMode} {s : State} (p : EntryPre M s) :
    WP isa (.block (oneEntry 40 16 24)) s (OneEntry s (K s) (W s) (SP s) (s.gpr .r8) (D s) (N s)) :=
  (oneEntryAt_okL (id:=1) (il:=2) (wo:=40) (by decide) (by decide) p.ctx rfl rfl rfl rfl rfl rfl (p.ctx.args 4 (by decide))).mono
    fun _ ⟨h,_⟩ => h

theorem entry_tag {M : CtxMode} {body : Prog isa} (hw : RecordOk M body) {s u : State} (p : EntryPre M s)
    (E : OneEntry s (K s) (W s) (SP s) (s.gpr .r8) (D s) (N s) u) :
    WP isa body u (TagAt (K s) (W s+16#64) (W s) (SP s) .rsp 32 (T s)) := by
  refine (hw p.ctx p.ext p.geo p.nowrap rfl rfl E rfl rfl rfl).mono fun v ⟨env,rd,wr,_,frame,_⟩ => ?_
  have sub : Region.Sub ⟨SP s+32#64,8⟩ ⟨SP s+8#64,8*5⟩ := by
    rw [show 32#64 = (BitVec.ofNat 64 (8+24)) from rfl,← add_ofNat_assoc]; exact Offset.sub_base _ (by decide)
  refine ⟨env,?_,by rw [env.rsp,rd,wr]; exact p.ctx.args 3 (by decide)⟩
  rw [env.rsp,frame.readW (Region.contains_self _ _) (fun b hb => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl
    · exact p.ctx.dA.sub_left sub
    · exact p.ctx.dAD.sub_left sub
    · exact Offset.disjoint_below _ (n:=24) (d:=32) (k:=8) (by decide)) (by decide)]; rfl

theorem entry_ct {M : CtxMode} {body : Prog isa} (hw : RecordOk M body) (hc : RecordCT M body)
    {a b : State} (p : EntryPre M a) (q : EntryPre M b) (eq : EntryPublic a b) :
    RelCT isa (fun x y => x=a ∧ y=b)
      (.seq (.block (oneEntry 40 16 24)) (.seq body (.seq (.block (tagOut (at_ .rsp 32))) (.block restore)))) (fun _ _ => True) := by
  have k : K b=K a := (eq.1 _ (by decide)).symm
  have sp : SP b=SP a := (eq.1 _ (by decide)).symm
  have w : W b=W a := (eq.2 4 (by decide)).symm
  have src : S b=S a := (eq.2 0 (by decide)).symm
  have dst : D b=D a := (eq.2 1 (by decide)).symm
  have n : N b=N a := congrArg BitVec.toNat (eq.2 2 (by decide)).symm
  have tag : T b=T a := (eq.2 3 (by decide)).symm
  have ar : b.gpr .r8=a.gpr .r8 := (eq.1 _ (by decide)).symm
  have no : b.gpr .rdx=a.gpr .rdx := (eq.1 _ (by decide)).symm
  have nl : (b.gpr .rcx).toNat=(a.gpr .rcx).toNat := congrArg BitVec.toNat (eq.1 _ (by decide)).symm
  have al : (b.gpr .r9).toNat=(a.gpr .r9).toNat := congrArg BitVec.toNat (eq.1 _ (by decide)).symm
  have r : (b.gpr .rsi).toNat=(a.gpr .rsi).toNat := congrArg BitVec.toNat (eq.1 _ (by decide)).symm
  have recordInput {u : State} (g : EntryPre M u) : RecordInput M u (K u) (W u) (SP u) (u.gpr .rdx) (u.gpr .r8) (S u) (D u)
      (u.gpr .rcx).toNat (u.gpr .r9).toNat (N u) (u.gpr .rsi).toNat :=
    ⟨g.ctx,g.ext,g.geo,g.nowrap,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have qb := recordInput q
  rw [k,w,sp,no,ar,src,dst,nl,al,n,r] at qb
  have ea := entry_start p
  have eb := entry_start q
  rw [k,w,sp,ar,dst,n] at eb
  have wtb (s) (e : OneEntry b (K a) (W a) (SP a) (a.gpr .r8) (D a) (N a) s) :
      WP isa body s (TagAt (K a) (W a+16#64) (W a) (SP a) .rsp 32 (T a)) := by
    rw [← k,← w,← sp,← ar,← dst,← n] at e
    simpa only [k,w,sp,tag] using entry_tag hw q e
  have mid := rel_next (hc (recordInput p) qb) (fun _ e => entry_tag hw p e) wtb
  rw [oneEntry,List.append_assoc,List.append_assoc,List.append_assoc] at ea eb ⊢
  refine rel_reassoc_mid (fn_rel₂ (Ctx:=K a) (St:=W a+16#64) (W:=W a) (SP:=SP a) (k:=40)
    [.rdi,.rsi,.rdx,.rcx,.r8,.r9,.rsp] (by simp) ⟨_,by taint_decide⟩ eq.1 w.symm
    (p.ctx.args 4 (by decide)) (q.ctx.args 4 (by decide)) ⟨_,by taint_decide⟩ ea eb ?_)
  exact RelCT.seq (mid.mono (fun _ _ h => h.2) (fun _ _ h => h)) (tagOut_rel (b:=.rsp) (d:=32) (by simp) ⟨_,by taint_decide⟩ (fun _ _ h => h))

/-- Lift the whole-record correctness and leakage proofs to a contract once its
memory, outputs and public ABI arguments have been identified. -/
theorem rawVerified {contract : Contract isa} {M : CtxMode} {body : Prog isa}
    (hw : RecordOk M body) (hc : RecordCT M body)
    (mx : (Contiguous.core body).allInstrs (fun i => !loadsMxcsr i)=true)
    (inputs : ∀ s,contract.pre s → EntryPre M s)
    (outputs : ∀ s t,contract.pre s → EntryPost s t → contract.post s t)
    (publicArgs : ∀ s t,contract.pub s t → EntryPublic s t)
    (sat : ∃ s,contract.pre s) : Verified X86_64.target (Contiguous.core body) contract := by
  refine ⟨fun s hs => ?_,fun s t _ _ _ _ hs ht pb ex ey => ?_,sat⟩
  · obtain ⟨tr,t,run,regs,post⟩ := entry_ok hw (inputs s hs)
    exact ⟨tr,t,run,abiPreserved_of_exec mx run regs,outputs s t hs post⟩
  · exact (entry_ct hw hc (inputs s hs) (inputs t ht) (publicArgs s t pb) s t _ _ _ _ ⟨rfl,rfl⟩ ex ey).1

end VG.Proof.AesGcm.X86_64.ContiguousSeal
