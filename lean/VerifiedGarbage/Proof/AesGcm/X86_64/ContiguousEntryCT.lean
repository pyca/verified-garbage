module
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.AesGcm.SealBuffers
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.FlagBranch
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Verified
public import VerifiedGarbage.Spec.Gcm.Contiguous
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

namespace VG.Proof.AesGcm.SealBuffers
open VG VG.Spec.Gcm

abbrev sig := sealContiguousSig 129

theorem agreements {m₁ m₂ : Mem} {k r iv nl ad al src dst n tag : Addr}
    (h : ∀ b ∈ Sig.bufs sig.params [k,r,iv,nl,ad,al,src,dst,n,tag], Agree m₁ m₂ b.1.base b.1.len) :
    Agree m₁ m₂ k 1032 ∧ Agree m₁ m₂ iv nl.toNat ∧ Agree m₁ m₂ ad al.toNat ∧ Agree m₁ m₂ src n.toNat ∧
      Agree m₁ m₂ dst n.toNat ∧ Agree m₁ m₂ tag 16 := by
  by_cases eq : src=dst
  · subst src
    simp [sig, sealContiguousSig, Sig.bufs, Elem.size] at h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.1,h.2.2.2.2⟩
  · simpa [sig,sealContiguousSig,Sig.bufs,Elem.size,eq] using h

theorem postInputs (vs : List Addr) (m m' out : Mem) (r : BitVec 0) (hl : vs.length=(sig.words 64).length)
    (hb : ∀ b∈Sig.bufs sig.params vs, ∀ a,b.1.Contains a 1 → m a=m' a)
    (h : Curry.apply (sig.words 64) (sealContiguousPost 64) vs m out r) :
    Curry.apply (sig.words 64) (sealContiguousPost 64) vs m' out r := by
  match vs,hl with
  | [k,rounds,iv,nl,ad,al,src,dst,n,tag],_ =>
    obtain ⟨key,nonce,aad,pt,_⟩ := agreements hb
    intro sk hk
    have hₖ := keyRounds_local (m:=m') (m':=m) (fun a ha => (key a ((Region.sub_prefix (show 256≤1032 by decide)) _ ha)).symm) hk
    change Spec.Gcm.aesGcmEncrypt sk 16 (Spec.Aes.bytesAt m' iv nl.toNat) (Spec.Aes.bytesAt m' src n.toNat) (Spec.Aes.bytesAt m' ad al.toNat) = _
    rw [bytesAt_congr (agree_of nonce),bytesAt_congr (agree_of pt),bytesAt_congr (agree_of aad)]
    exact h sk hₖ

theorem postOutputs (vs : List Addr) (m out out' : Mem) (r : BitVec 0) (hl : vs.length=(sig.words 64).length)
    (hb : ∀ b∈Sig.bufs sig.params vs, ∀ a,b.1.Contains a 1 → out a=out' a)
    (h : Curry.apply (sig.words 64) (sealContiguousPost 64) vs m out r) :
    Curry.apply (sig.words 64) (sealContiguousPost 64) vs m out' r := by
  match vs,hl with
  | [k,rounds,iv,nl,ad,al,src,dst,n,tag],_ =>
    obtain ⟨_,_,_,_,d,t⟩ := agreements hb
    intro sk hk
    change _ = (Spec.Aes.bytesAt out' dst n.toNat,Spec.Aes.bytesAt out' tag 16)
    rw [bytesAt_congr (agree_of d),bytesAt_congr (agree_of t)]
    exact h sk hk

end VG.Proof.AesGcm.SealBuffers

namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm

open VG.Impl.AesGcm.X86_64.Contiguous
abbrev Sp (c : Prog isa) := c.all (fun i => !isa.writesSp i)=true

/-- Properties needed before assigning a private work area to the raw entry. -/
structure CoreSafe (record : Prog isa) : Prop where
  sp : Sp (core record)
  depth : (core record).x86_64Depth ≤ 24
  mx : (core record).allInstrs (fun i => !loadsMxcsr i)=true

/-- One functional, leakage and stack certificate for an AES-GCM record body. -/
structure RecordProof (M : CtxMode) (p : Prog isa) : Prop where
  ok : RecordOk M p
  ct : RecordCT M p
  safe : CoreSafe p

abbrev Condition := Addr → Addr → Mem → Prop
def workSig : Sig := {sealContiguousSig 129 with params := (sealContiguousSig 129).params ++ [("scratch",.array true .u64 320)]}
def pre (P : Condition) : Curry ((sealContiguousSig 129).words 64) (Mem → Prop) := fun k r _ _ _ _ _ _ _ _ => P k r
def workContract (P : Condition) : Contract isa :=
  workSig.contract abi (pre:=fun k r _ _ _ _ _ _ _ _ _ => P k r)
    (post:=fun k r np nl a al src dst len tag _ => sealContiguousPost 64 k r np nl a al src dst len tag)
    (writeArgs:=true) (stack:=32)

theorem entryPublic {P : Condition} {s t : State} (h : (workContract P).pub s t) : EntryPublic s t := by
  have arg (i : Nat) := h.2.1 i
  refine ⟨?_,?_⟩
  · intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    exacts [arg 0 (by decide),arg 1 (by decide),arg 2 (by decide),arg 3 (by decide),
      arg 4 (by decide),arg 5 (by decide),h.1.1]
  · intro i hi
    have idx : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases idx with rfl|rfl|rfl|rfl|rfl
    exacts [arg 6 (by decide),arg 7 (by decide),arg 8 (by decide),arg 9 (by decide),arg 10 (by decide)]

theorem entryPost {P : Condition} {s t : State} (h : EntryPost s t) : (workContract P).post s t := by
  sig_post [workContract,workSig,sealContiguousSig,sealContiguousPost,abi,argRegs,Gather.stackArgs_five,List.append_eq]
  intro key hk
  exact SealBuffers.keyed hk h

theorem entryPre {P : Condition} {M : CtxMode} {s : State}
    (valid : P (K s) (s.gpr .rsi) s.mem → rounds s ∧ M.ok s.mem (K s))
    (h : (workContract P).pre s) : EntryPre M s := by
  have b : Region.Sub (below (SP s) 24) (below (SP s) 32) := below_sub (by decide) (by decide)
  by_cases same : stackArg s 0=stackArg s 1
  all_goals
    sig_pre [Sig.bufs.eq_7,Sig.lists.eq_7,Sig.descs.eq_7,Sig.alignedBufs.eq_7,
      workContract,workSig,sealContiguousSig,abi,argRegs,Gather.stackArgs_five,List.cons_append,List.nil_append] at h
    simp only [same,↓reduceIte] at h
    simp [Sig.pairFacts,Sig.conj,List.filterMap_cons,and_assoc] at h
  case pos =>
    obtain ⟨room,top,rd,wr,kd,_,kw,nd,_,nw,ad,_,aw,dt,dw,da,tw,_,wa,_,_,_,rett,rt,rw,_,sk,sn,sa,sd,_,sw,_,bk,bn,ba,bd,_,bw,p⟩ := h
    have sameAddr : S s=D s := same
    have L : Proof.AesGcm.oneLay M.len 4 5 s 1 2 :=
      ⟨kd.sub_left (Region.sub_prefix M.le),kw.sub_left (Region.sub_prefix M.le),nd,nw,ad,aw,dw,da,wa,rett,rw,
       (sk.sub_left b).sub_right (Region.sub_prefix M.le),sn.sub_left b,sa.sub_left b,sd.sub_left b,sw.sub_left b,by omega_using [M.le,bk],bn,ba,bd,by change (stackArg s 4).toNat+2560≤2^64; omega_using [bw],by omega_arith,by omega_arith,(valid p).1⟩
    apply EntryPre.ofLayout L _ _ _ _ _ _ (valid p).2 _ (Or.inl sameAddr) (sameAddr ▸ dw) (sameAddr ▸ (sd.sub_left b).symm)
      (sameAddr ▸ bd) _ dt.symm tw rt
    · exact covers_prefix (k:=1032) (covers_of_mem (by simp [rd,K])) M.le
    all_goals apply covers_of_mem; simp [rd,wr,D,N,S,T,W,SP,stackArgAddr,same]
  case neg =>
    obtain ⟨room,top,rd,wr,kd,_,kw,nd,_,nw,ad,_,aw,sd,_,sw,dt,dw,da,tw,_,wa,_,_,_,_,rett,rt,rw,_,sk,sn,sa,ss,ds,_,ws,_,bk,bn,ba,bs,bd,_,bw,p⟩ := h
    have L : Proof.AesGcm.oneLay M.len 4 5 s 1 2 :=
      ⟨kd.sub_left (Region.sub_prefix M.le),kw.sub_left (Region.sub_prefix M.le),nd,nw,ad,aw,dw,da,wa,rett,rw,
       (sk.sub_left b).sub_right (Region.sub_prefix M.le),sn.sub_left b,sa.sub_left b,ds.sub_left b,ws.sub_left b,by omega_using [M.le,bk],bn,ba,bd,by change (stackArg s 4).toNat+2560≤2^64; omega_using [bw],by omega_arith,by omega_arith,(valid p).1⟩
    apply EntryPre.ofLayout L _ _ _ _ _ _ (valid p).2 _ (Or.inr sd) sw (ss.sub_left b).symm bs _ dt.symm tw rt
    · exact covers_prefix (k:=1032) (covers_of_mem (by simp [rd,K])) M.le
    all_goals apply covers_of_mem; simp [rd,wr,D,N,S,T,W,SP,stackArgAddr]

/-- A zero-length in-place record, with valid zero powers in the prepared key. -/
def witnessMem (a : Addr) : Byte :=
  if a=0x1400 then 48 else if a=0x9021 then 0x50 else if a=0x9029 then 0x60 else 0

def witness (scratch : Bool) : State :=
  { Gather.gatherSat with
    mem := witnessMem
    rd := [⟨0x1000,1032⟩,⟨0x2000,0⟩,⟨0x3000,0⟩,⟨0x9008,if scratch then 40 else 32⟩]
    wr := [⟨0,0⟩,⟨0x5000,16⟩]++(if scratch then [⟨0x6000,2560⟩] else []) }

theorem witnessPowers : Proof.AesGcm.Flag.FlaggedPowers 48 witnessMem 0x1000 := by
  apply Proof.AesGcm.Flag.flaggedPowers_of_zeroMem (Nat.le_refl _)
  · intro i hi
    have lo := Gather.ctx_low hi
    simp only [witnessMem,Proof.AesGcm.Flag.ctx_ne1024 hi,ite_false]
    have a : (0x1000+BitVec.ofNat 64 i : Addr)≠0x9021 := fun e => lo (by rw [e]; decide)
    have b : (0x1000+BitVec.ofNat 64 i : Addr)≠0x9029 := fun e => lo (by rw [e]; decide)
    simp only [a,b,ite_false]
  · decide +kernel

theorem workSat {P : Condition} (ok : P 0x1000 10 witnessMem) : (workContract P).pre (witness true) := by
  sig_pre [Sig.bufs.eq_7,Sig.lists.eq_7,Sig.descs.eq_7,Sig.alignedBufs.eq_7,
      workContract,workSig,sealContiguousSig,abi,argRegs,Gather.stackArgs_five,List.cons_append,List.nil_append,
    witness,Gather.gatherSat,stackArg,stackArgAddr,Mem.readW,Mem.read,witnessMem]
  simp
  repeat' apply And.intro
  all_goals first | exact ok | exact Region.disjoint_of_sep (by decide)

private theorem stackFour (s : State) : List.map (stackArg s) (List.range 4) =
  [stackArg s 0,stackArg s 1,stackArg s 2,stackArg s 3] := rfl

theorem publicSat {P : Condition} (ok : P 0x1000 10 witnessMem) :
    ((sealContiguousSig 129).contract abi (pre P) (sealContiguousPost 64) true 2640).pre (witness false) := by
  sig_pre [Sig.bufs.eq_7,Sig.lists.eq_7,Sig.descs.eq_7,Sig.alignedBufs.eq_7,
      pre,sealContiguousSig,abi,argRegs,stackFour,List.cons_append,List.nil_append,
    witness,Gather.gatherSat,stackArg,stackArgAddr,Mem.readW,Mem.read,witnessMem]
  simp
  repeat' apply And.intro
  all_goals first | exact ok | exact Region.disjoint_of_sep (by decide)

def plainP : Condition := fun _ r _ => r.toNat=10 ∨ r.toNat=12 ∨ r.toNat=14
def powerP (t : Nat) : Condition := fun k r m => plainP k r m ∧ Proof.AesGcm.Flag.FlaggedPowers t m k

abbrev PreLocal (P : Condition) :=
  ∀ {k r : Addr} {m m' : Mem}, SealBuffers.Agree m m' k 1032 → P k r m → P k r m'

theorem preLocal {P : Condition} (loc : PreLocal P) (vs : List Addr) (m m' : Mem) (hl : vs.length=(SealBuffers.sig.words 64).length)
    (hb : ∀ b∈Sig.bufs SealBuffers.sig.params vs, ∀ a,b.1.Contains a 1 → m a=m' a)
    (h : Curry.apply (SealBuffers.sig.words 64) (pre P) vs m) : Curry.apply (SealBuffers.sig.words 64) (pre P) vs m' := by
  match vs,hl with
  | [k,r,iv,nl,a,al,s,d,n,t],_ => exact loc (SealBuffers.agreements hb).1 h

theorem framedVerified {P : Condition} {M : CtxMode} {body : Prog isa} (p : RecordProof M body) (locality : PreLocal P)
    (input : ∀ {k r m}, P k r m → plainP k r m ∧ M.ok m k) (inh : P 0x1000 10 witnessMem) :
    Verified target (Impl.AesGcm.X86_64.Contiguous.framed body)
      ((sealContiguousSig 129).contract abi (pre P) (sealContiguousPost 64) true 2640) := by
  apply X86_64.Verified.stackArgScratchL (sig:=sealContiguousSig 129) (nm:="scratch") (e:=.u64) (n:=320)
    (pre:=pre P) (post:=sealContiguousPost 64) (wa:=true) (stack:=32) (bytes:=2608)
    (hpostOut:=fun vs m a b r hl _ hb _ => SealBuffers.postOutputs vs m a b r hl hb)
    _ (by decide) (by decide) (by decide) p.safe.sp (Nat.le_trans p.safe.depth (by decide))
    (fun vs a b hl hb _ => preLocal (P:=P) locality vs a b hl hb)
    (fun vs a b m r hl hb _ => SealBuffers.postInputs vs a b m r hl hb) ⟨_,publicSat inh⟩
  apply rawVerified (contract:=workContract P) p.ok p.ct p.safe.mx
    (fun _ h => entryPre input h) (fun _ _ _ => entryPost) (fun _ _ => entryPublic) ⟨_,workSat inh⟩

def preparedP : Condition := fun k r m => plainP k r m ∧ PreparedRepr m k

theorem preparedLocal : PreLocal preparedP :=
  fun h p => ⟨p.1,SealBuffers.prepared_local h p.2⟩

theorem powersLocal (t : Nat) : PreLocal (powerP t) :=
  fun h p => ⟨p.1,Proof.AesGcm.Flag.flaggedPowers_congr (agree_of h) p.2⟩

abbrev apiContract := sealContiguousPreparedApi.contract abi 2640
abbrev recordContract (P : Condition) :=
  (sealContiguousSig 129).contract abi (pre P) (sealContiguousPost 64) true 2640

theorem prepInhabited : preparedP 0x1000 10 witnessMem := ⟨Or.inl rfl,witnessPowers.2⟩
theorem powerInhabited {t : Nat} (ht : t≤48) : powerP t 0x1000 10 witnessMem :=
  ⟨Or.inl rfl,Nat.le_trans ht witnessPowers.1,witnessPowers.2⟩

theorem plainPublic {c : Prog isa} (h : Verified target c (recordContract preparedP)) :
    Verified target c apiContract :=
  Verified.leak_flag h (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)

theorem onPowers {t : Nat} (ht : t=16 ∨ t=48) {a b : Prog isa}
    (ha : Verified target a (recordContract (powerP t))) (hb : Verified target b (recordContract preparedP)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag t a b) apiContract :=
  Verified.of_onFlagCtx ht (by decide) ha hb (fun _ _ _ _ _ _ _ _ _ _ _ p hf => ⟨p.1,hf,p.2⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ p _ => p) (fun _ _ _ _ _ _ _ _ _ _ _ => rfl) ⟨_,publicSat prepInhabited⟩

theorem outputLocal : VG.X86_64.Scrub.PostOut apiContract 0 :=
  VG.X86_64.Scrub.postOut_of_local (sig:=sealContiguousSig 129) (post:=sealContiguousPost 64)
    (leak:=some fun ctx rounds nonce nl aad al _ dst len tag => sealPreparedLeak 64 ctx rounds nonce nl aad al dst len tag)
    VG.X86_64.Scrub.ScrubAbi.plain SealBuffers.postOutputs

end VG.Proof.AesGcm.X86_64.ContiguousSeal
