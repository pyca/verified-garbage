module
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousDeferred
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.TagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Short
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Seal
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Body
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTag
import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
public import VerifiedGarbage.Proof.AesOcb.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Crypt
import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant
import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Contiguous
meta import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousDeferred
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! Batched scalar AES masks at the end of a contiguous GCM record. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Impl.AesGcm.X86_64.Contiguous (copyMask pairArgs mixMasks maskXor authReload authLens)
open VG.Spec.Gcm (blockAt)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes
open VG.Proof.AesOcb.X86_64 (BCall BPost blk_call)

/-- The existing AES block entry may write the two mask slots and its own scratch. -/
theorem mask_call_args {s : State} {Ctx W SP : Addr} {R : Nat} (L : Lay Ctx (W+16#64) W SP)
    (e : Env Ctx (W+16#64) W SP s) (rr : R=10 ∨ R=12 ∨ R=14)
    (di : s.gpr .rdi=Ctx) (si : s.gpr .rsi=BitVec.ofNat 64 R)
    (dx : s.gpr .rdx=W+256#64) (cx : s.gpr .rcx=2#64) (r8 : s.gpr .r8=W+512#64) :
    BCall s Ctx (W+256#64) (W+512#64) R 2 := by
  refine ⟨di,si,dx,cx,r8,rr,?_,(L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (d:=256) (by decide)),
    (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (d:=512) (by decide)),
    Offset.disjoint W (.inl (by decide)) (by decide) (by decide),?_,?_,?_,?_,?_⟩
  · have w := L.ww
    rw [BitVec.toNat_add_of_lt];all_goals simp at *;omega
  · rw [e.rsp];exact L.kc.sub_right (Region.sub_prefix (by decide))
  · rw [e.rsp];exact L.stk_w (by decide)
  · rw [e.rsp];exact L.stk_w (by decide)
  · exact covers_cons (by simpa only [BitVec.add_zero] using e.perm.ctxC (d:=0) (n:=240) (by decide)) (covers_cons (covers_left (e.perm.wC (by decide)))
      (covers_left (e.perm.wC (by decide))))
  · exact covers_cons (e.perm.wC (by decide)) (e.perm.wC (by decide))

theorem encrypted_mask_pair {s t : State} {Ctx W : Addr} {R : Nat}
    (h : BPost Spec.Aes.cipher s Ctx (W+256#64) (W+512#64) R 2 t) :
    blockAt t.mem (W+256#64) = ciphOf s.mem Ctx R (blockAt s.mem (W+256#64)) ∧
    blockAt t.mem (W+272#64) = ciphOf s.mem Ctx R (blockAt s.mem (W+272#64)) := by
  have a := h.enc (i:=0) (by decide)
  have b := h.enc (i:=1) (by decide)
  change blockAt t.mem ((W+256#64)+0#64)=ciphOf s.mem Ctx R (blockAt s.mem ((W+256#64)+0#64)) at a
  change blockAt t.mem ((W+256#64)+16#64)=ciphOf s.mem Ctx R (blockAt s.mem ((W+256#64)+16#64)) at b
  exact ⟨by simpa only [BitVec.add_zero] using a,by simpa only [BitVec.add_assoc,show 256#64+16#64=272#64 from rfl] using b⟩
open VG.Proof.Gcm.X86_64 (blockAt_eq pshufb_rev_xor)
theorem mixMasks_ok {s : State} {Ctx St W SP : Addr} (e : Env Ctx St W SP s) :
    WP isa (.block mixMasks) s fun t => Env Ctx St W SP t ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      Frame [⟨W,16⟩] s.mem t.mem ∧ blockAt t.mem W=blockAt s.mem (St+16#64) ^^^ blockAt s.mem (W+256#64) := by
  have rd := e.perm.wR (show 256+16≤2560 by decide)
  have rs := e.perm.stR (show 16+16≤80 by decide)
  have wr : InRegions s.wr W 16 := by simpa only [BitVec.add_zero] using e.perm.wW (d:=0) (n:=16) (by decide)
  let a := s.mem.readW (W+256#64) 128
  let b := s.mem.readW (St+16#64) 128
  let st := (((s.setXmm .xmm0 a).setXmm .xmm1 b).setXmm .xmm0 (a ^^^ b)).setMem (s.mem.writeW W (a ^^^ b))
  apply WP.of_runBlock
  refine ⟨st,?_,e.keep (fun _ _ => rfl) rfl rfl,rfl,rfl,?_,?_⟩
  · unfold mixMasks
    xrun [st,a,b,e.r15,e.r14,rd,rs,wr,BitVec.add_zero,State.load128,State.store128_eq,XOp.exec,XBinOp.eval,State.setXmm]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · change blockAt (s.mem.writeW W (a ^^^ b)) W=_
    rw [blockAt_eq,Mem.readW_writeW_self _ _ 16 _ (by decide),pshufb_rev_xor,BitVec.xor_comm]
    rw [blockAt_eq,blockAt_eq]
theorem copyMask_ok {s : State} {Ctx St W SP : Addr} (e : Env Ctx St W SP s) (fromOff toOff : Nat)
    (src : fromOff+16≤80) (dst : toOff+16≤2560) :
    WP isa (.block (copyMask fromOff toOff)) s fun t =>
      Env Ctx St W SP t ∧ t.gpr=s.gpr ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      Frame [⟨W+BitVec.ofNat 64 toOff,16⟩] s.mem t.mem ∧
      blockAt t.mem (W+BitVec.ofNat 64 toOff)=blockAt s.mem (St+BitVec.ofNat 64 fromOff) := by
  have rd := e.perm.stR src
  have wr := e.perm.wW dst
  let val := s.mem.readW (St+BitVec.ofNat 64 fromOff) 128
  let t := (s.setXmm .xmm0 val).setMem (s.mem.writeW (W+BitVec.ofNat 64 toOff) val)
  apply WP.of_runBlock
  refine ⟨t,?_,e.keep (fun _ _ => rfl) rfl rfl,rfl,rfl,rfl,?_,?_⟩
  · unfold copyMask
    xrun [State.load128,State.store128_eq,rd,wr,e.r14,e.r15,t,val,State.setXmm,BitVec.ofInt_natCast]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · change blockAt (s.mem.writeW (W+BitVec.ofNat 64 toOff) val) _=_
    rw [blockAt_eq,Mem.readW_writeW_self _ _ 16 _ (by decide),blockAt_eq]

theorem pairArgs_ok {s : State} {Ctx W SP : Addr} {R : Nat}
    (L : Lay Ctx (W+16#64) W SP) (e : Env Ctx (W+16#64) W SP s) (rr : RoundsAt s.mem W R) :
    WP isa (.block pairArgs) s fun t => BCall t Ctx (W+256#64) (W+512#64) R 2 ∧
      t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ (∀ r ∈ calleeSaved, t.gpr r=s.gpr r) := by
  have rd := e.perm.wR (show 176+8≤2560 by decide)
  unfold pairArgs
  obtain ⟨t,rn,di,si,dx,cx,r8,mem,dr,dw,saved⟩ :
      ∃ t, runBlock isa ([.mov .rdi (.reg .r13),.mov .rsi (.mem (at_ .r15 roundsO))] ++ ptr .rdx .r15 256 ++
        [.mov32 .rcx (imm 2)] ++ ptr .r8 .r15 scrO) s = some t ∧
      t.gpr .rdi=Ctx ∧ t.gpr .rsi=BitVec.ofNat 64 R ∧ t.gpr .rdx=W+256#64 ∧
      t.gpr .rcx=2#64 ∧ t.gpr .r8=W+512#64 ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r=s.gpr r) := by
    refine ⟨_,by xrun [e.r13,e.r15,roundsO,scrO,rd,ptr],?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals try rfl
    all_goals try (simp [gpr_setReg,rr.1];done)
    · intro r h;simp only [calleeSaved,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [gpr_setReg]
  exact WP.of_runBlock ⟨t,rn,mask_call_args L (e.of_saved saved dr dw) rr.2 di si dx cx r8,mem,dr,dw,saved⟩

abbrev pairFrame (W SP : Addr) : List Region := [⟨W+256#64,32⟩,⟨W+512#64,2048⟩,below SP 8]
abbrev makeMasks := Contiguous.makeMasks Contiguous.maskAES

theorem makeMasks_ok {s : State} {Ctx W SP : Addr} {R : Nat}
    (L : Lay Ctx (W+16#64) W SP) (e : Env Ctx (W+16#64) W SP s) (rr : RoundsAt s.mem W R) :
    WP isa makeMasks s fun t => Env Ctx (W+16#64) W SP t ∧
      (∀ r ∈ calleeSaved, t.gpr r=s.gpr r) ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      Frame (pairFrame W SP) s.mem t.mem ∧
      blockAt t.mem (W+256#64)=ciphOf s.mem Ctx R (blockAt s.mem (W+16#64)) ∧
      blockAt t.mem (W+272#64)=ciphOf s.mem Ctx R (blockAt s.mem ((W+16#64)+48#64)) := by
  unfold makeMasks Contiguous.makeMasks
  apply WP.seq
  rw [WP.block_append_iff,WP.block_append_iff]
  refine (copyMask_ok e 0 256 (by decide) (by decide)).mono fun a ⟨ea,ga,ra,wa,fa,ha⟩ => ?_
  refine (copyMask_ok ea 48 272 (by decide) (by decide)).mono fun b ⟨eb,gb,rb,wb,fb,hb⟩ => ?_
  have f : Frame [⟨W+256#64,32⟩] s.mem b.mem := by
    apply (fa.sub ?_).trans (fb.sub ?_)
    · intro x hx;obtain rfl := List.mem_singleton.mp hx
      exact ⟨_,List.mem_singleton_self _,Region.sub_prefix (by decide)⟩
    · intro x hx;obtain rfl := List.mem_singleton.mp hx
      exact ⟨_,List.mem_singleton_self _,Offset.sub W (d:=272) (e:=256) (n:=16) (k:=32) (by decide) (by decide)⟩
  have k : ciphOf b.mem Ctx R=ciphOf s.mem Ctx R := ciph_frame f (by
    intro q h;obtain rfl := List.mem_singleton.mp h
    exact L.cw'.sub_right (Lay.wSub (by decide))) rr.2
  have rr' : RoundsAt b.mem W R := ⟨(f.readW (r:=⟨W+176#64,8⟩) (Region.contains_self _ _) (by
    intro q h;obtain rfl := List.mem_singleton.mp h
    exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide)).trans rr.1,rr.2⟩
  have p : blockAt b.mem (W+256#64)=blockAt s.mem (W+16#64) := by
    rw [blockAt_frame fb (by intro q h;obtain rfl := List.mem_singleton.mp h;exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)),ha,BitVec.add_zero]
  have q : blockAt b.mem (W+272#64)=blockAt s.mem ((W+16#64)+48#64) := by
    rw [hb,blockAt_frame fa (by intro z h;obtain rfl := List.mem_singleton.mp h;exact L.st_w (by decide) (.inr ⟨by decide,by decide⟩))]
  refine (pairArgs_ok L eb rr').mono fun v ⟨args,mv,rv,wv,gv⟩ => ?_
  let aes := Proof.Aes.X86_64.BlocksImpl.scalar
  refine (blk_call (name:=aes.enc.name) aes.encOk aes.encNosp aes.encDepth args).mono fun t post => ?_
  obtain ⟨j,c⟩ := encrypted_mask_pair post
  rw [mv,k,p] at j
  rw [mv,k,q] at c
  have vsp := (gv _ (by decide : Reg.rsp ∈ calleeSaved)).trans eb.rsp
  have frame := post.frame
  rw [mv,vsp] at frame
  refine ⟨(eb.of_saved gv rv wv).of_saved post.saved post.rd post.wr,?_,post.rd.trans (rv.trans (rb.trans ra)),
    post.wr.trans (wv.trans (wb.trans wa)),?_,j,c⟩
  · intro r hr;rw [post.saved r hr,gv r hr,gb,ga]
  · exact (f.sub (fun r hr => ⟨r,by obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_self ..,fun _ h => h⟩)).trans frame


/-- XOR the remaining zero to fifteen bytes, reading each before it is written. -/
theorem maskXor_ok {s : State} {Ctx St W SP S D : Addr} {r : Nat} (e : Env Ctx St W SP s)
    (bx : s.gpr .rbx=S) (dst : s.gpr .r12=D) (len : s.gpr .rbp=BitVec.ofNat 64 r) (hr : r<16)
    (src : DataOk St W SP s S r) (out : DataW Ctx St W SP s D r)
    (alias : S=D ∨ (⟨S,r⟩ : Region).Disjoint ⟨D,r⟩) :
    WP isa maskXor s fun t => Env Ctx St W SP t ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      Frame [⟨D,r⟩] s.mem t.mem ∧ bytesAt t.mem D r=xorBytes s.mem S (W+272#64) r := by
  unfold maskXor
  apply WP.seq
  obtain ⟨u,run,zf,g,m,dr,dw⟩ : ∃ u,runBlock isa [.alu .test .rbp (.reg .rbp)] s=some u ∧ u.zf=some (decide (r=0)) ∧
      u.gpr=s.gpr ∧ u.mem=s.mem ∧ u.rd=s.rd ∧ u.wr=s.wr := by
    refine ⟨_,by xrun [len],?_,?_,?_,?_,?_⟩
    · simp only [zf_arithFlags];exact congrArg some (and_self_beq (by omega_using [hr]))
    all_goals rfl
  refine WP.of_runBlock ⟨u,run,WP.ite (decide (r=0)) (eval_e zf) (fun h => ?_) (fun h => ?_)⟩
  · have z : r=0 := of_decide_eq_true h
    subst r
    exact WP.of_runBlock ⟨u,rfl,e.keep (fun q _ => congrFun g q) dr dw,dr,dw,m ▸ Frame.refl _ _,rfl⟩
  · have pos : 1≤r := by have := of_decide_eq_false h;omega
    obtain ⟨v,rn,di,cx,si,gv,mv,rv,wv⟩ : ∃ v,runBlock isa
        ([.mov .rdi (.reg .r12),.mov .rcx (.reg .rbp)] ++ ptr .rsi .r15 272) u=some v ∧
        v.gpr .rdi=D ∧ v.gpr .rcx=BitVec.ofNat 64 r ∧ v.gpr .rsi=W+272#64 ∧
        (∀ z ∈ calleeSaved,v.gpr z=u.gpr z) ∧ v.mem=u.mem ∧ v.rd=u.rd ∧ v.wr=u.wr := by
      refine ⟨_,by xrun [ptr,g,dst,len,e.r15],?_,?_,?_,?_,?_,?_,?_⟩
      · simp [gpr_setReg]
      · simp [gpr_setReg]
      · simp [gpr_setReg]
      · intro z hz;simp only [calleeSaved,List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [gpr_setReg]
      all_goals rfl
    have keep : Env Ctx St W SP v := (e.keep (fun q _ => congrFun g q) dr dw).of_saved gv rv wv
    have lp : LoopPre v (W+272#64) D r := ⟨si,di,cx,pos,by omega_using [hr],
      covers_left (keep.perm.wC (by omega_using [hr])),by rw [wv,dw];exact out.wr,
      (out.ok.w.sub_right (Lay.wSub (by omega_using [hr]))).symm⟩
    refine WP.seq (WP.of_runBlock ⟨v,rn,?_⟩)
    refine (xorLoopG_ok true v lp (by change v.gpr .rbx=S;rw [gv _ (by decide),g,bx])
      (by rw [rv,dr,wv,dw];exact src.rd) alias).mono fun t ⟨hm,hg,rt,wt⟩ => ?_
    rw [mv,m] at hm
    have eq := length_xorBytes s.mem S (W+272#64) r
    refine ⟨keep.keep (fun q hq => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl|rfl|rfl <;> exact hg _ (by decide) (by decide) (by decide)) rt wt,
      rt.trans (rv.trans dr),wt.trans (wv.trans dw),?_,?_⟩
    · rw [hm];exact writeBytes_frame' _ eq
    · rw [hm];simpa only [eq] using bytesAt_writeBytes_self s.mem D (xorBytes s.mem S (W+272#64) r) (by rw [eq];omega_using [hr])


open VG.Spec.Gcm (Block ghashFrom ghash blocks zeros padLen ofBytes toBytes)
open VG.Proof.Gcm (Absorbed lensBlock)
abbrev authMasks (v : GcmImpl) := Contiguous.maskAuth v.callees

/-- Authenticate the ciphertext tail and mix in the previously encrypted tag counter. -/
theorem authMasks_ok (v : GcmImpl) {s : State} {Ctx W SP D : Addr} {n al N : Nat} {H : Block} {x : List Byte}
    (L : Lay Ctx (W+16#64) W SP) (he : Env Ctx (W+16#64) W SP s)
    (hH : blockAt s.mem (Ctx+240#64)=H) (hx16 : x.length%16=0)
    (hdat : s.mem.readW (W+200#64) 64=D) (hlen : s.mem.readW (W+208#64) 64=BitVec.ofNat 64 n)
    (htl : s.mem.readW (W+192#64) 64=BitVec.ofNat 64 N) (hN : N<2^64)
    (hal : s.mem.readW (W+184#64) 64=BitVec.ofNat 64 al)
    (hd : DataOk (W+16#64) W SP s D n) (habs : Absorbed s.mem ((W+16#64)+16#64) ((W+16#64)+32#64) H x) :
    WP isa (authMasks v) s fun t => Env Ctx (W+16#64) W SP t ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      Frame (⟨W,16⟩ :: wFrame W SP) s.mem t.mem ∧
      blockAt t.mem W=ghashFrom H (ghash H (blocks (x++bytesAt s.mem D n++zeros (padLen (x++bytesAt s.mem D n).length))))
        [ofBytes (lensBlock al N)] ^^^ blockAt s.mem (W+256#64) := by
  unfold authMasks Contiguous.maskAuth
  have q₁ := he.perm.wR (show 200+8≤2560 by decide)
  have q₂ := he.perm.wR (show 208+8≤2560 by decide)
  obtain ⟨s₁, run₁, h12, hbp, hbx, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa authReload s = some s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 (x.length % 16) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [authReload,he.r15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hdat]
    · simp [gpr_setReg, hlen]
    · simp [gpr_setReg, hx16]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁,run₁,?_⟩)
  have he₁ := he.keep (s':=s₁) (fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have ai : AbsIn Ctx (W+16#64) W SP 16 H x D n s₁ := ⟨he₁,h12,hbp,hbx,hd.of_eq hrd₁ hwr₁,hm₁ ▸ hH⟩
  refine WP.seq ((WP.with_rdwr (absorbPad_ok v L (.inr rfl) ai hx16)).mono fun u ⟨ad,ru,wu⟩ => ?_)
  obtain ⟨m,fa,ft⟩ := ad.frame
  have fw := (absFrame_one fa).trans (tFrame_one ft)
  have f : Frame (oneFrame W D SP n) s.mem u.mem := hm₁ ▸ wFrame_one (o:=0) (.inl rfl) (wFrame_cons fw)
  have kp (d) (lo : 128≤d) (hi : d+8≤216) := f.readW (w:=64) (r:=⟨W+BitVec.ofNat 64 d,8⟩)
    (Region.contains_self _ _) (kept_oneFrame L hd.w (.inl ⟨lo,hi⟩)) (by decide)
  have q₄ := ad.env.perm.wR (show 184+8≤2560 by decide)
  have q₅ := ad.env.perm.wR (show 192+8≤2560 by decide)
  obtain ⟨b,rn,bx,bp,gb,mb,rb,wb⟩ : ∃ b,runBlock isa authLens u=some b ∧
      b.gpr .rbx=BitVec.ofNat 64 al ∧ b.gpr .rbp=BitVec.ofNat 64 N ∧
      (∀ r, r≠.rbx → r≠.rbp → b.gpr r=u.gpr r) ∧ b.mem=u.mem ∧ b.rd=u.rd ∧ b.wr=u.wr := by
    refine ⟨_,by xrun [authLens,ad.env.r15,q₄,q₅],?_,?_,?_,?_,?_,?_⟩
    · simp [gpr_setReg,kp 184 (by decide) (by decide),hal]
    · simp [gpr_setReg,kp 192 (by decide) (by decide),htl]
    · intro r a b;simp [gpr_setReg,a,b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨b,rn,?_⟩)
  have eb := ad.env.keep (s':=b) (fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact gb _ (by decide) (by decide)) rb wb
  refine WP.seq ((WP.with_rdwr (lens_ok v L (yo:=16) (.inr rfl) eb (mb ▸ ad.hH))).mono fun q ⟨⟨eq,_,yl,fq⟩,rq,wq⟩ => ?_)
  refine (mixMasks_ok eq).mono fun t ⟨et,rt,wt,ff,mix⟩ => ?_
  have hw := (ad.abs (hm₁ ▸ habs)).whole_eq (by simp only [List.length_append,Proof.Gcm.length_zeros];exact Proof.Gcm.length_pad_mod _)
  have aa : ∀ z ∈ absFrame (W+16#64) W SP 16,(⟨W+256#64,16⟩ : Region).Disjoint z := by
    intro z hz;simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl
    · exact (L.st_w (by decide) (.inr ⟨by decide,by decide⟩)).symm
    · exact (L.st_w (by decide) (.inr ⟨by decide,by decide⟩)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm
  have tt : ∀ z ∈ tFrame (W+16#64) W SP 16,(⟨W+256#64,16⟩ : Region).Disjoint z := by
    intro z hz;simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl
    · exact (L.st_w (by decide) (.inr ⟨by decide,by decide⟩)).symm
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm
  rw [mb] at fq yl
  rw [bx,bp,toNat_ofNat_of_lt hN,BitVec.toNat_ofNat,lensBlock_mod_left,hw,hm₁] at yl
  rw [yl,blockAt_frame fq tt,blockAt_frame ft tt,blockAt_frame fa aa,hm₁] at mix
  rw [hm₁] at fw
  refine ⟨et,rt.trans (rq.trans (rb.trans (ru.trans hrd₁))),wt.trans (wq.trans (wb.trans (wu.trans hwr₁))),?_,mix⟩
  exact ((fw.trans (tFrame_one fq)).mono (fun r hr => List.mem_cons_of_mem _ hr)).trans
    (ff.mono fun r hr => by obtain rfl := List.mem_singleton.mp hr;exact List.mem_cons_self ..)

open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (inc32)
open VG.Proof.Gcm (xorKs padded)

theorem pairApart {p W SP : Addr} {k : Nat} (work : (⟨p,k⟩ : Region).Disjoint ⟨W,2560⟩)
    (stack : (⟨p,k⟩ : Region).Disjoint (below SP 8)) : ∀ z ∈ pairFrame W SP,(⟨p,k⟩ : Region).Disjoint z := by
  intro z hz;simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl
  · exact work.sub_right (Lay.wSub (by decide))
  · exact work.sub_right (Lay.wSub (by decide))
  · exact stack

theorem pairLow {Ctx W SP : Addr} (L : Lay Ctx (W+16#64) W SP) (i k : Nat) (hi : i+k≤256) :
    ∀ z ∈ pairFrame W SP,(⟨W+BitVec.ofNat 64 i,k⟩ : Region).Disjoint z := by
  intro z hz;simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl
  · exact Offset.disjoint W (.inl hi) (by omega_using [hi]) (by decide)
  · exact Offset.disjoint W (.inl (by omega_using [hi])) (by omega_using [hi]) (by decide)
  · exact (L.stk_w (by omega_using [hi])).symm

theorem pairOne {W D SP : Addr} {n : Nat} {m m' : Mem} (f : Frame (pairFrame W SP) m m') :
    Frame (oneFrame W D SP n) m m' := f.sub fun z hz => by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl
  · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_,by simp,fun _ h => h⟩

abbrev scalarMasks (v : GcmImpl) := Contiguous.finishMasks v.callees Contiguous.maskAES

/-- One postcondition for both layouts, from the end of the bulk loop through tag generation. -/
theorem scalarMasks_ok (v : GcmImpl) {M : CtxMode} : FinishOk M (scalarMasks v) := by
  intro Ctx W SP S D R n al s u H icb a reg ob post bulk hH hcb hal habs slot src _ _ _ _ _
  let off := 16*(n/16)
  let r := n-off
  have le : off≤n := Nat.mul_div_le _ _
  have hr : r<16 := by dsimp [r,off];omega
  have eo : n-r=off := by dsimp [r];omega
  have er : n%16=r := by dsimp [r,off];omega
  have ha : (a++zeros (padLen a.length)).length%16=0 := by
    simp only [List.length_append,Proof.Gcm.length_zeros];exact Proof.Gcm.length_pad_mod _
  obtain ⟨fr,rounds,hkey,ck,j,pre,count,abs,rem⟩ := ob_factsFrom reg.lay ob reg.sW reg.ks reg.sD
    post.frame hH hcb habs ha bulk.1 bulk.2.1 (Z:=bytesAt u.mem D off) (by rw [length_bytesAt];dsimp [off];omega)
    (by rw [bulk.2.2];change ghashFrom (blockAt s.mem (Ctx+240#64)) _ _=_;rw [hH,Proof.Gcm.blocksAt_eq];rfl)
  have slen : u.mem.readW (W+208#64) 64=BitVec.ofNat 64 r := er ▸ post.len
  have la := (fr.readW (w:=64) (r:=⟨W+184#64,8⟩) (Region.contains_self _ _)
      (kept_oneFrameB reg.lay reg.data.ok.w ob.t_w (.inl ⟨by decide,by decide⟩)) (by decide)).trans hal
  have hd := (reg.data.of_eq post.rd post.wr).drop le
  have hs := ((inputData reg).of_eq post.rd post.wr).drop le
  have lay : S+BitVec.ofNat 64 off=D+BitVec.ofNat 64 off ∨
      (⟨S+BitVec.ofNat 64 off,r⟩ : Region).Disjoint ⟨D+BitVec.ofNat 64 off,r⟩ := by
    rcases reg.sD with eq|apart
    · exact .inl (by rw [eq])
    · exact .inr ((apart.sub_left (Offset.sub_base _ (by dsimp [r];omega))).sub_right (Offset.sub_base _ (by dsimp [r];omega)))
  unfold scalarMasks Contiguous.finishMasks
  refine WP.seq ((scalarArgs_ok post.env (by rw [post.rd,post.wr];exact slot) src post.tlen slen post.dat (Nat.sub_le ..)).mono
    fun x ⟨px,dx,nx,ex,mx,rx,wx⟩ => ?_)
  rw [eo] at px
  refine WP.seq ((makeMasks_ok reg.lay ex (mx ▸ rounds)).mono fun b ⟨eb,gb,rb,wb,fb,jb,cb⟩ => ?_)
  rw [mx] at fb jb cb
  have br := rb.trans rx
  have bw := wb.trans wx
  have ctx := pairApart (W:=W) (SP:=SP) reg.lay.cw' reg.lay.kc.symm
  have spos := pairApart hs.w hs.stk.symm
  have sorig := bytesAt_frame fb spos (Nat.le_of_lt hs.lt)
  refine WP.seq ((maskXor_ok eb ((gb _ (by decide)).trans px) ((gb _ (by decide)).trans dx)
    ((gb _ (by decide)).trans nx) hr (hs.of_eq br bw) (hd.of_eq br bw) lay).mono fun t ⟨et,rt,wt,ft,xt⟩ => ?_)
  let F := fun {p k} (dis : (⟨p,k⟩ : Region).Disjoint ⟨D+BitVec.ofNat 64 off,r⟩) =>
    fun z (hz : z ∈ [(⟨D+BitVec.ofNat 64 off,r⟩ : Region)]) => (List.mem_singleton.mp hz).symm ▸ dis
  have base (i k : Nat) (hi : i+k≤256) : ∀ z ∈ [(⟨D+BitVec.ofNat 64 off,r⟩ : Region)],
      (⟨W+BitVec.ofNat 64 i,k⟩ : Region).Disjoint z :=
    F ((hd.ok.w.sub_right (Lay.wSub (by omega_using [hi]))).symm)
  have low (i : Nat) (hi : i+8≤256) : t.mem.readW (W+BitVec.ofNat 64 i) 64 = u.mem.readW (W+BitVec.ofNat 64 i) 64 :=
    (ft.readW (Region.contains_self _ _) (base i 8 hi) (by decide)).trans
      (fb.readW (Region.contains_self _ _) (pairLow reg.lay i 8 hi) (by decide))
  have hash : blockAt t.mem (Ctx+240#64)=H := (blockAt_frame ft (F (hd.ctx.sub_left (Lay.ctxSub (by decide))))).trans
     ((blockAt_frame fb (fun z hz => (ctx z hz).sub_left (Lay.ctxSub (by decide)))).trans hkey)
  have yk (d k : Nat) (hdk : d+k≤80) : ∀ z ∈ pairFrame W SP,
      (⟨(W+16#64)+BitVec.ofNat 64 d,k⟩ : Region).Disjoint z := by
    rw [add_ofNat_assoc];exact pairLow reg.lay (16+d) k (by omega_using [hdk])
  have yy (d k : Nat) (hdk : d+k≤80) := F ((hd.ok.st.sub_right (Lay.stSub hdk)).symm)
  have ax := abs.congr ((blockAt_frame ft (yy 16 16 (by decide))).trans (blockAt_frame fb (yk 16 16 (by decide))))
    ((bytesAt_frame ft (yy 32 _ (by have h := Nat.mod_lt (a++zeros (padLen a.length)++bytesAt u.mem D off).length (by decide : 0<16);omega)) (by omega_arith)).trans
      (bytesAt_frame fb (yk 32 _ (by have h := Nat.mod_lt (a++zeros (padLen a.length)++bytesAt u.mem D off).length (by decide : 0<16);omega)) (by omega_arith)))
  have hx : (a++zeros (padLen a.length)++bytesAt u.mem D off).length%16=0 := by
    rw [List.length_append,length_bytesAt];dsimp [off];omega
  refine (authMasks_ok v reg.lay et hash hx ((low 200 (by decide)).trans post.dat) ((low 208 (by decide)).trans slen)
    ((low 192 (by decide)).trans post.tlen) reg.data.ok.lt ((low 184 (by decide)).trans la)
    (hd.ok.of_eq (rt.trans br) (wt.trans bw)) ax).mono fun z ⟨ez,rz,wz,fz,tag⟩ => ?_
  have mk : blockAt t.mem (W+256#64)=ciphOf s.mem Ctx R (blockAt s.mem (W+16#64)) :=
    (blockAt_frame ft (F ((hd.ok.w.sub_right (Lay.wSub (by decide))).symm))).trans (by rw [jb,ck,j])
  have hc := FastOpen.ctr_tailK count (by omega) cb (d:=bytesAt b.mem (S+BitVec.ofNat 64 off) r)
    (by rw [length_bytesAt];exact hr)
  rw [length_bytesAt] at hc
  rw [xorBytes,hc,sorig,rem,ck] at xt
  have lt := reg.data.ok.lt
  have pref : bytesAt t.mem D off=bytesAt u.mem D off := (bytesAt_frame ft (F (by
    simpa using Offset.disjoint D (d:=0) (n:=off) (e:=off) (k:=r) (.inl (by omega)) (by omega_using [le,lt]) (by dsimp [r];omega_using [lt]))) (by omega_using [le,lt])).trans
    (bytesAt_frame fb (pairApart ((reg.data.take le).ok.w) ((reg.data.take le).ok.stk.symm)) (by omega_using [le,lt]))
  have split (m : Mem) (p : Addr) : bytesAt m p n=bytesAt m p off++bytesAt m (p+BitVec.ofNat 64 off) r := by
    rw [← bytesAt_add];congr 1;dsimp [r];omega
  have same : bytesAt z.mem D n=bytesAt t.mem D n := bytesAt_frame fz (fun q hq => by
    simp only [wFrame,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl
    · exact reg.data.ok.w.sub_right (Region.sub_prefix (by decide))
    · exact reg.data.ok.w.sub_right (Lay.wSub (by decide))
    · exact reg.data.ok.w.sub_right (Lay.wSub (by decide))
    · exact reg.data.ok.w.sub_right (Lay.wSub (by decide))
    · exact reg.data.ok.stk.symm) (Nat.le_of_lt lt)
  have cipher : bytesAt z.mem D n=xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem S n) := by
    rw [same,split t.mem D,split s.mem S,pref,pre,xt,Proof.Gcm.xorKs_append,length_bytesAt,Nat.zero_add]
  have cat : a++zeros (padLen a.length)++bytesAt u.mem D off++bytesAt t.mem (D+BitVec.ofNat 64 off) r =
      a++zeros (padLen a.length)++bytesAt z.mem D n := by rw [same,split t.mem D,pref,List.append_assoc]
  rw [cat,padded_eq,mk] at tag
  have fT : Frame (oneFrame W (D+BitVec.ofNat 64 off) SP r) b.mem t.mem := ft.mono fun q hq => by
    obtain rfl := List.mem_singleton.mp hq;exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  refine ⟨ez,rz.trans (rt.trans (br.trans post.rd)),wz.trans (wt.trans (bw.trans post.wr)),
    fr.trans ((oneFrame_B le (pairOne fb)).trans ((oneFrame_B le fT).trans
      (oneFrame_B (n:=n) (k:=0) (Nat.zero_le _) (by simpa using wFrame_one (D:=D) (n:=n) (o:=0) (.inl rfl) (by simpa using fz))))),
    cipher,?_⟩
  rw [Short.bytesAt_toBytes',tag]


open VG.Proof.AesOcb.X86_64 (blk_rel)
open Short (rel_env_regs rel_next)
theorem makeMasks_rel {Ctx W SP : Addr} {R : Nat} (L : Lay Ctx (W+16#64) W SP) :
    let F (s : State) := Env Ctx (W+16#64) W SP s ∧ RoundsAt s.mem W R
    RelCT isa (fun s t => F s ∧ F t) makeMasks (fun _ _ => True) := by
  let F (s : State) := Env Ctx (W+16#64) W SP s ∧ RoundsAt s.mem W R
  let C (s : State) := BCall s Ctx (W+256#64) (W+512#64) R 2 ∧ s.gpr .rsp=SP
  have prep (s) (h : F s) : WP isa (.block (copyMask 0 256 ++ copyMask 48 272 ++ pairArgs)) s C := by
    rw [WP.block_append_iff,WP.block_append_iff]
    refine (copyMask_ok h.1 0 256 (by decide) (by decide)).mono fun a ⟨ea,_,_,_,fa,_⟩ => ?_
    refine (copyMask_ok ea 48 272 (by decide) (by decide)).mono fun b ⟨eb,_,_,_,fb,_⟩ => ?_
    have rr : RoundsAt b.mem W R := ⟨(fb.readW (r:=⟨W+176#64,8⟩) (Region.contains_self _ _) (by
      intro q h;obtain rfl := List.mem_singleton.mp h;exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide)).trans
      ((fa.readW (r:=⟨W+176#64,8⟩) (Region.contains_self _ _) (by
      intro q h;obtain rfl := List.mem_singleton.mp h;exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide)).trans h.2.1),h.2.2⟩
    exact (pairArgs_ok L eb rr).mono fun _ ⟨call,_,_,_,g⟩ => ⟨call,(g _ (by decide)).trans eb.rsp⟩
  unfold makeMasks Contiguous.makeMasks
  apply RelCT.seq (rel_next (rel_env_regs [] (fun _ (h : F _) => h.1) (fun _ (h : F _) => h.1)
    (fun _ _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩) prep prep)
  let aes := Proof.Aes.X86_64.BlocksImpl.scalar
  exact blk_rel aes.encOk aes.encCt (fun _ _ h => ⟨_,_,_,_,_,h.1.1,h.2.1,h.1.2.trans h.2.2.symm⟩)

theorem authMasks_rel (v : GcmImpl) {Ctx W SP D : Addr} {R al n N : Nat} (L : Lay Ctx (W+16#64) W SP)
    (dw : (⟨D,n⟩ : Region).Disjoint ⟨W,2560⟩) :
    let T := OneT Ctx W SP R al D n N
    RelCT isa (fun s t => T s ∧ T t) (authMasks v) (fun _ _ => True) := by
  let T := OneT Ctx W SP R al D n N
  let A (s : State) := T s ∧ s.gpr .r12 = D ∧ s.gpr .rbp=BitVec.ofNat 64 n ∧ s.gpr .rbx=0
  have a (s) (h : T s) : WP isa (.block authReload) s A :=
    load2T_ok h h.dat h.len (h.env.perm.wR (show 200+8≤2560 by decide)) (h.env.perm.wR (show 208+8≤2560 by decide))
  have ai (s) (h : A s) : AbsIn Ctx (W+16#64) W SP 16 (blockAt s.mem (Ctx+240#64)) [] D n s :=
    ⟨h.1.env,h.2.1,h.2.2.1,h.2.2.2,h.1.dD,rfl⟩
  have aw (s) (h : A s) : WP isa (absorbPad v.callees 16) s T :=
    (WP.with_rdwr (absorbPad_ok v L (.inr rfl) (ai s h) rfl)).mono fun _ ⟨o,rd,wr⟩ => by
      obtain ⟨_,fa,ft⟩ := o.frame
      exact h.1.frame L o.env rd wr dw (w_one ((absFrame_one fa).trans (tFrame_one ft)))
  have ar : RelCT isa (fun x y => A x ∧ A y) (absorbPad v.callees 16) (fun _ _ => True) :=
    (RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
      absorbPad_rel v L (.inr rfl) (H₁ := H₁) (H₂ := H₂) (x₁ := []) (x₂ := []) (D := D) (n := n) rfl rfl).mono
        (fun _ _ h => ⟨_,_,ai _ h.1,ai _ h.2⟩) fun _ _ h => h
  let B (s : State) := T s ∧ s.gpr .rbx=BitVec.ofNat 64 al ∧ s.gpr .rbp=BitVec.ofNat 64 N
  have lensPrep (s) (h : T s) : WP isa (.block authLens) s B := by
    have q₁ := h.env.perm.wR (show 184+8≤2560 by decide)
    have q₂ := h.env.perm.wR (show 192+8≤2560 by decide)
    obtain ⟨u,rn,bx,bp,gu,mu,ru,wu⟩ : ∃ u,runBlock isa authLens s=some u ∧
        u.gpr .rbx=BitVec.ofNat 64 al ∧ u.gpr .rbp=BitVec.ofNat 64 N ∧
        (∀ r,r≠.rbx → r≠.rbp → u.gpr r=s.gpr r) ∧ u.mem=s.mem ∧ u.rd=s.rd ∧ u.wr=s.wr := by
      refine ⟨_,by xrun [authLens,h.env.r15,q₁,q₂],?_,?_,?_,?_,?_,?_⟩
      · simp [gpr_setReg,h.alen]
      · simp [gpr_setReg,h.tlen]
      · intro r a b;simp [gpr_setReg,a,b]
      all_goals rfl
    exact WP.of_runBlock ⟨u,rn,h.keep (fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl <;> exact gu _ (by decide) (by decide)) mu ru wu,bx,bp⟩
  have lr : RelCT isa (fun x y => B x ∧ B y) (lens v.callees 16) (fun _ _ => True) :=
    (lens_rel v L (.inr rfl)).mono (fun _ _ ⟨l,r⟩ => ⟨l.1.env,r.1.env,fun z hz => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl
      · rw [l.2.1,r.2.1]
      · rw [l.2.2,r.2.2]⟩) fun _ _ h => h
  have lw (s) (h : B s) : WP isa (lens v.callees 16) s (Env Ctx (W+16#64) W SP ·) :=
    (lens_ok v L (.inr rfl) h.1.env (H:=blockAt s.mem (Ctx+240#64)) rfl).mono fun _ v => v.1
  unfold authMasks Contiguous.maskAuth
  refine RelCT.seq (rel_next (rel_env_regs [] (fun _ (h : T _) => h.env) (fun _ (h : T _) => h.env) (fun _ _ _ _ _ h => by cases h)
    ⟨_,by taint_decide⟩) a a) (RelCT.seq (rel_next ar aw aw) (RelCT.seq (rel_next (rel_env_regs [] (fun _ (h : T _) => h.env)
    (fun _ (h : T _) => h.env) (fun _ _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩) lensPrep lensPrep) (RelCT.seq (rel_next lr lw lw) ?_)))
  exact rel_env_regs [] (fun _ h => h) (fun _ h => h) (fun _ _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩


structure MaskLive (Ctx W SP S D : Addr) (R al n r : Nat) (s : State) : Prop where
  tag : OneT Ctx W SP R al D r n s
  src : s.gpr .rbx=S
  dst : s.gpr .r12=D
  len : s.gpr .rbp=BitVec.ofNat 64 r
  input : DataOk (W+16#64) W SP s S r
  output : DataW Ctx (W+16#64) W SP s D r
  alias : S=D ∨ (⟨S,r⟩ : Region).Disjoint ⟨D,r⟩

theorem scalarMasks_ct (v : GcmImpl) {M : CtxMode} : FinishCT M (scalarMasks v) := by
  intro Ctx W SP S D R n al L _ dw
  let r := n%16
  let tail := D+BitVec.ofNat 64 (16*(n/16))
  let src := S+BitVec.ofNat 64 (n-r)
  let P := MaskLive Ctx W SP src tail R al n r
  let T := OneT Ctx W SP R al tail r n
  have dt : (⟨tail,r⟩ : Region).Disjoint ⟨W,2560⟩ := dw.sub_left (Offset.sub_base _ (by dsimp [r];omega))
  have setup (s) (after : AfterBulk M Ctx W SP S D R n al s) : WP isa (.block tailSetup) s P := by
    have h := after.scalar
    refine (scalarArgs_ok h.tag.env h.slot h.src h.tag.tlen h.tag.len h.tag.dat (Nat.mod_le ..)).mono
      fun t ⟨p,d,l,e,m,rd,wr⟩ => ?_
    exact ⟨⟨e,m ▸ h.tag.rounds,m ▸ h.tag.alen,m ▸ h.tag.dat,m ▸ h.tag.len,h.tag.dD.of_eq rd wr,m ▸ h.tag.tlen⟩,
      p,d,l,h.input.of_eq rd wr,h.output.of_eq rd wr,h.alias⟩
  have prep (s) (h : P s) : WP isa makeMasks s P :=
    (makeMasks_ok L h.tag.env h.tag.rounds).mono fun t ⟨e,g,rd,wr,frame,_,_⟩ =>
      ⟨h.tag.frame L e rd wr dt (pairOne frame),(g _ (by decide)).trans h.src,
        (g _ (by decide)).trans h.dst,(g _ (by decide)).trans h.len,h.input.of_eq rd wr,h.output.of_eq rd wr,h.alias⟩
  have tailw (s) (h : P s) : WP isa maskXor s T :=
    (maskXor_ok h.tag.env h.src h.dst h.len (Nat.mod_lt _ (by decide)) h.input h.output h.alias).mono fun t ⟨e,rd,wr,frame,_⟩ =>
      h.tag.frame L e rd wr dt (frame.mono fun q hq => by
        obtain rfl := List.mem_singleton.mp hq;exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  have tailCT : RelCT isa (fun a b => P a ∧ P b) maskXor (fun _ _ => True) := by
    apply rel_env_regs [.rbx,.r12,.rbp] (fun _ h => h.tag.env) (fun _ h => h.tag.env) _ ⟨_,by taint_decide⟩
    intro a b p q z hz;simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl
    · rw [p.src,q.src]
    · rw [p.dst,q.dst]
    · rw [p.len,q.len]
  unfold scalarMasks Contiguous.finishMasks
  exact RelCT.seq (rel_next (rel_env_regs [] (fun _ h => h.scalar.tag.env) (fun _ h => h.scalar.tag.env)
    (fun _ _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩) setup setup)
    (RelCT.seq (rel_next ((makeMasks_rel L).mono (fun _ _ ⟨l,r⟩ => ⟨⟨l.tag.env,l.tag.rounds⟩,r.tag.env,r.tag.rounds⟩) (fun _ _ h => h)) prep prep)
      (RelCT.seq (rel_next tailCT tailw tailw) (authMasks_rel v L dt)))

theorem masksRecord_ok (v : GcmImpl) (ctr : Proof.Aes.X86_64.Ctr32ToImpl) {M : CtxMode} :
    RecordOk M (Contiguous.masksBody v.callees ⟨ctr.callee.name,ctr.callee.code⟩ Contiguous.maskAES) := by
  intro o u Ctx W SP Np A S D nl al n C X geo wrap src dst E hp hl ha
  have bulk : BulkOk M (Contiguous.bulk (Contiguous.separate ⟨ctr.callee.name,ctr.callee.code⟩ v.callees.gh)) :=
    fun h ob a b c => separate_bulk_ok ctr v.gh h ob a b c
  exact body_ok bulk (scalarMasks_ok v) C X geo wrap ha src dst (oneMid_ok v C E hp hl ha)

theorem masksRecord_ct (v : GcmImpl) (ctr : Proof.Aes.X86_64.Ctr32ToImpl) {M : CtxMode} :
    RecordCT M (Contiguous.masksBody v.callees ⟨ctr.callee.name,ctr.callee.code⟩ Contiguous.maskAES) := by
  intro o p Ctx W SP Np A S D nl al n R a b
  have bulk : BulkOk M (Contiguous.bulk (Contiguous.separate ⟨ctr.callee.name,ctr.callee.code⟩ v.callees.gh)) :=
    fun h ob a b c => separate_bulk_ok ctr v.gh h ob a b c
  exact RelCT.seq (ordinaryAad_ct v a b) (run_ct bulk (separate_ct ctr v.gh) (separate_keeps ctr v.gh)
    (scalarMasks_ct v) a.ctx.lay (a.rounds ▸ a.ctx.rounds) a.ctx.dE)

end VG.Proof.AesGcm.X86_64.ContiguousSeal
