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
import VerifiedGarbage.Proof.Aes.X86_64.Ctr32
import VerifiedGarbage.Proof.Framework.AddrArith
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
open VG.Impl.AesGcm.X86_64.Contiguous (copyMask maskArgs mixMasks maskXor authReload authLens)
open VG.Spec.Gcm (blockAt)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes
open VG.Proof.AesOcb.X86_64 (BCall BPost blk_call)

/-- The existing AES block entry may write the two mask slots and its own scratch. -/
theorem encmask_call_args {s : State} {Ctx W SP : Addr} {R : Nat} (k : Nat) (small : k=1 ∨ k=2) (L : Lay Ctx (W+16#64) W SP)
    (e : Env Ctx (W+16#64) W SP s) (rr : R=10 ∨ R=12 ∨ R=14)
    (di : s.gpr .rdi=Ctx) (si : s.gpr .rsi=BitVec.ofNat 64 R)
    (dx : s.gpr .rdx=W+256#64) (cx : s.gpr .rcx=BitVec.ofNat 64 k) (r8 : s.gpr .r8=W+512#64) :
    BCall s Ctx (W+256#64) (W+512#64) R k := by
  rcases small with rfl|rfl <;> (
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
  · exact covers_cons (e.perm.wC (by decide)) (e.perm.wC (by decide)))

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

theorem maskArgs_ok {s : State} {Ctx W SP : Addr} {R : Nat}
    (k : Nat) (small : k=1 ∨ k=2) (L : Lay Ctx (W+16#64) W SP) (e : Env Ctx (W+16#64) W SP s) (rr : RoundsAt s.mem W R) :
    WP isa (.block (maskArgs k)) s fun t => BCall t Ctx (W+256#64) (W+512#64) R k ∧
      t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ (∀ r ∈ calleeSaved, t.gpr r=s.gpr r) := by
  have rd := e.perm.wR (show 176+8≤2560 by decide)
  unfold maskArgs
  obtain ⟨t,rn,di,si,dx,cx,r8,mem,dr,dw,saved⟩ :
      ∃ t, runBlock isa ([.mov .rdi (.reg .r13),.mov .rsi (.mem (at_ .r15 roundsO))] ++ ptr .rdx .r15 256 ++
        [.mov32 .rcx (imm k)] ++ ptr .r8 .r15 scrO) s = some t ∧
      t.gpr .rdi=Ctx ∧ t.gpr .rsi=BitVec.ofNat 64 R ∧ t.gpr .rdx=W+256#64 ∧
      t.gpr .rcx=BitVec.ofNat 64 k ∧ t.gpr .r8=W+512#64 ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r=s.gpr r) := by
    refine ⟨_,by xrun [e.r13,e.r15,roundsO,scrO,rd,ptr],?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals try rfl
    all_goals try (simp [gpr_setReg,rr.1];done)
    · rcases small with rfl|rfl <;> rfl
    · intro r h;simp only [calleeSaved,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [gpr_setReg]
  exact WP.of_runBlock ⟨t,rn,encmask_call_args k small L (e.of_saved saved dr dw) rr.2 di si dx cx r8,mem,dr,dw,saved⟩


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
  refine (maskArgs_ok 2 (.inr rfl) L eb rr').mono fun v ⟨args,mv,rv,wv,gv⟩ => ?_
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
  have prep (s) (h : F s) : WP isa (.block (copyMask 0 256 ++ copyMask 48 272 ++ maskArgs 2)) s C := by
    rw [WP.block_append_iff,WP.block_append_iff]
    refine (copyMask_ok h.1 0 256 (by decide) (by decide)).mono fun a ⟨ea,_,_,_,fa,_⟩ => ?_
    refine (copyMask_ok ea 48 272 (by decide) (by decide)).mono fun b ⟨eb,_,_,_,fb,_⟩ => ?_
    have rr : RoundsAt b.mem W R := ⟨(fb.readW (r:=⟨W+176#64,8⟩) (Region.contains_self _ _) (by
      intro q h;obtain rfl := List.mem_singleton.mp h;exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide)).trans
      ((fa.readW (r:=⟨W+176#64,8⟩) (Region.contains_self _ _) (by
      intro q h;obtain rfl := List.mem_singleton.mp h;exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide)).trans h.2.1),h.2.2⟩
    exact (maskArgs_ok 2 (.inr rfl) L eb rr).mono fun _ ⟨call,_,_,_,g⟩ => ⟨call,(g _ (by decide)).trans eb.rsp⟩
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

private theorem maskChoice_step {s u : State} {Ctx W SP D : Addr} {n : Nat} (p : ObPost Ctx W SP D n s u) :
    ∃ t, runBlock isa [.mov .rax (.mem (at_ .r15 lenO)),.alu .test .rax (.reg .rax)] u=some t ∧
      t.zf=some (decide (n%16=0)) ∧ t.mem=u.mem ∧ ObPost Ctx W SP D n s t := by
  have read := p.env.perm.wR (show 208+8≤2560 by decide)
  have hr : n%16<16 := Nat.mod_lt _ (by decide)
  obtain ⟨t,run,zf,g,m,rd,wr⟩ : ∃ t, runBlock isa [.mov .rax (.mem (at_ .r15 lenO)),.alu .test .rax (.reg .rax)] u=some t ∧
      t.zf=some (decide (n%16=0)) ∧ (∀ r,r≠.rax → t.gpr r=u.gpr r) ∧ t.mem=u.mem ∧ t.rd=u.rd ∧ t.wr=u.wr := by
    refine ⟨_,by xrun [p.env.r15,read,p.len],?_,?_,?_,?_,?_⟩
    · simp only [zf_arithFlags]; exact congrArg some (and_self_beq (by omega_using [hr]))
    · intro r hr;simp [gpr_setReg,hr]
    all_goals rfl
  exact ⟨t,run,zf,m,p.env.keep (fun r hr => g _ (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> decide)) rd wr,rd.trans p.rd,wr.trans p.wr,m ▸ p.frame,m ▸ p.tlen,m ▸ p.dat,m ▸ p.len⟩

theorem oneMask_ok {Ctx W SP : Addr} {R : Nat} {s : State} (L : Lay Ctx (W+16#64) W SP)
    (e : Env Ctx (W+16#64) W SP s) (rr : RoundsAt s.mem W R) :
    WP isa (Contiguous.oneMask Contiguous.maskAES) s fun t => Env Ctx (W+16#64) W SP t ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      Frame (pairFrame W SP) s.mem t.mem ∧ blockAt t.mem (W+256#64)=ciphOf s.mem Ctx R (blockAt s.mem (W+16#64)) := by
  unfold Contiguous.oneMask
  apply WP.seq
  rw [WP.block_append_iff]
  refine (copyMask_ok e 0 256 (by decide) (by decide)).mono fun a ⟨ea,_,ra,wa,fa,ha⟩ => ?_
  have dis (i : Nat) (h : i+8≤256) : ∀ z ∈ [(⟨W+256#64,16⟩ : Region)],(⟨W+BitVec.ofNat 64 i,8⟩ : Region).Disjoint z := by
    intro q hq;obtain rfl := List.mem_singleton.mp hq;exact Offset.disjoint W (.inl h) (by omega) (by decide)
  have rr' : RoundsAt a.mem W R := ⟨(fa.readW (r:=⟨W+176#64,8⟩) (Region.contains_self _ _) (dis 176 (by decide)) (by decide)).trans rr.1,rr.2⟩
  have key := ciph_frame fa (by intro q hq;obtain rfl := List.mem_singleton.mp hq;exact L.cw'.sub_right (Lay.wSub (by decide))) rr.2
  refine (maskArgs_ok 1 (.inl rfl) L ea rr').mono fun b ⟨args,mb,rb,wb,gb⟩ => ?_
  let aes := Proof.Aes.X86_64.BlocksImpl.scalar
  refine (blk_call (name:=aes.enc.name) aes.encOk aes.encNosp aes.encDepth args).mono fun t enc => ?_
  have out := enc.enc (i:=0) (by decide)
  change blockAt t.mem ((W+256#64)+0#64)=ciphOf b.mem Ctx R (blockAt b.mem ((W+256#64)+0#64)) at out
  simp only [BitVec.add_zero,mb,key,ha] at out
  have sp := (gb _ (by decide : Reg.rsp ∈ calleeSaved)).trans ea.rsp
  have f := enc.frame
  rw [sp,mb] at f
  refine ⟨(ea.of_saved gb rb wb).of_saved enc.saved enc.rd enc.wr,enc.rd.trans (rb.trans ra),enc.wr.trans (wb.trans wa),?_,?_⟩
  · refine (fa.sub ?_).trans (f.sub ?_)
    · intro z h; obtain rfl := List.mem_singleton.mp h; exact ⟨_,List.mem_cons_self ..,Region.sub_prefix (by decide)⟩
    · intro z h; simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl
      · exact ⟨_,List.mem_cons_self ..,Region.sub_prefix (by decide)⟩
      · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_self ..),fun _ h => h⟩
      · exact ⟨_,by simp,fun _ h => h⟩
  · simpa only [BitVec.add_zero] using out

theorem keepLensRounds {Ctx W SP : Addr} {R : Nat} {a b : Mem} (L : Lay Ctx (W+16#64) W SP)
    (fr : Frame (tFrame (W+16#64) W SP 16) a b) (rr : RoundsAt a W R) : RoundsAt b W R :=
  rounds_frame fr (fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact (L.st_w (by decide) (.inr ⟨by decide,by decide⟩)).symm
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm) rr

theorem directEcbTag_ok (v : GcmImpl) {Ctx W SP : Addr} {R : Nat} {s : State} {H : Block}
    (L : Lay Ctx (W+16#64) W SP) (e : Env Ctx (W+16#64) W SP s) (rr : RoundsAt s.mem W R)
    (hash : blockAt s.mem (Ctx+240#64)=H) : WP isa (Contiguous.directEcbTag v.callees Contiguous.maskAES) s fun t =>
      Env Ctx (W+16#64) W SP t ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ Frame (⟨W,16⟩::wFrame W SP) s.mem t.mem ∧
      bytesAt t.mem W 16=VG.Spec.Gcm.toBytes (ghashFrom H (blockAt s.mem (W+16#64+16#64))
        [VG.Spec.Gcm.ofBytes (lensBlock (s.gpr .rbx).toNat (s.gpr .rbp).toNat)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W+16#64))) := by
  refine WP.seq ((WP.with_rdwr (lens_ok v L (.inr rfl) e hash)).mono fun a ⟨⟨ea,_,y,fa⟩,ra,wa⟩ => ?_)
  have rr' := keepLensRounds L fa rr
  have jj : blockAt a.mem (W+16#64)=blockAt s.mem (W+16#64) := blockAt_frame fa (fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · simpa using L.st_st (a:=0) (n:=16) (d:=16) (k:=16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.st_w (a:=0) (n:=16) (d:=96) (k:=16) (by decide) (.inr ⟨by decide,by decide⟩)
    · simpa using L.st_w (a:=0) (n:=16) (d:=512) (k:=256) (by decide) (.inr ⟨by decide,by decide⟩)
    · simpa using (L.stk_st (a:=0) (n:=16) (by decide)).symm)
  have kk : ciphOf a.mem Ctx R=ciphOf s.mem Ctx R := ciph_frame fa (fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.kc.symm) rr.2
  refine WP.seq ((oneMask_ok L ea rr').mono fun b ⟨eb,rb,wb,fb,cb⟩ => ?_)
  refine (mixMasks_ok eb).mono fun t ⟨et,rt,wt,ft,mix⟩ => ?_
  have yy : blockAt b.mem (W+16#64+16#64)=blockAt a.mem (W+16#64+16#64) := by
    rw [show W+16#64+16#64=W+32#64 by rw [BitVec.add_assoc];rfl]
    exact blockAt_frame fb (pairLow L 32 16 (by decide))
  have bf : Frame (wFrame W SP) a.mem b.mem := fb.sub fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_,by simp,fun _ h => h⟩
  refine ⟨et,rt.trans (rb.trans ra),wt.trans (wb.trans wa),?_,?_⟩
  · exact (((tFrame_one fa).trans bf).mono fun r h => List.mem_cons_of_mem _ h).trans
      (ft.mono fun r h => by obtain rfl := List.mem_singleton.mp h;exact List.mem_cons_self ..)
  · rw [Short.bytesAt_toBytes',mix,yy,y,cb,kk,jj]


theorem oneMask_rel {Ctx W SP : Addr} {R : Nat} (L : Lay Ctx (W+16#64) W SP) :
    let F (s : State) := Env Ctx (W+16#64) W SP s ∧ RoundsAt s.mem W R
    RelCT isa (fun s t => F s ∧ F t) (Contiguous.oneMask Contiguous.maskAES) (fun _ _ => True) := by
  let F (s : State) := Env Ctx (W+16#64) W SP s ∧ RoundsAt s.mem W R
  let C (s : State) := BCall s Ctx (W+256#64) (W+512#64) R 1 ∧ s.gpr .rsp=SP
  have prep (s) (h : F s) : WP isa (.block (copyMask 0 256 ++ maskArgs 1)) s C := by
    rw [WP.block_append_iff]
    refine (copyMask_ok h.1 0 256 (by decide) (by decide)).mono fun a ⟨ea,_,_,_,fa,_⟩ => ?_
    have rr : RoundsAt a.mem W R := rounds_frame fa (fun z hz => by
      obtain rfl := List.mem_singleton.mp hz;exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) h.2
    exact (maskArgs_ok 1 (.inl rfl) L ea rr).mono fun _ ⟨call,_,_,_,g⟩ => ⟨call,(g _ (by decide)).trans ea.rsp⟩
  apply RelCT.seq (Short.rel_next (rel_env_regs [] (fun _ (h : F _) => h.1) (fun _ (h : F _) => h.1)
    (fun _ _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩) prep prep)
  let aes := Proof.Aes.X86_64.BlocksImpl.scalar
  exact VG.Proof.AesOcb.X86_64.blk_rel aes.encOk aes.encCt (fun _ _ h => ⟨_,_,_,_,_,h.1.1,h.2.1,h.1.2.trans h.2.2.symm⟩)
theorem directEcbTag_ct (v : GcmImpl) {Ctx W SP : Addr} {R n al : Nat} (L : Lay Ctx (W+16#64) W SP) :
    let F (s : State) := Env Ctx (W+16#64) W SP s ∧ RoundsAt s.mem W R ∧ s.gpr .rbx=BitVec.ofNat 64 al ∧ s.gpr .rbp=BitVec.ofNat 64 n
    RelCT isa (fun s t => F s ∧ F t) (Contiguous.directEcbTag v.callees Contiguous.maskAES) (fun _ _ => True) := by
  let F (s : State) := Env Ctx (W+16#64) W SP s ∧ RoundsAt s.mem W R ∧ s.gpr .rbx=BitVec.ofNat 64 al ∧ s.gpr .rbp=BitVec.ofNat 64 n
  let E (s : State) := Env Ctx (W+16#64) W SP s ∧ RoundsAt s.mem W R
  have sameLens : RelCT isa (fun s t => F s ∧ F t) (lens v.callees 16) (fun _ _ => True) := by
    apply (lens_rel v L (.inr rfl)).mono _ (fun _ _ h => h)
    intro s t h
    refine ⟨h.1.1,h.2.1,?_⟩
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · rw [h.1.2.2.1,h.2.2.2.1]
    · rw [h.1.2.2.2,h.2.2.2.2]
  have ln s (h : F s) : WP isa (lens v.callees 16) s E :=
    (lens_ok v L (.inr rfl) h.1 rfl).mono fun _ l => ⟨l.1,keepLensRounds L l.2.2.2 h.2.1⟩
  have mk s (h : E s) : WP isa (Contiguous.oneMask Contiguous.maskAES) s (Env Ctx (W+16#64) W SP ·) :=
    (oneMask_ok L h.1 h.2).mono fun _ m => m.1
  exact RelCT.seq (Short.rel_next sameLens ln ln) (RelCT.seq (Short.rel_next (oneMask_rel L) mk mk)
    (rel_env_regs [] (fun _ h => h) (fun _ h => h) (fun _ _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩))

private theorem tagArgs {Ctx W SP : Addr} {s : State} {al n : Nat}
    (e : Env Ctx (W+16#64) W SP s)
    (a : s.mem.readW (W+184#64) 64=BitVec.ofNat 64 al)
    (l : s.mem.readW (W+192#64) 64=BitVec.ofNat 64 n) :
    ∃ t,runBlock isa authLens s=some t ∧ Env Ctx (W+16#64) W SP t ∧
      t.gpr .rbx=BitVec.ofNat 64 al ∧ t.gpr .rbp=BitVec.ofNat 64 n ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  have ra := e.perm.wR (show 184+8≤2560 by decide)
  have rn := e.perm.wR (show 192+8≤2560 by decide)
  obtain ⟨t,run,g,bx,bp,m,rd,wr⟩ : ∃ t, runBlock isa authLens s=some t ∧ (∀ r,r≠.rbx → r≠.rbp → t.gpr r=s.gpr r) ∧
      t.gpr .rbx=BitVec.ofNat 64 al ∧ t.gpr .rbp=BitVec.ofNat 64 n ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr := by
    refine ⟨_,by xrun [authLens,e.r15,ra,rn],?_,?_,?_,?_,?_,?_⟩
    · intro r hr hb; simp [gpr_setReg,hr,hb]
    · simp [gpr_setReg,a]
    · simp [gpr_setReg,l]
    all_goals rfl
  exact ⟨t,run,e.keep (fun r hr => g _ (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> decide) (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> decide)) rd wr,bx,bp,m,rd,wr⟩

private theorem alignedTag_ok (v : GcmImpl) {M : CtxMode} {Ctx W SP S D : Addr} {R n al : Nat}
    {s u : State} {H icb : Block} {a : List Byte} (aligned : n%16=0)
    (reg : Split.SealRegions M Ctx W SP D S R n n s) (ob : ObPre M Ctx W SP R D n s)
    (post : ObPost Ctx W SP D n s u) (bulk : BlocksResult Ctx W R S D (n/16) s u)
    (hH : blockAt s.mem (Ctx+240#64)=H) (hcb : blockAt s.mem (cbA W)=icb)
    (hal : s.mem.readW (W+184#64) 64=BitVec.ofNat 64 al)
    (habs : Absorbed s.mem (yA W) (W+16#64+32#64) H (a++zeros (padLen a.length))) :
    WP isa (Contiguous.alignedTag v.callees Contiguous.maskAES) u (BodyPost Ctx W SP S D R n al H icb a s) := by
  have len : 16*(n/16)=n := by omega
  have ha : (a++zeros (padLen a.length)).length%16=0 := by
    simp only [List.length_append,Proof.Gcm.length_zeros];exact Proof.Gcm.length_pad_mod _
  obtain ⟨fr,rounds,hkey,ck,j,pre,_,abs,_⟩ := ob_factsFrom reg.lay ob reg.sW reg.ks reg.sD post.frame hH hcb habs ha
    bulk.1 bulk.2.1 (Z:=bytesAt u.mem D n) (by rw [length_bytesAt];exact aligned) (by
      rw [bulk.2.2];change ghashFrom (blockAt s.mem (Ctx+240#64)) _ _=_
      rw [hH,Proof.Gcm.blocksAt_eq,len]; rfl)
  rw [len] at pre
  have hx : (a++zeros (padLen a.length)++bytesAt u.mem D n).length%16=0 := by rw [List.length_append,length_bytesAt];omega
  have la := (fr.readW (w:=64) (r:=⟨W+184#64,8⟩) (Region.contains_self _ _)
    (kept_oneFrameB reg.lay reg.data.ok.w ob.t_w (.inl ⟨by decide,by decide⟩)) (by decide)).trans hal
  obtain ⟨t,run,e,bx,bp,m,rd,wr⟩ := tagArgs post.env la post.tlen
  refine WP.seq (WP.of_runBlock ⟨t,run,?_⟩)
  refine (directEcbTag_ok v reg.lay e (m ▸ rounds) (m ▸ hkey)).mono fun z ⟨ez,rz,wz,fz,tag'⟩ => ?_
  rw [m] at fz
  have f := fr.trans (oneFrame_B (n:=n) (k:=0) (Nat.zero_le _) (by simpa using wFrame_one (W:=W) (D:=D) (n:=n) (o:=0) (.inl rfl) (by simpa only [BitVec.add_zero] using fz)))
  have same : bytesAt z.mem D n=bytesAt u.mem D n := bytesAt_frame fz (fun q hq => by
    simp only [wFrame,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl
    · simpa using reg.data.ok.w.sub_right (Region.sub_prefix (show 16≤2560 by decide))
    · exact reg.data.ok.w.sub_right (Lay.wSub (by decide))
    · exact reg.data.ok.w.sub_right (Lay.wSub (by decide))
    · exact reg.data.ok.w.sub_right (Lay.wSub (by decide))
    · exact reg.data.ok.stk.symm) (Nat.le_of_lt reg.data.ok.lt)
  refine ⟨ez,rz.trans (rd.trans post.rd),wz.trans (wr.trans post.wr),f,same.trans pre,?_⟩
  have padded' := padded_eq a (bytesAt u.mem D n)
  rw [Proof.Gcm.padLen_of_mod hx, show zeros 0=[] from rfl,List.append_nil] at padded'
  have y := abs.whole_eq hx
  rw [padded'] at y
  rw [m,bx,bp,toNat_ofNat_of_lt reg.data.ok.lt,BitVec.toNat_ofNat,lensBlock_mod_left,ck,j,
    show blockAt u.mem (W+16#64+16#64)=_ from y] at tag'
  rw [same]
  simpa only [BitVec.add_zero] using tag'

private theorem alignedTag_ct (v : GcmImpl) {M : CtxMode} : FinishCT M (Contiguous.alignedTag v.callees Contiguous.maskAES) := by
  intro Ctx W SP S D R n al L _ _
  let P (s : State) := Env Ctx (W+16#64) W SP s ∧ RoundsAt s.mem W R ∧ s.gpr .rbx=BitVec.ofNat 64 al ∧ s.gpr .rbp=BitVec.ofNat 64 n
  have args s (h : AfterBulk M Ctx W SP S D R n al s) : WP isa (.block authLens) s P := by
    obtain ⟨t,run,e,bx,bp,m,_,_⟩ := tagArgs h.scalar.tag.env h.scalar.tag.alen h.scalar.tag.tlen
    exact WP.of_runBlock ⟨t,run,e,m ▸ h.scalar.tag.rounds,bx,bp⟩
  refine RelCT.seq (Short.rel_next (rel_env_regs [] (fun _ h => h.scalar.tag.env) (fun _ h => h.scalar.tag.env)
    (fun _ _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩) args args) ?_
  exact directEcbTag_ct v L

private theorem choiceOk (v : GcmImpl) {M : CtxMode} {g : Prog isa} (b : FinishOk M g) :
    FinishOk M (Contiguous.maskChoice (Contiguous.alignedTag v.callees Contiguous.maskAES) g) := by
  intro Ctx W SP S D R n al s u H icb bytes reg ob p bulk hH hcb hal habs read src apart dread dst dout dw
  obtain ⟨t,run,zf,m,p'⟩ := maskChoice_step p
  have bt : BlocksResult Ctx W R S D (n/16) s t := by simpa only [BlocksResult,m] using bulk
  have fs (z : decide (n%16=0)=true) := alignedTag_ok v (of_decide_eq_true z) reg ob p' bt hH hcb hal habs
  have gs := b reg ob p' bt hH hcb hal habs read (m ▸ src) apart dread (m ▸ dst) dout dw
  exact WP.seq (WP.of_runBlock ⟨t,run,WP.ite (decide (n%16=0)) (eval_e zf) fs (fun _ => gs)⟩)

private theorem choiceCT {M : CtxMode} {f g : Prog isa} (a : FinishCT M f) (b : FinishCT M g) : FinishCT M (Contiguous.maskChoice f g) := by
  intro Ctx W SP S D R n al L hR dw
  let P := AfterBulk M Ctx W SP S D R n al
  let F (s : State) := s.zf=some (decide (n%16=0)) ∧ P s
  have next (s) (h : P s) : WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)),.alu .test .rax (.reg .rax)]) s F := by
    obtain ⟨_,aa,p⟩ := h.origin
    obtain ⟨t,run,zf,_,p'⟩ := maskChoice_step p
    exact WP.of_runBlock ⟨t,run,zf,afterBulk_ok aa p'⟩
  apply RelCT.seq (Short.rel_next (rel_env_regs [] (fun _ (h : P _) => h.scalar.tag.env) (fun _ (h : P _) => h.scalar.tag.env)
    (fun _ _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩) next next)
  exact rel_ite_e (fun _ _ h => h.1.1.trans h.2.1.symm)
    ((a L hR dw).mono (fun _ _ h => ⟨h.1.1.2,h.1.2.2⟩) (fun _ _ h => h))
    ((b L hR dw).mono (fun _ _ h => ⟨h.1.1.2,h.1.2.2⟩) (fun _ _ h => h))

/- In a bounded whole-block record the same bitsliced AES call encrypts J0 and all counters.
Each output load happens before its store even when the input and output are identical. -/
open VG.Impl.AesGcm.X86_64.Contiguous (maskIndex xorOne packOne bumpMask batchAESArgs startMasks maskPtrs)

private theorem xorOne_ok {s : State} (S W D off : Addr) (src : s.gpr .rdi=S) (work : s.gpr .r15=W)
    (dst : s.gpr .rsi=D) (it : s.gpr .r10=off)
    (read : InRegions (s.rd++s.wr) (S+off) 16)
    (mask : InRegions (s.rd++s.wr) (W+off+272#64) 16) (write : InRegions s.wr (D+off) 16) :
    WP isa (.block xorOne) s fun t => t.gpr=s.gpr ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ Frame [⟨D+off,16⟩] s.mem t.mem ∧
      blockAt t.mem (D+off)=blockAt s.mem (S+off) ^^^ blockAt s.mem (W+off+272#64) := by
  let a := s.mem.readW (S+off) 128
  let b := s.mem.readW (W+off+272#64) 128
  let t := (((s.setXmm .xmm0 a).setXmm .xmm1 b).setXmm .xmm0 (a ^^^ b)).setMem (s.mem.writeW (D+off) (a ^^^ b))
  apply WP.of_runBlock
  refine ⟨t,?_,rfl,rfl,rfl,?_,?_⟩
  · have d0 : BitVec.ofInt 64 (Int.ofNat 0)=0#64 := rfl
    have d272 : BitVec.ofInt 64 (Int.ofNat 272)=272#64 := rfl
    unfold xorOne
    xrun [maskIndex,t,a,b,src,work,dst,it,read,mask,write,d0,d272,BitVec.mul_one,BitVec.ofInt_natCast,BitVec.add_zero,State.load128,State.store128_eq,XOp.exec,XBinOp.eval,State.setXmm]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · change blockAt (s.mem.writeW (D+off) (a ^^^ b)) (D+off)=_
    rw [blockAt_eq,Mem.readW_writeW_self _ _ 16 _ (by decide),pshufb_rev_xor,blockAt_eq,blockAt_eq]
private theorem storeCount (m : Mem) (p : Addr) (k : Nat) :
    let x := bswap32 (m.readW (p+12#64) 32)
    blockAt (m.writeW (p+12#64) (bswap32 (x+(BitVec.ofNat 64 k).setWidth 32))) p = Nat.repeat Spec.Gcm.inc32 k (blockAt m p) := by
  apply VG.Proof.Aes.X86_64.ctr_after
  intro i hi
  rw [VG.Proof.Aes.X86_64.writeW_apply,VG.Proof.Aes.X86_64.off_toNat p (by omega) (by omega)]
  by_cases h : i < 12
  · rw [ite_eq_right (show ¬12≤i by omega),ite_eq_right (show ¬2^64+i-12 < 32/8 by omega),ite_eq_left h]
  · rw [ite_eq_left (show 12≤i by omega),ite_eq_left (show i-12<32/8 by omega),ite_eq_right h,BitVec.setWidth_eq]
private theorem packOne_ok {s : State} (W off : Addr) (work : s.gpr .r15=W) (it : s.gpr .r10=off)
    (write : InRegions s.wr (W+off+272#64) 16) (low : InRegions s.wr (W+off+284#64) 4)
    (J : Block) (k : Nat) (orig : VG.X86_64.XBinOp.eval .pshufb (s.xmm .xmm0) VG.Proof.Gcm.X86_64.revMask = J)
    (count : (s.gpr .r11).setWidth 32 = J.extractLsb' 0 32 + BitVec.ofNat 32 k) :
    WP isa (.block packOne) s fun t => t.xmm .xmm0=s.xmm .xmm0 ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      (t.gpr .r11).setWidth 32 = J.extractLsb' 0 32 + BitVec.ofNat 32 (k+1) ∧
      (∀ r, r≠.rax → r≠.r11 → t.gpr r=s.gpr r) ∧ Frame [⟨W+off+272#64,16⟩] s.mem t.mem ∧
      blockAt t.mem (W+off+272#64) = Nat.repeat Spec.Gcm.inc32 (k+1) J := by
  let P := W+off+272#64
  let A := W+off+284#64
  have pa : A=P+12#64 := by dsimp [P,A];rw [BitVec.add_assoc (W+off)];rfl
  let m := s.mem.writeW P (s.xmm .xmm0)
  have block : blockAt m P=J := by
    rw [blockAt_eq,Mem.readW_writeW_self _ _ 16 _ (by decide)]
    exact orig
  let next : BitVec 32 := (s.gpr .r11).setWidth 32 + 1#32
  have num : next=J.extractLsb' 0 32 + BitVec.ofNat 32 (k+1) := by
    rw [BitVec.ofNat_add,←BitVec.add_assoc,← count]
  let out := m.writeW A (bswap32 next)
  have fresh : blockAt out P=Nat.repeat Spec.Gcm.inc32 (k+1) J := by
    have kk : (BitVec.ofNat 64 (k+1)).setWidth 32=BitVec.ofNat 32 (k+1) := by
      apply BitVec.eq_of_toNat_eq; simp
    have cnt : next=bswap32 (m.readW (P+12#64) 32)+(BitVec.ofNat 64 (k+1)).setWidth 32 := by
      rw [VG.Proof.Aes.X86_64.icb_lo,block,kk,num]
    simpa only [out,pa,cnt,block] using (storeCount m P (k+1))
  have d272 : BitVec.ofInt 64 (Int.ofNat 272)=272#64 := rfl
  have d284 : BitVec.ofInt 64 (Int.ofNat 284)=284#64 := rfl
  have f0 : Frame [⟨P,16⟩] s.mem m := (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have sub : (⟨P,16⟩ : Region).Contains A 4 := by
    rw [pa];exact Offset.contains_base P (by decide) (by decide)
  have frame : Frame [⟨P,16⟩] s.mem out := f0.writeW (List.mem_singleton_self _) _ sub
  apply WP.of_runBlock
  have shrink (x : BitVec 32) : (x.setWidth 64).setWidth 32=x := by simp
  unfold packOne
  refine ⟨_,by xrun [maskIndex,work,it,write,low,BitVec.mul_one,d272,d284,State.store128_eq,State.setMem,shrink],?_,?_,?_,?_,?_,?_,?_⟩
  all_goals try rfl
  · change ((next.setWidth 64).setWidth 32)=_
    rw [shrink,num]
  · intro r ha hb
    simp [gpr_setReg,ha,hb]
  · exact frame
  · exact fresh
private theorem countLoop {P : Nat → State → Prop} (body : Prog isa) {s : State} {n : Nat} (hn : 0<n) (h : P 0 s)
    (step : ∀ i t, i<n → P i t → WP isa body t (fun u => P (i+1) u ∧ u.zf=some (decide (i+1=n)))) :
    WP isa (.loop body .ne) s (P n) := by
  apply WP.loop (M:=isa) (body:=body) (c:=.ne) (fun rem t => ∃ i,rem=n-i ∧ i<n ∧ P i t) _ n s ⟨0,by omega,hn,h⟩
  rintro _ t ⟨i,rfl,hi,inv⟩
  refine (step i t hi inv).mono fun u ⟨h',z⟩ => ?_
  by_cases last : i+1=n
  · exact .inl ⟨by simp [eval,z,last],last ▸ h'⟩
  · exact .inr ⟨by simp [eval,z,last],n-(i+1),by omega,i+1,rfl,by omega,h'⟩

private theorem bump_ok {s : State} {k n : Nat} (hk : k<n) (hn : n≤15)
    (it : s.gpr .r10=BitVec.ofNat 64 (16*k)) (lim : s.gpr .rbp=BitVec.ofNat 64 (16*n)) :
    WP isa (.block bumpMask) s fun t => t.gpr .r10=BitVec.ofNat 64 (16*(k+1)) ∧
      t.zf=some (decide (k+1=n)) ∧ (∀ r, r≠.r10 → t.gpr r=s.gpr r) ∧
      t.xmm=s.xmm ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  have next : BitVec.ofNat 64 (16*k)+16#64=BitVec.ofNat 64 (16*(k+1)) := by rw [Nat.mul_add,BitVec.ofNat_add]
  have eq : (BitVec.ofNat 64 (16*(k+1))-BitVec.ofNat 64 (16*n)==0)=decide (k+1=n) := by
    rw [Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    by_cases h : k+1=n
    · simp [h]
    · simp [h,show 16*(k+1)≠16*n by omega]
  apply WP.of_runBlock
  unfold bumpMask
  refine ⟨_,by xrun [it,lim],?_,?_,?_,?_,?_,?_,?_⟩
  all_goals try rfl
  · exact next
  · change some (_ == _) = _
    rw [next,eq]
  · intro r hr;simp [gpr_setReg,hr]
private def maskAt (W : Addr) (i : Nat) := W+BitVec.ofNat 64 (16*i)+272#64
private theorem maskAt_off (W : Addr) (i : Nat) : maskAt W i=W+BitVec.ofNat 64 (272+16*i) := by
  unfold maskAt
  rw [BitVec.add_assoc,BitVec.ofNat_add,BitVec.add_comm (BitVec.ofNat 64 (16*i))]
private def packRegion (W : Addr) (n : Nat) : Region := ⟨W+272#64,16*n⟩
private theorem packLoop_ok {s : State} {W : Addr} {n : Nat} (hn : 0<n) (hn' : n≤15)
    (hw : s.gpr .r15=W) (len : s.gpr .rbp=BitVec.ofNat 64 (16*n)) (zero : s.gpr .r10=0)
    (cov : Covers [⟨W,2560⟩] s.wr) (J : Block)
    (init : VG.X86_64.XBinOp.eval .pshufb (s.xmm .xmm0) VG.Proof.Gcm.X86_64.revMask=J)
    (num : (s.gpr .r11).setWidth 32=J.extractLsb' 0 32) :
    WP isa (.loop (.block (packOne++bumpMask)) .ne) s fun t =>
      (∀ r,r≠.rax → r≠.r11 → r≠.r10 → t.gpr r=s.gpr r) ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      Frame [packRegion W n] s.mem t.mem ∧ (∀ i<n,blockAt t.mem (maskAt W i)=Nat.repeat Spec.Gcm.inc32 (i+1) J) := by
  let I (k : Nat) (t : State) := (∀ r,r≠.rax → r≠.r11 → r≠.r10 → t.gpr r=s.gpr r) ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
    Frame [packRegion W n] s.mem t.mem ∧ (∀ i<k,blockAt t.mem (maskAt W i)=Nat.repeat Spec.Gcm.inc32 (i+1) J) ∧
    t.xmm .xmm0=s.xmm .xmm0 ∧ (t.gpr .r11).setWidth 32=J.extractLsb' 0 32+BitVec.ofNat 32 k ∧ t.gpr .r10=BitVec.ofNat 64 (16*k)
  have start : I 0 s := ⟨fun _ _ _ _ => rfl,rfl,rfl,Frame.refl _ _,fun _ hz => by omega,rfl,by simpa using num,zero⟩
  refine (countLoop (P:=I) _ hn start ?_).mono fun t ⟨g,rd,wr,fr,blocks,_⟩ => ⟨g,rd,wr,fr,blocks⟩
  intro k t hk inv
  obtain ⟨g,rd,wr,fr,blocks,xmm,num,it⟩ := inv
  have w := (g _ (by decide) (by decide) (by decide)).trans hw
  have len' := (g _ (by decide) (by decide) (by decide)).trans len
  have has (d z : Nat) (hd : 16*k+d+z≤2560) :
      InRegions t.wr (W+BitVec.ofNat 64 (16*k)+BitVec.ofNat 64 d) z := by
    rw [wr,add_ofNat_assoc];exact in_off cov hd (by decide)
  rw [WP.block_append_iff]
  refine (packOne_ok W _ w it (has 272 16 (by omega)) (has 284 4 (by omega)) J k (xmm ▸ init) num).mono
    fun v ⟨xmv,rv,wv,cv,gv,fv,bv⟩ => ?_
  refine (bump_ok hk hn' ((gv _ (by decide) (by decide)).trans it) ((gv _ (by decide) (by decide)).trans len')).mono
    fun u ⟨it',zf,gu,xu,mu,ru,wu⟩ => ?_
  have f : Frame [packRegion W n] t.mem v.mem := fv.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_singleton_self _,?_⟩
    unfold packRegion;rw [add_ofNat_assoc]
    exact Offset.sub W (by omega) (by omega)
  refine ⟨⟨fun r a b c => (gu r c).trans ((gv r a b).trans (g r a b c)),ru.trans (rv.trans rd),
    wu.trans (wv.trans wr),mu ▸ fr.trans f,?_,?_,?_,it'⟩,zf⟩
  · intro i hi
    rw [mu]
    by_cases eq : i=k
    · subst eq;exact bv
    · rw [blockAt_frame fv (fun r hr => ?_),blocks i (by omega)]
      obtain rfl := List.mem_singleton.mp hr
      rw [maskAt_off,add_ofNat_assoc]
      exact Offset.disjoint W (.inl (by omega)) (by omega) (by omega)
  · rw [xu,xmv,xmm]
  · rw [gu _ (by decide),cv]

private theorem xorBlocks_ok {s : State} {W S D : Addr} {J : Block} {enc : Block → Block} {n : Nat} (hn : 0<n) (hn' : n≤15)
    (hw : s.gpr .r15=W) (hd : s.gpr .rsi=D) (hs : s.gpr .rdi=S) (len : s.gpr .rbp=BitVec.ofNat 64 (16*n)) (zero : s.gpr .r10=0)
    (maskW : Covers [⟨W,2560⟩] s.wr) (outW : Covers [⟨D,16*n⟩] s.wr) (srcR : Covers [⟨S,16*n⟩] (s.rd++s.wr))
    (overlap : S=D ∨ (⟨S,16*n⟩ : Region).Disjoint ⟨D,16*n⟩) (work : (⟨W,2560⟩ : Region).Disjoint ⟨D,16*n⟩)
    (keystream : ∀ i<n,blockAt s.mem (maskAt W i)=enc (Nat.repeat Spec.Gcm.inc32 (i+1) J)) :
    WP isa (.loop (.block (xorOne++bumpMask)) .ne) s fun t =>
      (∀ r,r≠.r10 → t.gpr r=s.gpr r) ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ Frame [⟨D,16*n⟩] s.mem t.mem ∧
      (∀ i<n,blockAt t.mem (D+BitVec.ofNat 64 (16*i))=
        blockAt s.mem (S+BitVec.ofNat 64 (16*i)) ^^^ enc (Nat.repeat Spec.Gcm.inc32 (i+1) J)) := by
  let I (k : Nat) (t : State) := (∀ r,r≠.r10 → t.gpr r=s.gpr r) ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
    Frame [⟨D,16*k⟩] s.mem t.mem ∧ (∀ i<k,blockAt t.mem (D+BitVec.ofNat 64 (16*i))=
      blockAt s.mem (S+BitVec.ofNat 64 (16*i)) ^^^ enc (Nat.repeat Spec.Gcm.inc32 (i+1) J)) ∧ t.gpr .r10=BitVec.ofNat 64 (16*k)
  have start : I 0 s := ⟨fun _ _ => rfl,rfl,rfl,Frame.refl _ _,fun _ hz => by omega,zero⟩
  refine (countLoop (P:=I) _ hn start ?_).mono fun t ⟨g,rd,wr,fr,blocks,_⟩ => ⟨g,rd,wr,fr,blocks⟩
  intro k t hk inv
  obtain ⟨g,rd,wr,fr,blocks,it⟩ := inv
  have su := Region.sub_prefix (base:=D) (show 16*k≤16*n by omega)
  have raw : blockAt t.mem (S+BitVec.ofNat 64 (16*k))=blockAt s.mem (S+BitVec.ofNat 64 (16*k)) := by
    apply blockAt_frame fr;intro r hr;obtain rfl := List.mem_singleton.mp hr
    rcases overlap with rfl|dis
    · exact Offset.disjoint_base S (by omega) (by omega)
    · exact (dis.sub_left (Offset.sub_base S (by omega))).sub_right su
  have mask : blockAt t.mem (maskAt W k)=enc (Nat.repeat Spec.Gcm.inc32 (k+1) J) := by
    rw [blockAt_frame fr (fun r hr => ?_),keystream k hk]
    obtain rfl := List.mem_singleton.mp hr
    rw [maskAt_off];exact (work.sub_left (Offset.sub_base W (by omega))).sub_right su
  have maskR : InRegions (t.rd++t.wr) (maskAt W k) 16 := by
    rw [rd,wr,maskAt_off];exact in_off (covers_left maskW) (by omega) (by decide)
  rw [WP.block_append_iff]
  refine (xorOne_ok S W D _ ((g _ (by decide)).trans hs) ((g _ (by decide)).trans hw) ((g _ (by decide)).trans hd) it
    (by rw [rd,wr];exact in_off srcR (by omega) (by omega)) maskR (by rw [wr];exact in_off outW (by omega) (by omega))).mono
    fun v ⟨gv,rv,wv,fv,ct⟩ => ?_
  refine (bump_ok hk hn' (gv ▸ it) (gv ▸ (g _ (by decide)).trans len)).mono fun u ⟨it',zf,gu,_,mu,ru,wu⟩ => ?_
  have fr' : Frame [⟨D,16*(k+1)⟩] s.mem v.mem := (fr.sub (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_singleton_self _,Region.sub_prefix (by omega)⟩)).trans (fv.sub (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr;exact ⟨_,List.mem_singleton_self _,Offset.sub_base D (by omega)⟩))
  refine ⟨⟨fun r h => (gu r h).trans (gv ▸ g r h),ru.trans (rv.trans rd),wu.trans (wv.trans wr),mu ▸ fr',?_,it'⟩,zf⟩
  intro i hi;rw [mu]
  by_cases eq : i=k
  · subst eq;rw [ct,raw,← mask];rfl
  · rw [blockAt_frame fv (fun r hr => ?_),blocks i (by omega)]
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint D (.inl (by omega)) (by omega) (by omega)

private theorem batchArgs_ok {s : State} {Ctx W SP : Addr} {R n : Nat} (hn : n ≤ 15)
    (L : Lay Ctx (W+16#64) W SP) (e : Env Ctx (W+16#64) W SP s) (rr : RoundsAt s.mem W R)
    (lim : s.gpr .rbp=BitVec.ofNat 64 (16*n)) :
    WP isa (.block batchAESArgs) s fun t => BCall t Ctx (W+256#64) (W+512#64) R (n+1) ∧
      t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ (∀ r ∈ calleeSaved, t.gpr r=s.gpr r) := by
  have rd := e.perm.wR (show 176+8≤2560 by decide)
  have cnt : (BitVec.ofNat 64 (16*n) >>> 4)+1#64=BitVec.ofNat 64 (n+1) := by
    rw [←BitVec.ofNat_add_ofNat];congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 16*n<2^64 by omega),Nat.mod_eq_of_lt (show n<2^64 by omega)]
  unfold batchAESArgs
  obtain ⟨t,rn,di,si,dx,cx,r8,mem,dr,dw,saved⟩ :
      ∃ t, runBlock isa (([.mov .rdi (.reg .r13),.mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++ ptr .rdx .r15 256 ++
        [.mov .rcx (.reg .rbp),.shift .shr .rcx 4,.alu .add .rcx (imm 1)] ++ ptr .r8 .r15 scrO) s=some t ∧
      t.gpr .rdi=Ctx ∧ t.gpr .rsi=BitVec.ofNat 64 R ∧ t.gpr .rdx=W+256#64 ∧ t.gpr .rcx=BitVec.ofNat 64 (n+1) ∧
      t.gpr .r8=W+512#64 ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ (∀ r ∈ calleeSaved, t.gpr r=s.gpr r) := by
    refine ⟨_,by xrun [e.r13,e.r15,roundsO,scrO,rd,ptr,lim],?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals try rfl
    all_goals try (simp [gpr_setReg,State.setFlags,rr.1,cnt];done)
    intro r h
    simp only [calleeSaved,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [gpr_setReg,State.setFlags]
  let et := e.of_saved saved dr dw
  refine WP.of_runBlock ⟨t,rn,⟨di,si,dx,cx,r8,rr.2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,mem,dr,dw,saved⟩
  · have w := L.ww
    rw [BitVec.toNat_add_of_lt];all_goals simp at *;omega
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by omega))
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · exact Offset.disjoint W (.inl (by omega)) (by omega) (by decide)
  · rw [et.rsp];exact L.kc.sub_right (Region.sub_prefix (by decide))
  · rw [et.rsp];exact L.stk_w (by omega)
  · rw [et.rsp];exact L.stk_w (by decide)
  · exact covers_cons (by simpa only [BitVec.add_zero] using et.perm.ctxC (d:=0) (n:=240) (by decide))
      (covers_cons (covers_left (et.perm.wC (by omega))) (covers_left (et.perm.wC (by decide))))
  · exact covers_cons (et.perm.wC (by omega)) (et.perm.wC (by decide))

private theorem batch_guard (x : BitVec 64) (h : ((x-16#64).rotateRight 4).toNat < 15) :
    ∃ k : Nat, k < 15 ∧ x.toNat = 16*(k+1) := by
  have hx : x.toNat < 18446744073709551616 := x.isLt
  have hy := (x-16#64).isLt
  let t := (x-16#64).toNat
  have he : t = (x.toNat + 18446744073709551600) % 18446744073709551616 := by
    simp [t,BitVec.toNat_sub,Nat.add_comm]
  rw [BitVec.toNat_rotateRight_eq_add] at h
  change ((t/16 + t*1152921504606846976) %18446744073709551616)<15 at h
  have ht : t < 18446744073709551616 := hy
  have hd : t=16*(t/16)+t%16 := by omega
  have hm : (t/16 + t*1152921504606846976) %18446744073709551616 =
      t/16 + (t%16)*1152921504606846976 := by
    omega
  rw [hm] at h
  have d : t%16 = 0 := by omega
  have a : t/16 < 15 := by omega
  have r : x.toNat=t+16 := by
    have bound : t ≤ 224 := by omega
    by_cases h16 : x.toNat < 16
    · have small : x.toNat+18446744073709551600<18446744073709551616 := by omega
      rw [Nat.mod_eq_of_lt small] at he
      omega
    · have hmul : x.toNat+18446744073709551600=(x.toNat-16)+18446744073709551616 := by omega
      rw [hmul,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)] at he
      omega
  exact ⟨t/16,a,by omega⟩

private abbrev preparedFrame (W SP : Addr) : List Region := [⟨W+192#64,8⟩,⟨W+256#64,2304⟩,below SP 8]
private theorem preparedLow {Ctx W SP : Addr} (L : Lay Ctx (W+16#64) W SP) {d n : Nat}
    (lo : d+n≤192 ∨ (200≤d ∧ d+n≤256)) : ∀ r ∈ preparedFrame W SP,(⟨W+BitVec.ofNat 64 d,n⟩ : Region).Disjoint r := by
  intro r hr;simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact Offset.disjoint W (by omega) (by omega) (by decide)
  · exact Offset.disjoint W (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm
private theorem preparedFar {W SP P : Addr} {N : Nat} (w : (⟨P,N⟩ : Region).Disjoint ⟨W,2560⟩)
    (stk : (⟨P,N⟩ : Region).Disjoint (below SP 8)) : ∀ r ∈ preparedFrame W SP,(⟨P,N⟩ : Region).Disjoint r := by
  intro r hr;simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact w.sub_right (Lay.wSub (by decide))
  · exact w.sub_right (Lay.wSub (by decide))
  · exact stk
private theorem startMasks_ok {s : State} {Ctx W SP : Addr} {n : Nat}
    (e : Env Ctx (W+16#64) W SP s) (len : s.mem.readW (W+208#64) 64=BitVec.ofNat 64 (16*n)) :
    let J := blockAt s.mem (W+16#64)
    WP isa (.block startMasks) s fun t => Env Ctx (W+16#64) W SP t ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      t.gpr .rbp=BitVec.ofNat 64 (16*n) ∧ t.gpr .r10=0 ∧
      (t.gpr .r11).setWidth 32=J.extractLsb' 0 32 ∧ VG.X86_64.XBinOp.eval .pshufb (t.xmm .xmm0) VG.Proof.Gcm.X86_64.revMask=J ∧
      Frame (preparedFrame W SP) s.mem t.mem ∧ blockAt t.mem (W+256#64)=J ∧ t.mem.readW (W+192#64) 64=BitVec.ofNat 64 (16*n) := by
  let Jp := W+16#64
  let Mp := W+256#64
  let Lp := W+192#64
  let j := s.mem.readW Jp 128
  let m := s.mem.writeW Mp j
  have fr : Frame [⟨Mp,16⟩] s.mem m := (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have jc : m.readW (Jp+12#64) 32=s.mem.readW (Jp+12#64) 32 := by
    rw [show Jp+12#64=W+28#64 by dsimp [Jp];rw [BitVec.add_assoc];rfl]
    exact fr.readW (Region.contains_self _ _) (by intro z hz;obtain rfl := List.mem_singleton.mp hz;exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide)
  have ln : m.readW (W+208#64) 64=BitVec.ofNat 64 (16*n) := (fr.readW (Region.contains_self _ _) (by
    intro z hz;obtain rfl := List.mem_singleton.mp hz;exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide)).trans len
  let o := m.writeW Lp (BitVec.ofNat 64 (16*n))
  have f' : Frame [⟨Lp,8⟩] m o := (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fm : Frame (preparedFrame W SP) s.mem o := (fr.sub (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr;exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_self ..),Region.sub_prefix (by decide)⟩)).trans
    (f'.mono (fun r hr => by obtain rfl := List.mem_singleton.mp hr;exact List.mem_cons_self ..))
  have first : blockAt o Mp=blockAt s.mem Jp := by
    rw [blockAt_frame f' (fun r hr => ?_),blockAt_eq,Mem.readW_writeW_self _ _ 16 _ (by decide),blockAt_eq]
    obtain rfl := List.mem_singleton.mp hr;exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  have saved : o.readW Lp 64=BitVec.ofNat 64 (16*n) := Mem.readW_writeW_self64 ..
  have rd := e.perm.wR (show 208+8≤2560 by decide)
  have rj : InRegions (s.rd++s.wr) Jp 16 := by simpa only [BitVec.add_zero] using e.perm.stR (d:=0) (n:=16) (by decide)
  have rc := e.perm.stR (show 12+4≤80 by decide)
  have wr := e.perm.wW (show 256+16≤2560 by decide)
  have wl := e.perm.wW (show 192+8≤2560 by decide)
  change InRegions (s.rd++s.wr) (Jp+12#64) 4 at rc
  change InRegions s.wr Mp 16 at wr
  change InRegions s.wr Lp 8 at wl
  have js : s.gpr .r14=Jp := e.r14
  have narrow (x : BitVec 32) : (x.setWidth 64).setWidth 32=x := by simp
  unfold startMasks
  apply WP.of_runBlock
  refine ⟨_,by xrun [js,e.r15,Jp,Mp,Lp,j,m,rd,rj,rc,wr,wl,ln,jc,narrow,BitVec.add_zero,
    State.load128,State.store128_eq,State.setMem,State.setXmm,tlenO,lenO],?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact e.keep (fun r hr => by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
                                 rcases hr with rfl|rfl|rfl|rfl <;> rfl) rfl rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change ((bswap32 (s.mem.readW (Jp+12#64) 32)).setWidth 64).setWidth 32=_
    rw [narrow];exact VG.Proof.Aes.X86_64.icb_lo ..
  · rw [blockAt_eq];rfl
  · exact fm
  · exact first
  · exact saved

private structure Masked (Ctx W SP : Addr) (R n : Nat) (s t : State) : Prop where
  env : Env Ctx (W+16#64) W SP t
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  frame : Frame (preparedFrame W SP) s.mem t.mem
  rbp : t.gpr .rbp=BitVec.ofNat 64 (16*n)
  len : t.mem.readW (W+192#64) 64=BitVec.ofNat 64 (16*n)
  tag : blockAt t.mem (W+256#64)=ciphOf s.mem Ctx R (blockAt s.mem (W+16#64))
  counters : ∀ i<n,blockAt t.mem (maskAt W i)=ciphOf s.mem Ctx R (Nat.repeat Spec.Gcm.inc32 (i+1) (blockAt s.mem (W+16#64)))

private theorem batchKeys_ok {s : State} {Ctx W SP : Addr} {R n : Nat} (hn : 0<n) (hn' : n≤15)
    (L : Lay Ctx (W+16#64) W SP) (e : Env Ctx (W+16#64) W SP s) (rr : RoundsAt s.mem W R)
    (len : s.mem.readW (W+208#64) 64=BitVec.ofNat 64 (16*n)) :
    WP isa (Contiguous.batchKeys Contiguous.maskAES) s (Masked Ctx W SP R n s) := by
  let J := blockAt s.mem (W+16#64)
  unfold Contiguous.batchKeys
  refine WP.seq ((startMasks_ok e len).mono fun a ⟨ea,ra,wa,al,a0,an,ax,fa,aj,atlen⟩ => ?_)
  refine WP.seq ((packLoop_ok hn hn' ea.r15 al a0 ea.perm.w J ax an).mono fun b ⟨gb,rb,wb,fb,cs⟩ => ?_)
  have eb := ea.keep (fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact gb _ (by decide) (by decide) (by decide)) rb wb
  have bl := (gb _ (by decide) (by decide) (by decide)).trans al
  have sm : Region.Sub (packRegion W n) ⟨W+256#64,2304⟩ := Offset.sub W (by decide) (by omega)
  have f : Frame (preparedFrame W SP) s.mem b.mem := fa.trans (fb.sub fun z hz => by
    obtain rfl := List.mem_singleton.mp hz; exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_self ..),sm⟩)
  have br := rounds_frame f (preparedLow L (.inl (by decide))) rr
  have bk := ciph_frame f (preparedFar L.cw' L.kc.symm) rr.2
  have bt : blockAt b.mem (W+256#64)=J := by
    rw [blockAt_frame fb (fun z hz => ?_),aj];obtain rfl := List.mem_singleton.mp hz
    exact Offset.disjoint W (.inl (by decide)) (by decide) (by omega)
  have tl : b.mem.readW (W+192#64) 64=BitVec.ofNat 64 (16*n) := (fb.readW (Region.contains_self _ _) (by
    intro z hz;obtain rfl := List.mem_singleton.mp hz;exact Offset.disjoint W (.inl (by decide)) (by decide) (by omega)) (by decide)).trans atlen
  refine WP.seq ((batchArgs_ok hn' L eb br bl).mono fun c ⟨ac,mc,rc,wc,gc⟩ => ?_)
  let aes := Proof.Aes.X86_64.BlocksImpl.scalar
  refine (blk_call (name:=aes.enc.name) aes.encOk aes.encNosp aes.encDepth ac).mono fun t post => ?_
  let ec := eb.of_saved gc rc wc
  have ff := post.frame
  rw [mc,ec.rsp] at ff
  have ff' : Frame (preparedFrame W SP) b.mem t.mem := ff.sub fun z hz => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz;rcases hz with rfl|rfl|rfl
    · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_self ..),Region.sub_prefix (by omega)⟩
    · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_self ..),Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_,by simp,fun _ h => h⟩
  have le : t.mem.readW (W+192#64) 64=BitVec.ofNat 64 (16*n) := (ff.readW (Region.contains_self _ _) (by
    intro z hz;simp only [List.mem_cons,List.not_mem_nil,or_false] at hz;rcases hz with rfl|rfl|rfl
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by omega)
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm) (by decide)).trans tl
  refine ⟨ec.of_saved post.saved post.rd post.wr,post.rd.trans (rc.trans (rb.trans ra)),post.wr.trans (wc.trans (wb.trans wa)),f.trans ff',
    (post.saved _ (by decide)).trans ((gc _ (by decide)).trans bl),le,?_,?_⟩
  · have v := post.enc (i:=0) (by omega)
    change blockAt t.mem ((W+256#64)+0#64)=ciphOf c.mem Ctx R (blockAt c.mem ((W+256#64)+0#64)) at v
    simpa only [BitVec.add_zero,mc,bk,bt] using v
  · intro i hi
    have v := post.enc (i:=i+1) (by omega)
    have p : (W+256#64)+BitVec.ofNat 64 (16*(i+1))=maskAt W i := by
      rw [maskAt_off,add_ofNat_assoc];congr 2;omega
    change blockAt t.mem ((W+256#64)+BitVec.ofNat 64 (16*(i+1)))=ciphOf c.mem Ctx R (blockAt c.mem ((W+256#64)+BitVec.ofNat 64 (16*(i+1)))) at v
    simpa only [p,mc,bk,cs i hi] using v

private theorem ptrs_ok {s : State} {Ctx W SP S D : Addr} (e : Env Ctx (W+16#64) W SP s)
    (r : InRegions (s.rd++s.wr) (SP+8#64) 8) (src : s.mem.readW (SP+8#64) 64=S) (dst : s.mem.readW (W+200#64) 64=D) :
    WP isa (.block maskPtrs) s fun t => t.gpr .rdi=S ∧ t.gpr .rsi=D ∧ t.gpr .r10=0 ∧ t.gpr .rbp=s.gpr .rbp ∧
      Env Ctx (W+16#64) W SP t ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  have rd := e.perm.wR (show 200+8≤2560 by decide)
  unfold maskPtrs
  apply WP.of_runBlock
  refine ⟨_,by xrun [e.rsp,e.r15,dataO,rd,r,src,dst],?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals try rfl
  exact e.keep (fun r h => by simp only [List.mem_cons,List.not_mem_nil,or_false] at h
                              rcases h with rfl|rfl|rfl|rfl <;> rfl) rfl rfl

private structure Ciphered (Ctx W SP S D : Addr) (R n : Nat) (s t : State) : Prop where
  env : Env Ctx (W+16#64) W SP t
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  frame : Frame (⟨D,16*n⟩::preparedFrame W SP) s.mem t.mem
  tag : blockAt t.mem (W+256#64)=ciphOf s.mem Ctx R (blockAt s.mem (W+16#64))
  len : t.mem.readW (W+192#64) 64=BitVec.ofNat 64 (16*n)
  text : bytesAt t.mem D (16*n)=xorKs (ciphOf s.mem Ctx R) (Spec.Gcm.inc32 (blockAt s.mem (W+16#64))) 0 (bytesAt s.mem S (16*n))

private theorem batchText_ok {s u : State} {Ctx W SP S D : Addr} {R n al : Nat} {M : CtxMode}
    (hn : 0<n) (hn' : n≤15) (aa : AfterAad M Ctx W SP S D R (16*n) al s) (m : Masked Ctx W SP R n s u) :
    WP isa Contiguous.batchText u (Ciphered Ctx W SP S D R n s) := by
  have L := aa.reg.lay
  have read : InRegions (u.rd++u.wr) (SP+8#64) 8 := by rw [m.rd,m.wr];exact aa.read
  have src : u.mem.readW (SP+8#64) 64=S := (m.frame.readW (Region.contains_self _ _)
    (preparedFar aa.apart (Offset.disjoint_below SP (by decide))) (by decide)).trans aa.src
  have dst : u.mem.readW (W+200#64) 64=D := (m.frame.readW (Region.contains_self _ _) (preparedLow L (.inr ⟨by decide,by decide⟩)) (by decide)).trans aa.ob.dat
  unfold Contiguous.batchText
  refine WP.seq ((ptrs_ok m.env read src dst).mono fun v ⟨vs,vd,zf,bp,ev,mv,rv,wv⟩ => ?_)
  have rd := rv.trans m.rd
  have wr := wv.trans m.wr
  have ks := (aa.reg.ks.sub_left (below_sub (sp:=SP) (a:=8) (b:=24) (by decide) (by decide))).symm
  have pre : bytesAt v.mem S (16*n)=bytesAt s.mem S (16*n) := by rw [mv];exact bytesAt_frame m.frame (preparedFar aa.reg.sW ks) (by omega)
  let J := blockAt s.mem (W+16#64)
  let enc := ciphOf s.mem Ctx R
  refine (xorBlocks_ok (J:=J) (enc:=enc) hn hn' ev.r15 vd vs (bp.trans m.rbp) zf ev.perm.w
    (by rw [wr];exact aa.ob.data.wr) (by rw [rd,wr];exact aa.reg.srcCov) aa.reg.sD aa.ob.data.ok.w.symm (mv ▸ m.counters)).mono
    fun t ⟨g,rt,wt,fr,blocks⟩ => ?_
  have eq : Spec.Gcm.blocksAt t.mem D n=Spec.Gcm.ctr32 enc (Spec.Gcm.inc32 J) (Spec.Gcm.blocksAt v.mem S n) := by
    apply List.ext_getElem
    · simp [Spec.Gcm.blocksAt,Spec.Gcm.ctr32,Spec.Gcm.keystream]
    · intro i h₁ h₂
      have hi : i<n := by simpa [Spec.Gcm.blocksAt] using h₁
      simp only [Spec.Gcm.blocksAt,Spec.Gcm.ctr32,Spec.Gcm.keystream,List.getElem_map,List.getElem_range,List.getElem_zipWith,List.length_map,List.length_range]
      have bi := blocks i hi
      rw [Proof.Gcm.repeat_add,show Nat.repeat inc32 1 J=inc32 J by simp [Nat.repeat]] at bi
      exact bi
  have cipher := Proof.Gcm.ctr_wholeTo_bytes (n:=0) (icb:=Spec.Gcm.inc32 J) rfl (by simpa only [Nat.zero_div,Nat.repeat] using eq)
  have tw (d k : Nat) (h : d+k≤2560) : ∀ q ∈ [(⟨D,16*n⟩ : Region)],(⟨W+BitVec.ofNat 64 d,k⟩ : Region).Disjoint q := by
    intro q hq;obtain rfl := List.mem_singleton.mp hq;exact aa.ob.data.ok.w.symm.sub_left (Lay.wSub h)
  refine ⟨ev.keep (fun r hr => g r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr;rcases hr with rfl|rfl|rfl|rfl <;> decide)) rt wt,
    rt.trans rd,wt.trans wr,?_,?_,?_,?_⟩
  · rw [mv] at fr
    exact (m.frame.mono fun _ h => List.mem_cons_of_mem _ h).trans (fr.mono fun q h => by obtain rfl := List.mem_singleton.mp h;exact List.mem_cons_self ..)
  · rw [blockAt_frame fr (tw 256 16 (by decide)),mv,m.tag]
  · rw [fr.readW (r:=⟨W+192#64,8⟩) (Region.contains_self _ _) (tw 192 8 (by decide)) (by decide),mv,m.len]
  · rw [cipher,pre]

private theorem batchPost_ok (v : GcmImpl) {Ctx W SP S D : Addr} {R n al : Nat} {H : Block} {a : List Byte} {M : CtxMode}
    {s t : State} (aa : AfterAad M Ctx W SP S D R (16*n) al s) (t' : Ciphered Ctx W SP S D R n s t)
    (hH : blockAt s.mem (Ctx+240#64)=H) (habs : Absorbed s.mem (yA W) (W+16#64+32#64) H (a++zeros (padLen a.length))) :
    WP isa (Contiguous.batchAuth v.callees) t (BodyPost Ctx W SP S D R (16*n) al H (inc32 (blockAt s.mem (W+16#64))) a s) := by
  let L := aa.reg.lay
  have d := aa.ob.data.of_eq t'.rd t'.wr
  have low (p k : Nat) (lo : p+k≤192 ∨ (200≤p ∧ p+k≤256)) :
      ∀ r ∈ (⟨D,16*n⟩::preparedFrame W SP),(⟨W+BitVec.ofNat 64 p,k⟩ : Region).Disjoint r := by
    intro r hr;rcases List.mem_cons.mp hr with rfl|h
    · exact d.ok.w.symm.sub_left (Lay.wSub (by rcases lo with h|h <;> omega))
    · exact preparedLow L lo r h
  have kp (p : Nat) (ok : p+8≤192 ∨ (200≤p ∧ p+8≤256)) :=
    t'.frame.readW (w:=64) (r:=⟨W+BitVec.ofNat 64 p,8⟩) (Region.contains_self _ _) (low p 8 ok) (by decide)
  have dst := (kp 200 (.inr ⟨by decide,by decide⟩)).trans aa.ob.dat
  have len := (kp 208 (.inr ⟨by decide,by decide⟩)).trans aa.ob.len
  have alen := (kp 184 (.inl (by decide))).trans aa.alen
  have hkey : blockAt t.mem (Ctx+240#64)=H := (blockAt_frame t'.frame (by
    intro r hr;rcases List.mem_cons.mp hr with rfl|h
    · exact d.ctx.sub_left (Lay.ctxSub (by decide))
    · exact preparedFar (L.cw'.sub_left (Lay.ctxSub (by decide))) (L.kc.symm.sub_left (Lay.ctxSub (by decide))) r h)).trans hH
  have yc : blockAt t.mem (yA W)=blockAt s.mem (yA W) := by
    change blockAt t.mem (W+16#64+16#64)=blockAt s.mem (W+16#64+16#64)
    rw [show W+16#64+16#64=W+32#64 by rw [BitVec.add_assoc];rfl];exact blockAt_frame t'.frame (low 32 16 (.inl (by decide)))
  let F : List Region := [⟨yA W,16⟩,⟨W+448#64,256⟩,below SP 8]
  have apart (p k : Nat) (hp : 48≤p) (hp' : p+k≤448) : ∀ r ∈ F,(⟨W+BitVec.ofNat 64 p,k⟩ : Region).Disjoint r := by
    intro r hr;simp only [F,List.mem_cons,List.not_mem_nil,or_false] at hr;rcases hr with rfl|rfl|rfl
    · change (⟨W+BitVec.ofNat 64 p,k⟩ : Region).Disjoint ⟨W+16#64+16#64,16⟩
      rw [show W+16#64+16#64=W+32#64 by rw [BitVec.add_assoc];rfl]
      exact Offset.disjoint W (.inr (by omega)) (by omega) (by decide)
    · exact Offset.disjoint W (.inl hp') (by omega) (by decide)
    · exact (L.stk_w (by omega)).symm
  have dataF : ∀ r ∈ F,(⟨D,16*n⟩ : Region).Disjoint r := by
    intro r hr;simp only [F,List.mem_cons,List.not_mem_nil,or_false] at hr;rcases hr with rfl|rfl|rfl
    · exact d.ok.st.sub_right (Lay.stSub (by decide))
    · exact d.ok.w.sub_right (Lay.wSub (by decide))
    · exact d.ok.stk.symm
  unfold Contiguous.batchAuth
  refine WP.seq ((hashArgs_ok L t'.env d dst len).mono fun u ⟨gu,ru,wu,mu,call⟩ => ?_)
  refine WP.seq ((gh_call v.gh call).mono fun b out => ?_)
  let eu := t'.env.of_saved gu ru wu
  let eb := eu.of_saved out.saved out.rd out.wr
  have f : Frame F t.mem b.mem := by simpa only [eu.rsp,mu] using out.frame
  have key : blockAt b.mem (Ctx+240#64)=H := (blockAt_frame f (by
    intro r hr;simp only [F,List.mem_cons,List.not_mem_nil,or_false] at hr;rcases hr with rfl|rfl|rfl
    · exact L.ctx_st (by decide) (by decide)
    · exact L.ctx_w (by decide) (by decide)
    · exact (L.stk_ctx (by decide)).symm)).trans hkey
  have y := out.out
  rw [mu,hkey,yc,Proof.Gcm.blocksAt_eq,Nat.mul_div_cancel_left _ (by decide : 0<16)] at y
  have ha : (a++zeros (padLen a.length)).length%16=0 := by simp only [List.length_append,Proof.Gcm.length_zeros];exact Proof.Gcm.length_pad_mod _
  have hc : (bytesAt t.mem D (16*n)).length%16=0 := by rw [length_bytesAt];omega
  have hx : (a++zeros (padLen a.length)++bytesAt t.mem D (16*n)).length%16=0 := by rw [List.length_append];omega
  have dataY := (Proof.Gcm.absorb_whole habs ha hc y).whole_eq hx
  have pad := padded_eq a (bytesAt t.mem D (16*n))
  rw [Proof.Gcm.padLen_of_mod hx,show zeros 0=[] from rfl,List.append_nil] at pad
  rw [pad] at dataY
  obtain ⟨x,run,ex,bx,bp,mx,rx,wx⟩ := tagArgs eb ((f.readW (Region.contains_self _ _) (apart 184 8 (by decide) (by decide)) (by decide)).trans alen)
    ((f.readW (Region.contains_self _ _) (apart 192 8 (by decide) (by decide)) (by decide)).trans t'.len)
  refine WP.seq (WP.of_runBlock ⟨x,run,?_⟩)
  refine WP.seq ((WP.with_rdwr (lens_ok v L (.inr rfl) ex (mx ▸ key))).mono fun q ⟨⟨eq,_,yl,fq⟩,rq,wq⟩ => ?_)
  refine (mixMasks_ok eq).mono fun z ⟨ez,rz,wz,fz,mix⟩ => ?_
  rw [mx] at fq yl
  have tt : ∀ r ∈ tFrame (W+16#64) W SP 16,(⟨W+256#64,16⟩ : Region).Disjoint r := by
    intro r hr;simp only [List.mem_cons,List.not_mem_nil,or_false] at hr;rcases hr with rfl|rfl|rfl|rfl
    · exact (L.st_w (by decide) (.inr ⟨by decide,by decide⟩)).symm
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm
  rw [bx,bp,toNat_ofNat_of_lt d.ok.lt,BitVec.toNat_ofNat,lensBlock_mod_left,dataY] at yl
  rw [yl,blockAt_frame fq tt,blockAt_frame f (apart 256 16 (by decide) (by decide)),t'.tag] at mix
  have tail : Frame (⟨W,16⟩ :: wFrame W SP) b.mem z.mem :=
    ((tFrame_one fq).mono fun _ h => List.mem_cons_of_mem _ h).trans (fz.mono fun r h => by obtain rfl := List.mem_singleton.mp h;exact List.mem_cons_self ..)
  have same : bytesAt z.mem D (16*n)=bytesAt t.mem D (16*n) := by
    rw [bytesAt_frame tail (fun r hr => ?_) (Nat.le_of_lt d.ok.lt),bytesAt_frame f dataF (Nat.le_of_lt d.ok.lt)]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr;rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact d.ok.w.sub_right (Region.sub_prefix (by decide))
    · exact d.ok.w.sub_right (Lay.wSub (by decide))
    · exact d.ok.w.sub_right (Lay.wSub (by decide))
    · exact d.ok.w.sub_right (Lay.wSub (by decide))
    · exact d.ok.stk.symm
  refine ⟨ez,rz.trans (rq.trans (rx.trans (out.rd.trans (ru.trans t'.rd)))),wz.trans (wq.trans (wx.trans (out.wr.trans (wu.trans t'.wr)))),?_,same.trans t'.text,?_⟩
  · refine (t'.frame.sub ?_).trans ((f.sub ?_).trans (oneFrame_B (n:=16*n) (k:=0) (Nat.zero_le _) (by
      simpa using wFrame_one (W:=W) (D:=D) (n:=16*n) (o:=0) (.inl rfl) (by simpa only [BitVec.add_zero] using tail))))
    · intro r hr;simp only [preparedFrame,List.mem_cons,List.not_mem_nil,or_false] at hr;rcases hr with rfl|rfl|rfl|rfl
      · exact ⟨_,by simp,fun _ h => h⟩
      · exact ⟨⟨W+192#64,32⟩,by simp,Region.sub_prefix (by decide)⟩
      · exact ⟨⟨W+240#64,2320⟩,by simp,Offset.sub W (by decide) (by decide)⟩
      · exact ⟨below SP 24,by simp,below_sub (by decide) (by decide)⟩
    · intro r hr;simp only [F,List.mem_cons,List.not_mem_nil,or_false] at hr;rcases hr with rfl|rfl|rfl
      · exact ⟨⟨W,128⟩,by simp,by change Region.Sub ⟨W+16#64+16#64,16⟩ _;rw [BitVec.add_assoc];exact Offset.sub_base W (d:=32) (by decide)⟩
      · exact ⟨⟨W+240#64,2320⟩,by simp,Offset.sub W (by decide) (by decide)⟩
      · exact ⟨below SP 24,by simp,below_sub (by decide) (by decide)⟩
  · rw [Short.bytesAt_toBytes',mix,same]

private theorem batchChoice_step {s : State} {Ctx W SP : Addr} {n : Nat} (e : Env Ctx (W+16#64) W SP s)
    (len : s.mem.readW (W+208#64) 64=BitVec.ofNat 64 n) :
    ∃ t, runBlock isa [.mov .rax (.mem (at_ .r15 lenO)),.alu .sub .rax (imm 16),.shift .ror .rax 4,
      .alu .cmp .rax (imm 7)] s=some t ∧ t.cf=some (decide (((BitVec.ofNat 64 n-16#64).rotateRight 4).toNat<7)) ∧
      Env Ctx (W+16#64) W SP t ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  have read := e.perm.wR (show 208+8≤2560 by decide)
  refine ⟨_,by xrun [e.r15,read,len],?_,?_,?_,?_,?_⟩
  · rfl
  · exact e.keep (fun r h => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl <;> rfl) rfl rfl
  all_goals rfl

theorem softwareRecord_ok (v : GcmImpl) (ctr : Proof.Aes.X86_64.Ctr32ToImpl) {M : CtxMode} :
    RecordOk M (Contiguous.softwareBody v.callees ⟨ctr.callee.name,ctr.callee.code⟩ Contiguous.maskAES) := by
  intro o u Ctx W SP Np A S D nl al n C X geo wrap src dst E hp hl ha
  unfold Contiguous.softwareBody Contiguous.chooseBatch
  refine WP.seq ((oneMid_ok v C E hp hl ha).mono fun s m => ?_)
  obtain ⟨t,run,cf,et,mt,rt,wt⟩ := batchChoice_step m.env m.len
  have m' : OneMid o Ctx W SP D n (Spec.Gcm.ctxH o.mem Ctx) (bytesAt o.mem Np nl) (bytesAt o.mem A al) u.mem t :=
    ⟨et,mt ▸ m.hH,mt ▸ m.rounds,mt ▸ m.dat,mt ▸ m.len,mt ▸ m.alen,mt ▸ m.j0,
      mt ▸ m.abs,mt ▸ m.cb,mt ▸ m.saved,mt ▸ m.frame,mt ▸ m.fr,rt.trans m.rd,wt.trans m.wr⟩
  have aa := afterAad_ok C X geo wrap ha src dst m'
  refine WP.seq (WP.of_runBlock ⟨t,run,?_⟩)
  refine WP.ite _ cf (fun yes => ?_) (fun _ => ?_)
  · obtain ⟨k,hk,hn⟩ := batch_guard (BitVec.ofNat 64 n) (Nat.lt_of_lt_of_le (of_decide_eq_true yes) (show 7≤15 by decide))
    rw [toNat_ofNat_of_lt C.data.ok.lt] at hn
    subst n
    unfold Contiguous.batchMasks
    refine WP.seq ((batchKeys_ok (n:=k+1) (by omega) (by omega) C.lay et m'.rounds m'.len).mono fun a masks => ?_)
    refine WP.seq ((batchText_ok (by omega) (by omega) aa masks).mono fun b ct => ?_)
    refine (batchPost_ok v aa ct m'.hH m'.abs).mono fun z post => ?_
    rw [m'.j0] at post
    exact afterAad_to_seal C geo m' post
  · have bulk : BulkOk M (Contiguous.bulk (Contiguous.separate ⟨ctr.callee.name,ctr.callee.code⟩ v.callees.gh)) :=
      fun h ob a b c => separate_bulk_ok ctr v.gh h ob a b c
    have fin : FinishOk M (Contiguous.maskFinish v.callees Contiguous.maskAES) := choiceOk v (scalarMasks_ok v)
    exact (bulkFinish_ok bulk fin aa m'.hH m'.cb m'.abs).mono fun _ post => afterAad_to_seal C geo m' post

private theorem batchKeys_rel {Ctx W SP : Addr} {R n : Nat} (hn : 0<n) (hn' : n≤15)
    (L : Lay Ctx (W+16#64) W SP) :
    let F (s : State) := Env Ctx (W+16#64) W SP s ∧ RoundsAt s.mem W R ∧ s.mem.readW (W+208#64) 64=BitVec.ofNat 64 (16*n)
    RelCT isa (fun s t => F s ∧ F t) (Contiguous.batchKeys Contiguous.maskAES) (fun _ _ => True) := by
  let F (s : State) := Env Ctx (W+16#64) W SP s ∧ RoundsAt s.mem W R ∧ s.mem.readW (W+208#64) 64=BitVec.ofNat 64 (16*n)
  let G (s : State) := Env Ctx (W+16#64) W SP s ∧ RoundsAt s.mem W R ∧ s.gpr .rbp=BitVec.ofNat 64 (16*n)
  let P (s : State) := G s ∧ s.gpr .r10=0 ∧ ∃ J : Block, (s.gpr .r11).setWidth 32=J.extractLsb' 0 32 ∧
    VG.X86_64.XBinOp.eval .pshufb (s.xmm .xmm0) VG.Proof.Gcm.X86_64.revMask=J
  let B (s : State) := BCall s Ctx (W+256#64) (W+512#64) R (n+1) ∧ s.gpr .rsp=SP
  have prep s (f : F s) : WP isa (.block startMasks) s P :=
    (startMasks_ok f.1 f.2.2).mono fun a ⟨ea,_,_,al,zero,num,ax,fr,_,_⟩ =>
      ⟨⟨ea,rounds_frame fr (preparedLow L (.inl (by decide))) f.2.1,al⟩,zero,_,num,ax⟩
  have loop s (p : P s) : WP isa (.loop (.block (packOne++bumpMask)) .ne) s G := by
    obtain ⟨⟨e,rr,len⟩,zero,J,num,ax⟩ := p
    refine (packLoop_ok hn hn' e.r15 len zero e.perm.w J ax num).mono fun t ⟨g,rd,wr,fr,_⟩ => ?_
    refine ⟨e.keep (fun r h => by simp only [List.mem_cons,List.not_mem_nil,or_false] at h
                                  rcases h with rfl|rfl|rfl|rfl <;> exact g _ (by decide) (by decide) (by decide)) rd wr,
      ⟨?_,rr.2⟩,(g _ (by decide) (by decide) (by decide)).trans len⟩
    exact (fr.readW (r:=⟨W+176#64,8⟩) (Region.contains_self _ _) (by
      intro z hz
      obtain rfl := List.mem_singleton.mp hz
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by omega)) (by decide)).trans rr.1
  have arg s (g : G s) : WP isa (.block batchAESArgs) s B :=
    (batchArgs_ok hn' L g.1 g.2.1 g.2.2).mono fun _ ⟨ac,_,_,_,saved⟩ => ⟨ac,(saved _ (by decide)).trans g.1.rsp⟩
  unfold Contiguous.batchKeys
  refine RelCT.seq (rel_next (rel_env_regs [] (fun _ (h : F _) => h.1) (fun _ (h : F _) => h.1)
    (fun _ _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩) prep prep) ?_
  refine RelCT.seq (rel_next (rel_env_regs [.r10,.rbp] (fun _ (h : P _) => h.1.1) (fun _ (h : P _) => h.1.1)
    (fun _ _ a b r h => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl
      · rw [a.2.1,b.2.1]
      · rw [a.1.2.2,b.1.2.2]) ⟨_,by taint_decide⟩) loop loop) ?_
  refine RelCT.seq (rel_next (rel_env_regs [] (fun _ (h : G _) => h.1) (fun _ (h : G _) => h.1)
    (fun _ _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩) arg arg) ?_
  let aes := Proof.Aes.X86_64.BlocksImpl.scalar
  exact blk_rel aes.encOk aes.encCt (fun _ _ h => ⟨_,_,_,_,_,h.1.1,h.2.1,h.1.2.trans h.2.2.symm⟩)

private theorem batchText_rel {Ctx W SP S D : Addr} {n : Nat} :
    let F (s : State) := Env Ctx (W+16#64) W SP s ∧ InRegions (s.rd++s.wr) (SP+8#64) 8 ∧
      s.mem.readW (SP+8#64) 64=S ∧ s.mem.readW (W+200#64) 64=D ∧ s.gpr .rbp=BitVec.ofNat 64 (16*n)
    RelCT isa (fun s t => F s ∧ F t) Contiguous.batchText (fun _ _ => True) := by
  let F (s : State) := Env Ctx (W+16#64) W SP s ∧ InRegions (s.rd++s.wr) (SP+8#64) 8 ∧
    s.mem.readW (SP+8#64) 64=S ∧ s.mem.readW (W+200#64) 64=D ∧ s.gpr .rbp=BitVec.ofNat 64 (16*n)
  let G (s : State) := Env Ctx (W+16#64) W SP s ∧ s.gpr .rdi=S ∧ s.gpr .rsi=D ∧ s.gpr .r10=0 ∧ s.gpr .rbp=BitVec.ofNat 64 (16*n)
  have prep s (f : F s) : WP isa (.block maskPtrs) s G :=
    (ptrs_ok f.1 f.2.1 f.2.2.1 f.2.2.2.1).mono fun _ ⟨di,si,z,l,e,_,_,_⟩ => ⟨e,di,si,z,l.trans f.2.2.2.2⟩
  refine RelCT.seq (rel_next (rel_env_regs [] (fun _ (h : F _) => h.1) (fun _ (h : F _) => h.1)
    (fun _ _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩) prep prep) ?_
  exact rel_env_regs [.rdi,.rsi,.r10,.rbp] (fun _ (h : G _) => h.1) (fun _ (h : G _) => h.1)
    (fun _ _ a b r h => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl
      · rw [a.2.1,b.2.1]
      · rw [a.2.2.1,b.2.2.1]
      · rw [a.2.2.2.1,b.2.2.2.1]
      · rw [a.2.2.2.2,b.2.2.2.2]) ⟨_,by taint_decide⟩

private theorem batchAuth_rel (v : GcmImpl) {Ctx W SP D : Addr} {n al : Nat} (L : Lay Ctx (W+16#64) W SP) :
    let T (s : State) := Env Ctx (W+16#64) W SP s ∧ s.mem.readW (W+184#64) 64=BitVec.ofNat 64 al ∧ s.mem.readW (W+192#64) 64=BitVec.ofNat 64 n
    let F (s : State) := T s ∧ DataW Ctx (W+16#64) W SP s D n ∧ s.mem.readW (W+200#64) 64=D ∧ s.mem.readW (W+208#64) 64=BitVec.ofNat 64 n
    RelCT isa (fun s t => F s ∧ F t) (Contiguous.batchAuth v.callees) (fun _ _ => True) := by
  let E := Env Ctx (W+16#64) W SP
  let T (s : State) := E s ∧ s.mem.readW (W+184#64) 64=BitVec.ofNat 64 al ∧ s.mem.readW (W+192#64) 64=BitVec.ofNat 64 n
  let F (s : State) := T s ∧ DataW Ctx (W+16#64) W SP s D n ∧ s.mem.readW (W+200#64) 64=D ∧ s.mem.readW (W+208#64) 64=BitVec.ofNat 64 n
  let H (s : State) := T s ∧ GhCall s (Ctx+240#64) (yA W) D (W+448#64) (n/16)
  let A (s : State) := E s ∧ s.gpr .rbx=BitVec.ofNat 64 al ∧ s.gpr .rbp=BitVec.ofNat 64 n
  have arg s (f : F s) : WP isa (.block Contiguous.hashArgs) s H :=
    (hashArgs_ok L f.1.1 f.2.1 f.2.2.1 f.2.2.2).mono fun _ ⟨g,r,w,m,c⟩ => ⟨⟨f.1.1.of_saved g r w,m ▸ f.1.2⟩,c⟩
  have gh s (h : H s) : WP isa (Contiguous.call v.callees.gh) s T := by
    refine (gh_call v.gh h.2).mono fun t o => ?_
    have f := o.frame
    rw [h.1.1.rsp] at f
    have keep (p : Nat) (lo : 48≤p) (hi : p+8≤448) : t.mem.readW (W+BitVec.ofNat 64 p) 64=s.mem.readW (W+BitVec.ofNat 64 p) 64 := by
      apply f.readW (r:=⟨W+BitVec.ofNat 64 p,8⟩) (Region.contains_self _ _) _ (by decide)
      intro r hr;simp only [List.mem_cons,List.not_mem_nil,or_false] at hr;rcases hr with rfl|rfl|rfl
      · change (⟨W+BitVec.ofNat 64 p,8⟩ : Region).Disjoint ⟨W+16#64+16#64,16⟩
        rw [show W+16#64+16#64=W+32#64 by rw [BitVec.add_assoc];rfl]
        exact Offset.disjoint W (.inr (by omega)) (by omega) (by decide)
      · exact Offset.disjoint W (.inl hi) (by omega) (by decide)
      · exact (L.stk_w (by omega)).symm
    exact ⟨h.1.1.of_saved o.saved o.rd o.wr,(keep 184 (by decide) (by decide)).trans h.1.2.1,
      (keep 192 (by decide) (by decide)).trans h.1.2.2⟩
  have argL s (h : T s) : WP isa (.block authLens) s A := by
    obtain ⟨t,run,et,bx,bp,_,_,_⟩ := tagArgs h.1 h.2.1 h.2.2
    exact WP.of_runBlock ⟨t,run,et,bx,bp⟩
  have ln s (h : A s) : WP isa (lens v.callees 16) s E := (lens_ok v L (.inr rfl) h.1 rfl).mono fun _ out => out.1
  unfold Contiguous.batchAuth
  refine RelCT.seq (rel_next (rel_env_regs [] (fun _ (h : F _) => h.1.1) (fun _ (h : F _) => h.1.1)
    (fun _ _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩) arg arg) ?_
  refine RelCT.seq (rel_next (gh_rel v.gh (fun _ _ h => ⟨_,_,_,_,_,h.1.2,h.2.2,h.1.1.1.rsp.trans h.2.1.1.rsp.symm⟩)) gh gh) ?_
  refine RelCT.seq (rel_next (rel_env_regs [] (fun _ (h : T _) => h.1) (fun _ (h : T _) => h.1)
    (fun _ _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩) argL argL) ?_
  refine RelCT.seq (rel_next ((lens_rel v L (.inr rfl)).mono ?_ (fun _ _ h => h)) ln ln) ?_
  · intro a b h
    refine ⟨h.1.1,h.2.1,?_⟩
    intro r hr;simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · rw [h.1.2.1,h.2.2.1]
    · rw [h.1.2.2,h.2.2.2]
  · exact rel_env_regs [] (fun _ (h : E _) => h) (fun _ h => h) (fun _ _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩

private theorem batch_rel (v : GcmImpl) {Ctx W SP S D : Addr} {M : CtxMode} {n R al : Nat}
    (hn : 0<n) (hn' : n≤15) (L : Lay Ctx (W+16#64) W SP) :
    let F := AfterAad M Ctx W SP S D R (16*n) al
    RelCT isa (fun s t => F s ∧ F t) (Contiguous.batchMasks v.callees Contiguous.maskAES) (fun _ _ => True) := by
  let F := AfterAad M Ctx W SP S D R (16*n) al
  let G (s : State) := ∃ o, F o ∧ Masked Ctx W SP R n o s
  let T (s : State) := ∃ o, F o ∧ Ciphered Ctx W SP S D R n o s
  have keys s (aa : F s) : WP isa (Contiguous.batchKeys Contiguous.maskAES) s G :=
    (batchKeys_ok hn hn' L aa.ob.env aa.ob.rounds aa.ob.len).mono fun _ m => ⟨s,aa,m⟩
  have text s (g : G s) : WP isa Contiguous.batchText s T := by
    obtain ⟨o,aa,m⟩ := g
    exact (batchText_ok hn hn' aa m).mono fun _ t => ⟨o,aa,t⟩
  have ptrs s (g : G s) : Env Ctx (W+16#64) W SP s ∧ InRegions (s.rd++s.wr) (SP+8#64) 8 ∧
      s.mem.readW (SP+8#64) 64=S ∧ s.mem.readW (W+200#64) 64=D ∧ s.gpr .rbp=BitVec.ofNat 64 (16*n) := by
    obtain ⟨o,aa,m⟩ := g
    exact ⟨m.env,by rw [m.rd,m.wr];exact aa.read,(m.frame.readW (Region.contains_self _ _)
      (preparedFar aa.apart (Offset.disjoint_below SP (by decide))) (by decide)).trans aa.src,
      (m.frame.readW (Region.contains_self _ _) (preparedLow L (.inr ⟨by decide,by decide⟩)) (by decide)).trans aa.ob.dat,m.rbp⟩
  have auth s (t : T s) : (Env Ctx (W+16#64) W SP s ∧ s.mem.readW (W+184#64) 64=BitVec.ofNat 64 al ∧
      s.mem.readW (W+192#64) 64=BitVec.ofNat 64 (16*n)) ∧ DataW Ctx (W+16#64) W SP s D (16*n) ∧
      s.mem.readW (W+200#64) 64=D ∧ s.mem.readW (W+208#64) 64=BitVec.ofNat 64 (16*n) := by
    obtain ⟨o,aa,m⟩ := t
    have saved (p : Nat) (lo : p+8≤192 ∨ (200≤p ∧ p+8≤256)) :
        s.mem.readW (W+BitVec.ofNat 64 p) 64=o.mem.readW (W+BitVec.ofNat 64 p) 64 :=
      m.frame.readW (Region.contains_self _ _) (fun r hr => by
        rcases List.mem_cons.mp hr with rfl|h
        · exact aa.ob.data.ok.w.symm.sub_left (Lay.wSub (by rcases lo with h|h <;> omega))
        · exact preparedLow L lo r h) (by decide)
    exact ⟨⟨m.env,(saved 184 (.inl (by decide))).trans aa.alen,m.len⟩,aa.ob.data.of_eq m.rd m.wr,
      (saved 200 (.inr ⟨by decide,by decide⟩)).trans aa.ob.dat,(saved 208 (.inr ⟨by decide,by decide⟩)).trans aa.ob.len⟩
  unfold Contiguous.batchMasks
  refine RelCT.seq (rel_next ((batchKeys_rel hn hn' L).mono (fun _ _ (h : F _ ∧ F _) =>
    ⟨⟨h.1.ob.env,h.1.ob.rounds,h.1.ob.len⟩,⟨h.2.ob.env,h.2.ob.rounds,h.2.ob.len⟩⟩) (fun _ _ h => h)) keys keys) ?_
  exact RelCT.seq (rel_next (batchText_rel.mono (fun _ _ h => ⟨ptrs _ h.1,ptrs _ h.2⟩) (fun _ _ h => h)) text text)
    ((batchAuth_rel v L).mono (fun _ _ h => ⟨auth _ h.1,auth _ h.2⟩) (fun _ _ h => h))

theorem softwareRecord_ct (v : GcmImpl) (ctr : Proof.Aes.X86_64.Ctr32ToImpl) {M : CtxMode} :
    RecordCT M (Contiguous.softwareBody v.callees ⟨ctr.callee.name,ctr.callee.code⟩ Contiguous.maskAES) := by
  intro o p Ctx W SP Np A S D nl al n R a b
  let F := AfterAad M Ctx W SP S D R n al
  let flag := decide (((BitVec.ofNat 64 n-16#64).rotateRight 4).toNat<7)
  let G (s : State) := F s ∧ s.cf=some flag
  have guard s (aa : F s) : WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)),.alu .sub .rax (imm 16),.shift .ror .rax 4,
      .alu .cmp .rax (imm 7)]) s G := by
    obtain ⟨t,run,cf,et,mt,rt,wt⟩ := batchChoice_step aa.reg.env aa.ob.len
    refine WP.of_runBlock ⟨t,run,?_,cf⟩
    let ext : CtxExt M Ctx (W+16#64) W SP D n t := { aa.reg.ext with
      cov := by rw [rt,wt];exact aa.reg.ext.cov
      ok := mt ▸ aa.reg.ext.ok }
    let reg : Split.SealRegions M Ctx W SP D S R n n t := { aa.reg with
      env := et, rounds := mt ▸ aa.reg.rounds, data := aa.reg.data.of_eq rt wt, ext := ext
      srcCov := by rw [rt,wt];exact aa.reg.srcCov }
    let ob : ObPre M Ctx W SP R D n t := { aa.ob with
      env := et, rounds := mt ▸ aa.ob.rounds, data := aa.ob.data.of_eq rt wt,
      dat := mt ▸ aa.ob.dat, len := mt ▸ aa.ob.len, ext := ext }
    exact ⟨⟨reg,ob,by rw [rt,wt];exact aa.read,mt ▸ aa.src,aa.apart⟩,mt ▸ aa.alen,mt ▸ aa.dst,
      by rw [rt,wt];exact aa.slotRead,aa.dstWork,aa.dstOut,aa.slotDst⟩
  unfold Contiguous.softwareBody Contiguous.chooseBatch
  refine RelCT.seq (ordinaryAad_ct v a b) (RelCT.seq (rel_next (rel_env_regs [] (fun _ (h : F _) => h.ob.env)
    (fun _ (h : F _) => h.ob.env) (fun _ _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩) guard guard) ?_)
  refine RelCT.ite (fun _ _ h => h.1.2.trans h.2.2.symm) ?_ ?_
  · apply Split.rel_each
    intro x y ⟨⟨hx,hy⟩,take⟩
    have eq : flag=true := Option.some.inj (hx.2.symm.trans take)
    obtain ⟨k,hk,hn⟩ := batch_guard _ (Nat.lt_of_lt_of_le (of_decide_eq_true eq) (show 7≤15 by decide))
    rw [toNat_ofNat_of_lt a.ctx.data.ok.lt] at hn
    subst n
    refine (batch_rel v (M:=M) (S:=S) (D:=D) (R:=R) (al:=al) (n:=k+1) (by omega) (by omega) a.ctx.lay).mono ?_ (fun _ _ h => h)
    intro u w hu
    rw [hu.1,hu.2]
    exact ⟨hx.1,hy.1⟩
  · have bulk : BulkOk M (Contiguous.bulk (Contiguous.separate ⟨ctr.callee.name,ctr.callee.code⟩ v.callees.gh)) :=
      fun h ob x y z => separate_bulk_ok ctr v.gh h ob x y z
    have fin : FinishCT M (Contiguous.maskFinish v.callees Contiguous.maskAES) := choiceCT (alignedTag_ct v) (scalarMasks_ct v)
    exact (run_ct bulk (separate_ct ctr v.gh) (separate_keeps ctr v.gh) fin a.ctx.lay (a.rounds ▸ a.ctx.rounds) a.ctx.dE).mono
      (fun _ _ h => ⟨h.1.1.1,h.1.2.1⟩) (fun _ _ h => h)

end VG.Proof.AesGcm.X86_64.ContiguousSeal
