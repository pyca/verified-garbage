module

-- separate module: The body-to-payload precondition proof depends on the concrete register and workspace layout.

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.PayloadCT
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.Exit
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.OneBs
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset

/-! # From the contiguous call arguments to the common RISC-V seal payload -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Gcm (Block blockAt j0 ctxH inc32 zeros padLen)
open VG.Spec.Aes (bytesAt)

/-- Values read from the public contiguous bitsliced calling convention. -/
structure Args where
  ctx : Addr
  rounds : Nat
  iv : Addr
  ivLen : Addr
  aad : Addr
  aadLen : Addr
  src : Addr
  dst : Addr
  len : Addr
  tag : Addr
  keys : Addr
  work : Addr
  sp : Addr

abbrev Args.st (p : Args) := p.work+BitVec.ofNat 64 16

@[expose] def Args.regs (p : Args) (payload : Bool) : Reg → Addr
  | .s0 => p.work
  | .s1 => p.st
  | .s2 => p.ctx
  | .s3 => BitVec.ofNat 64 p.rounds
  | .s7 => if payload then p.keys else p.ivLen
  | .s8 => p.dst
  | .s9 => if payload then p.dst-p.src else p.tag
  | .s10 => p.aadLen
  | .s11 => p.len
  | _ => 0

structure ArgsAt (p : Args) (s : State) : Prop where
  shape : EntryArgs s p.work p.tag
  sp : s.sp=p.sp
  ctx : s.gpr .a0=p.ctx
  nr : s.gpr .a1=BitVec.ofNat 64 p.rounds
  iv : s.gpr .a2=p.iv
  ivLen : s.gpr .a3=p.ivLen
  aad : s.gpr .a4=p.aad
  aadLen : s.gpr .a5=p.aadLen
  src : s.gpr .a6=p.src
  dst : s.gpr .a7=p.dst
  len : stackArg s 0=p.len
  bk : stackArg s 2=p.keys
  lay : Lay p.ctx p.st p.work
  stk : StkOk p.ctx p.st p.work p.sp
  ctxRead : Covers [⟨p.ctx,256⟩] (s.rd++s.wr)
  ivRead : DataOk p.st p.work s p.iv p.ivLen.toNat
  aadRead : DataOk p.st p.work s p.aad p.aadLen.toNat
  srcRead : DataOk p.st p.work s p.src p.len.toNat
  dstWrite : DataW p.ctx p.st p.work s p.dst p.len.toNat
  buffers : Alias true p.src p.dst p.len.toNat
  tagWrite : Covers [⟨p.tag,16⟩] s.wr
  tagWork : (⟨p.tag,16⟩ : Region).Disjoint ⟨p.work,2560⟩
  tagData : (⟨p.tag,16⟩ : Region).Disjoint ⟨p.dst,p.len.toNat⟩
  stackWork : (args s 4).Disjoint ⟨p.work,2560⟩
  stackData : (args s 4).Disjoint ⟨p.dst,p.len.toNat⟩
  stackBelow : (args s 4).Disjoint (below p.sp 2048)
  rounds : p.rounds=10 ∨ p.rounds=12 ∨ p.rounds=14
  keys : BkIn p.keys p.ctx p.st p.work p.sp p.rounds s.mem p.src p.dst p.len.toNat s

structure BeforeAad (p : Args) (s t : State) : Prop where
  env : Env (p.regs false) p.sp t
  keeps : Keeps' s t
  saved : SavedAt t.mem p.work s
  frame : Frame [oneR p.work] s.mem t.mem
  nonce : t.gpr .s4=p.iv
  nonceLen : t.gpr .s5=p.ivLen
  aad : t.mem.readW (p.work+BitVec.ofNat 64 aadO) 64=p.aad
  src : t.mem.readW (p.work+BitVec.ofNat 64 dataO) 64=p.src

theorem begin_wp {p : Args} {s : State} (h : ArgsAt p s) :
    WP isa (.block VG.Impl.AesGcm.RISCV64.Contiguous.entry) s (BeforeAad p s) := by
  refine WP.mono (entry_wp h.shape) fun v got => ?_
  obtain ⟨u,z,eq⟩ := got
  subst v
  let t := (u.write .s8 (s.gpr .a7)).write .s11 (stackArg s 0)
  have eu := one_env z (h.ctx ▸ h.ctxRead) h.shape.work (by rw [h.ctx,h.sp];exact h.stk)
  have regs : ∀ r ∈ frozen,t.gpr r=p.regs false r := by
    intro r hr;cases r <;> simp_all [frozen,t,State.write,Args.regs,z.s0,z.s1,z.s2,z.s3,z.s7,z.s10,z.s9,h.ctx,h.nr,h.ivLen,h.aadLen,h.len,h.dst]
  refine ⟨⟨regs,eu.sp.trans h.sp,?_,?_⟩,⟨z.keeps.rd,z.keeps.wr,z.keeps.sp⟩,z.saved,z.frame,?_,?_,z.aad.trans h.aad,z.dat.trans h.src⟩
  · change Perm p.ctx p.st p.work t
    simpa only [z.s2,z.s1,z.s0,h.ctx] using eu.perm.of_eq (s' := t) rfl rfl
  · change StkOk p.ctx p.st p.work u.sp
    rw [z.keeps.sp,h.sp];exact h.stk
  · simpa [State.write] using z.s4.trans h.iv
  · simpa [State.write] using z.s5.trans h.ivLen

abbrev beforeFrame (p : Args) := oneR p.work :: j0Frame p.st p.work p.sp

structure AfterAad (p : Args) (s t : State) : Prop where
  auth : ∃ m, OA (p.regs false) p.sp (ctxH s.mem p.ctx) (bytesAt s.mem p.iv p.ivLen.toNat)
    (bytesAt s.mem p.aad p.aadLen.toNat) m t
  keeps : Keeps' s t
  saved : SavedAt t.mem p.work s
  frame : Frame (beforeFrame p) s.mem t.mem
  aad : t.mem.readW (p.work+BitVec.ofNat 64 aadO) 64=p.aad
  src : t.mem.readW (p.work+BitVec.ofNat 64 dataO) 64=p.src

theorem before_apart {p : Args} {r : Region} (w : r.Disjoint ⟨p.work,2560⟩) (b : r.Disjoint (below p.sp 2048)) :
    ∀ q ∈ beforeFrame p,r.Disjoint q := by
  intro q h
  simp only [beforeFrame,j0Frame,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact w.sub_right (Lay.wSub (by decide))
  · exact w.sub_right (Lay.wSub (by decide))
  · exact w.sub_right (Lay.wSub (by decide))
  · exact w.sub_right (Lay.wSub (by decide))
  · exact b

abbrev sealAction (invoke : Prog isa) (p : Args) (s : State) :=
  FramedHashAction invoke (p.ctx+BitVec.ofNat 64 240) (sealWrites p.st p.work p.dst p.sp p.len.toNat) s

theorem before_sealSub {p : Args} : ∀ r∈beforeFrame p,∃ q∈sealWrites p.st p.work p.dst p.sp p.len.toNat,r.Sub q := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl|other
  · exact ⟨⟨p.work,2560⟩,by simp [sealWrites],Lay.wSub (by decide)⟩
  · exact j0_sealSub _ other

theorem aad_wp {invoke : Prog isa} {p : Args} {s v : State} (h : ArgsAt p s) (e : BeforeAad p s v) (exec : sealAction invoke p s) :
    WP isa (oneAadWith invoke) v (AfterAad p s) := by
  have cx : blockAt v.mem (p.ctx+BitVec.ofNat 64 240)=ctxH s.mem p.ctx := ctxH_keep e.frame (fun r hr => by obtain rfl := List.mem_singleton.mp hr;exact h.lay.cw'.sub_right (Lay.wSub (by decide)))
  have iv : bytesAt v.mem p.iv p.ivLen.toNat=bytesAt s.mem p.iv p.ivLen.toNat := bytesAt_frame e.frame (fun r hr => by obtain rfl := List.mem_singleton.mp hr;exact h.ivRead.w.sub_right (Lay.wSub (by decide))) (by exact Nat.le_of_lt p.ivLen.isLt)
  have ad : bytesAt v.mem p.aad p.aadLen.toNat=bytesAt s.mem p.aad p.aadLen.toNat := bytesAt_frame e.frame (fun r hr => by obtain rfl := List.mem_singleton.mp hr;exact h.aadRead.w.sub_right (Lay.wSub (by decide))) (by exact Nat.le_of_lt p.aadLen.isLt)
  have fr₀ : Frame (sealWrites p.st p.work p.dst p.sp p.len.toNat) s.mem v.mem := e.frame.sub fun r hr =>
    before_sealSub r (List.mem_cons.mpr (.inl (List.mem_singleton.mp hr)))
  refine WP.mono (WP.with_rdwr (oneAad_ok_with (V := p.regs false) h.lay e.env cx e.nonce
    (n := p.ivLen.toNat) (by simpa using e.nonceLen) (by simp [Args.regs])
    (h.ivRead.of_eq e.keeps.rd e.keeps.wr e.keeps.sp) (h.aadRead.of_eq e.keeps.rd e.keeps.wr e.keeps.sp) e.aad (FramedHashAction.narrow (FramedHashAction.after exec e.keeps fr₀) j0_sealSub)))
    fun t ⟨oa,rd,wr,sp⟩ => ?_
  change OA _ _ _ (bytesAt v.mem p.iv p.ivLen.toNat) (bytesAt v.mem p.aad p.aadLen.toNat) _ _ at oa
  rw [iv,ad] at oa
  have fr : Frame (beforeFrame p) s.mem t.mem :=
    (e.frame.mono (fun r hr => List.mem_cons.mpr (.inl (List.mem_singleton.mp hr)))).trans
      (oa.frame.mono (fun r hr => List.mem_cons_of_mem _ hr))
  refine ⟨⟨v.mem,oa⟩,⟨rd.trans e.keeps.rd,wr.trans e.keeps.wr,sp.trans e.keeps.sp⟩,
    e.saved.frame oa.frame (saved_j0Frame h.lay h.stk),fr,?_,?_⟩
  · exact (slot_keep oa.frame (slot_j0 h.lay h.stk (by decide))).trans e.aad
  · exact (slot_keep oa.frame (slot_j0 h.lay h.stk (by decide))).trans e.src

structure Prepared (p : Args) (s t : State) : Prop where
  payload : PayloadIn (p.regs true) p.sp p.src p.dst p.rounds (ctxH s.mem p.ctx) (bytesAt s.mem p.aad p.aadLen.toNat) t
  j : blockAt t.mem p.st=j0 (ctxH s.mem p.ctx) (bytesAt s.mem p.iv p.ivLen.toNat)
  aad : t.mem.readW (p.work+BitVec.ofNat 64 aadO) 64=p.aad
  cut : t.gpr .t0=241
  saved : SavedAt t.mem p.work s
  frame : Frame (beforeFrame p) s.mem t.mem
  keeps : Keeps' s t

private theorem slot_arg {p : Args} {s t : State} (h : ArgsAt p s) (sp : t.sp=s.sp) (i : Nat) (hi : i<4)
    (frame : Frame (beforeFrame p) s.mem t.mem) : stackArg t i=stackArg s i := by
  unfold stackArg stackArgAddr
  rw [sp]
  exact slot_keep frame (fun r hr => (before_apart h.stackWork h.stackBelow r hr).sub_left
    (Offset.sub s.sp (d := 8*i) (n := 8) (e := 0) (k := 32) (by omega) (by omega)))

theorem prepare_wp {p : Args} {s v : State} (h : ArgsAt p s) (e : AfterAad p s v) :
    WP isa (.block (VG.Impl.AesGcm.RISCV64.Contiguous.payloadArgs ++ ([.li .t0 241] : List Instr))) v (Prepared p s) := by
  obtain ⟨_,oa⟩ := e.auth
  have vv (r : Reg) (hr : r ∈ frozen) := oa.env.fr r hr
  have w : v.gpr .s0=p.work := vv _ (by decide)
  have dst : v.gpr .s8=p.dst := vv _ (by decide)
  have ln : v.gpr .s11=p.len := vv _ (by decide)
  have sp := e.keeps.sp.trans h.sp
  have bk : v.mem.readW (v.sp+BitVec.ofNat 64 16) 64=p.keys := (slot_arg h e.keeps.sp 2 (by decide) e.frame).trans h.bk
  rw [WP.block_append_iff]
  have vW : Covers [⟨p.work,2560⟩] v.wr := e.keeps.wr ▸ h.shape.work
  refine WP.mono (payloadArgs_wp (by rw [w];exact h.lay.wal8 (by decide) (by decide))
    (by rw [w];exact in_off vW (by decide) (by decide))
    (by rw [e.keeps.sp];exact Spill.al8 (by have := h.shape.spAlign;omega) (by decide))
    (by rw [e.keeps.rd,e.keeps.wr,e.keeps.sp]; exact h.shape.slot 2 (by decide))) fun _ eq => ?_
  subst_vars
  let t := (payloadState v).write .t0 241
  have step : WP isa (.block [.li .t0 241]) (payloadState v) (· = t) := Steps.WP.cons (exec_li (by decide)) (WP.block_nil rfl)
  refine WP.mono step fun _ eq => ?_
  subst_vars
  have src : v.mem.readW (v.gpr .s0+BitVec.ofNat 64 dataO) 64=p.src := w ▸ e.src
  have gr (r : Reg) (hr : r ∈ frozen) : t.gpr r=p.regs true r := by
    have z := vv r hr
    simp only [frozen,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [t,payloadState,State.write,src,dst,bk,z,Args.regs]
  have eu : Env (p.regs true) p.sp t :=
    ⟨gr,sp,oa.env.perm.of_eq (s' := t) rfl rfl,by change StkOk p.ctx p.st p.work v.sp;rw [sp];exact h.stk⟩
  have mem : t.mem=v.mem.writeW (p.work+BitVec.ofNat 64 dataO) p.dst := by simp [t,payloadState,State.write,w,dst]
  have f : Frame [⟨p.work+BitVec.ofNat 64 dataO,8⟩] v.mem t.mem := by
    rw [mem];exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have wf : (⟨p.work+BitVec.ofNat 64 dataO,8⟩ : Region).Sub ⟨p.work,2560⟩ := Lay.wSub (by decide)
  have fr : Frame (beforeFrame p) s.mem t.mem := e.frame.trans (f.sub (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_self ..,Offset.sub p.work (d := dataO) (n := 8) (e := 128) (k := 120) (by decide) (by decide)⟩))
  have non (R : Region) (sep : R.Disjoint ⟨p.work+BitVec.ofNat 64 dataO,8⟩) : ∀ r ∈ [⟨p.work+BitVec.ofNat 64 dataO,8⟩],R.Disjoint r :=
    fun _ hr => List.mem_singleton.mp hr ▸ sep
  have sblock (d : Nat) (bound : d+16≤80) :
      blockAt t.mem (p.st+BitVec.ofNat 64 d)=blockAt v.mem (p.st+BitVec.ofNat 64 d) :=
    blockAt_frame f (non _ (h.lay.st_w bound (.inr ⟨by decide,by decide⟩)))
  have j' : blockAt t.mem p.st=j0 (ctxH s.mem p.ctx) (bytesAt s.mem p.iv p.ivLen.toNat) :=
    (by simpa using sblock 0 (by decide) : blockAt t.mem p.st=blockAt v.mem p.st) |>.trans oa.j
  have key := h.keys.frame h.rounds fr (before_apart h.keys.w h.keys.sk) (before_apart h.lay.cw' h.stk.c)
    (s' := t) e.keeps.rd e.keeps.wr
  have ads := (slot_keep f (non _ (Lay.w_w (w := p.work) (a := aadO) (n := 8) (d := dataO) (k := 8)
    (.inl (by decide)) (by decide) (by decide)))).trans e.aad
  refine ⟨⟨eu,?_,gr _ (by decide),?_,rfl,
    h.srcRead.of_eq e.keeps.rd e.keeps.wr e.keeps.sp,h.dstWrite.of_eq e.keeps.rd e.keeps.wr e.keeps.sp,
    h.buffers,rfl,h.rounds,key,?_,(length_bytesAt _ _ _).symm,?_,?_,?_⟩,j',ads,rfl,?_,fr,
    ⟨e.keeps.rd,e.keeps.wr,e.keeps.sp⟩⟩
  · simp [t,payloadState,State.write,src]
  · simp [t,payloadState,State.write,ln,Args.regs]
  · exact (blockAt_frame f (non _ ((h.lay.cw'.sub_left (Lay.ctxSub (by decide))).sub_right wf))).trans oa.hH
  · exact oa.abs.congr (sblock 16 (by decide))
      (bytesAt_frame f (non _ (h.lay.st_w (by omega) (.inr ⟨by decide,by decide⟩))) (by omega))
  · change t.mem.readW (p.work+BitVec.ofNat 64 dataO) 64=p.dst
    rw [mem,Mem.readW_writeW_self64]
  · exact (sblock 48 (by decide)).trans (oa.cb.trans (congrArg inc32 j'.symm))
  · exact e.saved.frame f (non _ (Offset.disjoint p.work (.inl (by decide)) (by decide) (by decide)))

end VG.Proof.AesGcm.RISCV64.Contiguous
