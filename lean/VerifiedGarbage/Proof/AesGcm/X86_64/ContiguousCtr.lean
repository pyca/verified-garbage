module
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousBulk
import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Whole
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Contiguous
/-! Counter and authentication calls for CPUs without a fused bulk loop. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (blocksAt blockAt ctr32 ctxH ctxCiph ghashFrom inc32)
open Split (SealRegions)

theorem inputData {M : CtxMode} {Ctx W SP S D : Addr} {R n : Nat} {s : State}
    (h : SealRegions M Ctx W SP D S R n n s) : DataOk (W+16#64) W SP s S n :=
  ⟨h.srcCov,h.data.ok.lt,h.sWrap,h.sW.sub_right (Lay.wSub (by decide)),h.sW,
   h.ks.sub_left (below_sub (by decide) (by decide))⟩

theorem ctrArgs_ok {M : CtxMode} {Ctx W SP S D : Addr} {R n q : Nat} {s : State}
    (h : SealRegions M Ctx W SP D S R n n s) (hq : 16*q≤n)
    (qreg : s.gpr .rax = BitVec.ofNat 64 q)
    (read : InRegions (s.rd++s.wr) (SP+8#64) 8) (src : s.mem.readW (SP+8#64) 64 = S)
    (dst : s.mem.readW (W+200#64) 64 = D) :
    WP isa (.block Contiguous.ctrArgs) s fun t =>
      (∀ z ∈ calleeSaved, t.gpr z = s.gpr z) ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.mem=s.mem ∧
      CtrToCall t Ctx (cbA W) S D (W+448#64) R q := by
  have e := h.env
  have rr := h.rounds.1
  have rd := e.perm.wR (show 176+8 ≤ 2560 by decide)
  have dd := e.perm.wR (show 200+8 ≤ 2560 by decide)
  have x := inputData h
  have geo : S=D ∨ (⟨S,16*q⟩ : Region).Disjoint ⟨D,16*q⟩ :=
    h.sD.imp id (fun u => (u.sub_left (Region.sub_prefix hq)).sub_right (Region.sub_prefix hq))
  unfold Contiguous.ctrArgs
  apply WP.of_runBlock
  refine ⟨_, by xrun [Contiguous.src,e.rsp,e.r15,read,src,dst,rd,dd,rr], ?_⟩
  generalize hb : (State.setReg _ .r9 _) = t
  have keep (z : Reg) (hz : z ∈ calleeSaved) : t.gpr z = s.gpr z := by
    subst t
    simp only [calleeSaved,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [gpr_setReg]
  refine ⟨keep, by subst t; rfl, by subst t; rfl, by subst t; rfl, ?_⟩
  have et := e.of_saved keep (by subst t; rfl) (by subst t; rfl)
  apply DirectGather.ctrCallArgs (offset:=448) (by decide) h.lay et
    ((x.take hq).of_eq (by subst t; rfl) (by subst t; rfl))
    ((h.data.take hq).of_eq (by subst t; rfl) (by subst t; rfl)) geo h.rounds.2
  all_goals subst t; simp [gpr_setReg, e.r13, e.r14, bScrO, qreg]

theorem hashArgs_ok {Ctx W SP D : Addr} {n : Nat} {s : State}
    (L : Lay Ctx (W+16#64) W SP) (e : Env Ctx (W+16#64) W SP s)
    (d : DataW Ctx (W+16#64) W SP s D n)
    (dst : s.mem.readW (W+200#64) 64 = D) (len : s.mem.readW (W+208#64) 64 = BitVec.ofNat 64 n) :
    WP isa (.block Contiguous.hashArgs) s fun t =>
      (∀ z ∈ calleeSaved, t.gpr z = s.gpr z) ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.mem=s.mem ∧
      GhCall t (Ctx+240#64) (yA W) D (W+448#64) (n/16) := by
  have rr := e.perm.wR (show 208+8 ≤ 2560 by decide)
  have dd := e.perm.wR (show 200+8 ≤ 2560 by decide)
  have shift := shr4 n d.ok.lt
  have q : 16*(n/16)≤n := Nat.mul_div_le _ _
  have buf := d.take q
  unfold Contiguous.hashArgs
  apply WP.of_runBlock
  refine ⟨_, by xrun [e.r15,rr,dd,dst,len,shift], ?_⟩
  generalize hb : (State.setReg _ .r8 _) = t
  have keep (z : Reg) (hz : z ∈ calleeSaved) : t.gpr z = s.gpr z := by
    subst t
    simp only [calleeSaved,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [gpr_setReg, gpr_setFlags]
  have sp := (keep _ (by decide)).trans e.rsp
  refine ⟨keep, by subst t; rfl, by subst t; rfl, by subst t; rfl, ?_⟩
  refine ⟨?_,?_,?_,?_,?_,buf.ok.lt,L.ctx_st (by decide) (by decide),L.ctx_w (by decide) (by decide),
    (buf.ok.st.sub_right (Lay.stSub (by decide))).symm,L.st_w (by decide) (.inr ⟨by decide,by decide⟩),
    buf.ok.w.sub_right (Lay.wSub (by decide)),?_,?_,?_,?_,?_,?_⟩
  · subst t; simp [gpr_setReg, gpr_setFlags, e.r13]
  · subst t; simp [gpr_setReg, gpr_setFlags, e.r14]
  · subst t; simp [gpr_setReg, gpr_setFlags]
  · subst t; simp [gpr_setReg]
  · subst t; simp [gpr_setReg, bScrO]
  · rw [sp]; exact L.stk_ctx (by decide)
  · rw [sp]; exact L.stk_st (by decide)
  · rw [sp]; exact buf.ok.stk
  · rw [sp]; exact L.stk_w (by decide)
  · subst t; exact covers_cons (e.perm.ctxC (by decide)) (covers_cons buf.ok.rd
      (covers_cons (covers_left (e.perm.stC (by decide))) (covers_left (e.perm.wC (by decide)))))
  · subst t; exact covers_cons (e.perm.stC (by decide)) (e.perm.wC (by decide))


theorem separate_ok {M : CtxMode} (ctr : Proof.Aes.X86_64.Ctr32ToImpl) (gh : GhashImpl)
    {Ctx W SP D S : Addr} {R n : Nat} {s : State}
    (h : SealRegions M Ctx W SP D S R n n s) (qreg : s.gpr .rax = BitVec.ofNat 64 (n/16))
    (read : InRegions (s.rd++s.wr) (SP+8#64) 8) (src : s.mem.readW (SP+8#64) 64 = S)
    (dst : s.mem.readW (W+200#64) 64 = D) (len : s.mem.readW (W+208#64) 64 = BitVec.ofNat 64 n) :
    WP isa (Contiguous.separate ⟨ctr.callee.name,ctr.callee.code⟩ gh.fn) s fun t =>
      (∀ z ∈ calleeSaved, t.gpr z = s.gpr z) ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      Frame (obFrame (W+16#64) W SP D (n/16)) s.mem t.mem ∧ BlocksResult Ctx W R S D (n/16) s t := by
  let q := n/16
  have hq : 16*q ≤ n := Nat.mul_div_le _ _
  have Dq := h.data.take hq
  have dW := Dq.ok.w
  have kS : Region.Sub (below SP 8) (below SP 24) := below_sub (by decide) (by decide)
  have kW := h.kw.sub_left (below_sub (by decide : 24≤56) (by decide))
  have L := h.lay
  unfold Contiguous.separate Contiguous.call
  refine WP.seq ((ctrArgs_ok h hq qreg read src dst).mono fun u ⟨gu,ru,wu,mu,c⟩ => ?_)
  refine WP.seq ((ctrTo_call ctr c).mono fun v hc => ?_)
  have eu := h.env.of_saved gu ru wu
  have ev := eu.of_saved hc.saved hc.rd hc.wr
  have df := Dq.of_eq (hc.rd.trans ru) (hc.wr.trans wu)
  have full := h.data.of_eq (hc.rd.trans ru) (hc.wr.trans wu)
  have ctrframe := hc.frame
  rw [eu.rsp,mu] at ctrframe
  have cf : Frame (obFrame (W+16#64) W SP D q) s.mem v.mem := by
    refine ctrframe.sub fun r hr => ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact ⟨_,List.mem_cons_self ..,fun _ hx => hx⟩
    · exact ⟨⟨D,q*16⟩,by simp [obFrame],Region.sub_prefix (by omega_arith)⟩
    · exact ⟨⟨W+448#64,2112⟩,by simp [obFrame],Region.sub_prefix (by decide)⟩
    · exact ⟨below SP 24,by simp [obFrame],kS⟩
  have slot {j : Nat} (lo : 176≤j) (hi : j+8≤240) :=
    cf.readW (w:=64) (r:=⟨W+BitVec.ofNat 64 j,8⟩) (Region.contains_self _ _) (ob_slots L h.data.ok.w (by omega_arith : q*16≤n) kW lo hi) (by decide)
  have dj := (slot (by decide : 176≤200) (by decide)).trans dst
  have nj := (slot (by decide : 176≤208) (by decide)).trans len
  have hHash := hashArgs_ok L ev full dj nj
  refine WP.seq (hHash.mono fun x ⟨gx,rx,wx,mx,a⟩ => ?_)
  refine (gh_call gh a).mono fun t hh => ?_
  have ex := ev.of_saved gx rx wx
  have hashframe := hh.frame
  rw [ex.rsp,mx] at hashframe
  have hf : Frame (obFrame (W+16#64) W SP D q) v.mem t.mem := by
    refine hashframe.sub fun r hr => ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact ⟨⟨yA W,16⟩, by simp [obFrame,yA],fun _ hx => hx⟩
    · exact ⟨⟨W+448#64,2112⟩,by simp [obFrame],Region.sub_prefix (by decide)⟩
    · exact ⟨below SP 24,by simp [obFrame],kS⟩
  have hk : blockAt v.mem (Ctx+240#64) = blockAt s.mem (Ctx+240#64) := by
    apply blockAt_frame ctrframe
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact L.ctx_st (by decide) (by decide)
    · exact Dq.ctx.sub_left (Lay.ctxSub (by decide))
    · exact L.ctx_w (by decide) (by decide)
    · exact (L.stk_ctx (by decide)).symm
  have cy : (⟨yA W,16⟩ : Region).Disjoint ⟨cbA W,16⟩ := Offset.disjoint (W+16#64) (.inl (by decide)) (by decide) (by decide)
  have y : blockAt v.mem (yA W) = blockAt s.mem (yA W) := by
    apply blockAt_frame ctrframe
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact cy
    · exact (Dq.ok.st.sub_right (Lay.stSub (by decide))).symm
    · exact L.st_w (by decide) (.inr ⟨by decide,by decide⟩)
    · exact (L.stk_st (by decide)).symm
  have db : blocksAt t.mem D q = blocksAt v.mem D q := by
    apply blocksAt_frame hashframe _ (by have := Dq.ok.lt; omega_arith)
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact Dq.ok.st.sub_right (Lay.stSub (by decide))
    · exact dW.sub_right (Lay.wSub (by decide))
    · exact Dq.ok.stk.symm
  have cb : blockAt t.mem (cbA W) = blockAt v.mem (cbA W) := by
    apply blockAt_frame hashframe
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact cy.symm
    · exact L.st_w (by decide) (.inr ⟨by decide,by decide⟩)
    · exact (L.stk_st (by decide)).symm
  refine ⟨fun z hz => (hh.saved z hz).trans ((gx z hz).trans ((hc.saved z hz).trans (gu z hz))),
    hh.rd.trans (rx.trans (hc.rd.trans ru)), hh.wr.trans (wx.trans (hc.wr.trans wu)), cf.trans hf, ?_, ?_, ?_⟩
  · simpa only [mu,q,ctxCiph] using db.trans hc.out
  · simpa only [mu] using cb.trans hc.ctr
  · rw [show blocksAt t.mem D (n/16) = blocksAt v.mem D (n/16) from db]
    change _ = ghashFrom (blockAt s.mem (Ctx+240#64)) _ _
    simpa only [mx,hk,y] using hh.out

end VG.Proof.AesGcm.X86_64.ContiguousSeal
