module

public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Start
public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Step
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.TagBridge
public import VerifiedGarbage.Proof.AesGcm.X86.Gather.Verified
import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.BodyCT
import VerifiedGarbage.Proof.Framework.X86.Scrub
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

public section
namespace VG.Proof.AesGcm.X86.DirectGather
open VG VG.X86 VG.Impl.AesGcm.X86 VG.Spec.Gcm
open VG.Spec.Aes (bytesAt)

variable {N : Nat}



abbrev expected (s : State) := encryptWith (ctxCiph s.mem (w64 (Gather.K s)) (arg s 1).toNat)
  (ctxH s.mem (w64 (Gather.K s))) 16 (bytesAt s.mem (w64 (Gather.Nn s)) (Gather.NL s))
  (Gather.pt s (Gather.Cnt s)) (bytesAt s.mem (w64 (Gather.Ad s)) (Gather.AL s))

theorem stack_agrees {s u : State} (h : Gather.Lay N s) (f : Frame [Gather.stkR s N] s.mem u.mem) :
    (text N s).buf u.mem (text N s).count=Gather.pt s (Gather.Cnt s) := by
  apply Proof.AesGcm.gathered_congr_le (Nat.le_refl _)
  intro r hr x hx
  have dis : (Gather.stkR s N).Disjoint r := by
    rcases List.mem_cons.mp hr with rfl|hr
    · exact h.bds
    · exact h.bls _ hr
  exact (f x fun r' hr' hx' => by obtain rfl := List.mem_singleton.mp hr'; exact dis x hx' hx).symm

abbrev ciph (s : State) := ctxCiph s.mem (w64 (Gather.K s)) (arg s 1).toNat
abbrev hash (s : State) := ctxH s.mem (w64 (Gather.K s))
abbrev iv (s : State) := bytesAt s.mem (w64 (Gather.Nn s)) (Gather.NL s)
abbrev ad (s : State) := bytesAt s.mem (w64 (Gather.Ad s)) (Gather.AL s)

structure Source (s t : State) : Prop where
  key : ctxCiph t.mem (w64 ((pub t).2 0)) ((pub t).2 1).toNat = ciph s
  h : ctxH t.mem (w64 ((pub t).2 0)) = hash s
  nonce : bytesAt t.mem (w64 ((pub t).2 2)) ((pub t).2 3).toNat = iv s
  aad : bytesAt t.mem (w64 ((pub t).2 4)) ((pub t).2 5).toNat = ad s
  al : ((pub t).2 5).toNat = Gather.AL s

theorem source {s t : State} (h : Gather.Lay N s) (p : Prepared N s t) : Source s t := by
  have f := start_frame h p (Frame.refl (scratchAreas N s) t.mem)
  have sep {r : Region} (hr : (Gather.stkR s N).Disjoint r) : ∀ q ∈ [Gather.stkR s N], r.Disjoint q := by
    intro q hq; obtain rfl := List.mem_singleton.mp hq; exact hr.symm
  obtain ⟨kc,kh⟩ := Proof.AesGcm.ctx_frame f (sep h.bk) h.hR
  have z := p.params
  have n : (pub t).2 2=Gather.Nn s := p.arg_eq 2 (by decide)
  have nl : ((pub t).2 3).toNat=Gather.NL s := congrArg BitVec.toNat (p.arg_eq 3 (by decide))
  have a : (pub t).2 4=Gather.Ad s := p.arg_eq 4 (by decide)
  have al : ((pub t).2 5).toNat=Gather.AL s := congrArg BitVec.toNat (p.arg_eq 5 (by decide))
  refine ⟨by rw [z.c,z.r]; exact kc,by rw [z.c]; exact kh,?_,?_,al⟩
  · rw [n,nl]; exact Proof.Cmac.bytesAt_frame f (sep h.bn) (by omega_using [h.on])
  · rw [a,al]; exact Proof.Cmac.bytesAt_frame f (sep h.ba) (by omega_using [h.oa])

theorem ciphertext {s t x y z : State} (h : Gather.Lay N s) (p : Prepared N s t)
    (b : Begun N s t x) (a : TextAt N (text N s) x (inc32 (jOf (pub t) t)) (text N s).count y)
    (ts : SetupPost y (work N s) (SP N s) 6 7 dataO lenO (w64 (SP N s)) z) :
    bytesAt z.mem (w64 (Gather.Dst s)) (Gather.L s) = (expected s).1 := by
  have f := start_frame h p b.frame
  have key : ciphOf x.mem (Gather.K s) (arg s 1).toNat = ciph s := by
    exact ciph_frame f (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.bk.symm) h.hR
  have k := source h p
  have j : jOf (pub t) t = j0 (hash s) (iv s) := by unfold jOf; rw [k.h,k.nonce]
  have out := a.out
  rw [b.input.total,stack_agrees h f] at out
  have d : bytesAt z.mem (w64 (Gather.Dst s)) (Gather.L s) =
      bytesAt y.mem (w64 (Gather.Dst s)) (Gather.L s) := by
    apply Proof.Cmac.bytesAt_frame ts.frame _ (by omega_using [h.od])
    intro r hr; simp only [slotSetupFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact b.input.dstOutside.w.sub_right (Lay.wSub (by decide))
    · exact b.input.dstOutside.w.sub_right (Lay.wSub (by decide))
    · exact b.input.dstOutside.sp
  rw [d]; change _ = gctr (ciph s) (inc32 (j0 (hash s) (iv s))) (Gather.pt s (Gather.Cnt s))
  rw [Proof.Gcm.gctr_eq,← key,←j]; exact out

theorem tag_suffix (v : GcmImpl) [WSize N v.ctr.scr] {s t z : State} (h : Gather.Lay N s) (p : Prepared N s t)
    (ti : OTIn N (pub t) t z)
    (ct : bytesAt z.mem (w64 (Gather.Dst s)) (Gather.L s) = (expected s).1) :
    WP isa (.seq (oneTag v.callees 0) (.seq (tagOut 0) (.block restore))) z fun u =>
      abiPreserved t u ∧ Gather.gatherPost s u := by
  have ps := p.params
  have k := source h p
  have G := (p.op h).ol rfl (by decide) (p := pub t) rfl
  have tg : arg t 8=Gather.Tg s := p.arg_eq 8 (by decide)
  have tgW : Covers [Gather.tgR s] t.wr := by
    rw [p.wr]; exact covers_of_mem (List.mem_cons_of_mem _ (h.wr ▸ by simp))
  refine WP.seq (WP.mono ((oneTag_pc (vg := v) G (o := 0) (.inl rfl)).wp (t,z) z ⟨ti,rfl⟩) ?_)
  intro a fa
  obtain ⟨o,tag,frame⟩ := fa
  have bp : WEnv N ((pub t).2 8) a := ⟨o.env.ebp,o.env.wW,G.L.fw,by wle⟩
  refine WP.seq (WP.mono (tagOut_ok bp (o := 0) (by decide) (o.tp.trans tg) (o.wr ▸ tgW) h.ot) ?_)
  intro b fb
  obtain ⟨tag',one,bp',_,sp',rd',wr'⟩ := fb
  have saved := o.saved.frame one (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    rw [ps.w]; exact (h.bt.sub_left (fun x hx => (zones h).workspace x (Lay.wSub  (d := 128) (n := 16) (by decide) (by wle) x hx))))
  have rsep : ∀ r ∈ [Gather.tgR s], (⟨w64 (SP N s),4⟩ : Region).Disjoint r := fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact h.bt.sub_left (zones h).ret
  have ret := ret_kept one rsep
  have sp : t.gpr .esp=SP N s := ps.sp
  refine WP.mono (exit_ok (s₀ := t) (bp'.trans bp.ebp) (sp'.trans o.env.esp)
    (by rw [rd',wr']; exact covers_left o.env.wW) G.L.fw saved ?_) ?_
  · rw [sp,ret,← ps.sp]; exact o.ret
  intro u hu
  have ca := bytesAt_frame (oT_oF frame) (d_woF G (by decide)) (by omega_using [G.fd])
  rw [ps.d,ps.l] at ca
  have cb := Proof.Cmac.bytesAt_frame one (p := w64 (Gather.Dst s)) (n := Gather.L s)
    (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.dt) (by omega_using [h.od])
  refine ⟨hu.1,?_⟩
  change expected s = (bytesAt u.mem (w64 (Gather.Dst s)) (Gather.L s),bytesAt u.mem (w64 (Gather.Tg s)) 16)
  rw [hu.2.1,cb,ca,ct,tag',tag]
  apply Prod.ext
  · rfl
  · change (fullTag (ciph s) (hash s) (iv s) (ad s) (expected s).1).take 16 = _
    rw [Proof.Gcm.fullTag_eq,toBytes_take16,padded_eq]
    have aad := k.aad
    rw [k.al] at aad
    simp only [xA,k.h,k.key,k.al,aad,ps.d,ps.l,jOf,k.nonce,ct]
    rw [show (ad s).length=Gather.AL s from length_bytesAt ..,
      show (expected s).1.length=Gather.L s from ct ▸ length_bytesAt ..]

end VG.Proof.AesGcm.X86.DirectGather

end

public section
namespace VG.Proof.AesGcm.X86.DirectGather
open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Impl.AesGcm.X86.DirectGather (body frameArgs pieces partialHead)

variable {N : Nat}


theorem body_safe (v : GcmImpl) : (body v.callees).all (fun i => !isa.writesSp i) = true := by
  simp only [body,pieces,partialHead,Open.decTo,Open.wholeTo,Open.ctrToCall,
    absorb,absorbHead,absorbWhole,ctrCall,flush,ghCall,ghash1,j0,j0hash,
    lens,oneAad,oneTag,tag,tagOut,Code.all,GcmImpl.callees,
    v.ctr.spSafe,v.gh.spSafe,Bool.and_true]
  decide +kernel

theorem body_depth (v : GcmImpl) : stackUse (body v.callees) ≤ 32 := by
  simp only [body,pieces,partialHead,Open.decTo,Open.wholeTo,Open.ctrToCall,
    absorb,absorbHead,absorbWhole,ctrCall,flush,ghCall,ghash1,j0,j0hash,
    lens,oneAad,oneTag,tag,tagOut,stackUse,GcmImpl.callees,
    v.ctr.stack,v.gh.stack,Nat.max_le,X86.frameBytes,List.length_cons,List.length_nil,Nat.zero_le,true_and,and_true]
  decide +kernel

theorem before_safe (v : GcmImpl) (hN : N = 768 ∨ N = 2560) :
    ((Code.block (frameArgs (N + 52))).seq (body v.callees)).all (fun i => !isa.writesSp i) = true := by
  change (_ && _) = true
  rw [body_safe,Bool.and_true]; rcases hN with rfl | rfl <;> decide +kernel

theorem core_safe (v : GcmImpl) (hN : N = 768 ∨ N = 2560) :
    (Impl.AesGcm.X86.DirectGather.sealGather v.callees N).all (fun i => !isa.writesSp i)=true := by
  change ((true && _) && true) = true
  rw [before_safe v hN]; rfl

theorem body_wp (v : GcmImpl) [WSize N v.ctr.scr] {s t : State} (h : Gather.Lay N s) (p : Prepared N s t) :
    WP isa (body v.callees) t fun z => abiPreserved t z ∧ Gather.gatherPost s z := by
  let P := pub t
  have G := (p.op h).ol rfl (by decide) (p := P) rfl
  refine WP.seq (WP.mono ((entry_pc G).wp t t ⟨p.op h,rfl,rfl⟩) ?_)
  intro e en
  refine WP.seq (WP.mono ((oneAad_pc (vg := v) G).wp (t,e) e ⟨en,rfl⟩) ?_)
  intro u au
  have keep := setupEnv h p (p := P) rfl au.1.o.env.ebp au.1.o.env.esp au.1.o.rd au.1.o.wr
  refine WP.seq (WP.mono (loopSetup_ok keep) ?_)
  intro x ls
  have b := begun h p en au.1 au.2 ls
  refine WP.seq (WP.mono (b.input.pieces_ok v b.ptr b.count b.off b.ctr) ?_)
  intro y ay
  have ky : KeepEnv N (work N s) (SP N s) 12 y :=
    keep.keep (ay.env.ebp.trans keep.ebp.symm) (ay.env.esp.trans keep.esp.symm)
      (ay.rd.trans ls.rd) (ay.wr.trans ls.wr)
  have perm : InRegions y.wr (w64 (SP N s)) 4 := by
    rw [ay.wr]; exact b.input.spW _ _ ⟨_,List.mem_singleton_self _,Region.contains_self _ _⟩
  refine WP.seq (WP.mono (tagSetup_ok ky perm b.input.argW) ?_)
  intro z ts
  exact tag_suffix v h p (tagBridge_ok ⟨h,p,rfl,en,au.1,au.2,ls⟩ b.input ay ts)
    (ciphertext h p b ay ts)

theorem sealGather_verified (v : GcmImpl) [WSize N v.ctr.scr] (hN : N = 768 ∨ N = 2560) :
    Verified X86.target (Impl.AesGcm.X86.DirectGather.sealGather v.callees N)
      (Proof.AesGcm.sealGatherRoundsContract X86.abi (N + 128)) := by
  apply Verified.of_correct (k := (Gather.gatherX86 N)) _ (sealGather_ct v (by rcases hN with rfl | rfl <;> decide)) (Gather.gather_implies hN)
  intro s hs
  have h := Gather.lay hs (WSize.big v.ctr.scr) (by rcases hN with rfl | rfl <;> decide)
  let core := Impl.AesGcm.X86.DirectGather.sealGather v.callees
  have safe : NoSp (core N) := VG.X86.noSp_of_all (core_safe v hN)
  have depth : stackUse (core N) ≤ (N + 128) := by
    change max 0 (stackUse (body v.callees))+(N + 52) ≤ (N + 128)
    omega_using [body_depth v]
  have allocSub : (below (s.gpr .esp) (N + 52)).Sub (Gather.stkR s N) := by
    rw [show Gather.stkR s N=below (s.gpr .esp) (N + 128) from below_eq h.w₁]
    exact X86.below_sub (by gdec) h.w₁
  have inner : WP isa (core N) s fun z =>
      (∀ r ∈ calleeSaved, z.gpr r=s.gpr r) ∧ Gather.gatherPost s z := by
    apply Gather.WP.alloc ⟨by gdec,by gdec,by gdec⟩ (by omega_using [h.w₁])
      (VG.X86.noSp_of_all (before_safe v hN))
    obtain ⟨t,run,p⟩ := prepare_run h
    refine WP.seq ⟨_,t,Exec.block_iff.mpr run,?_⟩
    refine WP.mono (body_wp v h p) ?_
    intro out hf m unk fr
    obtain ⟨abi,post⟩ := hf
    refine ⟨?_,?_⟩
    · intro r hr
      by_cases esp : r=.esp
      · subst r
        change out.gpr .esp+BitVec.ofNat 32 (N + 52)=s.gpr .esp
        rw [abi.1 _ (by decide),show t.gpr .esp=SP N s from p.params.sp]; exact BitVec.sub_add_cancel _ _
      · have eax : r≠.eax := by intro er; subst r; exact (by decide : Reg.eax ∉ calleeSaved) hr
        change (out.setReg .esp _).gpr r=_
        rw [gpr_setReg_of_ne _ _ esp,abi.1 _ hr,p.regs r eax]; exact gpr_setReg_of_ne _ _ esp
    · have outside {r : Region} (hr : (Gather.stkR s N).Disjoint r) :
          ∀ q ∈ [below (s.gpr .esp) (N + 52)], r.Disjoint q := by
        intro q hq; obtain rfl := List.mem_singleton.mp hq; exact (hr.sub_left allocSub).symm
      unfold Gather.gatherPost at post ⊢
      change expected s = (Spec.Aes.bytesAt m _ _,Spec.Aes.bytesAt m _ _)
      rw [Proof.Cmac.bytesAt_frame fr (outside h.bd) (by omega_using [h.od]),
        Proof.Cmac.bytesAt_frame fr (outside h.bt) (by decide)]
      exact post
  obtain ⟨tr,z,exec,g,post⟩ := inner
  have f := VG.X86.Exec.frameSp exec safe (by omega_using [depth,h.w₁])
  have retStack : (Gather.retR s).Disjoint (Gather.stkR s N) := by
    change Region.Disjoint ⟨w64 (s.gpr .esp),4⟩ ⟨Gather.Bs N s,(N + 128)⟩
    rw [h.hE]; exact Offset.disjoint_base _ (by gdec) (by gdec)
  refine ⟨tr,z,exec,⟨g,f.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)⟩,post⟩
  rw [h.wr] at hr
  simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact h.ed
  · exact h.et
  · change (Gather.retR s).Disjoint (Gather.argR s)
    change Region.Disjoint ⟨w64 (s.gpr .esp),4⟩ _
    rw [h.hArg,h.hE]; exact Offset.disjoint _ (by gdec) (by gdec) (by gdec)
  · apply retStack.sub_right
    rw [show Gather.stkR s N=below (s.gpr .esp) (N + 128) from below_eq h.w₁]
    exact X86.below_sub depth h.w₁

end VG.Proof.AesGcm.X86.DirectGather

end
