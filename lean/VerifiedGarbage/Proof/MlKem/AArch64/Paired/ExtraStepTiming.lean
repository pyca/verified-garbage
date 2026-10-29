module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Context
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.NextBlock
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Continue
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Extra
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraBoth

import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeTiming
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Trace
import VerifiedGarbage.Proof.Framework.RelCTAssoc

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/ContinueTiming.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure ResumeW (w16 : Bool) (L : List Zq) (B : Nat→Byte) (aP : Addr) (s : State) : Prop where
  env : Rej8.EnvW w16 56 B (s.gpr .x20) aP s
  constants : Rej8.Constants s
  len : L.length≤256
  coeffs : Rej8.Scalar.CoeffsW w16 s.mem aP L
  x3 : s.gpr .x3=cAddr w16 aP L.length
  x4 : (s.gpr .x4).toNat=256-L.length

abbrev Resume := ResumeW false

theorem continue_relCT {w16 : Bool} {s u : State}
    {B : Nat→Byte} {L : List Zq} {aP : Addr} (ps : ResumeW w16 L B aP s) (pu : ResumeW w16 L B aP u)
    (hsp : s.sp=u.sp) (h20 : s.gpr .x20=u.gpr .x20) (h1 : s.gpr .x1=u.gpr .x1)
    (h16 : s.gpr .x16=u.gpr .x16) :
    RelCT isa (fun a b=>a=s ∧ b=u)
      (.seq (.block (continueEntry)) (Impl.MlKem.AArch64.Rej8.rejLoop w16))
      (fun a b=>a.sp=b.sp ∧ a.gpr .x1=b.gpr .x1) := by
  have start : RelCT isa (fun a b=>a=s ∧ b=u) (.block (continueEntry))
      (fun a b=>Rej8.EntryW w16 L 56 B (s.gpr .x20) aP a ∧
        Rej8.EntryW w16 L 56 B (s.gpr .x20) aP b ∧ a.sp=b.sp ∧ a.gpr .x16=b.gpr .x16) := by
    intro a b tr ur a' b' h ea eb
    rcases h with ⟨ha,hb'⟩
    subst a; subst b
    obtain ⟨ka,ha⟩ := exec_post (continueEntry_ok s ps.env ps.constants ps.len ps.coeffs ps.x3 ps.x4) ea
    obtain ⟨kb,hb'⟩ := exec_post (continueEntry_ok u pu.env pu.constants pu.len pu.coeffs pu.x3 pu.x4) eb
    refine ⟨continueEntry_ct s u tr ur a' b' trivial trivial (agree_of hsp (by simp)) ea eb,
      ha,?_,ka.sp.trans (hsp.trans kb.sp.symm),?_⟩
    · simpa only [h20] using hb'
    · rw [ka.get .x16,kb.get .x16,h16]
  have trace := RelCT.seq start (segment_entry_relCT L 56 B _ aP (by decide) (by decide))
  intro a b tr ur a' b' h ea eb
  rcases h with ⟨ha,hb'⟩
  subst a; subst b
  obtain ⟨ht,hsp'⟩ := trace s u tr ur a' b' ⟨rfl,rfl⟩ ea eb
  have hs := exec_post (continue_ok s ps.env ps.constants ps.len ps.coeffs ps.x3 ps.x4) ea
  have hu := exec_post (continue_ok u pu.env pu.constants pu.len pu.coeffs pu.x3 pu.x4) eb
  exact ⟨ht,hsp',by rw [hs.1.get .x1,hu.1.get .x1,h1]⟩

end VG.Proof.MlKem.AArch64.Paired
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/ExtraTiming.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem load_resume {w16 : Bool} {s : State} {L : List Zq} {B : Nat→Byte} {aP : Addr}
    (h : ReadyW w16 L B (s.gpr .x20) (s.gpr .x1) aP s) (hc : Rej8.Constants s) :
    WP isa (.block [.ldr .x .x3 .x1 0,.ldr .x .x4 .x1 8]) s fun t =>
      Only [.x3,.x4] s t ∧ ResumeW w16 L B aP t := by
  have h0 : InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 0) 8 := by rw [ptr_zero]; exact h.out0
  refine WP.mono (load_checkpoint s (r:=.x1) (slot:=0) (by decide) (by decide) (in_rd_wr h0)
    (in_rd_wr h.out1)) fun t ⟨kt,hv,t3,t4⟩ => ?_
  refine ⟨kt,?_,?_,h.len,?_,?_,?_⟩
  · rw [kt.get .x20]
    exact h.env.transfer kt.mem kt.rd kt.wr (kt.get .x16)
  · exact ⟨by rw [hv]; exact hc.index,by rw [hv]; exact hc.mask,
      by simpa only [hv] using hc.q,by simpa only [hv] using hc.weights,
      by simpa only [hv] using hc.zero⟩
  · rw [kt.mem]; exact h.coeffs
  · rw [t3,ptr_zero]; exact h.saved.1
  · rw [t4]; exact h.saved.2

theorem extra_relCT {w16 : Bool} {s u : State} {B : Nat→Byte} {L : List Zq} {aP : Addr}
    (ps : ReadyW w16 L B (s.gpr .x20) (s.gpr .x1) aP s) (pu : ReadyW w16 L B (u.gpr .x20) (u.gpr .x1) aP u)
    (cs : Rej8.Constants s) (cu : Rej8.Constants u)
    (hsp : s.sp=u.sp) (h20 : s.gpr .x20=u.gpr .x20) (h1 : s.gpr .x1=u.gpr .x1)
    (h16 : s.gpr .x16=u.gpr .x16) :
    RelCT isa (fun a b=>a=s ∧ b=u) (Impl.MlKem.AArch64.Paired.extraReject w16)
      (fun a b=>ExtraPostW w16 L B aP (s.gpr .x1) s a ∧ ExtraPostW w16 L B aP (u.gpr .x1) u b) := by
  let R := fun a b=>ResumeW w16 L B aP a ∧ ResumeW w16 L B aP b ∧
    a.sp=b.sp ∧ a.gpr .x20=b.gpr .x20 ∧ a.gpr .x1=b.gpr .x1 ∧ a.gpr .x16=b.gpr .x16
  have start : RelCT isa (fun a b=>a=s ∧ b=u) (.block [.ldr .x .x3 .x1 0,.ldr .x .x4 .x1 8]) R := by
    intro a b tr ur a' b' h ea eb
    rcases h with ⟨ha',hb'⟩
    subst a; subst b
    obtain ⟨ka,pa⟩ := exec_post (load_resume ps cs) ea
    obtain ⟨kb,pb⟩ := exec_post (load_resume pu cu) eb
    refine ⟨cursor_ct s u tr ur a' b' trivial trivial
      (agree_of hsp (by intro r hr; rw [List.mem_singleton.mp hr]; exact h1)) ea eb,
      pa,pb,ka.sp.trans (hsp.trans kb.sp.symm),?_,?_,?_⟩
    · rw [ka.get .x20,kb.get .x20,h20]
    · rw [ka.get .x1,kb.get .x1,h1]
    · rw [ka.get .x16,kb.get .x16,h16]
  have trace : RelCT isa (fun a b=>a=s ∧ b=u) (Impl.MlKem.AArch64.Paired.extraReject w16) (fun _ _=>True) := by
    refine RelCT.seq start (RelCT.ite ?_ ?_ ?_)
    · intro a b h
      have he : a.gpr .x4=b.gpr .x4 := BitVec.eq_of_toNat_eq (h.1.x4.trans h.2.1.x4.symm)
      change some (a.gpr .x4 == 0)=some (b.gpr .x4 == 0)
      rw [he]
    · intro a b tr ur a' b' h ea eb
      have ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
          (.block [.movz .x .x0 1 0]) :=
        VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl
      exact ⟨ct a b tr ur a' b' trivial trivial (agree_of h.1.2.2.1 (by simp)) ea eb,trivial⟩
    · apply RelCT.assoc
      refine RelCT.seq (R:=fun a b : State=>a.sp=b.sp ∧ a.gpr .x1=b.gpr .x1) ?_ ?_
      · intro a b tr ur a' b' h ea eb
        exact continue_relCT h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2
          a b tr ur a' b' ⟨rfl,rfl⟩ ea eb
      · intro a b tr ur a' b' h ea eb
        exact ⟨storeCursor_ct a b tr ur a' b' trivial trivial
          (agree_of h.1 (by intro r hr; rw [List.mem_singleton.mp hr]; exact h.2)) ea eb,trivial⟩
  intro a b tr ur a' b' h ea eb
  rcases h with ⟨ha',hb'⟩
  subst a; subst b
  exact ⟨(trace s u tr ur a' b' ⟨rfl,rfl⟩ ea eb).1,
    exec_post (extra_ok s ps.env cs ps.len ps.coeffs ps.saved ps.out0 ps.out1 ps.apart) ea,
    exec_post (extra_ok u pu.env cu pu.len pu.coeffs pu.saved pu.out0 pu.out1 pu.apart) eb⟩

end VG.Proof.MlKem.AArch64.Paired
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/ExtraBothTiming.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem bothStart_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block [.addImm .x .x20 .x19 400,.addImm .x .x1 .x19 1680,.movz .x .x22 1 0,.movz .x .x23 2 0]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

theorem bothNext_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block [.logic .and .x .x22 .x22 .x0,.addImm .x .x20 .x20 504,.addImm .x .x1 .x1 16,
      .subImm .x .x23 .x23 1]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

theorem bothEnd_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block [Impl.MlKem.AArch64.mov .x6 .x22]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

/-- An iteration of `extraBoth` from a stream ready at the same place in both runs. -/
theorem bothBody_relCT {w16 : Bool} {t v : State} {L : List Zq} {B : Nat→Byte} {aP : Addr}
    (pt : ReadyW w16 L B (t.gpr .x20) (t.gpr .x1) aP t) (pv : ReadyW w16 L B (v.gpr .x20) (v.gpr .x1) aP v)
    (ct : Rej8.Constants t) (cv : Rej8.Constants v) (sp : t.sp=v.sp) (h20 : t.gpr .x20=v.gpr .x20)
    (h1 : t.gpr .x1=v.gpr .x1) (h16 : t.gpr .x16=v.gpr .x16) :
    RelCT isa (fun x y=>x=t ∧ y=v) (bothBody w16) (fun _ _=>True) := by
  refine RelCT.seq (R:=fun x y : State=>x.sp=y.sp) ?_ ?_
  · intro x y tx ty x' y' h ex ey
    have r := extra_relCT pt pv ct cv sp h20 h1 h16 x y tx ty x' y' h ex ey
    exact ⟨r.1,r.2.1.keep.sp.trans (sp.trans r.2.2.keep.sp.symm)⟩
  · intro x y tx ty x' y' h ex ey
    exact ⟨bothNext_ct x y tx ty x' y' trivial trivial (agree_of h (by simp)) ex ey,trivial⟩

theorem extraBoth_relCT {w16 : Bool} {s u : State} {L M : List Zq} {A B : Nat→Byte} {p a b : Addr}
    (hs : BothReadyW w16 L M A B p a b s) (hu : BothReadyW w16 L M A B p a b u)
    (sp : s.sp=u.sp) (table : s.gpr .x16=u.gpr .x16) :
    RelCT isa (fun x y=>x=s ∧ y=u) (Impl.MlKem.AArch64.Paired.extraBoth w16) (fun _ _=>True) := by
  let I : Nat → State → State → Prop := fun n t v =>
    (n=2 ∧ BothInv w16 L M A B p a b s 0 t ∧ BothInv w16 L M A B p a b u 0 v) ∨
    (n=1 ∧ BothInv w16 L M A B p a b s 1 t ∧ BothInv w16 L M A B p a b u 1 v)
  have start : RelCT isa (fun x y=>x=s ∧ y=u)
      (.block [.addImm .x .x20 .x19 400,.addImm .x .x1 .x19 1680,.movz .x .x22 1 0,.movz .x .x23 2 0]) (I 2) := by
    intro x y tx ty x' y' h ex ey
    rcases h with ⟨rfl,rfl⟩
    exact ⟨bothStart_ct x y tx ty x' y' trivial trivial (agree_of sp (by simp)) ex ey,
      .inl ⟨rfl,exec_post (bothStart_ok hs) ex,exec_post (bothStart_ok hu) ey⟩⟩
  have loop : RelCT isa (I 2) (.loop (bothBody w16) (.nonzero .x .x23)) (fun t v=>t.sp=v.sp) := by
    refine RelCT.loop (M:=isa) I (fun n => ?_) 2
    intro t v tt tv t' v' hI et ev
    rcases hI with ⟨rfl,it,iv⟩|⟨rfl,it,iv⟩
    · obtain ⟨kt,_,ct,t20,t1,_,_,ra,_⟩ := id it
      obtain ⟨kv,_,cv,v20,v1,_,_,rb,_⟩ := id iv
      have tq := bothBody_relCT (by rw [t20,t1]; exact ra) (by rw [v20,v1]; exact rb) ct cv
        (kt.sp.trans (sp.trans kv.sp.symm)) (t20.trans v20.symm) (t1.trans v1.symm)
        (by rw [kt.get .x16,kv.get .x16,table]) t v tt tv t' v' ⟨rfl,rfl⟩ et ev
      have it' := (exec_post (bothStep0_ok hs it) et).1
      have iv' := (exec_post (bothStep0_ok hu iv) ev).1
      have et23 : isa.eval (.nonzero .x .x23) t'=some true := by rw [eval_nonzero,it'.2.2.2.2.2.1]; rfl
      have ev23 : isa.eval (.nonzero .x .x23) v'=some true := by rw [eval_nonzero,iv'.2.2.2.2.2.1]; rfl
      refine ⟨tq.1,by rw [et23,ev23],fun h => (by rw [et23] at h; cases h),fun _ => ⟨1,by decide,.inr ⟨rfl,it',iv'⟩⟩⟩
    · obtain ⟨kt,_,ct,t20,t1,_,_,_,_,rb⟩ := id it
      obtain ⟨kv,_,cv,v20,v1,_,_,_,_,rb'⟩ := id iv
      have tq := bothBody_relCT (by rw [t20,t1]; exact rb) (by rw [v20,v1]; exact rb') ct cv
        (kt.sp.trans (sp.trans kv.sp.symm)) (t20.trans v20.symm) (t1.trans v1.symm)
        (by rw [kt.get .x16,kv.get .x16,table]) t v tt tv t' v' ⟨rfl,rfl⟩ et ev
      have it' := (exec_post (bothStep1_ok hs it) et).1
      have iv' := (exec_post (bothStep1_ok hu iv) ev).1
      have et23 : isa.eval (.nonzero .x .x23) t'=some false := by rw [eval_nonzero,it'.2.2.2.1]; rfl
      have ev23 : isa.eval (.nonzero .x .x23) v'=some false := by rw [eval_nonzero,iv'.2.2.2.1]; rfl
      refine ⟨tq.1,by rw [et23,ev23],fun _ => it'.1.sp.trans (sp.trans iv'.1.sp.symm),
        fun h => by rw [et23] at h; cases h⟩
  refine RelCT.seq start (RelCT.seq loop ?_)
  intro t v tt tv t' v' h et ev
  exact ⟨bothEnd_ct t v tt tv t' v' trivial trivial (agree_of h (by simp)) et ev,trivial⟩

end VG.Proof.MlKem.AArch64.Paired
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem VG.Spec.MlKem VG.Proof.Sha3.AArch64.Neon

structure StepReadyW (w16 : Bool) (A B : Spec.Sha3.State) (L M : List Zq) (p a b c : Addr) (s : State) : Prop where
 context : Context p a b c s
 pointer : s.gpr .x19=p
 symbol : s.syms "VG_MLKEM_REJ_SHUFFLE"=c
 pair : PairAt s.mem p A B
 lenLeft : L.length≤256
 lenRight : M.length≤256
 left : Rej8.Scalar.CoeffsW w16 s.mem a L
 right : Rej8.Scalar.CoeffsW w16 s.mem b M
 saveLeft : checkpointW w16 (p+1680) a L s.mem
 saveRight : checkpointW w16 (p+1696) b M s.mem

theorem nextBlock_ready {w16 : Bool} {s : State} {A B : Spec.Sha3.State} {L M : List Zq} {p a b c : Addr}
 (h : StepReadyW w16 A B L M p a b c s) :
 WP isa nextBlock s fun u=> Keep nextRegs s u ∧ u.gpr .x16=c ∧
   BothReadyW w16 L M (Proof.Sha3.byteOf (Spec.Sha3.keccakF A))
     (Proof.Sha3.byteOf (Spec.Sha3.keccakF B)) p a b u := by
 rcases h with ⟨ctx,hp,sym,pair,hl,hm,ca,cb,sa,sb⟩
 refine WP.mono_syms (nextBlock_ok hp ctx.scratch pair) fun u h hsym => ?_
 rcases h with ⟨ku,fu,precise,up,pu,ra,rb,cs,ut⟩
 have fu' : Frame (stepWrites p a b) s.mem u.mem := fu.mono (by simp [stepWrites])
 have cu := ctx.frame ku.rd ku.wr fu'
 have ux : u.gpr .x16=c := by rw [ut,hsym,sym]
 have ua := coeffs_frame ca hl fu (by intro r hr; rw [List.mem_singleton.mp hr]; exact ctx.farA.symm)
 have ub := coeffs_frame cb hm fu (by intro r hr; rw [List.mem_singleton.mp hr]; exact ctx.farB.symm)
 have checkpoints {off : Nat} (ho : off=1680 ∨ off=1696) :
     ∀r∈nextWrites p,(Region.mk (p+BitVec.ofNat 64 off) 16).Disjoint r := by
  have hlo : 1680≤off := by omega
  have hhi : off≤1696 := by omega
  intro r hr
  simp only [nextWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact Offset.disjoint_base p (d:=off) (n:=16) (k:=400) (by omega) (by omega)
  · exact Offset.disjoint p (d:=off) (n:=16) (e:=400) (k:=168) (by omega) (by omega) (by decide)
  · exact Offset.disjoint p (d:=off) (n:=16) (e:=904) (k:=168) (by omega) (by omega) (by decide)
  · exact Offset.disjoint p (d:=off) (n:=16) (e:=1536) (k:=136) (by omega) (by omega) (by decide)
  · exact Offset.disjoint p (d:=off) (n:=16) (e:=1408) (k:=8) (by omega) (by omega) (by decide)
 have usa := checkpoint_frame sa precise (checkpoints (Or.inl rfl))
 have usb := checkpoint_frame sb precise (checkpoints (Or.inr rfl))
 have ea := cu.envW (w16 := w16) ux (N:=56) (off:=400) (by decide) (by decide) (Or.inl rfl) (fun i hi=>ra.byte hi)
 have eb := cu.envW (w16 := w16) ux (N:=56) (off:=904) (by decide) (by decide) (Or.inr rfl) (fun i hi=>rb.byte hi)
 have iw {o l : Nat} (ho : o+l≤2048) := Noise.inScratch cu.scratch ho (by decide)
 refine ⟨ku,ux,up,cu.scratch,cu.farA,cu.farB,cu.apart,?_,?_,?_,cs⟩
 · exact ⟨ea,hl,ua,usa,iw (o:=1680) (by decide),by rw [BitVec.add_assoc]; exact iw (o:=1688) (by decide),
     cu.farA.symm.sub_right (Offset.sub_base p (by decide))⟩
 · exact ⟨eb,hm,ub,usb,iw (o:=1696) (by decide),by rw [BitVec.add_assoc]; exact iw (o:=1704) (by decide),
     cu.farB.symm.sub_right (Offset.sub_base p (by decide))⟩
 · intro mask hm; rw [ux]; exact cu.tableScratch.sub_left (Rej8.table_sub c hm)
theorem extraStep_relCT {w16 : Bool} {s u : State} {A B : Spec.Sha3.State} {L M : List Zq} {p a b c : Addr}
 (hs : StepReadyW w16 A B L M p a b c s) (hu : StepReadyW w16 A B L M p a b c u)
 (sp : s.sp=u.sp) :
 RelCT isa (fun x y=>x=s ∧ y=u) (Impl.MlKem.AArch64.Paired.extraStep w16) (fun _ _=>True) := by
 have first : RelCT isa (fun x y=>x=s ∧ y=u) nextBlock
     (fun x y=>BothReadyW w16 L M (Proof.Sha3.byteOf (Spec.Sha3.keccakF A))
         (Proof.Sha3.byteOf (Spec.Sha3.keccakF B)) p a b x ∧
       BothReadyW w16 L M (Proof.Sha3.byteOf (Spec.Sha3.keccakF A))
         (Proof.Sha3.byteOf (Spec.Sha3.keccakF B)) p a b y ∧ x.sp=y.sp ∧ x.gpr .x16=y.gpr .x16) := by
  intro x y tx ty x' y' h ex ey
  rcases h with ⟨hx,hy⟩
  subst x; subst y
  obtain ⟨kx,tx16,px⟩ := exec_post (nextBlock_ready hs) ex
  obtain ⟨ky,ty16,py⟩ := exec_post (nextBlock_ready hu) ey
  exact ⟨nextBlock_ct s u tx ty x' y' trivial trivial
    (agree_of sp (by intro r hr; rw [List.mem_singleton.mp hr]; exact hs.pointer.trans hu.pointer.symm)) ex ey,
    px,py,kx.sp.trans (sp.trans ky.sp.symm),tx16.trans ty16.symm⟩
 have grouped : RelCT isa (fun x y=>x=s ∧ y=u) (.seq nextBlock (Impl.MlKem.AArch64.Paired.extraBoth w16)) (fun _ _=>True) := by
  refine RelCT.seq first ?_
  intro x y tx ty x' y' h ex ey
  exact extraBoth_relCT h.1 h.2.1 h.2.2.1 h.2.2.2 x y tx ty x' y' ⟨rfl,rfl⟩ ex ey
 intro x y tx ty x' y' h ex ey
 cases ex with
 | seq e1 ex =>
  cases ex with
  | seq e2 ex =>
   cases ex with
   | seq e3 e4 =>
    cases ey with
    | seq f1 ey =>
     cases ey with
     | seq f2 ey =>
      cases ey with
      | seq f3 f4 =>
       obtain ⟨ht,hq⟩ := grouped _ _ _ _ _ _ h
         (.seq (.seq e1 (.seq e2 e3)) e4) (.seq (.seq f1 (.seq f2 f3)) f4)
       exact ⟨by simpa only [List.append_assoc] using ht,hq⟩

end VG.Proof.MlKem.AArch64.Paired
