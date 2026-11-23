module
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Finish
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.LoopCT
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTFin
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Finish

/-! # Public suffix length, GHASH padding and tag computation -/
@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_seq rel_taint)
open VG.Spec.Gcm (blockAt)

theorem ct_at {s t : State} {I : State → Prop} {c : Prog isa} (ct : CT I c) (x : I s) (y : I t) :
    RelCT isa (Eq2 s t) c TT :=
  RelCT.mono ct (fun _ _ ⟨rfl,rfl⟩ => ⟨x,y⟩) fun _ _ h => h

theorem padTag_ct [Proof.Gcm.PPC64LE.GhashLaw] {C S W sp : Addr} {R : Nat} {A T : Addr}
    (L : Lay C S W) (rounds : R=10 ∨ R=12 ∨ R=14) : CT (FTI C S W sp R A T) padTag := by
  let J : State → Prop := fun s => FTI C S W sp R A T s ∧ s.gpr .r26=BitVec.ofNat 64 (T.toNat%16)
  refine CT.seq (J:=J) ?_ (fun s ⟨V,hC,hS,hW,hR,hA,hT,env⟩ =>
    WP.mono (padPrep_wp env) fun _ ⟨r26,e,_⟩ => ⟨⟨V,hC,hS,hW,hR,hA,hT,e⟩,hT ▸ r26⟩) ?_
  · obtain ⟨_,cert⟩ : ∃ hint, (taint.check (Taint.ofRegs []) (.block padPrep) hint).isSome=true := ⟨_,by taint_decide⟩
    exact CT.taint _ (fun _ _ ⟨_,_,_,_,_,_,_,x⟩ ⟨_,_,_,_,_,_,_,y⟩ =>
      ⟨x.sp.trans y.sp.symm,fun _ hr => by simp at hr⟩) cert
  refine CT.seq (J:=FTI C S W sp R A T)
    ((flush_ct L (yo:=16) (.inr rfl) (Nat.mod_lt T.toNat (by decide : 0<16))).mono
      fun _ ⟨⟨V,hC,hS,hW,_,_,_,env⟩,r26⟩ => ⟨⟨V,hC,hS,hW,env⟩,r26⟩)
    (fun s ⟨⟨V,hC,hS,hW,hR,hA,hT,env⟩,r26⟩ =>
      WP.mono (flush_ok (L.v hC hS hW) (yo:=16) (.inr rfl) (x:=List.replicate (T.toNat%16) 0)
        ⟨env,rfl⟩ (by simpa using r26)) fun _ fl => ⟨V,hC,hS,hW,hR,hA,hT,fl.env⟩) ?_
  refine CT.seq (J:=EnvR C S W sp R) ?_
    (fun _ ⟨V,hC,hS,hW,hR,_,_,env⟩ => WP.mono (tagLengths_wp env) fun _ ⟨_,_,e,_⟩ => ⟨V,hC,hS,hW,hR,e⟩)
    (tag_ct L (.inl rfl) rounds)
  obtain ⟨_,cert⟩ : ∃ hint, (taint.check (Taint.ofRegs []) (.block tagLengths) hint).isSome=true := ⟨_,by taint_decide⟩
  exact CT.taint _ (fun _ _ ⟨_,_,_,_,_,_,_,x⟩ ⟨_,_,_,_,_,_,_,y⟩ =>
    ⟨x.sp.trans y.sp.symm,fun _ hr => by simp at hr⟩) cert

theorem finish_rel [Proof.Gcm.PPC64LE.GhashLaw] {a d : LoopArgs} {e f s t : State} {b : Nat}
    (pub : LoopPublic a d e f) (h : LoopInput a e) (g : LoopInput d f)
    (x : LoopAt a e a.count b s) (y : LoopAt d f d.count b t) (aad : a.V .r22=d.V .r22)
    (tx : (a.V .r23).toNat=a.pos e a.count) (ty : (d.V .r23).toNat=d.pos f d.count) :
    RelCT isa (Eq2 s t) Impl.AesGcm.PPC64LE.DirectGather.finish TT := by
  have sp := pub.sp
  have key := pub.regs.key
  have st := pub.regs.state
  have work := pub.regs.work
  have dst := pub.regs.data
  change a.O=d.O at dst
  have n : a.pos e a.count=d.pos f d.count := (pub.pos (Nat.le_refl _)).trans (by rw [pub.count])
  have text : a.V .r23=d.V .r23 := BitVec.eq_of_toNat_eq (tx.trans (n.trans ty.symm))
  have r28 : a.V .r28=BitVec.ofNat 64 a.rounds := by rw [←h.roundReg,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have w31 : s.gpr .r31=t.gpr .r31 := x.env.r31.trans (work.trans y.env.r31.symm)
  refine rel_seq (rel_taint [.r31] (x.env.sp.trans (sp.trans y.env.sp.symm)) (by simpa using w31) (by taint_decide))
    (finishPrep_wp h x tx) (finishPrep_wp g y ty) (fun u v ⟨s24,s25,s26,es,ks⟩ ⟨t24,t25,t26,et,kt⟩ => ?_)
  have ai : AbsIn (a.finalV e) a.sp 16 (Spec.Gcm.ctxH e.mem a.C) [] (a.O+BitVec.ofNat 64 (16*b)) (a.pos e a.count-16*b) u :=
    ⟨es,s24,s25,s26,((finishData h x).drop x.hashLe).of_eq ks.rd ks.wr,ks.mem ▸ x.keyH h⟩
  have bi : AbsIn (d.finalV f) d.sp 16 (Spec.Gcm.ctxH f.mem d.C) [] (d.O+BitVec.ofNat 64 (16*b)) (d.pos f d.count-16*b) v :=
    ⟨et,t24,t25,t26,((finishData g y).drop y.hashLe).of_eq kt.rd kt.wr,kt.mem ▸ y.keyH g⟩
  have first : AbsI a.C (a.V .r30) (a.V .r31) a.sp 16 (a.O+BitVec.ofNat 64 (16*b)) (a.pos e a.count-16*b) 0 u :=
    ⟨a.finalV e,_,[],rfl,rfl,rfl,rfl,ai⟩
  have second : AbsI a.C (a.V .r30) (a.V .r31) a.sp 16 (a.O+BitVec.ofNat 64 (16*b)) (a.pos e a.count-16*b) 0 v := by
    change a.C=d.C at key
    rw [key,st,work,sp,dst,n]; exact ⟨d.finalV f,_,[],rfl,rfl,rfl,rfl,bi⟩
  refine rel_seq (ct_at (absorb_ct h.layout (.inr rfl) (by decide : 0<16)) first second)
    (absorb_ok (V:=a.finalV e) h.layout (.inr rfl) ai) (absorb_ok (V:=d.finalV f) g.layout (.inr rfl) bi) (fun u v au bv => ?_)
  exact ct_at (padTag_ct h.layout h.rounds)
    (show FTI a.C (a.V .r30) (a.V .r31) a.sp a.rounds (a.V .r22) (a.V .r23) u from
      ⟨a.finalV e,rfl,rfl,rfl,r28,rfl,rfl,au.env⟩)
    (by
      change a.C=d.C at key
      rw [key,st,work,sp,aad,text]
      exact ⟨d.finalV f,rfl,rfl,rfl,pub.regs.rounds.symm.trans r28,rfl,rfl,bv.env⟩)

end VG.Proof.AesGcm.PPC64LE.DirectGather
