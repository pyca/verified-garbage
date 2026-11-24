module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.General
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumCached
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.General
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8

/-! Lend the caller's authenticated key table and pointer to the bounded descriptor body. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.MediumRecord
open VG VG.AArch64 DirectGather Gather

abbrev extra (o : State) := [Prepared.powerR o,callerArgs o]
abbrev view (o t : State) := t.withRegions ((VG.Proof.AesGcm.AArch64.Contiguous.view t).rd ++ extra o) (VG.Proof.AesGcm.AArch64.Contiguous.view t).wr

theorem layout {o t : State} (h : Entered o t) (c : Caller o) : BoundedLay (view o t) (extra o) := by
  let s := VG.Proof.AesGcm.AArch64.Contiguous.view t
  have l := Gather.lay (h.pre c)
  obtain ⟨rd,wr,kd,_,_,_,_,_,dsDst,_,_,dt,da,_,_,_,_,_,_,sa,_⟩ := l.pre
  have sub : (boundedStack t).Sub (stkR t) := Offset.sub_below _ (by decide) (by decide)
  refine ⟨?_,wr,kd,dsDst,dt,da,l.bk.sub_left sub,l.bn.sub_left sub,l.ba.sub_left sub,
    l.bds.sub_left sub,fun r hr => (l.bl r hr).sub_left sub,sa.sub_left sub,l.bd.sub_left sub,l.bt.sub_left sub,
    Nat.le_trans (by decide) l.w₁,l.hR,l.hgl,l.ods,?_⟩
  · change ((VG.Proof.AesGcm.AArch64.Contiguous.view t).rd ++ extra o) = _
    rw [rd]
    simp only [List.append_assoc,List.cons_append,List.nil_append]; rfl
  · change (∀ r ∈ lsR t, r.Disjoint (dR t)) ∨ (Cnt t = 1 ∧ sb t.mem (Src t) 0 = Dst t)
    rcases c.sd with dis | same
    · left; rw [h.regions.slices,h.regions.d]; simpa only [List.mem_singleton,forall_eq] using dis
    · right
      refine ⟨by simp only [Cnt,h.count]; decide,?_⟩
      change t.mem.readW (t.gpr .x6 + _) 64 = stackArg t 0
      simpa [h.desc,h.dst,same] using h.sb.trans same

theorem input {o t : State} (h : Entered o t) (c : Caller o) (key : Prepared.Powers o) :
    Mid.CachedInput (view o t) (stackArg o 2) := by
  have slot : t.sp + 64#64 = stackArgAddr o 2 := by
    change t.sp+64#64 = o.sp+16#64
    rw [h.sp,show (64#64:Addr) = 48#64+16#64 from rfl,← BitVec.add_assoc]
    exact congrArg (·+16#64) (BitVec.sub_add_cancel o.sp 48#64)
  have sub : (Mid.scratch t).Sub (below o.sp 2640) := by
    change (⟨t.sp-752#64,752⟩ : Region).Sub _
    rw [h.sp,BitVec.sub_sub]
    exact Offset.sub_below o.sp (a := 800) (b := 2640) (by decide) (by decide)
  have outer : (below o.sp 48).Sub (below o.sp 2640) := Offset.sub_below _ (by decide) (by decide)
  have args : (callerArgs o).Disjoint (below o.sp 2640) := by
    change (⟨o.sp+0#64,24⟩ : Region).Disjoint _
    rw [BitVec.add_zero]; exact Offset.base_disjoint_below _ (by decide)
  have subSlot : (⟨stackArgAddr o 2,8⟩ : Region).Sub (callerArgs o) := by
    change (⟨o.sp+16#64,8⟩ : Region).Sub ⟨o.sp+0#64,24⟩
    rw [BitVec.add_zero]; exact Offset.sub_base _ (by decide)
  have tabRead : Prepared.powerR o ∈ (view o t).rd := by simp [view,extra]
  have argsRead : callerArgs o ∈ (view o t).rd := by simp [view,extra]
  have ctx : Spec.Gcm.ctxH t.mem (K t) = Spec.Gcm.ctxH o.mem (K o) := by
    unfold K
    rw [h.regs .x0 (by decide)]
    exact blockAt_frame h.frame (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact (((c.stack _ (by simp [externalRegions] : kR .plain o ∈ externalRegions o)).sub_left outer).symm).sub_left (Lay.ctxSub (by decide)))
  refine ⟨?_,?_,?_,?_,Covers.one ⟨_,List.mem_append_left _ tabRead,Region.contains_self _ _⟩,
    key.stack.sub_right sub,?_,?_⟩
  · change InRegions _ (t.sp+64#64) 8; rw [slot]
    exact ⟨_,List.mem_append_left _ argsRead,stackArg_contains o 2 (by decide)⟩
  · change t.mem.readW (t.sp+64#64) 64 = _; rw [slot]
    exact h.frame.readW (r := callerArgs o) (stackArg_contains o 2 (by decide))
      (by simpa only [List.mem_singleton,forall_eq] using args.sub_right outer) (by decide)
  · change (⟨t.sp+64#64,8⟩ : Region).Disjoint (Mid.scratch t)
    rw [slot]; exact (args.sub_left subSlot).sub_right sub
  · change (⟨t.sp+64#64,8⟩ : Region).Disjoint (dR t)
    rw [slot,h.regions.d]; exact c.dstArgs.symm.sub_left subSlot
  · change (Prepared.powerR o).Disjoint (dR t); rw [h.regions.d]; exact key.dst
  · change Spec.Gcm.Powers8Repr t.mem _ (Spec.Gcm.ctxH t.mem (K t)); rw [ctx]
    exact Proof.AesGcm.powers8Repr_congr (fun i hi => h.frame.bytes (R := Prepared.powerR o)
      (by simpa only [List.mem_singleton,forall_eq] using key.stack.sub_right outer)
      (by change (128:Nat) ≤ 2^64; decide) hi) key.repr

end VG.Proof.AesGcm.AArch64.Contiguous.MediumRecord

namespace VG.Proof.AesGcm.AArch64.Contiguous.MediumRecord
open VG VG.AArch64 DirectGather Gather
open VG.Impl.AesGcm.AArch64.Contiguous

theorem included {o t : State} (h : Entered o t) (c : Caller o) (key : Prepared.Powers o) :
    Covers ((view o t).rd ++ (view o t).wr) (t.rd++t.wr) ∧ Covers (view o t).wr t.wr := by
  obtain ⟨r,w⟩ := h.covers c
  have wide : Covers (o.rd++o.wr) (t.rd++t.wr) := Covers.append (h.rd ▸ Covers.refl _) (Covers.of_mem fun _ hr => by
    rw [h.wr]; exact List.mem_cons_of_mem _ hr)
  have extraRead : Covers (extra o) (t.rd++t.wr) :=
    (key.read.trans wide).cons ((Covers.of_mem (by simp [callerArgs])).trans (c.read.trans wide))
  exact ⟨Covers.append_left (Covers.append_left (Covers.trans (Covers.of_mem (fun _ hr => List.mem_append_left _ hr)) r) extraRead)
    (Covers.right w),w⟩

theorem within {o t : State} (h : Entered o t) (iv : NL o=12) (al : AL o≤16) (len : (stackArg o 0).toNat≤224) :
    recordWithin 224 (view o t) :=
  ⟨by change (t.gpr .x3).toNat=12; rwa [h.regs .x3 (by decide)],
   by change (t.gpr .x5).toNat≤16; rwa [h.regs .x5 (by decide)],
   by change (stackArg t 1).toNat≤224; rwa [h.len]⟩

theorem inner_ok (v : GcmImpl) (z : v.ctr.scratch=0) (hash : Hash16WithOk)
    {o t : State} (h : Entered o t) (c : Caller o) (key : Prepared.Powers o) (size : recordWithin 224 (view o t)) :
    WP isa (mediumInner v.callees) (view o t) fun u =>
      (∀ r ∈ preserved, u.gpr r=t.gpr r) ∧ gatherPost (view o t) u := by
  have l := layout h c
  apply WP.alloc (by decide) l.w₁
  refine (Mid.cachedBody_ok v z hash _ l (input h c key) size.1 size.2.1 size.2.2).mono ?_
  intro y ⟨post,g,sp⟩ m u fr
  exact ⟨g,leafPost_frame (by decide : 752≤752) l post fr rfl⟩

theorem frame_ok (v : GcmImpl) (z : v.ctr.scratch=0) (hash : Hash16WithOk)
    {o : State} (c : Caller o) (key : Prepared.Powers o) (iv : NL o=12) (al : AL o≤16) (len : (stackArg o 0).toNat≤224)
    (keeps : (mediumFrame v.callees).allInstrs keepsV = true)
    (depth : 16*(mediumInner v.callees).aarch64Depth < 2^64) :
    WP isa (mediumFrame v.callees) o fun u => abiPreserved o u ∧ result o u := by
  apply WP.withPreservedV (hc := keeps)
  apply WP.alloc (by decide) (by have := c.room; omega)
  refine WP.seq ((enter o c).mono ?_)
  intro t h
  obtain ⟨rd,wr⟩ := included h c key
  refine WP.narrowF (inner_ok v z hash h c key (within h iv al len)) rd wr ?_ depth
  intro u _ _ sp _ ⟨regs,post⟩ m y fr
  refine ⟨⟨?_,?_⟩,result_frame c (by decide) (h.post c post) fr⟩
  · intro r hr
    exact (regs r hr).trans (h.regs _ ((by decide : ∀ q ∈ preserved, q ∉ [.x6,.x7,.x9,.x10]) _ hr))
  · change u.sp+48#64=o.sp
    rw [sp,h.sp]; exact BitVec.sub_add_cancel _ _

theorem frame_rel (v : GcmImpl) (z : v.ctr.scratch=0) (hash : Hash16WithOk) {a b : State} (ca : Caller a) (cb : Caller b)
    (ka : Prepared.Powers a) (kb : Prepared.Powers b) (ai : NL a=12) (bi : NL b=12) (aa : AL a≤16) (ba : AL b≤16)
    (an : (stackArg a 0).toNat≤224) (bn : (stackArg b 0).toNat≤224) (pub : onePub 3 a b) (dit : a.dit=b.dit) :
    RelCT isa (Eq2 a b) (mediumFrame v.callees) TT := by
  have sp := pub.2.2.2.2.2.2.2.2.1
  apply RelCT.alloc (R := TT)
  suffices body : RelCT isa (Eq2 (allocated 48 a) (allocated 48 b)) _ TT from
    body.mono (by rintro x y ⟨_,_,⟨rfl,rfl⟩,rfl,rfl⟩; exact ⟨rfl,rfl⟩) (fun _ _ h => h)
  have asp : (allocated 48 a).sp = (allocated 48 b).sp := by simp only [allocated,sp]
  refine rel_seq (rel_taint [] asp (by simp) ⟨_,by taint_decide⟩) (enter a ca) (enter b cb) ?_
  intro t u ht hu
  obtain ⟨tr,tw⟩ := included ht ca ka
  obtain ⟨ur,uw⟩ := included hu cb kb
  have atab := input ht ca ka
  have btab := input hu cb kb
  have lenA := within ht ai aa an
  have lenB := within hu bi ba bn
  have eqPower := pub.2.2.2.2.2.2.2.2.2 2 (by decide)
  have inner : RelCT isa (Eq2 (view a t) (view b u)) (mediumInner v.callees) TT := by
    apply RelCT.alloc (P := Eq2 (view a t) (view b u)) (R := TT)
    exact (Mid.cachedBody_rel v z hash (layout ht ca) (layout hu cb) atab (eqPower ▸ btab) lenA lenB
      (ht.public hu pub dit)).mono (by rintro _ _ ⟨_,_,⟨rfl,rfl⟩,rfl,rfl⟩; exact ⟨rfl,rfl⟩) (fun _ _ h => h)
  rintro _ _ τ υ _ _ ⟨rfl,rfl⟩ et eu
  obtain ⟨_,_,ea,_⟩ := inner_ok v z hash ht ca ka lenA
  obtain ⟨_,_,eb,_⟩ := inner_ok v z hash hu cb kb lenB
  have wa := VG.AArch64.Exec.widen ea tr tw
  have wb := VG.AArch64.Exec.widen eb ur uw
  simp only [view,State.withRegions_withRegions,State.withRegions_self] at wa wb
  obtain ⟨rfl,_⟩ := Exec.det wa et
  obtain ⟨rfl,_⟩ := Exec.det wb eu
  exact ⟨(inner _ _ _ _ _ _ ⟨rfl,rfl⟩ ea eb).1,trivial⟩

end VG.Proof.AesGcm.AArch64.Contiguous.MediumRecord
