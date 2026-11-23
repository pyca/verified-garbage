module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Bind
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Finish
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish

-- separate module: the caller’s memory layout and frame proofs connect the descriptor loop to both the correctness and timing arguments in Scrub.
/-! # The gathered byte sequence and loop invariant at entry -/
@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Proof.AesGcm.PPC64LE.Gather
open VG.Spec.Gcm (blockAt ctxH)
open VG.Proof.Gather.PPC64LE (slice_mem)
abbrev descAgree (s u : State) :=
  ∀ r∈Sig.descRegion 64 (Src s) (Cnt s)::lsR s,∀ x,r.Contains x 1 → s.mem x=u.mem x

theorem agree {s u : State} (h : GatherSplit.Layout s) (fr : Frame [stack s] s.mem u.mem) : descAgree s u := by
  intro r hr x hx
  apply Eq.symm
  apply fr
  intro k hk
  rcases List.mem_singleton.mp hk with rfl
  rcases List.mem_cons.mp hr with rfl|hr
  · exact fun hh => stack_disjoint h (r:=dsR s) (by simp) x hh hx
  · exact fun hh => stack_disjoint h (r:=r) (by simp [hr]) x hh hx

structure Regs (s u : State) : Prop where
  r31 : u.gpr .r31=work s
  r30 : u.gpr .r30=base s+144
  r29 : u.gpr .r29=C s
  r28 : u.gpr .r28=s.gpr .r4
  r22 : u.gpr .r22=s.gpr .r8
  sp : u.sp=base s
  rd : u.rd=s.rd
  wr : u.wr=frameR 1280 s::s.wr

theorem bind_regs {s e t v u : State} (p : Args s e) (q : SO1 (work s) (Dst s) e t)
    (oa : OA t.gpr e.sp (ctxH s.mem (C s)) (iv s) (aad s) t.mem v)
    (rd : v.rd=t.rd) (wr : v.wr=t.wr) (b : Bound s v u) : Regs s u := by
  have k (r : Reg) (hr : r∈[Reg.r2,.r14,.r15,.r16,.r17,.r22,.r28,.r29,.r30,.r31]) : u.gpr r=t.gpr r :=
    (b.keep r hr).trans (oa.env.fr r (by revert hr; revert r; decide))
  exact ⟨(k _ (by decide)).trans q.r31,by rw [k _ (by decide),q.r30]; exact Offset.add_ofNat_add_ofNat ..,
    (k _ (by decide)).trans (q.r29.trans (p.regs _ (by decide) (by decide))),
    (k _ (by decide)).trans (q.r28.trans (p.regs _ (by decide) (by decide))),
    (k _ (by decide)).trans (q.r22.trans (p.regs _ (by decide) (by decide))),
    b.sp.trans (oa.env.sp.trans p.sp),b.rd.trans (rd.trans (q.en.keeps.rd.trans p.rd)),
    b.wr.trans (wr.trans (q.en.keeps.wr.trans p.wr))⟩

theorem input {s v u : State} (h : GatherSplit.Layout s) (r : Regs s u) (b : Bound s v u)
    (ag : descAgree s u) : LoopInput (argsFor s u) u := by
  have f := bounds h
  have total := (Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) ag).trans h.base.hgl
  have listed := (Proof.AesGcm.listed_congr_le (Nat.le_refl _) ag).1
  have loc {i : Nat} (hi : i<Cnt s) : (⟨(argsFor s u).base u i,(argsFor s u).len u i⟩ : Region)∈lsR s := by
    change _ ∈ Sig.listed 64 s.mem .u8 (Src s) (Cnt s)
    rw [←listed]; exact slice_mem _ _ hi
  have rd {z : Region} (hz : z∈[cR s,nR s,aR s,dsR s]++lsR s++[argR s]) : Covers [z] (u.rd++u.wr) := by
    rw [r.rd,h.base.pre.1]; exact Covers.of_mem (by simpa only [List.mem_singleton,forall_eq] using List.mem_append_left u.wr hz)
  have fullfit : (base s).toNat+1280≤2^64 := (base_fit h) ▸ Nat.le_of_lt s.sp.isLt
  have W := oneLay f.key (work_fit h) (((stack_disjoint h (r:=cR s) (by simp)).symm).sub_right (work_sub s))
  have st : work s+BitVec.ofNat 64 16=base s+144 := Offset.add_ofNat_add_ofNat ..
  change LoopInput ⟨u.gpr,base s,Src s,Cnt s,Rn s,initialCounter s⟩ u
  refine ⟨r.r31,r.r30,congrArg BitVec.toNat r.r28,h.base.hR,?_,count_lt h,?_,fullfit,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change Lay (u.gpr .r29) (u.gpr .r30) (u.gpr .r31)
    rw [r.r29,r.r30,r.r31,←st]; exact W
  · change VG.Spec.Gcm.gatheredLen 64 u.mem (Src s) (Cnt s)<2^64
    rw [total]; exact (stackArg s 1).isLt
  · change (u.gpr .r29).toNat+256≤2^64; rw [r.r29]; exact f.key
  · change (u.gpr .r27).toNat+VG.Spec.Gcm.gatheredLen 64 u.mem (Src s) (Cnt s)≤2^64
    rw [b.dst,total]; exact f.dst
  · change Covers [⟨u.gpr .r29,256⟩] _; rw [r.r29]; exact rd (by simp)
  · rw [Nat.mul_comm]; exact rd (by simp)
  · change Covers [⟨u.gpr .r27,VG.Spec.Gcm.gatheredLen 64 u.mem (Src s) (Cnt s)⟩] _
    rw [b.dst,total,r.wr,h.base.pre.2.1]; exact Covers.of_mem (by simp)
  · rw [r.wr]; exact Covers.of_mem (by simp)
  · change (stack s).Disjoint ⟨u.gpr .r29,256⟩; rw [r.r29]; exact stack_disjoint h (by simp)
  · rw [Nat.mul_comm]; exact stack_disjoint h (by simp)
  · change (stack s).Disjoint ⟨u.gpr .r27,VG.Spec.Gcm.gatheredLen 64 u.mem (Src s) (Cnt s)⟩
    rw [b.dst,total]; exact stack_disjoint h (by simp)
  · change (⟨u.gpr .r29,256⟩ : Region).Disjoint ⟨u.gpr .r27,VG.Spec.Gcm.gatheredLen 64 u.mem (Src s) (Cnt s)⟩
    rw [r.r29,b.dst,total]; exact f.ctxDst
  · change (⟨Src s,16*Cnt s⟩ : Region).Disjoint ⟨u.gpr .r27,VG.Spec.Gcm.gatheredLen 64 u.mem (Src s) (Cnt s)⟩
    rw [Nat.mul_comm,b.dst,total]; exact f.descDst
  · intro i hi; exact rd (List.mem_append_left _ (List.mem_append_right _ (loc hi)))
  · intro i hi; exact f.list _ (loc hi)
  · intro i hi; exact stack_disjoint h (List.mem_append_left _ (List.mem_append_right _ (loc hi)))
  · intro i hi
    change (⟨_,_⟩ : Region).Disjoint ⟨u.gpr .r27,VG.Spec.Gcm.gatheredLen 64 u.mem (Src s) (Cnt s)⟩
    rw [b.dst,total]; exact f.listDst _ (loc hi)

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-! # Original inputs, caller registers and authenticated data at loop entry -/
@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Proof.AesGcm.PPC64LE.Gather
open VG.Spec.Gcm (blockAt ctxH j0 inc32 zeros padLen)
open VG.Spec.Aes (bytesAt)

abbrev paddedAad (s : State) := aad s ++ zeros (padLen (aad s).length)
abbrev low : List Reg := [.r2,.r14,.r15,.r16,.r17]

structure Start (s e u : State) extends Regs s u where
  input : LoopInput (argsFor s u) u
  atZero : LoopAt (argsFor s u) u 0 0 u
  agree : descAgree s u
  frame : Frame [stack s] s.mem u.mem
  dst : u.gpr .r27=Dst s
  len : u.gpr .r23=stackArg s 1
  tag : u.gpr .r20=Tg s
  y : Proof.Gcm.Absorbed u.mem (base s+160) (base s+176) (ctxH s.mem (C s)) (paddedAad s)
  j : blockAt u.mem (base s+144)=j0 (ctxH s.mem (C s)) (iv s)
  saved : SavedAt u.mem (work s) e
  lowRegs : ∀ r∈low,u.gpr r=e.gpr r

theorem start {s e t v u : State} (h : GatherSplit.Layout s) (p : Args s e) (q : SO1 (work s) (Dst s) e t)
    (oa : OA t.gpr e.sp (ctxH s.mem (C s)) (iv s) (aad s) t.mem v)
    (rd : v.rd=t.rd) (wr : v.wr=t.wr) (b : Bound s v u) : Start s e u := by
  obtain r := bind_regs p q oa rd wr b
  have fr := bindFrame p q oa b
  have ag := agree h fr
  have hs := input h r b ag
  have slot : Frame [⟨base s+240,8⟩] v.mem u.mem := by
    rw [b.slot]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have same (d : Nat) (hd : d+16≤240) : blockAt u.mem (base s+BitVec.ofNat 64 d)=blockAt v.mem (base s+BitVec.ofNat 64 d) :=
    blockAt_frame slot (fun k hk => by rcases List.mem_singleton.mp hk with rfl; exact Offset.disjoint _ (.inl hd) (by omega_using [hd]) (by decide))
  have state : t.gpr .r30=base s+BitVec.ofNat 64 144 := q.r30.trans (Offset.add_ofNat_add_ofNat ..)
  have counter := oa.cb
  rw [state,Offset.add_ofNat_add_ofNat] at counter
  have key := oa.j
  rw [state] at key
  have aa := oa.abs
  rw [state,Offset.add_ofNat_add_ofNat,Offset.add_ofNat_add_ofNat] at aa
  have store0 : u.mem.readW (base s+240) 64=0 := by rw [b.slot,Mem.readW_writeW_self64]
  have ev : Env (cursors ((argsFor s u).regs 0) ((argsFor s u).O+BitVec.ofNat 64 ((argsFor s u).pos u 0))) (base s) u := by
    refine ⟨?_,r.sp,?_,?_,?_⟩
    · intro i hi
      by_cases i19 : i=.r19
      · subst i; exact b.desc.trans (BitVec.add_zero _).symm
      by_cases i18 : i=.r18
      · subst i; simpa only [argsFor,LoopArgs.regs,cursors,reduceCtorEq,ite_false,ite_true,Nat.sub_zero,Cnt,
          BitVec.ofNat_toNat,BitVec.setWidth_eq] using b.count
      by_cases i21 : i=.r21
      · subst i; change u.gpr .r21=u.gpr .r27+0; rw [b.pos,b.dst]; exact (BitVec.add_zero _).symm
      simp only [cursors,i19,i18,i21,LoopArgs.regs,ite_false,argsFor]
    · exact hs.keyRead
    · change Covers [⟨u.gpr .r30,80⟩] u.wr
      rw [r.r30,r.wr]; exact Covers.one ⟨_,List.mem_cons_self,Offset.contains _ (by decide) (by decide) (by decide)⟩
    · change Covers [⟨u.gpr .r31,288⟩] u.wr
      rw [r.r31,r.wr]; exact Covers.one ⟨_,List.mem_cons_self,Offset.contains _ (by decide) (by decide) (by decide)⟩
  have v0 : LoopAt (argsFor s u) u 0 0 u := by
    refine ⟨Nat.zero_le _,Nat.zero_le _,ev,rfl,rfl,store0,?_,?_,rfl,Frame.refl _ _⟩
    · rfl
    · change Proof.Gcm.Ctr u.mem (base s+192) (base s+208) _ (initialCounter s) 0
      refine ⟨?_,fun hn => (hn rfl).elim⟩
      simpa only [initialCounter,BitVec.ofNat_eq_ofNat,Nat.zero_add,Nat.reduceDiv,Nat.repeat] using (same 192 (by decide)).trans counter
  refine ⟨r,hs,v0,ag,fr,b.dst,b.len,b.tag,?_,(same 144 (by decide)).trans key,?_,?_⟩
  · apply aa.congr (same 160 (by decide))
    apply bytesAt_frame slot _ (by omega_using [Nat.mod_lt (paddedAad s).length (by decide : 0<16)])
    intro k hk
    rcases List.mem_singleton.mp hk with rfl
    exact Offset.disjoint _ (.inl (by omega_using [Nat.mod_lt (paddedAad s).length (by decide : 0<16)]))
      (by omega_using [Nat.mod_lt (paddedAad s).length (by decide : 0<16)]) (by decide)
  · have L := hs.layout
    change Lay (u.gpr .r29) (u.gpr .r30) (u.gpr .r31) at L
    rw [r.r29,r.r30,r.r31] at L
    have f := oa.frame
    rw [state,q.r31] at f
    refine (q.en.saved.frame f (saved_j0Frame L)).frame slot ?_
    intro k hk
    rcases List.mem_singleton.mp hk with rfl
    change (⟨base s+BitVec.ofNat 64 128+BitVec.ofNat 64 128,120⟩ : Region).Disjoint _
    rw [Offset.add_ofNat_add_ofNat]
    exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  · intro i hi
    exact (b.keep i (by revert hi;revert i;decide)).trans ((oa.env.fr i (by revert hi;revert i;decide)).trans (q.en.low i hi))

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-! # Publish the ciphertext and tag, and restore the caller's saved registers -/
@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Proof.AesGcm.PPC64LE.Gather
open VG.Spec.Gcm (blockAt ctxH ctxCiph fullTag encryptWith gctr)
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.PPC64LE (tagOut restore)

theorem Start.total {s e u : State} (h : GatherSplit.Layout s) (p : Start s e u) :
    (argsFor s u).pos u (Cnt s)=L s :=
  (Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) p.agree).trans h.base.hgl

theorem Start.key {s e u : State} (h : GatherSplit.Layout s) (p : Start s e u) :
    ctxH u.mem (argsFor s u).C=ctxH s.mem (C s) := by
  change blockAt u.mem (u.gpr .r29+240)=_
  rw [p.r29]
  apply blockAt_frame p.frame
  intro r hr; rcases List.mem_singleton.mp hr with rfl
  exact ((stack_disjoint h (r:=cR s) (by simp)).symm).sub_left (Offset.sub_base _ (by decide))

theorem Start.cipher {s e u : State} (h : GatherSplit.Layout s) (p : Start s e u) :
    ciphOf u.mem (argsFor s u).C (argsFor s u).rounds=ctxCiph s.mem (C s) (Rn s) := by
  change ciphOf u.mem (u.gpr .r29) (Rn s)=_
  rw [p.r29]
  exact ciph_frame p.frame (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact (stack_disjoint h (r:=cR s) (by simp)).symm) h.base.hR

theorem Start.finish [Proof.Gcm.PPC64LE.GhashLaw] {s e u z : State} {b : Nat} (h : GatherSplit.Layout s)
    (p : Start s e u) (q : LoopAt (argsFor s u) u (Cnt s) b z) :
    WP isa VG.Impl.AesGcm.PPC64LE.DirectGather.finish z (Finished (argsFor s u) u z (iv s) (aad s)) := by
  apply finish_wp p.input q
  · change (u.gpr .r22).toNat=(aad s).length; rw [p.r22]; exact (length_bytesAt ..).symm
  · change (u.gpr .r23).toNat=_; rw [p.len]; exact (p.total h).symm
  · rw [p.key h]; exact p.j
  · rw [p.key h]; exact p.y

theorem finish_sub {s e u : State} (p : Start s e u) :
    ∀ r∈finishFrame (argsFor s u),Region.Sub r (stack s) := by
  intro r hr
  change r∈absFrame (u.gpr .r30) (u.gpr .r31) 16++tagFrame (u.gpr .r30) (u.gpr .r31) 0 at hr
  rw [p.r30,p.r31] at hr
  change r ∈ [⟨base s+BitVec.ofNat 64 144+BitVec.ofNat 64 16,16⟩,⟨base s+BitVec.ofNat 64 144+BitVec.ofNat 64 32,16⟩,
    ⟨base s+BitVec.ofNat 64 144,32⟩,⟨base s+BitVec.ofNat 64 128+BitVec.ofNat 64 96,16⟩,⟨base s+BitVec.ofNat 64 128+BitVec.ofNat 64 0,16⟩] at hr
  simp only [Offset.add_ofNat_add_ofNat,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl <;> exact Offset.sub_base _ (by decide)

theorem saved_loop {s e u : State} (h : GatherSplit.Layout s) (p : Start s e u) :
    ∀ r∈loopFrame (argsFor s u) ((argsFor s u).pos u (Cnt s)),(savedR (work s)).Disjoint r := by
  intro r hr
  change (⟨base s+BitVec.ofNat 64 128+BitVec.ofNat 64 128,120⟩ : Region).Disjoint _
  rw [Offset.add_ofNat_add_ofNat]
  simp only [loopFrame,bulkAreas,callAreas,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  case inr.inr.inr.inr.inr.inl =>
    change (⟨base s+BitVec.ofNat 64 (128+128),120⟩ : Region).Disjoint ⟨u.gpr .r27,_⟩
    rw [p.dst,p.total h]
    exact (stack_disjoint h (r:=dR s) (by simp)).sub_left (Offset.sub_base _ (by decide))
  all_goals exact Offset.disjoint _ (by decide) (by decide) (by decide)

theorem saved_finish {s e u : State} (p : Start s e u) :
    ∀ r∈finishFrame (argsFor s u),(savedR (work s)).Disjoint r := by
  have L := p.input.layout
  change Lay (u.gpr .r29) (u.gpr .r30) (u.gpr .r31) at L
  rw [←p.r31]
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · exact saved_absFrame L (.inr rfl) r hr
  · obtain ⟨x,hx,sub⟩ := tag_otSub r hr
    exact (saved_otFrame L (.inl rfl) x hx).sub_right sub

theorem prepared {s e u z t : State} {b : Nat} (h : GatherSplit.Layout s) (pp : Args s e) (p : Start s e u)
    (q : LoopAt (argsFor s u) u (Cnt s) b z) (f : Finished (argsFor s u) u z (iv s) (aad s) t) :
    WP isa (.seq (.block tagOut) (.block restore)) t (fun y => abiPreserved e y ∧ gatherPost s y) := by
  let a := argsFor s u
  have ds := (stack_disjoint h (r:=dR s) (by simp)).symm
  have ts := (stack_disjoint h (r:=tgR s) (by simp)).symm
  have wr := f.wr.trans (q.wr.trans p.wr)
  have ct : bytesAt z.mem (Dst s) (L s)=gctr (ctxCiph s.mem (C s) (Rn s)) (initialCounter s) (pt s (Cnt s)) := by
    have hh := q.out
    rw [p.cipher h,p.total h] at hh
    change bytesAt z.mem (u.gpr .r27) (L s)=_ at hh
    rw [p.dst] at hh
    rw [VG.Proof.Gcm.gctr_eq]
    exact hh.trans (congrArg _ (Proof.AesGcm.gathered_congr_le (Nat.le_refl _) p.agree))
  have tag := f.tag
  have tot : (argsFor s u).pos u (argsFor s u).count=L s := p.total h
  rw [p.cipher h,p.key h,tot] at tag
  change bytesAt t.mem (u.gpr .r31) 16=fullTag _ _ _ _ (bytesAt z.mem (u.gpr .r27) _) at tag
  rw [p.r31,p.dst] at tag
  have same := bytesAt_frame f.frame (fun r hr => ds.sub_right (finish_sub p r hr)) (Nat.le_of_lt (stackArg s 1).isLt)
  have tagW : Covers [⟨a.finalV u .r20,16⟩] t.wr := by
    change Covers [⟨u.gpr .r20,16⟩] _; rw [p.tag,wr,h.base.pre.2.1]; exact Covers.of_mem (by simp)
  have tw : (⟨a.finalV u .r20,16⟩ : Region).Disjoint ⟨a.finalV u .r31,16⟩ := by
    change (⟨u.gpr .r20,16⟩ : Region).Disjoint ⟨u.gpr .r31,16⟩
    rw [p.tag,p.r31]; exact ts.sub_right (Offset.sub_base _ (by decide))
  refine WP.seq (WP.mono (tagOut_ok f.env tagW tw) fun w ⟨out,fr,k,hk⟩ => ?_)
  have tr : Frame [tgR s] t.mem w.mem := by
    change Frame [⟨u.gpr .r20,16⟩] _ _ at fr
    rwa [p.tag] at fr
  have dest := bytesAt_frame tr (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact (bounds h).dt)
    (Nat.le_of_lt (stackArg s 1).isLt)
  have tk : bytesAt w.mem (Tg s) 16=bytesAt t.mem (work s) 16 := by
    change bytesAt w.mem (u.gpr .r20) 16=bytesAt t.mem (u.gpr .r31) 16 at out
    rwa [p.tag,p.r31] at out
  have reg : w.gpr .r31=work s := (k _ (by decide)).trans (f.env.r31.trans p.r31)
  have readW : Covers [workR s] (w.rd++w.wr) := by
    rw [hk.wr,wr,←pp.wr]; exact Covers.right pp.workWrite
  have sv := ((p.saved.frame q.frame (saved_loop h p)).frame f.frame (saved_finish p)).frame tr (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl
    change (⟨base s+BitVec.ofNat 64 128+BitVec.ofNat 64 128,120⟩ : Region).Disjoint _
    rw [Offset.add_ofNat_add_ofNat]
    exact ts.symm.sub_left (Offset.sub_base _ (by decide)))
  refine WP.mono (restore_ok reg readW sv (hk.sp.trans (f.env.sp.trans pp.sp.symm)) (fun r hr => ?_)) fun y ⟨abi,mem,_,_,_⟩ => ?_
  · have sf : ∀ r∈low,r∈frozen := by decide
    have ke := k r (by revert hr; revert r; decide)
    have eq : a.finalV u r=u.gpr r := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl <;> rfl
    exact ke.trans ((f.env.fr r (sf r hr)).trans (eq.trans (p.lowRegs r hr)))
  · refine ⟨abi,?_⟩
    unfold gatherPost
    rw [mem,dest,same,tk,tag,ct]
    unfold encryptWith
    refine Prod.ext rfl ?_
    exact List.take_of_length_le (by rw [VG.Spec.Gcm.fullTag,Proof.Gcm.length_gctr,Proof.Cmac.toBytes_length])

end VG.Proof.AesGcm.PPC64LE.DirectGather
