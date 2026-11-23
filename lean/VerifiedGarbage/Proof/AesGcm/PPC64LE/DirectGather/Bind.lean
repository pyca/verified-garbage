module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.Contract
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Loop
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.Framework.PPC64LE.Run

/-! # Private frame and copied arguments of direct gather seal -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.Gather
open VG.Impl.StackScratch.PPC64LE

abbrev base (s : State) : Addr := s.sp - 1280
abbrev stack (s : State) : Region := ⟨base s,1280⟩
abbrev work (s : State) : Addr := base s + 128

theorem stack_disjoint {s : State} (h : GatherSplit.Layout s) {r : Region}
    (hr : r∈[cR s,nR s,aR s,dsR s]++lsR s++[dR s,tgR s,argR s]) : (stack s).Disjoint r :=
  (h.stack r hr).sub_left (below_sub (by decide) (by decide))

theorem base_old (s : State) : base s + BitVec.ofNat 64 1280 = s.sp := BitVec.sub_add_cancel _ _

theorem base_fit {s : State} (h : GatherSplit.Layout s) : (base s).toNat+1280=s.sp.toNat := by
  change (s.sp-BitVec.ofNat 64 1280).toNat+1280=s.sp.toNat
  rw [BitVec.toNat_sub]
  have hs := s.sp.isLt
  have hp := h.space
  simp only [BitVec.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  omega_using [hs,hp]

theorem alloc_ok {s : State} (h : GatherSplit.Layout s) :
    isa.push (.alloc 1280) s = some (allocated 1280 s) := by
  change push (.alloc 1280) s=_
  simp only [push,show 32<1280 by decide,show 1280<4096 by decide,show 1280%16=0 by decide,
    show 1280≤s.sp.toNat by omega_using [h.space],and_self,ite_true,allocated]

theorem slot_read {s : State} (h : GatherSplit.Layout s) {j : Nat} (hj : j<3) :
    InRegions ((allocated 1280 s).rd++(allocated 1280 s).wr)
      (base s+BitVec.ofNat 64 (1280+96+8*j)) 8 := by
  refine ⟨argR s,List.mem_append_left _ h.base.argIn,?_⟩
  change (⟨s.sp+BitVec.ofNat 64 96,24⟩ : Region).Contains _ _
  have addr : base s+BitVec.ofNat 64 (1280+96+8*j) = s.sp+BitVec.ofNat 64 (96+8*j) := by
    rw [← base_old s,Offset.add_ofNat_add_ofNat]
    congr 2
    omega_using []
  rw [addr]
  exact Offset.contains _ (by omega_using []) (by omega_using [hj]) (by decide)

theorem slot_write {s : State} {j : Nat} (hj : j≤3) :
    InRegions (allocated 1280 s).wr (base s+BitVec.ofNat 64 (96+8*j)) 8 :=
  ⟨frameR 1280 s,List.mem_cons_self,Offset.contains _ (by omega_using []) (by omega_using [hj]) (by decide)⟩

structure Args (s e : State) : Prop where
  sp : e.sp=base s
  lr : e.lr=s.lr
  regs : ∀ r,r≠.r0 → r≠.r12 → e.gpr r=s.gpr r
  rd : e.rd=s.rd
  wr : e.wr=frameR 1280 s :: s.wr
  copied : ∀ j<3,e.mem.readW (base s+BitVec.ofNat 64 (96+8*j)) 64=stackArg s j
  buf : e.mem.readW (base s+120) 64=work s
  frame : Frame [stack s] s.mem e.mem

theorem args_run {s : State} (h : GatherSplit.Layout s) :
    execBlock isa (setArgs 1280 3) (allocated 1280 s)=
        some (setArgsState 1280 3 (allocated 1280 s),setArgsTrace 1280 (base s) 3) ∧
    Args s (setArgsState 1280 3 (allocated 1280 s)) := by
  obtain ⟨run,rd,wr,sp,lr,regs,fr,copied,buf⟩ := setArgs_run (bytes:=1280) (m:=3) (u:=allocated 1280 s)
    (by decide) (by decide) (by decide) (by decide) (fun _ hj => slot_read h hj) (fun _ hj => slot_write hj)
  have pushFrame : Frame [stack s] s.mem (allocated 1280 s).mem :=
    (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self' (by decide))
  refine ⟨run,⟨sp,lr,regs,rd,wr,?_,buf,pushFrame.trans (fr.sub ?_)⟩⟩
  · intro j hj
    change (setArgsState 1280 3 (allocated 1280 s)).mem.readW ((allocated 1280 s).sp+BitVec.ofNat 64 (96+8*j)) 64=_
    rw [copied j hj]
    have addr : (allocated 1280 s).sp+BitVec.ofNat 64 (1280+96+8*j)=stackArgAddr s j := by
      change base s+BitVec.ofNat 64 (1280+96+8*j)=s.sp+BitVec.ofNat 64 (32+8*(8+j))
      rw [← base_old s,Offset.add_ofNat_add_ofNat]
      congr 2
      omega_using []
    rw [addr]
    apply Frame.readW pushFrame (r:=argR s) _ _ (by decide)
    · change (⟨s.sp+BitVec.ofNat 64 96,24⟩ : Region).Contains (s.sp+BitVec.ofNat 64 (32+8*(8+j))) 8
      exact Offset.contains _ (by omega_using []) (by omega_using [hj]) (by decide)
    · simpa only [List.mem_singleton,forall_eq] using (stack_disjoint h (r:=argR s) (by simp)).symm
  · intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact ⟨_,List.mem_singleton_self _,Offset.sub_base _ (by decide)⟩

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-! # Initial counter block and padded AAD for gathered plaintext -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Proof.AesGcm.PPC64LE.Gather
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH blockAt)
open VG.Impl.AesGcm.PPC64LE (oneAad oneEntry)

abbrev iv (s : State) := bytesAt s.mem (Nn s) (NL s)
abbrev aad (s : State) := bytesAt s.mem (Ad s) (AL s)

structure Bounds (s : State) : Prop where
  key : (C s).toNat+256≤2^64
  nonce : (Nn s).toNat+NL s≤2^64
  aad : (Ad s).toNat+AL s≤2^64
  list : ∀ r∈lsR s,r.base.toNat+r.len≤2^64
  dst : (Dst s).toNat+L s≤2^64
  ctxDst : (cR s).Disjoint (dR s)
  descDst : (dsR s).Disjoint (dR s)
  listDst : ∀ r∈lsR s,r.Disjoint (dR s)
  dt : (dR s).Disjoint (tgR s)

theorem bounds {s : State} (h : GatherSplit.Layout s) : Bounds s := by
  obtain ⟨_,_,cd,_,_,_,_,_,ds,_,ls,dt,_,_,_,_,_,_,_,_,_,_,fc,fn,fa,_,fl,fd,_⟩ := h.base.pre
  exact ⟨fc,fn,fa,fl,fd,cd,ds,fun r hr => (ls r hr).1,dt⟩

theorem count_lt {s : State} (h : GatherSplit.Layout s) : Cnt s*16<2^64 := by
  have hd := h.base.ods
  apply Nat.lt_of_not_ge
  intro ge
  have eq : Cnt s*16=2^64 := by omega_using [hd,ge]
  apply h.base.bds (Gather.Bs s) (by simp [Region.Contains])
  change (Gather.Bs s-Src s).toNat+1 ≤ Cnt s*16
  rw [eq]
  omega_using [(Gather.Bs s-Src s).isLt]

abbrev workR (s : State) : Region := ⟨work s,1152⟩

theorem work_sub (s : State) : Region.Sub (workR s) (stack s) := Offset.sub_base _ (by decide)

theorem work_fit {s : State} (h : GatherSplit.Layout s) : (work s).toNat+1152≤2^64 := by
  have hf := base_fit h
  have hs := s.sp.isLt
  change (base s+BitVec.ofNat 64 128).toNat+1152≤2^64
  rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (a:=128) (by decide),
    Nat.mod_eq_of_lt (by omega_using [hf,hs])]
  omega_using [hf,hs]

theorem Args.read {s e : State} (p : Args s e) (h : GatherSplit.Layout s) {r : Region}
    (hr : r∈[cR s,nR s,aR s,dsR s]++lsR s++[argR s]) : Covers [r] (e.rd++e.wr) := by
  rw [p.rd,h.base.pre.1]
  exact Covers.of_mem (by simpa only [List.mem_singleton,forall_eq] using List.mem_append_left e.wr hr)

theorem Args.workWrite {s e : State} (p : Args s e) : Covers [workR s] e.wr := by
  rw [p.wr]
  exact Covers.one ⟨_,List.mem_cons_self,Offset.contains _ (by decide) (by decide) (by decide)⟩

theorem Args.one {s e : State} (p : Args s e) :
    WP isa (.block (oneEntry 120)) e (SO1 (work s) (Dst s) e) := by
  have readSlot (j : Nat) (hj : j≤3) : InRegions (e.rd++e.wr) (e.sp+BitVec.ofNat 64 (96+8*j)) 8 := by
    rw [p.sp,p.wr]
    exact (Covers.right (Covers.refl _)) _ _ (slot_write hj)
  apply one1_at (off:=120) (n:=1152) (by decide) (by decide) p.workWrite (readSlot 3 (by decide))
    (by rw [p.sp]; exact p.buf) (readSlot 0 (by decide)) (by rw [p.sp]; exact p.copied 0 (by decide))
  rw [p.sp]
  change (⟨base s+BitVec.ofNat 64 96,8⟩ : Region).Disjoint ⟨base s+BitVec.ofNat 64 128+BitVec.ofNat 64 128,120⟩
  rw [Offset.add_ofNat_add_ofNat]
  exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)

theorem aad_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {s e t : State}
    (h : GatherSplit.Layout s) (p : Args s e) (q : SO1 (work s) (Dst s) e t) :
    WP isa oneAad t (OA t.gpr e.sp (ctxH s.mem (C s)) (iv s) (aad s) t.mem) := by
  have hp := bounds h
  have key := p.regs .r3 (by decide) (by decide)
  have n := p.regs .r5 (by decide) (by decide)
  have nl := p.regs .r6 (by decide) (by decide)
  have a := p.regs .r7 (by decide) (by decide)
  have al := p.regs .r8 (by decide) (by decide)
  have sub := work_sub s
  have full : Frame [stack s] s.mem t.mem := p.frame.trans (q.en.frame.sub (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl
    exact ⟨_,List.mem_singleton_self _,fun addr ha => sub addr ((Offset.sub_base _ (show 128+120≤1152 by decide)) addr ha)⟩))
  have read : ∀ {r}, r∈[cR s,nR s,aR s,dsR s]++lsR s++[argR s] → Covers [r] (t.rd++t.wr) := by
    intro r hr; rw [q.en.keeps.rd,q.en.keeps.wr]; exact p.read h hr
  have L := oneLay hp.key (work_fit h) ((stack_disjoint h (r:=cR s) (by simp)).symm.sub_right sub)
  have V := L.v (q.r29.trans key) q.r30 q.r31
  have he := one_env q (by rw [key]; exact p.read h (r:=cR s) (by simp)) p.workWrite
  have disj {r : Region} (hr : r∈[cR s,nR s,aR s,dsR s]++lsR s++[dR s,tgR s,argR s]) :
      ∀ x∈[stack s],r.Disjoint x := by
    intro x hx; rcases List.mem_singleton.mp hx with rfl; exact (stack_disjoint h hr).symm
  have data {r : Region} (hr : r∈[cR s,nR s,aR s,dsR s]++lsR s++[dR s,tgR s,argR s])
      (fit : r.base.toNat+r.len≤2^64) (lt : r.len<2^64) (rd : Covers [r] (t.rd++t.wr)) :
      DataOk (t.gpr .r30) (t.gpr .r31) t r.base r.len := by
    rw [q.r30,q.r31]
    have sep := ((stack_disjoint h hr).symm.sub_right sub)
    exact ⟨rd,lt,fit,sep.sub_right (Offset.sub_base _ (by decide)),sep.sub_right (Region.sub_prefix (by decide))⟩
  have H : blockAt t.mem (t.gpr .r29+240)=ctxH s.mem (C s) := by
    rw [q.r29,key]
    exact blockAt_frame full (fun r hr => (disj (r:=cR s) (by simp) r hr).sub_left (Offset.sub_base _ (by decide)))
  have ni := bytesAt_frame full (disj (r:=nR s) (by simp)) (Nat.le_of_lt (s.gpr .r6).isLt)
  have ai := bytesAt_frame full (disj (r:=aR s) (by simp)) (Nat.le_of_lt (s.gpr .r8).isLt)
  have lemmaA := oneAad_ok V he H (q.r24.trans n) (by rw [q.r25,nl]; simp only [NL,BitVec.ofNat_toNat,BitVec.setWidth_eq])
    (by rw [q.r18,nl]; simp only [NL,BitVec.ofNat_toNat,BitVec.setWidth_eq])
    (data (r:=nR s) (by simp) hp.nonce (s.gpr .r6).isLt (read (by simp)))
    (by rw [q.r21,q.r22,a,al]; exact data (r:=aR s) (by simp) hp.aad (s.gpr .r8).isLt (read (by simp)))
  simpa only [q.r21,q.r22,a,al,ni,ai] using lemmaA

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-! # Bind the descriptor loop to its caller's arguments -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Proof.AesGcm.PPC64LE.Gather
open VG.Spec.Gcm (Block blockAt ctxH j0 inc32)
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.PPC64LE (mov)

abbrev loadArgs : List Instr :=
  [mov .r19 .r27, mov .r18 .r23, .addSp .r12 0, .load .d .r27 .r12 96,
   .load .d .r23 .r12 104, .load .d .r20 .r12 112, mov .r21 .r27, .li .r0 0, .store .d .r0 .r31 112]

abbrev initialCounter (s : State) := inc32 (j0 (ctxH s.mem (C s)) (iv s))
def argsFor (s u : State) : LoopArgs := ⟨u.gpr,base s,Src s,Cnt s,Rn s,initialCounter s⟩

structure Bound (s before u : State) : Prop where
  slot : u.mem=(before.mem.writeW (base s+240) (0 : BitVec 64))
  sp : u.sp=before.sp
  rd : u.rd=before.rd
  wr : u.wr=before.wr
  desc : u.gpr .r19=Src s
  count : u.gpr .r18=s.gpr .r10
  dst : u.gpr .r27=Dst s
  pos : u.gpr .r21=Dst s
  len : u.gpr .r23=stackArg s 1
  tag : u.gpr .r20=Tg s
  keep : ∀ r∈[Reg.r2,.r14,.r15,.r16,.r17,.r22,.r28,.r29,.r30,.r31],u.gpr r=before.gpr r

theorem loadArgs_wp {s e t v : State} (p : Args s e) (q : SO1 (work s) (Dst s) e t)
    (oa : OA t.gpr e.sp (ctxH s.mem (C s)) (iv s) (aad s) t.mem v) (wr : v.wr=t.wr) :
    WP isa (.block loadArgs) v (Bound s v) := by
  have stackEq : v.sp=base s := oa.env.sp.trans p.sp
  have workEq : v.gpr .r31=work s := (oa.env.fr _ (by decide)).trans q.r31
  have desc : v.gpr .r27=Src s := (oa.env.fr _ (by decide)).trans (q.r27.trans (p.regs _ (by decide) (by decide)))
  have count : v.gpr .r23=s.gpr .r10 := (oa.env.fr _ (by decide)).trans (q.r23.trans (p.regs _ (by decide) (by decide)))
  have ww : v.wr=frameR 1280 s :: s.wr := wr.trans (q.en.keeps.wr.trans p.wr)
  have load (j : Nat) (hj : j<3) : InRegions (v.rd++v.wr) (base s+BitVec.ofNat 64 (96+8*j)) 8 := by
    rw [ww]; exact (Covers.right (Covers.refl _)) _ _ (slot_write (s:=s) (j:=j) (by omega_using [hj]))
  have val (j : Nat) (hj : j<3) : v.mem.readW (base s+BitVec.ofNat 64 (96+8*j)) 64=stackArg s j := by
    rw [Frame.readW (q.aadFrame oa) (Region.contains_self (base s+BitVec.ofNat 64 (96+8*j)) 8)
      (fun r hr => by rcases List.mem_singleton.mp hr with rfl
                      exact Offset.disjoint _ (.inl (by omega_using [hj])) (by omega_using [hj]) (by decide)) (by decide)]
    exact p.copied _ hj
  have writeSlot : InRegions v.wr (base s+240) 8 := by
    rw [ww]; exact ⟨_,List.mem_cons_self,Offset.contains _ (by decide) (by decide) (by decide)⟩
  have addr : work s+BitVec.ofNat 64 112=base s+240 := Offset.add_ofNat_add_ofNat ..
  have c0 : InRegions (v.rd++v.wr) (base s+BitVec.ofNat 64 96) 8 := load 0 (by decide)
  have c1 : InRegions (v.rd++v.wr) (base s+BitVec.ofNat 64 104) 8 := load 1 (by decide)
  have c2 : InRegions (v.rd++v.wr) (base s+BitVec.ofNat 64 112) 8 := load 2 (by decide)
  have v0 : v.mem.readW (base s+BitVec.ofNat 64 96) 64=Dst s := val 0 (by decide)
  have v1 : v.mem.readW (base s+BitVec.ofNat 64 104) 64=stackArg s 1 := val 1 (by decide)
  have v2 : v.mem.readW (base s+BitVec.ofNat 64 112) 64=Tg s := val 2 (by decide)
  apply WP.of_runBlock
  simp only [loadArgs,runBlock_cons,runStep_some,runBlock_nil,exec,State.write,VG.PPC64LE.addr,State.load,State.store,
    mov,BitVec.or_self,Size.bytes,Proof.Gcm.PPC64LE.read_8,BitVec.setWidth_eq,BitVec.add_zero,
    stackEq,workEq,desc,count,addr,c0,c1,c2,v0,v1,v2,writeSlot,Option.bind_some,Option.map_some,
    Option.some.injEq,exists_eq_left',reduceCtorEq,ne_eq,not_false_eq_true,
    Nat.reduceLT,Nat.reduceMod,Nat.reducePow,↓reduceIte,and_self,implies_true]
  constructor
  all_goals first | rfl | exact stackEq.symm | exact v0 | exact v1 | exact v2 | (intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)

theorem bindFrame {s e t v u : State} (p : Args s e) (q : SO1 (work s) (Dst s) e t)
    (oa : OA t.gpr e.sp (ctxH s.mem (C s)) (iv s) (aad s) t.mem v) (b : Bound s v u) :
    Frame [stack s] s.mem u.mem := by
  rw [b.slot]
  have f := p.frame.trans ((q.aadFrame oa).sub (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; exact ⟨_,List.mem_singleton_self _,work_sub s⟩))
  exact f.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))

end VG.Proof.AesGcm.PPC64LE.DirectGather
