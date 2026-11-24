module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.CallLayout
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Entry
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # Allocate the POWER frame and copy the two public stack arguments -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.StackScratch.PPC64LE

abbrev base (s : State) : Addr := s.sp - 1280
abbrev stack (s : State) : Region := ⟨base s,1280⟩
abbrev work (s : State) : Addr := base s + 128

theorem stack_disjoint {s : State} (h : CallLayout s) {r : Region} (hr : r∈argsRegions s) : (stack s).Disjoint r :=
  (h.stack r hr).sub_left (below_sub (by decide) (by decide))

theorem base_old (s : State) : base s + BitVec.ofNat 64 1280 = s.sp := BitVec.sub_add_cancel _ _

theorem base_fit {s : State} (h : CallLayout s) : (base s).toNat+1280=s.sp.toNat := by
  change (s.sp-BitVec.ofNat 64 1280).toNat+1280=s.sp.toNat
  rw [BitVec.toNat_sub]
  have hs := s.sp.isLt
  have hp := h.space
  simp only [BitVec.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  omega_using [hs,hp]

theorem alloc_ok {s : State} (h : CallLayout s) :
    isa.push (.alloc 1280) s = some (allocated 1280 s) := by
  change push (.alloc 1280) s=_
  simp only [push,show 32<1280 by decide,show 1280<4096 by decide,show 1280%16=0 by decide,
    show 1280≤s.sp.toNat by omega_using [h.space],and_self,ite_true,allocated]

theorem slot_read {s : State} (h : CallLayout s) {j : Nat} (hj : j<2) :
    InRegions ((allocated 1280 s).rd++(allocated 1280 s).wr)
      (base s+BitVec.ofNat 64 (1280+96+8*j)) 8 := by
  refine ⟨slotsR s,List.mem_append_left _ (by change slotsR s∈s.rd;rw [h.rd];exact List.mem_append_right _ (List.mem_singleton_self _)),?_⟩
  change (⟨s.sp+BitVec.ofNat 64 96,16⟩ : Region).Contains _ _
  have addr : base s+BitVec.ofNat 64 (1280+96+8*j) = s.sp+BitVec.ofNat 64 (96+8*j) := by
    rw [← base_old s,Offset.add_ofNat_add_ofNat]
    congr 2
    omega_using []
  rw [addr]
  exact Offset.contains _ (by omega_using []) (by omega_using [hj]) (by decide)

theorem slot_write {s : State} {j : Nat} (hj : j≤2) :
    InRegions (allocated 1280 s).wr (base s+BitVec.ofNat 64 (96+8*j)) 8 :=
  ⟨frameR 1280 s,List.mem_cons_self,Offset.contains _ (by omega_using []) (by omega_using [hj]) (by decide)⟩

structure Args (s e : State) : Prop where
  sp : e.sp=base s
  lr : e.lr=s.lr
  regs : ∀ r,r≠.r0 → r≠.r12 → e.gpr r=s.gpr r
  rd : e.rd=s.rd
  wr : e.wr=frameR 1280 s :: s.wr
  copied : ∀ j<2,e.mem.readW (base s+BitVec.ofNat 64 (96+8*j)) 64=stackArg s j
  buf : e.mem.readW (base s+112) 64=work s
  frame : Frame [stack s] s.mem e.mem

theorem args_run {s : State} (h : CallLayout s) :
    execBlock isa (setArgsAt 1280 2 128) (allocated 1280 s)=
        some (setArgsAtState 1280 2 128 (allocated 1280 s),setArgsTrace 1280 (base s) 2) ∧
    Args s (setArgsAtState 1280 2 128 (allocated 1280 s)) := by
  obtain ⟨run,rd,wr,sp,lr,regs,fr,copied,buf⟩ := setArgsAt_run (bytes:=1280) (m:=2) (workOff:=128) (u:=allocated 1280 s)
    (by decide) (by decide) (by decide) (by decide) (by decide) (fun _ hj => slot_read h hj) (fun _ hj => slot_write hj)
  have pushFrame : Frame [stack s] s.mem (allocated 1280 s).mem :=
    (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self' (by decide))
  refine ⟨run,⟨sp,lr,regs,rd,wr,?_,buf,pushFrame.trans (fr.sub ?_)⟩⟩
  · intro j hj
    change (setArgsAtState 1280 2 128 (allocated 1280 s)).mem.readW ((allocated 1280 s).sp+BitVec.ofNat 64 (96+8*j)) 64=_
    rw [copied j hj]
    have addr : (allocated 1280 s).sp+BitVec.ofNat 64 (1280+96+8*j)=stackArgAddr s j := by
      change base s+BitVec.ofNat 64 (1280+96+8*j)=s.sp+BitVec.ofNat 64 (32+8*(8+j))
      rw [← base_old s,Offset.add_ofNat_add_ofNat]
      congr 2
      omega_using []
    rw [addr]
    apply Frame.readW pushFrame (r:=slotsR s) _ _ (by decide)
    · change (⟨s.sp+BitVec.ofNat 64 96,16⟩ : Region).Contains (s.sp+BitVec.ofNat 64 (32+8*(8+j))) 8
      exact Offset.contains _ (by omega_using []) (by omega_using [hj]) (by decide)
    · simpa only [List.mem_singleton,forall_eq] using (stack_disjoint h (r:=slotsR s) (by simp [argsRegions])).symm
  · intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact ⟨_,List.mem_singleton_self _,Offset.sub_base _ (by decide)⟩

abbrev workR (s : State) : Region := ⟨work s,1152⟩

theorem work_sub (s : State) : Region.Sub (workR s) (stack s) := Offset.sub_base _ (by decide)

theorem work_fit {s : State} (h : CallLayout s) : (work s).toNat+1152≤2^64 := by
  have hf := base_fit h
  change (base s+BitVec.ofNat 64 128).toNat+1152≤2^64
  rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (a:=128) (by decide),Nat.mod_eq_of_lt (by omega_using [hf,s.sp.isLt])]
  omega_using [hf,s.sp.isLt]

theorem Args.workWrite {s e : State} (p : Args s e) : Covers [workR s] e.wr := by
  rw [p.wr]
  exact Covers.one ⟨_,List.mem_cons_self,Offset.contains _ (by decide) (by decide) (by decide)⟩

theorem Args.arguments {s e : State} (p : Args s e) : Arguments e (work s) := by
  refine ⟨p.workWrite,by rw [p.sp];exact p.buf,?_,?_⟩
  · intro i hi
    rw [p.sp,p.wr]
    exact (Covers.right (Covers.refl _)) _ _ (slot_write (s:=s) (by omega_using [hi]))
  · intro i hi
    rw [p.sp]
    change (⟨base s+BitVec.ofNat 64 (96+8*i),8⟩ : Region).Disjoint ⟨base s+BitVec.ofNat 64 128+BitVec.ofNat 64 128,120⟩
    rw [Offset.add_ofNat_add_ofNat]
    exact Offset.disjoint _ (.inl (by omega_using [hi])) (by omega_using [hi]) (by decide)

theorem Args.read {s e : State} (p : Args s e) (h : CallLayout s) {r : Region}
    (hr : r∈[ctxR s,nonceR s,aadR s]) : Covers [r] (e.rd++e.wr) := by
  apply covers_mem
  rw [p.rd,h.rd]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))

theorem Args.enteredFrame {s e t : State} (p : Args s e) (q : Started e (work s) t) :
    Frame [stack s] s.mem t.mem :=
  p.frame.trans (q.entered.frame.sub (by
    intro r hr;obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_singleton_self _,fun addr ha => work_sub s addr ((Offset.sub_base _ (by decide : 128+120≤1152)) addr ha)⟩))

end VG.Proof.AesGcm.PPC64LE.Contiguous
