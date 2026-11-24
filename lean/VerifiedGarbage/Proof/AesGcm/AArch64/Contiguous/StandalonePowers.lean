module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandaloneEntry
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.LeafCT
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
import VerifiedGarbage.Proof.Framework.Offset

/-! The singleton frame can read the caller's third stack argument lazily when
a long record starts its first batch. Shorter records never load that word. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Standalone
open VG VG.AArch64 VG.Spec.Gcm
open VG.Proof.AesGcm.AArch64.DirectGather

abbrev powerSlotR (wn : Nat) (sp : Addr) : Region := ⟨sp+BitVec.ofNat 64 (wn+48),8⟩

structure BatchPowers (wn : Nat) (Ctx W P : Addr) (s : State) : Prop where
  offset : (wn+48)%8=0 ∧ wn+48<32768
  ptr : s.mem.readW (powerSlotR wn s.sp).base 64 = P
  slot : InRegions (s.rd++s.wr) (powerSlotR wn s.sp).base 8
  reads : Covers [⟨P,128⟩] (s.rd++s.wr)
  repr : Spec.Gcm.Powers8Repr s.mem P (ctxH s.mem Ctx)
  slotWork : (powerSlotR wn s.sp).Disjoint (workR wn W)
  tableWork : (⟨P,128⟩ : Region).Disjoint (workR wn W)
  keyWork : (⟨Ctx+240#64,16⟩ : Region).Disjoint (workR wn W)

theorem BatchPowers.after {wn : Nat} {Ctx W P : Addr} {s t : State}
    (p : BatchPowers wn Ctx W P s) (frame : Frame [workR wn W] s.mem t.mem)
    (sp : t.sp=s.sp) (rd : t.rd=s.rd) (wr : t.wr=s.wr) : BatchPowers wn Ctx W P t := by
  have key : blockAt t.mem (Ctx+240#64) = blockAt s.mem (Ctx+240#64) :=
    blockAt_frame frame (by simpa only [List.mem_singleton,forall_eq] using p.keyWork)
  refine ⟨p.offset,?_,by rw [rd,wr,sp]; exact p.slot,by rw [rd,wr]; exact p.reads,?_,
    by rw [sp]; exact p.slotWork,p.tableWork,p.keyWork⟩
  · rw [sp]; exact (frame.readW (r := powerSlotR wn s.sp) (Region.contains_self _ _)
      (by simpa only [List.mem_singleton,forall_eq] using p.slotWork) (by decide : 64/8<2^64)).trans p.ptr
  · change Spec.Gcm.Powers8Repr t.mem P (blockAt t.mem (Ctx+240#64))
    rw [key]; exact Proof.AesGcm.powers8Repr_congr (fun i hi => frame.bytes (R := ⟨P,128⟩)
      (by simpa only [List.mem_singleton,forall_eq] using p.tableWork) (by decide : 128≤2^64) hi) p.repr

theorem originalPowers {wn : Nat} {o s : State} (c : Caller o) (p : Prepared.Powers o)
    (e : FrameIn o s wn) (align : wn%16=0) :
    BatchPowers wn (s.gpr .x0) (genWork o wn) (stackArg o 2) s := by
  have bound := e.bound
  have slot : (powerSlotR wn s.sp).base = stackArgAddr o 2 := by
    rw [e.sp]; exact genArgAddr o wn 2
  have sub : (genStack o wn).Sub (below o.sp 2640) := Offset.sub_below _ (by omega) (by omega)
  have wk : (workR wn (genWork o wn)).Sub (genStack o wn) :=
    Offset.sub_base (genBase o wn) (by change 32+wn≤wn+32;omega)
  have slotAway : (powerSlotR wn s.sp).Disjoint (genStack o wn) := by
    change (⟨(powerSlotR wn s.sp).base,8⟩ : Region).Disjoint _
    rw [slot]; exact Offset.disjoint_below o.sp (n := wn+32) (d := 16) (by omega)
  have pwAway := p.stack.sub_right sub
  have keyAway : (⟨o.gpr .x0+240#64,16⟩ : Region).Disjoint (genStack o wn) :=
    (((c.stack _ (by simp [externalRegions] : Gather.kR .plain o ∈ externalRegions o)).symm.sub_right sub).sub_left
      (Lay.ctxSub (by decide)))
  have small := Region.sub_prefix (base := genBase o wn) (show 32 ≤ wn+32 by omega)
  have F : Frame [genStack o wn] o.mem s.mem := e.frame.sub fun r hr =>
    ⟨_,List.mem_singleton_self _,List.mem_singleton.mp hr ▸ small⟩
  have widen : Covers (o.rd++o.wr) (s.rd++s.wr) := Covers.of_mem fun r hr => by
    rw [e.rd,e.wr]; rcases List.mem_append.mp hr with l|w
    · exact List.mem_append_left _ l
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ w)
  have regs := e.regs .x0 (by decide) (by decide)
  rw [regs]
  refine ⟨by omega,?_,?_,p.read.trans widen,?_,slotAway.sub_right wk,pwAway.sub_right wk,keyAway.sub_right wk⟩
  · exact (F.readW (r := powerSlotR wn s.sp) (Region.contains_self _ _)
      (by simpa only [List.mem_singleton,forall_eq] using slotAway) (by decide : 64/8<2^64)).trans (by rw [slot];rfl)
  · rw [slot]; apply widen; exact c.read _ _ ⟨callerArgs o,by simp,stackArg_contains o 2 (by decide)⟩
  · change Spec.Gcm.Powers8Repr s.mem _ (blockAt s.mem (o.gpr .x0+240#64))
    rw [blockAt_frame F (by simpa only [List.mem_singleton,forall_eq] using keyAway)]
    exact Proof.AesGcm.powers8Repr_congr (fun i hi => F.bytes (R := Prepared.powerR o)
      (by simpa only [List.mem_singleton,forall_eq] using pwAway) (by decide : 128≤2^64) hi) p.repr

end VG.Proof.AesGcm.AArch64.Contiguous.Standalone
