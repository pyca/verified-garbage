module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.BodyCT
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

/-! # RISC-V contiguous seal stack layout and copied arguments -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.Impl.StackScratch.RISCV64
open VG.Spec.Aes (bytesAt)

abbrev allocated (s : State) := allocd 2608 s
abbrev inner (s : State) := setArgsAtState 2608 3 40 (allocated s)
abbrev callArgs (s : State) : Args :=
  ⟨s.gpr .a0,(s.gpr .a1).toNat,s.gpr .a2,s.gpr .a3,s.gpr .a4,s.gpr .a5,s.gpr .a6,s.gpr .a7,
    stackArg s 0,stackArg s 1,stackArg s 2,(allocated s).sp+40,(allocated s).sp⟩
abbrev Args.regions (p : Args) : List Region := [⟨p.ctx,256⟩,⟨p.iv,p.ivLen.toNat⟩,⟨p.aad,p.aadLen.toNat⟩,
  ⟨p.src,p.len.toNat⟩,⟨p.keys,960⟩,⟨p.dst,p.len.toNat⟩,⟨p.tag,16⟩]

/-- Public argument effects needed by the native entry. The callee may only modify the
two output regions and its private frame. Read permissions allow either buffer layout. -/
structure Caller (s : State) : Prop where
  align : s.sp.toNat % 16=0
  space : 4656≤s.sp.toNat
  slots : ∀ i<3,InRegions (s.rd++s.wr) (stackArgAddr s i) 8
  read : ∀ r∈(callArgs s).regions,Covers [r] (s.rd++s.wr)
  fit : ∀ r∈(callArgs s).regions,r.base.toNat+r.len≤2^64
  apart : ∀ r∈(callArgs s).regions,r.Disjoint (below s.sp 4656)
  dst : Covers [⟨(callArgs s).dst,(callArgs s).len.toNat⟩] s.wr
  tag : Covers [⟨(callArgs s).tag,16⟩] s.wr
  tagData : (⟨(callArgs s).tag,16⟩ : Region).Disjoint ⟨(callArgs s).dst,(callArgs s).len.toNat⟩
  ctxData : (⟨(callArgs s).ctx,256⟩ : Region).Disjoint ⟨(callArgs s).dst,(callArgs s).len.toNat⟩
  keyData : (⟨(callArgs s).keys,960⟩ : Region).Disjoint ⟨(callArgs s).dst,(callArgs s).len.toNat⟩
  buffers : Alias true (callArgs s).src (callArgs s).dst (callArgs s).len.toNat
  ctxAlign : (callArgs s).ctx.toNat%8=0
  keyAlign : (callArgs s).keys.toNat%8=0
  rounds : (callArgs s).rounds=10 ∨ (callArgs s).rounds=12 ∨ (callArgs s).rounds=14
  keys : Proof.Aes.RISCV64.KeysAt s.mem (callArgs s).keys (callArgs s).rounds (bytesAt s.mem (callArgs s).ctx (16*((callArgs s).rounds+1)))

abbrev frameR (s : State) : Region := ⟨(allocated s).sp,2608⟩

theorem frame_sub (s : State) : (frameR s).Sub (below s.sp 4656) :=
  Offset.sub_below s.sp (by decide) (by decide)

theorem below_sub (s : State) : (below (allocated s).sp 2048).Sub (below s.sp 4656) := by
  change Region.Sub ⟨s.sp-BitVec.ofNat 64 2608-BitVec.ofNat 64 2048,2048⟩ _
  rw [BitVec.sub_sub]
  exact Region.sub_prefix (by decide)

theorem inner_align {s : State} (h : Caller s) : (allocated s).sp.toNat%16=0 := by
  change (s.sp-BitVec.ofNat 64 2608).toNat %16=0
  rw [toNat_sub_ofNat' (by have := h.space;omega)]
  have := h.align;omega

theorem extended_read {s : State} (h : Covers rs (s.rd++s.wr)) : Covers rs ((allocated s).rd++(allocated s).wr) := by
  intro a n ha
  obtain ⟨r,hr,hit⟩ := h a n ha
  exact ⟨r,(List.mem_append.mp hr).elim (List.mem_append_left _) (fun k => List.mem_append_right _ (List.mem_cons_of_mem _ k)),hit⟩

structure Copied (s t : State) : Prop where
  rd : t.rd=s.rd
  wr : t.wr=(allocated s).wr
  sp : t.sp=(allocated s).sp
  regs : ∀ q, q≠.t0 → q≠.t1 → t.gpr q=s.gpr q
  frame : Frame [⟨(allocated s).sp,32⟩] s.mem t.mem
  args : ∀ i<3,stackArg t i=stackArg s i
  work : stackArg t 3=(callArgs s).work

theorem copied_run {s : State} (h : Caller s) :
    execBlock isa (setArgsAt 2608 3 40) (allocated s)=some (inner s,setArgsTrace 2608 (allocated s).sp 3) ∧ Copied s (inner s) := by
  have loc (i : Nat) : (allocated s).sp+BitVec.ofNat 64 (2608+8*i)=stackArgAddr s i := by
    change s.sp-BitVec.ofNat 64 2608+BitVec.ofNat 64 (2608+8*i)=_
    rw [←Offset.add_add,BitVec.sub_add_cancel];rfl
  have hr (i : Nat) (hi : i<3) : InRegions ((allocated s).rd++(allocated s).wr) ((allocated s).sp+BitVec.ofNat 64 (2608+8*i)) 8 := by
    rw [loc]
    obtain ⟨r,mem,hit⟩ := h.slots i hi
    exact ⟨r,(List.mem_append.mp mem).elim (List.mem_append_left _) (fun k => List.mem_append_right _ (List.mem_cons_of_mem _ k)),hit⟩
  have hw (i : Nat) (hi : i≤3) : InRegions (allocated s).wr ((allocated s).sp+BitVec.ofNat 64 (8*i)) 8 :=
    ⟨_,List.mem_cons_self ..,Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨run,rd,wr,sp,rg,fr,ar,w⟩ := setArgsAt_run (m := 3) (bytes := 2608) (workOff := 40) (u := allocated s)
    (by decide) (by have := inner_align h;omega) (by decide) (by decide) (by decide) (by decide) hr hw
  constructor
  · exact run
  constructor
  · exact rd
  · exact wr
  · exact sp
  · intro q h0 h1
    unfold inner
    exact rg q h0 h1
  · exact fr
  · intro i hi
    change (inner s).mem.readW ((inner s).sp+BitVec.ofNat 64 (8*i)) 64=_
    change (inner s).sp=(allocated s).sp at sp
    rw [sp];exact (ar i hi).trans (congrArg (fun x => s.mem.readW x 64) (loc i))
  · change (inner s).mem.readW ((inner s).sp+BitVec.ofNat 64 24) 64=_
    change (inner s).sp=(allocated s).sp at sp
    rw [sp];exact w

end VG.Proof.AesGcm.RISCV64.Contiguous
