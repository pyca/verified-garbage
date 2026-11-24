module

-- separate module: Isolate argument decoding from execution of the 4,656-byte allocated frame.

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.Frame
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Satisfying the contiguous RISC-V body from public call arguments -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64
open VG.Spec.Aes (bytesAt)

theorem Copied.satisfies {s t : State} (v : Copied s t) (h : Caller s) : ArgsAt (callArgs s) t := by
  let p := callArgs s
  have ge : 2608≤s.sp.toNat := by have := h.space;omega
  have num : p.sp.toNat=s.sp.toNat-2608 := toNat_sub_ofNat' ge
  have al : p.sp.toNat%16=0 := inner_align h
  have wal : p.work.toNat%8=0 := Spill.al8 (by omega : p.sp.toNat%8=0) (by decide : 40%8=0)
  have sub : (⟨p.work,2560⟩ : Region).Sub (frameR s) := Offset.sub_base p.sp (by decide)
  have wad (r : Region) (hr : r∈p.regions) := ((h.apart r hr).sub_right (frame_sub s)).sub_right sub
  have bad (r : Region) (hr : r∈p.regions) := (h.apart r hr).sub_right (below_sub s)
  have read (r : Region) (hr : r∈p.regions) : Covers [r] (t.rd++t.wr) := by rw [v.rd,v.wr];exact extended_read (h.read r hr)
  have region (r : Region) (hr : r∈p.regions) (lt : r.len<2^64) : DataOk p.st p.work t r.base r.len :=
    ⟨read _ hr,lt,h.fit _ hr,(wad _ hr).sub_right (Offset.sub_base _ (by decide)),wad _ hr,v.sp ▸ bad _ hr⟩
  have wr {r : Region} (q : Covers [r] s.wr) : Covers [r] t.wr := by
    intro a n hi;obtain ⟨z,mem,hit⟩ := q a n hi
    exact ⟨z,v.wr ▸ List.mem_cons_of_mem _ mem,hit⟩
  have work : Covers [⟨p.work,2560⟩] t.wr := by
    rw [v.wr];apply Covers.of_sub;intro r hr;obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_self ..,40,rfl,by change 40+2560≤2608;decide⟩
  have lay : Lay p.ctx p.st p.work := oneLay (h.fit ⟨p.ctx,256⟩ (by simp [Args.regions,p])) (by
    change (p.sp+BitVec.ofNat 64 40).toNat+2560≤2^64
    rw [Offset.toNat_add_ofNat,Nat.mod_eq_of_lt (by have := s.sp.isLt;omega : p.sp.toNat+40<2^64)]
    have := s.sp.isLt;omega) (wad ⟨p.ctx,256⟩ (by simp [Args.regions])) h.ctxAlign wal
  have wb : (⟨p.work,2560⟩ : Region).Disjoint (below p.sp 2048) := Offset.disjoint_below p.sp (by decide)
  have stk : StkOk p.ctx p.st p.work p.sp := ⟨bad ⟨p.ctx,256⟩ (by simp [Args.regions]),wb.sub_left (Offset.sub_base _ (by decide)),wb,al,
    by have := h.space;omega⟩
  have sr : VG.Proof.AesGcm.RISCV64.args t 4=⟨p.sp+BitVec.ofNat 64 0,32⟩ := by unfold VG.Proof.AesGcm.RISCV64.args stackArgAddr;rw [v.sp]
  have argsW : (VG.Proof.AesGcm.RISCV64.args t 4).Disjoint ⟨p.work,2560⟩ := by rw [sr];exact Offset.disjoint p.sp (.inl (by decide)) (by decide) (by decide)
  have slots (i : Nat) (hi : i<4) : InRegions (t.rd++t.wr) (t.sp+BitVec.ofNat 64 (8*i)) 8 := by
    rw [v.wr,v.sp];apply in_left
    exact ⟨_,List.mem_cons_self ..,Offset.contains_base _ (by omega) (by omega)⟩
  have shape : EntryArgs t p.work p.tag := ⟨work,wal,v.sp ▸ al,slots,fun i hi => by
    rw [v.sp]
    change Region.Disjoint ⟨p.sp+BitVec.ofNat 64 (8*i),8⟩ ⟨p.sp+BitVec.ofNat 64 40+BitVec.ofNat 64 128,120⟩
    rw [Offset.add_add];exact Offset.disjoint p.sp (.inl (by omega)) (by omega) (by decide),v.work,v.args 1 (by decide)⟩
  have tagged : (⟨p.tag,16⟩ : Region)∈p.regions := by simp [Args.regions]
  have d : (⟨p.dst,p.len.toNat⟩ : Region)∈p.regions := by simp [Args.regions]
  have k : (⟨p.keys,960⟩ : Region)∈p.regions := by simp [Args.regions]
  have c : (⟨p.ctx,256⟩ : Region)∈p.regions := by simp [Args.regions]
  have kept (r : Region) (hr : r∈p.regions) : ∀ z∈[⟨(allocated s).sp,32⟩],r.Disjoint z := by
    intro z hz;obtain rfl := List.mem_singleton.mp hz
    exact ((h.apart r hr).sub_right (frame_sub s)).sub_right (Region.sub_prefix (by decide))
  refine ⟨shape,v.sp,v.regs _ (by decide) (by decide),?_,v.regs _ (by decide) (by decide),v.regs _ (by decide) (by decide),
    v.regs _ (by decide) (by decide),v.regs _ (by decide) (by decide),v.regs _ (by decide) (by decide),v.regs _ (by decide) (by decide),
    v.args 0 (by decide),v.args 2 (by decide),lay,stk,read _ c,?_,?_,?_,⟨region _ d p.len.isLt,wr h.dst,h.ctxData⟩,
    h.buffers,wr h.tag,wad _ tagged,h.tagData,argsW,?_,?_,h.rounds,⟨read _ k,h.keyAlign,(wad _ k).sub_right (Offset.sub_base _ (by decide)),
      wad _ k,bad _ k,h.keyData,keysAt_ctx_frame h.rounds v.frame (kept _ k) (kept _ c) h.keys⟩⟩
  · simpa using v.regs .a1 (by decide) (by decide)
  · exact region ⟨p.iv,p.ivLen.toNat⟩ (by simp [Args.regions]) p.ivLen.isLt
  · exact region ⟨p.aad,p.aadLen.toNat⟩ (by simp [Args.regions]) p.aadLen.isLt
  · exact region ⟨p.src,p.len.toNat⟩ (by simp [Args.regions]) p.len.isLt
  · rw [sr]; exact (((h.apart _ d).sub_right (frame_sub s)).sub_right (Offset.sub_base _ (by decide))).symm
  · rw [sr]; exact Offset.disjoint_below _ (by decide)

/-- Copying the public arguments into the new frame preserves the prepared table
and makes its pointer available at stack slot two throughout the operation. -/
theorem Copied.hashScope {s t : State} (v : Copied s t) (run : PreparedInvocationLaw) (h : Caller s) (extra : PreparedCaller s) :
    HashScope ((callArgs s).ctx+BitVec.ofNat 64 240) (callArgs s).keys
      (sealWrites (callArgs s).st (callArgs s).work (callArgs s).dst (callArgs s).sp (callArgs s).len.toNat) t := by
  let p := callArgs s
  let T := p.keys+BitVec.ofNat 64 960
  let a := v.satisfies h
  have ptr : t.mem.readW (t.sp+BitVec.ofNat 64 16) 64=p.keys := v.args 2 (by decide)
  have tableWork := (extra.apart.sub_right (frame_sub s)).sub_right (Offset.sub_base p.sp (d:=40) (n:=2560) (by decide))
  have tableBelow := extra.apart.sub_right (below_sub s)
  have rd : Covers [⟨T,288⟩] (t.rd++t.wr) := by rw [v.rd,v.wr];exact extended_read extra.table.read
  have kept : ∀ q∈[⟨(allocated s).sp,32⟩],(⟨T,288⟩ : Region).Disjoint q := by
    intro q hq
    obtain rfl := List.mem_singleton.mp hq
    exact (extra.apart.sub_right (frame_sub s)).sub_right (Region.sub_prefix (by decide))
  have hf := extra.table.transfer v.frame kept (v.sp ▸ tableBelow.symm) rd
  have hc : Spec.Gcm.ctxH t.mem p.ctx=Spec.Gcm.ctxH s.mem p.ctx := ctxH_keep v.frame fun q hq => by
    obtain rfl := List.mem_singleton.mp hq
    exact ((h.apart ⟨p.ctx,256⟩ (by simp [Args.regions,p])).sub_right (frame_sub s)).sub_right (Region.sub_prefix (by decide))
  have input : HashInput t (Spec.Gcm.ctxH t.mem p.ctx) := by
    refine ⟨Spill.al8 (by omega_using [a.shape.spAlign]) (by decide),a.shape.slot 2 (by decide),?_⟩
    rw [ptr,hc]
    exact hf
  rw [← ptr]
  apply preparedHashScope run input
  · have sl : (⟨t.sp+BitVec.ofNat 64 16,8⟩ : Region).Sub (VG.Proof.AesGcm.RISCV64.args t 4) := Offset.sub t.sp (d:=16) (n:=8) (e:=0) (k:=32) (by decide) (by decide)
    intro r hr
    simp only [sealWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact a.stackData.sub_left sl
    · exact a.stackWork.sub_left sl
    · exact (a.stackWork.sub_left sl).sub_right (Offset.sub_base _ (by decide))
    · exact a.stackBelow.sub_left sl
  · rw [ptr]
    intro r hr
    simp only [sealWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact extra.dst
    · exact tableWork
    · exact tableWork.sub_right (Offset.sub_base _ (by decide))
    · exact tableBelow
  · intro r hr
    simp only [sealWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact h.ctxData.sub_left (Lay.ctxSub (by decide))
    · exact a.lay.cw'.sub_left (Lay.ctxSub (by decide))
    · exact a.lay.cs.sub_left (Lay.ctxSub (by decide))
    · exact a.stk.c.sub_left (Lay.ctxSub (by decide))

theorem Copied.hashAction {s t : State} (v : Copied s t) (run : PreparedInvocationLaw) (h : Caller s) (extra : PreparedCaller s) :
    sealAction VG.Impl.Gcm.RISCV64.Prepared.preparedInvocation (callArgs s) t :=
  (v.hashScope run h extra).action

end VG.Proof.AesGcm.RISCV64.Contiguous
