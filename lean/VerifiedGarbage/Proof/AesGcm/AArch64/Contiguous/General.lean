module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.General
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.LeafCT
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.Setup
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesGcm.AArch64.Crypt
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.General

/-! The public contiguous adapter presents a one-element descriptor to the
general body. Its outgoing input and destination pointers remain independent. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.AesGcm.AArch64.Contiguous
abbrev slot (b : Addr) (n : Nat) := b + BitVec.ofNat 64 n

def view (s : State) : State := s.withRegions
  ([Gather.kR .plain s,Gather.nR s,Gather.aR s,Gather.dsR s] ++ Gather.lsR s ++ [Gather.argR s])
  [Gather.dR s,Gather.tgR s]

theorem wordBytes {s t : State} {p q : Addr} (word : s.mem.readW p 64 = t.mem.readW q 64)
    {i : Nat} (hi : i < 8) : s.mem (p + BitVec.ofNat 64 i) = t.mem (q + BitVec.ofNat 64 i) := by
  have eq : s.mem.read p 8 = t.mem.read q 8 := by simpa only [Mem.readW,BitVec.setWidth_eq] using word
  rw [← Mem.extractLsb'_read s.mem p (n := 8) hi,eq,Mem.extractLsb'_read t.mem q hi]


def saveArgs (m : Mem) (sp src dst len tag : Addr) : Mem :=
  ((((m.writeW (slot sp 0) dst).writeW (slot sp 8) len).writeW (slot sp 16) tag).writeW
    (slot sp 24) src).writeW (slot sp 32) len

theorem saveArgs_slots (m : Mem) (sp src dst len tag : Addr) :
    (saveArgs m sp src dst len tag).readW (slot sp 0) 64 = dst ∧
    (saveArgs m sp src dst len tag).readW (slot sp 8) 64 = len ∧
    (saveArgs m sp src dst len tag).readW (slot sp 16) 64 = tag ∧
    (saveArgs m sp src dst len tag).readW (slot sp 24) 64 = src ∧
    (saveArgs m sp src dst len tag).readW (slot sp 32) 64 = len := by
  unfold saveArgs slot
  refine ⟨?_,?_,?_,?_,?_⟩ <;> repeat (first
    | rw [Mem.readW_writeW_self64]
    | rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)])

theorem saveArgs_frame (m : Mem) (sp src dst len tag : Addr) :
    Frame [⟨sp,48⟩] m (saveArgs m sp src dst len tag) := by
  have atSlot {n : Nat} (h : n+8 ≤ 48) : (⟨sp,48⟩ : Region).Contains (slot sp n) 8 :=
    Offset.contains_base _ h (by omega)
  unfold saveArgs
  repeat apply Frame.writeW _ (List.mem_singleton_self _) _ (atSlot (by decide))
  exact Frame.refl _ _

theorem args_ok (s : State)
    (readLen : InRegions (s.rd ++ s.wr) (slot s.sp 48) 8)
    (readTag : InRegions (s.rd ++ s.wr) (slot s.sp 56) 8)
    (writeFrame : (⟨s.sp,48⟩ : Region) ∈ s.wr) :
    WP isa (.block generalArgs) s fun t =>
      t.mem = saveArgs s.mem s.sp (s.gpr .x6) (s.gpr .x7)
        (s.mem.readW (slot s.sp 48) 64) (s.mem.readW (slot s.sp 56) 64) ∧
      t.gpr .x6 = slot s.sp 24 ∧ t.gpr .x7 = 1 ∧
      (∀ r, r ∉ [.x6,.x7,.x9,.x10] → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.dit = s.dit := by
  have store {n : Nat} (h : n+8 ≤ 48) : InRegions s.wr (slot s.sp n) 8 :=
    ⟨_,writeFrame, Offset.contains_base _ h (by omega)⟩
  have w0 := store (n := 0) (by decide)
  have w8 := store (n := 8) (by decide)
  have w16 := store (n := 16) (by decide)
  have w24 := store (n := 24) (by decide)
  have w32 := store (n := 32) (by decide)
  unfold slot at readLen readTag w0 w8 w16 w24 w32
  apply WP.of_runBlock
  refine ⟨_,by arun [generalArgs,readLen,readTag,w0,w8,w16,w24,w32],?_⟩
  simp only [saveArgs,slot,State.write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
    BitVec.add_zero,Size.bits]
  refine ⟨rfl,trivial,rfl,?_,trivial,trivial,trivial,trivial⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp [hr.1,hr.2.1,hr.2.2.1,hr.2.2.2]



abbrev srcR (s : State) : Region := ⟨s.gpr .x6,(stackArg s 0).toNat⟩
abbrev dstR (s : State) : Region := ⟨s.gpr .x7,(stackArg s 0).toNat⟩
abbrev tagR (s : State) : Region := ⟨stackArg s 1,16⟩
abbrev callerArgs (s : State) : Region := ⟨stackArgAddr s 0,24⟩
abbrev externalRegions (s : State) : List Region :=
  [Gather.kR .plain s,Gather.nR s,Gather.aR s,srcR s,dstR s,tagR s]

/-- The same facts are established for both cases of the paired-buffer API. -/
structure Caller (s : State) : Prop where
  read : Covers [Gather.kR .plain s,Gather.nR s,Gather.aR s,srcR s,callerArgs s] (s.rd ++ s.wr)
  write : Covers [dstR s,tagR s] s.wr
  kd : (Gather.kR .plain s).Disjoint (dstR s)
  kt : (Gather.kR .plain s).Disjoint (tagR s)
  nd : (Gather.nR s).Disjoint (dstR s)
  nt : (Gather.nR s).Disjoint (tagR s)
  ad : (Gather.aR s).Disjoint (dstR s)
  atag : (Gather.aR s).Disjoint (tagR s)
  sd : (srcR s).Disjoint (dstR s) ∨ s.gpr .x6 = s.gpr .x7
  st : (srcR s).Disjoint (tagR s)
  dt : (dstR s).Disjoint (tagR s)
  dstArgs : (dstR s).Disjoint (callerArgs s)
  stack : ∀ r ∈ externalRegions s, (below s.sp 2640).Disjoint r
  nowrap : ∀ r ∈ externalRegions s, r.base.toNat + r.len ≤ 2^64
  room : 2640 ≤ s.sp.toNat
  top : s.sp.toNat+24 ≤ 2^64
  rounds : VG.Proof.AesGcm.AArch64.rounds (s.gpr .x1)

namespace Prepared

abbrev powerR (s : State) : Region := ⟨stackArg s 2,128⟩
structure Powers (o : State) : Prop where
  read : Covers [powerR o] (o.rd++o.wr)
  dst : (powerR o).Disjoint (dstR o)
  stack : (powerR o).Disjoint (below o.sp 2640)
  repr : Spec.Gcm.Powers8Repr o.mem (stackArg o 2) (Spec.Gcm.ctxH o.mem (o.gpr .x0))

end Prepared

structure Entered (o t : State) : Prop where
  sp : t.sp = o.sp - 48
  rd : t.rd = o.rd
  wr : t.wr = below o.sp 48 :: o.wr
  regs : ∀ r, r ∉ [.x6,.x7,.x9,.x10] → t.gpr r = o.gpr r
  dit : t.dit = o.dit
  desc : t.gpr .x6 = slot t.sp 24
  count : t.gpr .x7 = 1
  dst : stackArg t 0 = o.gpr .x7
  len : stackArg t 1 = stackArg o 0
  tag : stackArg t 2 = stackArg o 1
  sb : t.mem.readW (slot t.sp 24) 64 = o.gpr .x6
  sl : t.mem.readW (slot t.sp 32) 64 = stackArg o 0
  frame : Frame [below o.sp 48] o.mem t.mem

theorem enter (o : State) (c : Caller o) :
    WP isa (.block generalArgs) (allocated 48 o) (Entered o) := by
  let u := allocated 48 o
  have start : slot u.sp 48 = o.sp := BitVec.sub_add_cancel _ _
  have next : slot u.sp 56 = slot o.sp 8 := by
    change o.sp - 48 + (48 + 8) = o.sp + 8
    rw [← BitVec.add_assoc,BitVec.sub_add_cancel]
  have read {n : Nat} (h : n+8 ≤ 24) : InRegions (u.rd ++ u.wr) (slot o.sp n) 8 := by
    have v : InRegions (o.rd ++ o.wr) (slot o.sp n) 8 := c.read _ _
      ⟨callerArgs o,by simp,by
        simpa only [callerArgs,stackArgAddr,Nat.mul_zero,BitVec.add_zero] using
          Offset.contains_base o.sp h (by omega)⟩
    obtain ⟨r,hr,hc⟩ := v
    exact ⟨r,by change r ∈ o.rd ++ _ :: o.wr; simp only [List.mem_append,List.mem_cons] at hr ⊢; exact hr.imp_right Or.inr,hc⟩
  have len : InRegions (u.rd ++ u.wr) (slot u.sp 48) 8 := by
    rw [start]; simpa only [slot,BitVec.add_zero] using read (n := 0) (by decide)
  have tag : InRegions (u.rd ++ u.wr) (slot u.sp 56) 8 := next ▸ read (n := 8) (by decide)
  refine (args_ok u len tag (List.mem_cons_self ..)).mono ?_
  intro t ⟨hm,desc,cnt,regs,sp,rd,wr,dit⟩
  have a : u.mem.readW (slot u.sp 48) 64 = stackArg o 0 := by
    rw [start]; simp only [stackArg,stackArgAddr,Nat.mul_zero,BitVec.add_zero]; rfl
  have b : u.mem.readW (slot u.sp 56) 64 = stackArg o 1 := by rw [next]; rfl
  rw [a,b] at hm
  obtain ⟨d,l,tg,src,sl⟩ := saveArgs_slots u.mem u.sp (u.gpr .x6) (u.gpr .x7) (stackArg o 0) (stackArg o 1)
  refine ⟨sp,rd,wr,regs,dit,desc.trans (congrArg (fun z => slot z 24) sp.symm),cnt,?_,?_,?_,?_,?_,?_⟩
  · change t.mem.readW (slot t.sp 0) 64 = _; rw [hm,sp]; exact d
  · change t.mem.readW (slot t.sp 8) 64 = _; rw [hm,sp]; exact l
  · change t.mem.readW (slot t.sp 16) 64 = _; rw [hm,sp]; exact tg
  · rw [hm,sp]; exact src
  · rw [hm,sp]; exact sl
  · rw [hm]; exact saveArgs_frame _ _ _ _ _ _ 



theorem Entered.listed {o t : State} (h : Entered o t) : Gather.lsR t = [srcR o] := by
  have next : slot t.sp 24 + 8#64 = slot t.sp 32 := by simp only [slot,BitVec.add_assoc]; rfl
  simp [Gather.lsR,Gather.Src,Gather.Cnt,h.desc,h.count,Sig.listed,Elem.size,next,h.sb,h.sl,srcR]

theorem Entered.plaintext {o t : State} (h : Entered o t) :
    Gather.pt t (Gather.Cnt t) = Spec.Aes.bytesAt t.mem (o.gpr .x6) (stackArg o 0).toNat := by
  simp only [Gather.pt,Spec.Gcm.gathered,h.listed,List.flatMap_cons,List.flatMap_nil,List.append_nil,srcR]

theorem Entered.length {o t : State} (h : Entered o t) : Gather.gl t (Gather.Cnt t) = Gather.L t := by
  simp only [Gather.gl,Spec.Gcm.gatheredLen,h.listed,Gather.L,h.len,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Nat.add_zero,srcR]

structure Regions (o t : State) : Prop where
  k : Gather.kR .plain t = Gather.kR .plain o
  n : Gather.nR t = Gather.nR o
  a : Gather.aR t = Gather.aR o
  d : Gather.dR t = dstR o
  tg : Gather.tgR t = tagR o
  desc : Gather.dsR t = ⟨slot t.sp 24,16⟩
  args : Gather.argR t = ⟨t.sp,24⟩
  slices : Gather.lsR t = [srcR o]

theorem Entered.regions {o t : State} (h : Entered o t) : Regions o t := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,h.listed⟩
  · exact congrArg (fun a => (⟨a,256⟩ : Region)) (h.regs .x0 (by decide))
  · simp only [Gather.nR,Gather.Nn,Gather.NL,h.regs .x2 (by decide),h.regs .x3 (by decide)]
  · simp only [Gather.aR,Gather.Ad,Gather.AL,h.regs .x4 (by decide),h.regs .x5 (by decide)]
  · simp only [Gather.dR,Gather.Dst,Gather.L,h.dst,h.len,dstR]
  · simp only [Gather.tgR,Gather.Tg,h.tag,tagR]
  · simp [Gather.dsR,Gather.Src,Gather.Cnt,h.count,h.desc]
  · simp [Gather.argR,stackArgAddr]

theorem Entered.pre {o t : State} (h : Entered o t) (c : Caller o) :
    Gather.gatherPreFor .plain (view t)
      (Gather.sharedSource (view t)) := by
  let f : Region := ⟨t.sp,48⟩
  have reg := h.regions
  have localSub : f.Sub (below o.sp 2640) := by
    change (⟨t.sp,48⟩ : Region).Sub _; rw [h.sp]; exact Offset.sub_below _ (by decide) (by decide)
  have coreSub : (Gather.stkR t).Sub (below o.sp 2640) := by
    change (⟨t.sp-2592,2592⟩ : Region).Sub _; rw [h.sp,BitVec.sub_sub]
    exact Offset.sub_below _ (by decide) (by decide)
  have descSub : (Gather.dsR t).Sub f := by rw [reg.desc]; exact Offset.sub_base _ (by decide)
  have argsSub : (Gather.argR t).Sub f := by
    rw [reg.args]; exact fun _ hc => Nat.le_trans hc (by decide : 24 ≤ 48)
  have coreLocal : (Gather.stkR t).Disjoint f :=
    (Offset.base_disjoint_below t.sp (by decide : 2592+48 ≤ 2^64)).symm
  have core (r : Region) (hr : r ∈ externalRegions o) := (c.stack r hr).sub_left coreSub
  have localA (r : Region) (hr : r ∈ externalRegions o) := (c.stack r hr).sub_left localSub
  have pos : t.sp.toNat = o.sp.toNat - 48 := by
    rw [h.sp,show (48 : Addr) = BitVec.ofNat 64 48 from rfl,Offset.toNat_sub_ofNat]
    have := c.room; have := o.sp.isLt; omega
  have dsn : (Gather.Src t).toNat + Gather.Cnt t * 16 ≤ 2^64 := by
    simp only [Gather.Src,Gather.Cnt,h.desc,h.count,slot,BitVec.toNat_add]
    have := c.room; have := c.top
    change (t.sp.toNat+24) % (2^64) + 16 ≤ 2^64
    omega
  refine ⟨rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,dsn,?_,?_,?_,?_,?_,?_,h.length⟩
  · change (Gather.kR .plain t).Disjoint (Gather.dR t); rw [reg.k,reg.d]; exact c.kd
  · change (Gather.kR .plain t).Disjoint (Gather.tgR t); rw [reg.k,reg.tg]; exact c.kt
  · change (Gather.nR t).Disjoint (Gather.dR t); rw [reg.n,reg.d]; exact c.nd
  · change (Gather.nR t).Disjoint (Gather.tgR t); rw [reg.n,reg.tg]; exact c.nt
  · change (Gather.aR t).Disjoint (Gather.dR t); rw [reg.a,reg.d]; exact c.ad
  · change (Gather.aR t).Disjoint (Gather.tgR t); rw [reg.a,reg.tg]; exact c.atag
  · change (Gather.dsR t).Disjoint (Gather.dR t); rw [reg.d]; exact (localA _ (by simp [externalRegions])).sub_left descSub
  · change (Gather.dsR t).Disjoint (Gather.tgR t); rw [reg.tg]; exact (localA _ (by simp [externalRegions])).sub_left descSub
  · change ∀ r ∈ Gather.lsR t, Gather.sharedSource t r ∧ r.Disjoint (Gather.tgR t)
    rw [reg.slices,reg.tg]; simp only [List.mem_singleton,forall_eq]
    refine ⟨?_,c.st⟩
    rcases c.sd with hd|eq
    · exact Or.inl (reg.d ▸ hd)
    · exact Or.inr ⟨by rw [Gather.Cnt,h.count]; rfl,eq.trans h.dst.symm⟩
  · change (Gather.dR t).Disjoint (Gather.tgR t); rw [reg.d,reg.tg]; exact c.dt
  · change (Gather.dR t).Disjoint (Gather.argR t); rw [reg.d]; exact ((localA _ (by simp [externalRegions])).sub_left argsSub).symm
  · change (Gather.tgR t).Disjoint (Gather.argR t); rw [reg.tg]; exact ((localA _ (by simp [externalRegions])).sub_left argsSub).symm
  · change (Gather.stkR t).Disjoint (Gather.kR .plain t); rw [reg.k]; exact core _ (by simp [externalRegions])
  · change (Gather.stkR t).Disjoint (Gather.nR t); rw [reg.n]; exact core _ (by simp [externalRegions])
  · change (Gather.stkR t).Disjoint (Gather.aR t); rw [reg.a]; exact core _ (by simp [externalRegions])
  · exact coreLocal.sub_right descSub
  · change ∀ r ∈ Gather.lsR t, (Gather.stkR t).Disjoint r
    rw [reg.slices]; simpa only [List.mem_singleton,forall_eq] using core _ (by simp [externalRegions])
  · exact coreLocal.sub_right argsSub
  · change (Gather.stkR t).Disjoint (Gather.dR t); rw [reg.d]; exact core _ (by simp [externalRegions])
  · change (Gather.stkR t).Disjoint (Gather.tgR t); rw [reg.tg]; exact core _ (by simp [externalRegions])
  · change (Gather.kR .plain t).base.toNat + (Gather.kR .plain t).len ≤ 2^64
    rw [reg.k]; exact c.nowrap _ (by simp [externalRegions])
  · change (Gather.nR t).base.toNat + (Gather.nR t).len ≤ 2^64
    rw [reg.n]; exact c.nowrap _ (by simp [externalRegions])
  · change (Gather.aR t).base.toNat + (Gather.aR t).len ≤ 2^64
    rw [reg.a]; exact c.nowrap _ (by simp [externalRegions])
  · change ∀ r ∈ Gather.lsR t, r.base.toNat + r.len ≤ 2^64
    rw [reg.slices]; simpa only [List.mem_singleton,forall_eq] using c.nowrap (srcR o) (by simp [externalRegions])
  · change (Gather.dR t).base.toNat + (Gather.dR t).len ≤ 2^64
    rw [reg.d]; exact c.nowrap _ (by simp [externalRegions])
  · change (Gather.tgR t).base.toNat + (Gather.tgR t).len ≤ 2^64
    rw [reg.tg]; exact c.nowrap _ (by simp [externalRegions])
  · change 2592 ≤ t.sp.toNat; have := c.room; omega
  · change t.sp.toNat+24 ≤ 2^64; have := c.top; omega
  · change VG.Proof.AesGcm.AArch64.rounds (t.gpr .x1)
    rw [h.regs .x1 (by decide)]; exact c.rounds



theorem Entered.covers {o t : State} (h : Entered o t) (c : Caller o) :
    Covers ((view t).rd ++ (view t).wr) (t.rd ++ t.wr) ∧
    Covers (view t).wr t.wr := by
  have reg := h.regions
  have wr : Covers o.wr t.wr := Covers.of_mem (fun r hr => by rw [h.wr]; exact List.mem_cons_of_mem _ hr)
  have rd : Covers (o.rd ++ o.wr) (t.rd ++ t.wr) := Covers.append (h.rd ▸ Covers.refl _) wr
  have out : Covers [Gather.dR t,Gather.tgR t] t.wr := by rw [reg.d,reg.tg]; exact c.write.trans wr
  refine ⟨Covers.append_left ?_ out.right,out⟩
  change Covers (([_,_,_,_] ++ Gather.lsR t) ++ [_]) _
  rw [reg.k,reg.n,reg.a,reg.desc,reg.slices,reg.args]
  have frame {n k : Nat} (hn : n+k ≤ 48) : Covers [⟨slot t.sp n,k⟩] (t.rd ++ t.wr) := by
    apply Covers.one
    refine ⟨below o.sp 48,List.mem_append_right _ (by rw [h.wr]; simp),?_⟩
    change (⟨o.sp-48,48⟩ : Region).Contains (slot t.sp n) k
    rw [←h.sp]; exact Offset.contains_base _ hn (by omega)
  have external {r : Region} (hr : r ∈ [Gather.kR .plain o,Gather.nR o,Gather.aR o,srcR o,callerArgs o]) :
      Covers [r] (t.rd ++ t.wr) := (Covers.of_mem (by simpa only [List.mem_singleton,forall_eq] using hr)).trans (c.read.trans rd)
  apply Covers.append_left _ (by simpa only [slot,BitVec.add_zero] using frame (n := 0) (k := 24) (by decide))
  apply Covers.append_left _ (external (by simp))
  exact (external (by simp)).cons ((external (by simp)).cons ((external (by simp)).cons (frame (by decide))))

/-- Authenticate precisely the bytes at the source in the caller's original memory. -/
def result (s t : State) : Prop :=
  Spec.Gcm.encryptWith (Spec.Gcm.ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat)
      (Spec.Gcm.ctxH s.mem (s.gpr .x0)) 16
      (Spec.Aes.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
      (Spec.Aes.bytesAt s.mem (s.gpr .x6) (stackArg s 0).toNat)
      (Spec.Aes.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
    (Spec.Aes.bytesAt t.mem (s.gpr .x7) (stackArg s 0).toNat,Spec.Aes.bytesAt t.mem (stackArg s 1) 16)

theorem Entered.post {o t u : State} (h : Entered o t) (c : Caller o)
    (post : Gather.gatherPost (view t) u) : result o u := by
  have sub : (below o.sp 48).Sub (below o.sp 2640) := Offset.sub_below _ (by decide) (by decide)
  have apart {r : Region} (mem : r ∈ externalRegions o) : ∀ w ∈ [below o.sp 48], r.Disjoint w := by
    simpa only [List.mem_singleton,forall_eq] using ((c.stack _ mem).sub_left sub).symm
  have cipher : Spec.Gcm.ctxCiph t.mem (o.gpr .x0) (o.gpr .x1).toNat =
      Spec.Gcm.ctxCiph o.mem (o.gpr .x0) (o.gpr .x1).toNat :=
    ciph_frame h.frame (apart (r := Gather.kR .plain o) (by simp [externalRegions])) c.rounds
  have hash : Spec.Gcm.ctxH t.mem (o.gpr .x0) = Spec.Gcm.ctxH o.mem (o.gpr .x0) :=
    blockAt_frame h.frame (fun w hw => (apart (r := Gather.kR .plain o) (by simp [externalRegions]) w hw).sub_left
      (Lay.ctxSub (by decide)))
  have nonce := bytesAt_frame h.frame (apart (r := Gather.nR o) (by simp [externalRegions])) (Nat.le_of_lt (o.gpr .x3).isLt)
  have aad := bytesAt_frame h.frame (apart (r := Gather.aR o) (by simp [externalRegions])) (Nat.le_of_lt (o.gpr .x5).isLt)
  have data := bytesAt_frame h.frame (apart (r := srcR o) (by simp [externalRegions])) (Nat.le_of_lt (stackArg o 0).isLt)
  change Gather.gatherPost t u at post
  unfold Gather.gatherPost at post
  rw [h.plaintext] at post
  simp only [Gather.K,Gather.Nn,Gather.NL,Gather.Ad,Gather.AL,Gather.L,Gather.Dst,Gather.Tg,
    h.dst,h.len,h.tag,h.regs .x0 (by decide),h.regs .x1 (by decide),h.regs .x2 (by decide),
    h.regs .x3 (by decide),h.regs .x4 (by decide),h.regs .x5 (by decide),cipher,hash,nonce,aad,data] at post
  exact post

theorem result_frame {o u v : State} (c : Caller o) {k : Nat} (le : k ≤ 2640)
    (p : result o u) (f : Frame [below o.sp k] u.mem v.mem) : result o v := by
  have sub : (below o.sp k).Sub (below o.sp 2640) := Offset.sub_below _ le (by omega)
  have apart {r : Region} (mem : r ∈ externalRegions o) : ∀ w ∈ [below o.sp k], r.Disjoint w := by
    simpa only [List.mem_singleton,forall_eq] using ((c.stack _ mem).sub_left sub).symm
  unfold result at *
  rw [bytesAt_frame f (apart (r := dstR o) (by simp [externalRegions])) (Nat.le_of_lt (stackArg o 0).isLt),
    bytesAt_frame f (apart (r := tagR o) (by simp [externalRegions])) (by decide)]
  exact p



theorem Entered.public {a b t u : State} (ha : Entered a t) (hb : Entered b u)
    (pub : onePub 3 a b) (dit : a.dit = b.dit) :
    Gather.gatherPub (view t) (view u) := by
  obtain ⟨g0,g1,g2,g3,g4,g5,g6,g7,sp,stk⟩ := pub
  have stacks : t.sp = u.sp := by rw [ha.sp,hb.sp,sp]
  have g (r : Reg) (hr : r ∉ [.x6,.x7,.x9,.x10]) (eq : a.gpr r = b.gpr r) :
      t.gpr r = u.gpr r := (ha.regs _ hr).trans (eq.trans (hb.regs _ hr).symm)
  change Gather.gatherPub t u
  refine ⟨g .x0 (by decide) g0,g .x1 (by decide) g1,g .x2 (by decide) g2,g .x3 (by decide) g3,
    g .x4 (by decide) g4,g .x5 (by decide) g5,by rw [ha.desc,hb.desc,stacks],ha.count.trans hb.count.symm,
    stacks,ha.dit.trans (dit.trans hb.dit.symm),ha.dst.trans (g7.trans hb.dst.symm),
    ha.len.trans ((stk 0 (by decide)).trans hb.len.symm),ha.tag.trans ((stk 1 (by decide)).trans hb.tag.symm),?_⟩
  intro i hi
  have hi' : i < 16 := by rw [Gather.Cnt,ha.count] at hi; exact hi
  rw [Gather.Src,ha.desc]
  by_cases lo : i < 8
  · have bytes := wordBytes (s := t) (t := u) (ha.sb.trans (g6.trans hb.sb.symm)) lo
    simpa only [stacks] using bytes
  · have bytes := wordBytes (s := t) (t := u)
      (ha.sl.trans ((stk 0 (by decide)).trans hb.sl.symm)) (i := i-8) (by omega)
    have addr (p : Addr) : slot p 32 + BitVec.ofNat 64 (i-8) = slot p 24 + BitVec.ofNat 64 i := by
      unfold slot; rw [Offset.add_add,Offset.add_add]; congr 2; omega
    simpa only [addr,stacks] using bytes

end VG.Proof.AesGcm.AArch64.Contiguous
