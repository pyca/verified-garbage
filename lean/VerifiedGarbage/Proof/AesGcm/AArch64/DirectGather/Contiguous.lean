module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
public import VerifiedGarbage.Spec.Gcm.Powers8
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather.Contiguous
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.LeafCT
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.AesGcm.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.AesGcm.AArch64.Crypt
import VerifiedGarbage.Proof.AesGcm.AArch64.Save
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather.Contiguous

/-! The bounded contiguous seal adapter turns its data pointer and length
into a single gather descriptor. All metadata lives in its own 32-byte frame. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Contiguous

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.AesGcm.AArch64.DirectGather.Contiguous

abbrev slot (b : Addr) (n : Nat) := b + BitVec.ofNat 64 n

/-- The four outgoing ABI words include the saved link. -/
def saveWords (m : Mem) (sp a b c lr : Addr) : Mem :=
  (((m.writeW (slot sp 0) a).writeW (slot sp 8) b).writeW (slot sp 16) c).writeW (slot sp 24) lr

theorem saveWords_slots (m : Mem) (sp a b c lr : Addr) :
    (saveWords m sp a b c lr).readW (slot sp 0) 64 = a ∧
    (saveWords m sp a b c lr).readW (slot sp 8) 64 = b ∧
    (saveWords m sp a b c lr).readW (slot sp 16) 64 = c ∧
    (saveWords m sp a b c lr).readW (slot sp 24) 64 = lr := by
  unfold saveWords slot
  refine ⟨?_,?_,?_,?_⟩ <;> repeat (first
    | rw [Mem.readW_writeW_self64]
    | rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)])

theorem saveWords_frame (m : Mem) (sp a b c lr : Addr) : Frame [⟨sp,32⟩] m (saveWords m sp a b c lr) := by
  have atSlot {n : Nat} (h : n+8 ≤ 32) : (⟨sp,32⟩ : Region).Contains (slot sp n) 8 :=
    Offset.contains_base _ h (by omega)
  exact (((((Frame.refl [⟨sp,32⟩] m).writeW (List.mem_singleton_self _) _ (atSlot (by decide))).writeW
    (List.mem_singleton_self _) _ (atSlot (by decide))).writeW (List.mem_singleton_self _) _ (atSlot (by decide))).writeW
    (List.mem_singleton_self _) _ (atSlot (by decide)))

def saved (s : State) : Mem := saveWords s.mem s.sp (s.gpr .x6) (s.gpr .x7) (s.mem.readW (slot s.sp 32) 64) (s.gpr .x30)

theorem setup_ok (s : State) (readTag : InRegions (s.rd ++ s.wr) (slot s.sp 32) 8)
    (writeFrame : (⟨s.sp,32⟩ : Region) ∈ s.wr) :
    WP isa (.block setup) s fun t =>
      t.mem = saved s ∧ t.gpr .x6 = s.sp ∧ t.gpr .x7 = 1 ∧
      (∀ r, r ∉ [.x6,.x7,.x9] → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.dit = s.dit := by
  have store {n : Nat} (h : n+8 ≤ 32) : InRegions s.wr (slot s.sp n) 8 :=
    ⟨_,writeFrame, Offset.contains_base _ h (by omega)⟩
  have w0 := store (n := 0) (by decide)
  have w8 := store (n := 8) (by decide)
  have w16 := store (n := 16) (by decide)
  have w24 := store (n := 24) (by decide)
  unfold slot at readTag w0 w8 w16 w24
  apply WP.of_runBlock
  refine ⟨_,by arun [setup,readTag,w0,w8,w16,w24],?_⟩
  simp only [saved,saveWords,slot,State.write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
    BitVec.add_zero,Size.bits]
  refine ⟨rfl,trivial,rfl,?_,trivial,trivial,trivial,trivial⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp [hr.1,hr.2.1,hr.2.2]

/-- The outgoing stack arguments occupy the first three slots. The gather
descriptor occupies the first two slots, so its slice is the whole output. -/
structure Args (d n tag : Addr) (s : State) : Prop where
  desc : s.gpr .x6 = s.sp
  count : s.gpr .x7 = 1
  dst : stackArg s 0 = d
  len : stackArg s 1 = n
  tag : stackArg s 2 = tag

theorem Args.listed {d n tag : Addr} {s : State} (h : Args d n tag s) :
    Gather.lsR s = [⟨d,n.toNat⟩] := by
  have d0 : s.mem.readW s.sp 64 = d := by simpa only [stackArg,stackArgAddr,Nat.mul_zero,BitVec.add_zero] using h.dst
  have n8 : s.mem.readW (s.sp+8#64) 64 = n := h.len
  simp [Gather.lsR,Gather.Src,Gather.Cnt,h.desc,h.count,Sig.listed,Elem.size,d0,n8]

theorem Args.plaintext {d n tag : Addr} {s : State} (h : Args d n tag s) :
    Gather.pt s (Gather.Cnt s) = Spec.Aes.bytesAt s.mem d n.toNat := by
  simp only [Gather.pt,Spec.Gcm.gathered,h.listed, List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem Args.length {d n tag : Addr} {s : State} (h : Args d n tag s) :
    Gather.gl s (Gather.Cnt s) = Gather.L s := by
  simp only [Gather.gl,Spec.Gcm.gatheredLen,h.listed,Gather.L,h.len,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Nat.add_zero]

theorem Args.source {d n tag : Addr} {s : State} (h : Args d n tag s) :
    Gather.Cnt s = 1 ∧ Gather.sb s.mem (Gather.Src s) 0 = Gather.Dst s := by
  refine ⟨by rw [Gather.Cnt,h.count]; rfl,?_⟩
  simp only [Gather.Src,h.desc,Gather.Dst,Gather.sb,stackArg,stackArgAddr,Nat.mul_zero,BitVec.add_zero]

/-- The permissions of a call of the shared bounded leaf. A source may
also occur in the write set when it is the contiguous destination. -/
def view (s : State) : State := s.withRegions
  ([Gather.kR .plain s,Gather.nR s,Gather.aR s,Gather.dsR s] ++ Gather.lsR s ++ [Gather.argR s])
  [Gather.dR s,Gather.tgR s]

theorem layout {s : State} {d n tag : Addr} (a : Args d n tag s)
    (kd : (Gather.kR .plain s).Disjoint (Gather.dR s)) (dt : (Gather.dR s).Disjoint (Gather.tgR s))
    (stackData : (⟨s.sp,32⟩ : Region).Disjoint (Gather.dR s))
    (bk : (boundedStack s).Disjoint (Gather.kR .plain s))
    (bn : (boundedStack s).Disjoint (Gather.nR s))
    (ba : (boundedStack s).Disjoint (Gather.aR s))
    (bd : (boundedStack s).Disjoint (Gather.dR s))
    (bt : (boundedStack s).Disjoint (Gather.tgR s))
    (room : 752 ≤ s.sp.toNat) (top : s.sp.toNat+32 ≤ 2^64)
    (rounds : VG.Proof.AesGcm.AArch64.rounds (s.gpr .x1)) : BoundedLay (view s) := by
  have cnt := a.source.1
  have desc : Gather.dsR s = ⟨s.sp,16⟩ := by simp [Gather.dsR,Gather.Src,a.desc,cnt]
  have args : Gather.argR s = ⟨s.sp,24⟩ := by simp [Gather.argR,stackArgAddr]
  have below (k : Nat) (hk : k ≤ 32) : (boundedStack s).Disjoint ⟨s.sp,k⟩ :=
    (Offset.base_disjoint_below s.sp (by omega : 752+k ≤ 2^64)).symm
  have initial (k : Nat) (hk : k ≤ 32) : (⟨s.sp,k⟩ : Region).Sub ⟨s.sp,32⟩ :=
    fun _ h => by exact Nat.le_trans h hk
  have slices : Gather.lsR s = [Gather.dR s] := by rw [a.listed]; simp [Gather.dR,Gather.Dst,Gather.L,a.dst,a.len]
  refine ⟨rfl,rfl,kd,?_,dt,?_,bk,bn,ba,?_,?_,?_,bd,bt,room,rounds,a.length,?_,Or.inr a.source⟩
  · change (Gather.dsR s).Disjoint _; rw [desc]; exact stackData.sub_left (initial _ (by decide))
  · change (Gather.dR s).Disjoint (Gather.argR s); rw [args]; exact (stackData.sub_left (initial _ (by decide))).symm
  · change (boundedStack s).Disjoint (Gather.dsR s); rw [desc]; exact below _ (by decide)
  · change ∀ r ∈ Gather.lsR s, (boundedStack s).Disjoint r
    rw [slices]; simpa using bd
  · change (boundedStack s).Disjoint (Gather.argR s); rw [args]; exact below _ (by decide)
  · change (Gather.Src s).toNat + Gather.Cnt s * 16 ≤ 2^64
    rw [Gather.Src,a.desc,cnt]; omega

abbrev dataR (s : State) : Region := ⟨s.gpr .x6,(s.gpr .x7).toNat⟩
abbrev tagR (s : State) : Region := ⟨stackArg s 0,16⟩
abbrev powerR (s : State) : Region := ⟨stackArg s 1,128⟩
abbrev callerArgs (s : State) : Region := ⟨stackArgAddr s 0,16⟩

/-- Facts about the public in-place API needed by the bounded call. -/
structure Caller (s : State) : Prop where
  rd : s.rd = [Gather.kR .plain s,Gather.nR s,Gather.aR s,powerR s,callerArgs s]
  wr : s.wr = [dataR s,tagR s]
  kd : (Gather.kR .plain s).Disjoint (dataR s)
  dt : (dataR s).Disjoint (tagR s)
  stack : ∀ r ∈ [Gather.kR .plain s,Gather.nR s,Gather.aR s,dataR s,tagR s],
    (below s.sp 1056).Disjoint r
  room : 1056 ≤ s.sp.toNat
  top : s.sp.toNat+16 ≤ 2^64
  rounds : VG.Proof.AesGcm.AArch64.rounds (s.gpr .x1)

private theorem stackWords (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0,stackArg s 1] := rfl

theorem caller_of_pre {s : State} (h : (Spec.Gcm.sealWithPowersContract abi 1056).pre s) : Caller s := by
  sig_pre [Spec.Gcm.sealWithPowersContract,Spec.Gcm.sealWithPowersSig,Spec.Gcm.sealSig,
    Spec.Gcm.withPowersParam,Spec.Gcm.sealWithPowersPre,Spec.Gcm.sealPre,abi,argRegs,stackWords,
    List.cons_append,List.nil_append] at h
  obtain ⟨space,top,rd,wr,sep,sk,sn,sa,more,_,_,_,_,rounds,_⟩ := h
  refine ⟨rd,wr,?_,?_,?_,space,top,?_⟩
  · exact sep.1
  · exact sep.2.2.2.2.2.2.1
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact sk
    · exact sn
    · exact sa
    · exact more.1
    · exact more.2.1
  · exact rounds

/-- The caller remains recoverable after setting up the callee's arguments. -/
structure Entered (o t : State) : Prop where
  args : Args (o.gpr .x6) (o.gpr .x7) (stackArg o 0) t
  sp : t.sp = o.sp - 32
  rd : t.rd = o.rd
  wr : t.wr = below o.sp 32 :: o.wr
  regs : ∀ r, r ∉ [.x6,.x7,.x9] → t.gpr r = o.gpr r
  dit : t.dit = o.dit
  link : t.mem.readW (t.sp+24#64) 64 = o.gpr .x30
  frame : Frame [below o.sp 32] o.mem t.mem

theorem enter (o : State) (c : Caller o) :
    WP isa (.block setup) (allocated 32 o) (Entered o) := by
  let u := allocated 32 o
  have tag : u.sp+32#64 = o.sp := BitVec.sub_add_cancel _ _
  have read : InRegions (u.rd ++ u.wr) (slot u.sp 32) 8 := by
    rw [slot,tag]
    change InRegions (o.rd ++ _) o.sp 8
    refine ⟨callerArgs o,List.mem_append_left _ (by rw [c.rd]; simp),?_⟩
    change (⟨o.sp+0#64,16⟩ : Region).Contains o.sp 8
    simpa only [BitVec.add_zero] using Offset.contains_base o.sp (d := 0) (n := 8) (k := 16) (by decide) (by decide)
  refine (setup_ok u read (List.mem_cons_self ..)).mono ?_
  intro t ⟨hm,ds,n,g,sp,rd,wr,dit⟩
  obtain ⟨d,l,tg,lr⟩ := saveWords_slots u.mem u.sp (u.gpr .x6) (u.gpr .x7) (u.mem.readW (slot u.sp 32) 64) (u.gpr .x30)
  have base : u.sp = o.sp-32 := rfl
  have originalTag : u.mem.readW (slot u.sp 32) 64 = stackArg o 0 := by simp only [slot,tag,stackArg,stackArgAddr,Nat.mul_zero,BitVec.add_zero]; rfl
  refine ⟨⟨ds.trans sp.symm,n,?_,?_,?_⟩,sp.trans base,rd,wr,g,dit,?_,?_⟩
  · change t.mem.readW (slot t.sp 0) 64 = _
    rw [sp,hm]; exact d
  · change t.mem.readW (slot t.sp 8) 64 = _
    rw [sp,hm]; exact l
  · change t.mem.readW (slot t.sp 16) 64 = _
    rw [sp,hm,saved,tg,originalTag]
  · rw [sp,hm]; exact lr
  · rw [hm]; exact saveWords_frame _ _ _ _ _ _

theorem Args.call {d n tag : Addr} {s : State} (a : Args d n tag s) : Args d n tag s.callEntry :=
  ⟨(State.callEntry_gpr _ (by decide)).trans a.desc, (State.callEntry_gpr _ (by decide)).trans a.count,
    a.dst,a.len,a.tag⟩

theorem Entered.regions {o t : State} (h : Entered o t) :
    Gather.kR .plain t.callEntry = Gather.kR .plain o ∧
    Gather.nR t.callEntry = Gather.nR o ∧ Gather.aR t.callEntry = Gather.aR o ∧
    Gather.dR t.callEntry = dataR o ∧ Gather.tgR t.callEntry = tagR o := by
  have a := h.args.call
  have g (r : Reg) (hr : r ∉ [.x6,.x7,.x9]) (hl : r ∉ linkRegs) : t.callEntry.gpr r = o.gpr r :=
    (State.callEntry_gpr _ hl).trans (h.regs _ hr)
  have k : Gather.kR .plain t.callEntry = Gather.kR .plain o :=
    congrArg (fun (addr : Addr) => (⟨addr,256⟩ : Region)) (g .x0 (by decide) (by decide))
  have n : Gather.nR t.callEntry = Gather.nR o := by
    simp only [Gather.nR,Gather.Nn,Gather.NL,g .x2 (by decide) (by decide),
      g .x3 (by decide) (by decide)]
  have aad : Gather.aR t.callEntry = Gather.aR o := by
    simp only [Gather.aR,Gather.Ad,Gather.AL,g .x4 (by decide) (by decide),
      g .x5 (by decide) (by decide)]
  have d : Gather.dR t.callEntry = dataR o := by simp only [Gather.dR,Gather.Dst,Gather.L,a.dst,a.len,dataR]
  have tag : Gather.tgR t.callEntry = tagR o := by simp only [Gather.tgR,Gather.Tg,a.tag,tagR]
  exact ⟨k,n,aad,d,tag⟩

theorem Entered.pre {o t : State} (h : Entered o t) (c : Caller o) :
    BoundedLay (view t.callEntry) := by
  have a := h.args.call
  obtain ⟨k,n,aad,d,tag⟩ := h.regions
  have belowSub : (boundedStack t.callEntry).Sub (below o.sp 1056) := by
    change (⟨t.sp - 752,752⟩ : Region).Sub (below o.sp 1056)
    rw [h.sp,BitVec.sub_sub]
    exact Offset.sub_below o.sp (a := 784) (b := 1056) (by decide) (by decide)
  have localSub : (⟨t.callEntry.sp,32⟩ : Region).Sub (below o.sp 1056) := by
    rw [State.callEntry_sp,h.sp]
    exact Offset.sub_below o.sp (a := 32) (b := 1056) (by decide) (by decide)
  have stackN : t.sp.toNat = o.sp.toNat-32 := by
    have := o.sp.isLt
    have := c.room
    rw [h.sp,show (32 : Addr) = BitVec.ofNat 64 32 from rfl,Offset.toNat_sub_ofNat]
    omega
  apply layout a
  · rw [k,d]; exact c.kd
  · rw [d]; rw [tag]; exact c.dt
  · rw [d]; exact (c.stack _ (by simp)).sub_left localSub
  · rw [k]; exact (c.stack _ (by simp)).sub_left belowSub
  · rw [n]; exact (c.stack _ (by simp)).sub_left belowSub
  · rw [aad]; exact (c.stack _ (by simp)).sub_left belowSub
  · rw [d]; exact (c.stack _ (by simp)).sub_left belowSub
  · rw [tag]; exact (c.stack _ (by simp)).sub_left belowSub
  · rw [State.callEntry_sp,stackN]; have := c.room; omega
  · rw [State.callEntry_sp,stackN]; have := c.top; omega
  · rw [State.callEntry_gpr _ (by decide),h.regs .x1 (by decide)]; exact c.rounds

theorem Entered.covers {o t : State} (h : Entered o t) (c : Caller o) :
    Covers ((view t.callEntry).rd ++ (view t.callEntry).wr) (t.rd ++ t.wr) ∧
    Covers (view t.callEntry).wr t.wr := by
  obtain ⟨k,n,aad,d,tag⟩ := h.regions
  have a := h.args.call
  have cnt := a.source.1
  have desc : Gather.dsR t.callEntry = ⟨t.sp,16⟩ := by
    simp [Gather.dsR,Gather.Src,a.desc,cnt]
  have args : Gather.argR t.callEntry = ⟨t.sp,24⟩ := by simp [Gather.argR,stackArgAddr]
  have frame {len : Nat} (hl : len ≤ 32) : Covers [⟨t.sp,len⟩] (t.rd ++ t.wr) := by
    apply Covers.one
    refine ⟨below o.sp 32,List.mem_append_right _ (by rw [h.wr]; simp),?_⟩
    change (t.sp - (o.sp - 32)).toNat + len ≤ 32
    simpa only [h.sp,BitVec.sub_self,BitVec.toNat_zero,Nat.zero_add] using hl
  change Covers ((_ ++ _) ++ [_,_]) _ ∧ Covers [_,_] _
  have out : Covers [Gather.dR t.callEntry,Gather.tgR t.callEntry] t.wr := by
    rw [d,tag,h.wr,c.wr]
    apply Covers.of_mem
    simp
  refine ⟨Covers.append_left ?_ out.right,out⟩
  change Covers (([_,_,_,_] ++ Gather.lsR t.callEntry) ++ [_]) _
  rw [k,n,aad,desc,a.listed,args]
  apply Covers.append_left _ (frame (by decide))
  apply Covers.append_left
  · apply Covers.cons _ (Covers.cons _ (Covers.cons _ (frame (by decide))))
    all_goals apply Covers.left; apply Covers.of_mem; rw [h.rd,c.rd]; simp
  · apply Covers.right; apply Covers.of_mem; rw [h.wr,c.wr]; simp [dataR]

theorem Entered.post {o t u : State} (h : Entered o t) (c : Caller o)
    (post : Gather.gatherPost (view t.callEntry) u) : (sealAArch64).post o u := by
  have a := h.args.call
  have g (r : Reg) (hr : r ∉ [.x6,.x7,.x9]) (hl : r ∉ linkRegs) :
      t.callEntry.gpr r = o.gpr r := (State.callEntry_gpr _ hl).trans (h.regs _ hr)
  have s32 : (below o.sp 32).Sub (below o.sp 1056) := Offset.sub_below _ (by decide) (by decide)
  have apart {r : Region} (hr : r ∈ [Gather.kR .plain o,Gather.nR o,Gather.aR o,dataR o,tagR o]) :
      ∀ w ∈ [below o.sp 32], r.Disjoint w := by
    simpa only [List.mem_singleton,forall_eq] using ((c.stack r hr).sub_left s32).symm
  have cipher : Spec.Gcm.ctxCiph t.mem (o.gpr .x0) (o.gpr .x1).toNat =
      Spec.Gcm.ctxCiph o.mem (o.gpr .x0) (o.gpr .x1).toNat :=
    ciph_frame h.frame (apart (r := Gather.kR .plain o) (by simp)) c.rounds
  have hash : Spec.Gcm.ctxH t.mem (o.gpr .x0) = Spec.Gcm.ctxH o.mem (o.gpr .x0) :=
    blockAt_frame h.frame (fun w hw => (apart (r := Gather.kR .plain o) (by simp) w hw).sub_left
      (Lay.ctxSub (by decide)))
  have nonce := bytesAt_frame h.frame (apart (r := Gather.nR o) (by simp)) (Nat.le_of_lt (o.gpr .x3).isLt)
  have aad := bytesAt_frame h.frame (apart (r := Gather.aR o) (by simp)) (Nat.le_of_lt (o.gpr .x5).isLt)
  have data := bytesAt_frame h.frame (apart (r := dataR o) (by simp)) (Nat.le_of_lt (o.gpr .x7).isLt)
  change Gather.gatherPost t.callEntry u at post
  unfold Gather.gatherPost at post
  rw [a.plaintext] at post
  simp only [Gather.K,Gather.Nn,Gather.NL,Gather.Ad,Gather.AL,Gather.L,Gather.Dst,Gather.Tg,
    a.dst,a.len,a.tag,g .x0 (by decide) (by decide),g .x1 (by decide) (by decide),
    g .x2 (by decide) (by decide),g .x3 (by decide) (by decide),g .x4 (by decide) (by decide),
    g .x5 (by decide) (by decide),State.callEntry_mem,cipher,hash,nonce,aad,data] at post
  exact post

theorem savedLink {t u : State} {bytes : Nat} (hb : bytes ≤ 752)
    (hd : (⟨t.sp,32⟩ : Region).Disjoint (Gather.dR t.callEntry))
    (ht : (⟨t.sp,32⟩ : Region).Disjoint (Gather.tgR t.callEntry))
    (f : Frame ((view t.callEntry).wr ++ [below t.sp bytes]) t.mem u.mem) :
    u.mem.readW (t.sp + 24#64) 64 = t.mem.readW (t.sp + 24#64) 64 := by
  let lr : Region := ⟨t.sp + 24#64,8⟩
  have fits : lr.Sub ⟨t.sp,32⟩ := Offset.sub_base _ (by decide)
  apply f.readW (r := lr) (by simp [lr,Region.Contains]) _ (by decide)
  change ∀ r ∈ [Gather.dR t.callEntry,Gather.tgR t.callEntry,below t.sp bytes], _
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hd.sub_left fits
  · exact ht.sub_left fits
  · exact Offset.disjoint_below _ (by omega)

theorem Caller.postFrame {o t v : State} (c : Caller o) (p : (sealAArch64).post o t) {bytes : Nat}
    (hb : bytes ≤ 1056) (f : Frame [below o.sp bytes] t.mem v.mem) : (sealAArch64).post o v := by
  have sub : (below o.sp bytes).Sub (below o.sp 1056) := Offset.sub_below _ hb (by omega)
  have apart {r : Region} (hr : r ∈ [dataR o,tagR o]) : ∀ w ∈ [below o.sp bytes], r.Disjoint w := by
    have hh := c.stack r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; exact Or.inr (Or.inr (Or.inr hr)))
    simpa only [List.mem_singleton,forall_eq] using (hh.sub_left sub).symm
  change _ = (Spec.Aes.bytesAt v.mem _ _,Spec.Aes.bytesAt v.mem _ _)
  rw [bytesAt_frame f (apart (r := dataR o) (by simp)) (Nat.le_of_lt (o.gpr .x7).isLt),
    bytesAt_frame f (apart (r := tagR o) (by simp)) (by decide)]
  exact p

theorem Entered.within {o t : State} (h : Entered o t)
    (iv : (o.gpr .x3).toNat = 12) (ad : (o.gpr .x5).toNat ≤ 16) {limit : Nat}
    (ln : (o.gpr .x7).toNat ≤ limit) : recordWithin limit (view t.callEntry) := by
  have g (r : Reg) (hr : r ∉ [.x6,.x7,.x9]) (hl : r ∉ linkRegs) :
      t.callEntry.gpr r = o.gpr r := (State.callEntry_gpr _ hl).trans (h.regs _ hr)
  have a := h.args.call
  change (t.callEntry.gpr .x3).toNat = 12 ∧ (t.callEntry.gpr .x5).toNat ≤ 16 ∧ (stackArg t.callEntry 1).toNat ≤ limit
  rw [g .x3 (by decide) (by decide),g .x5 (by decide) (by decide),a.len]
  exact ⟨iv,ad,ln⟩


/-- Both ABI adapters call the same authenticated-encryption machine body.
Their proofs supply its permissions and the observable output; the call,
link-register reload, and frame release are proved once. -/
structure CallReady (o t : State) (Q : State → Prop) : Prop where
  pre : (sharedBoundedContract 96).pre (view t.callEntry)
  read : Covers ((view t.callEntry).rd ++ (view t.callEntry).wr) (t.rd ++ t.wr)
  write : Covers (view t.callEntry).wr t.wr
  sp : t.sp = o.sp-32
  wr : t.wr = below o.sp 32 :: o.wr
  keeps : ∀ r ∈ preserved, t.gpr r = o.gpr r
  link : t.mem.readW (t.sp+24#64) 64 = o.gpr .x30
  dataApart : (⟨t.sp,32⟩ : Region).Disjoint (Gather.dR t.callEntry)
  tagApart : (⟨t.sp,32⟩ : Region).Disjoint (Gather.tgR t.callEntry)
  post : ∀ u, Gather.gatherPost (view t.callEntry) u → ∀ v, Frame [below o.sp 32] u.mem v.mem → Q v

theorem callReady_ok {args : List Instr} (hash : HashEightOk) {o : State} {Q : State → Prop}
    (space : 32 ≤ o.sp.toNat) (enter : WP isa (.block args) (allocated 32 o) fun t => CallReady o t Q)
    (vectors : (callFrame args shortName Impl.AesGcm.AArch64.DirectGather.shortWork
      Impl.AesGcm.AArch64.DirectGather.shortBody).allInstrs keepsV = true) :
    WP isa (callFrame args shortName Impl.AesGcm.AArch64.DirectGather.shortWork
      Impl.AesGcm.AArch64.DirectGather.shortBody) o fun v => abiPreserved o v ∧ Q v := by
  have checked : Verified target rawLeaf (sharedBoundedContract 96) :=
    boundedRaw_verified _ (by decide) shortSide (shortBody_ok hash) (shortBody_rel hash)
  apply WP.withPreservedV (hc := vectors)
  apply WP.alloc (by decide) space
  refine WP.seq (enter.mono ?_)
  intro t h
  refine WP.seq (WP.callFV checked.1 h.pre h.read h.write ?_)
  intro u rd wr sp frame regs _ post
  have depth : 16*rawLeaf.aarch64Depth = 368 := by decide
  rw [depth] at frame
  have link := (savedLink (by decide) h.dataApart h.tagApart frame).trans h.link
  have canRead : InRegions (u.rd ++ u.wr) (u.sp+24#64) 8 := by
    refine ⟨below o.sp 32,List.mem_append_right _ (by rw [wr,h.wr]; simp),?_⟩
    rw [sp]
    change (⟨o.sp-32,32⟩ : Region).Contains (t.sp+24#64) 8
    rw [←h.sp]
    exact Offset.contains_base _ (by decide) (by decide)
  apply WP.of_runBlock
  refine ⟨_,by arun [canRead],?_⟩
  intro m un f
  constructor
  · constructor
    · intro r hr
      by_cases eq : r = .x30
      · subst r; simpa only [freed,State.write,ite_true,BitVec.setWidth_eq,sp,Mem.readW] using link
      · simpa only [freed,State.write,eq,ite_false] using (regs r hr eq).trans (h.keeps r hr)
    · change u.sp+32#64=o.sp; rw [sp,h.sp]; exact BitVec.sub_add_cancel _ _
  · exact h.post u post _ f

theorem shortFrame_ok (hash : HashEightOk) {o : State} (c : Caller o)
    (iv : (o.gpr .x3).toNat = 12) (ad : (o.gpr .x5).toNat ≤ 16) (ln : (o.gpr .x7).toNat ≤ 96) :
    WP isa (callFrame setup shortName Impl.AesGcm.AArch64.DirectGather.shortWork
      Impl.AesGcm.AArch64.DirectGather.shortBody) o fun v => abiPreserved o v ∧ (sealAArch64).post o v := by
  apply callReady_ok hash (by have := c.room; omega) _ (by decide +kernel)
  refine (enter o c).mono ?_
  intro t h
  obtain ⟨read,write⟩ := h.covers c
  obtain ⟨_,_,_,data,tag⟩ := h.regions
  have sub : (⟨t.sp,32⟩ : Region).Sub (below o.sp 1056) := by
    rw [h.sp]; exact Offset.sub_below _ (by decide) (by decide)
  refine ⟨⟨h.pre c,h.within iv ad ln⟩,read,write,h.sp,h.wr,?_,h.link,?_,?_,
    fun u p _ f => c.postFrame (h.post c p) (by decide) f⟩
  · exact fun r hr => h.regs r ((by decide : ∀ x ∈ preserved, x ∉ [.x6,.x7,.x9]) r hr)
  · rw [data]; exact (c.stack _ (by simp)).sub_left sub
  · rw [tag]; exact (c.stack _ (by simp)).sub_left sub

theorem wordBytes {s t : State} {p q : Addr} (word : s.mem.readW p 64 = t.mem.readW q 64)
    {i : Nat} (hi : i < 8) : s.mem (p + BitVec.ofNat 64 i) = t.mem (q + BitVec.ofNat 64 i) := by
  have eq : s.mem.read p 8 = t.mem.read q 8 := by simpa only [Mem.readW,BitVec.setWidth_eq] using word
  rw [← Mem.extractLsb'_read s.mem p (n := 8) hi,eq,Mem.extractLsb'_read t.mem q hi]

theorem Args.descriptorBytes {d n tag : Addr} {t u : State} (a : Args d n tag t) (b : Args d n tag u)
    {i : Nat} (hi : i < 16) : t.mem (t.sp + BitVec.ofNat 64 i) = u.mem (u.sp + BitVec.ofNat 64 i) := by
  by_cases lo : i < 8
  · apply wordBytes (i := i) _ lo
    simpa only [stackArg,stackArgAddr,Nat.mul_zero,BitVec.add_zero] using a.dst.trans b.dst.symm
  · have upper : i-8 < 8 := by omega
    have eq : t.mem.readW (t.sp + BitVec.ofNat 64 8) 64 = u.mem.readW (u.sp + BitVec.ofNat 64 8) 64 :=
      a.len.trans b.len.symm
    have shifted := wordBytes (s := t) (t := u) eq upper
    rwa [Offset.add_add,Offset.add_add,Nat.add_sub_of_le (by omega : 8 ≤ i)] at shifted

theorem Entered.public {a b t u : State} (ha : Entered a t) (hb : Entered b u)
    (pub : onePub 2 a b) (dit : t.dit = u.dit) : Gather.gatherPub (view t.callEntry) (view u.callEntry) := by
  obtain ⟨g0,g1,g2,g3,g4,g5,g6,g7,sp,stk⟩ := pub
  have tag := stk 0 (by decide)
  have aa := ha.args.call
  have ab := hb.args.call
  rw [←g6,←g7,←tag] at ab
  have stacks : t.callEntry.sp = u.callEntry.sp := by simp only [State.callEntry_sp,ha.sp,hb.sp,sp]
  have g (r : Reg) (hr : r ∉ [.x6,.x7,.x9]) (hl : r ∉ linkRegs) (eq : a.gpr r = b.gpr r) :
      t.callEntry.gpr r = u.callEntry.gpr r := by
    rw [State.callEntry_gpr _ hl,State.callEntry_gpr _ hl,ha.regs _ hr,hb.regs _ hr,eq]
  refine ⟨g .x0 (by decide) (by decide) g0,g .x1 (by decide) (by decide) g1,
    g .x2 (by decide) (by decide) g2,g .x3 (by decide) (by decide) g3,g .x4 (by decide) (by decide) g4,
    g .x5 (by decide) (by decide) g5,aa.desc.trans (stacks.trans ab.desc.symm),aa.count.trans ab.count.symm,
    stacks,dit,aa.dst.trans ab.dst.symm,aa.len.trans ab.len.symm,aa.tag.trans ab.tag.symm,?_⟩
  change ∀ i < Gather.Cnt t.callEntry*16, t.callEntry.mem (t.callEntry.gpr .x6 + BitVec.ofNat 64 i) =
    u.callEntry.mem (t.callEntry.gpr .x6 + BitVec.ofNat 64 i)
  rw [aa.source.1,aa.desc]
  intro i hi
  exact (aa.descriptorBytes ab hi).trans (by rw [stacks])

abbrev boundedArgs (s : State) := (s.gpr .x3).toNat = 12 ∧ (s.gpr .x5).toNat ≤ 16 ∧ (s.gpr .x7).toNat ≤ 96

theorem callReturn_rel (hash : HashEightOk) {t u : State}
    (ta : (sharedBoundedContract 96).pre (view t.callEntry)) (ub : (sharedBoundedContract 96).pre (view u.callEntry))
    (pub : Gather.gatherPub (view t.callEntry) (view u.callEntry))
    (tr : Covers ((view t.callEntry).rd ++ (view t.callEntry).wr) (t.rd ++ t.wr)) (tw : Covers (view t.callEntry).wr t.wr)
    (ur : Covers ((view u.callEntry).rd ++ (view u.callEntry).wr) (u.rd ++ u.wr)) (uw : Covers (view u.callEntry).wr u.wr) :
    RelCT isa (Eq2 t u) (.seq (.call shortName rawLeaf) (.block [.ldrSp .x30 24])) TT := by
  have sp : t.sp=u.sp := pub.2.2.2.2.2.2.2.2.1
  have checked : Verified target rawLeaf (sharedBoundedContract 96) :=
    boundedRaw_verified _ (by decide) shortSide (shortBody_ok hash) (shortBody_rel hash)
  have timing : RelCT isa (Eq2 t u) (.call shortName rawLeaf) TT := by
    apply RelCT.callEx checked.1 checked.2.1
    rintro _ _ ⟨rfl,rfl⟩
    exact ⟨_,_,_,_,ta,ub,pub,tr,tw,ur,uw⟩
  refine rel_seq timing (WP.callFV checked.1 ta tr tw (fun _ _ _ s _ _ _ _ => s))
    (WP.callFV checked.1 ub ur uw (fun _ _ _ s _ _ _ _ => s)) ?_
  intro x y hx hy
  have same : x.sp = y.sp := by rw [hx,hy,sp]
  exact rel_taint [] same (by simp) ⟨_,by taint_decide⟩

theorem shortFrame_rel (hash : HashEightOk) {a b : State} (ca : Caller a) (cb : Caller b)
    (ra : boundedArgs a) (rb : boundedArgs b) (pub : onePub 2 a b) (dit : a.dit = b.dit) :
    RelCT isa (Eq2 a b) (callFrame setup shortName Impl.AesGcm.AArch64.DirectGather.shortWork
      Impl.AesGcm.AArch64.DirectGather.shortBody) TT := by
  have sp := pub.2.2.2.2.2.2.2.2.1
  apply RelCT.alloc (R := TT)
  suffices body : RelCT isa (Eq2 (allocated 32 a) (allocated 32 b)) _ TT from
    body.mono (by rintro x y ⟨_,_,⟨rfl,rfl⟩,rfl,rfl⟩; exact ⟨rfl,rfl⟩) (fun _ _ h => h)
  have asp : (allocated 32 a).sp = (allocated 32 b).sp := by simp only [allocated,sp]
  refine rel_seq (rel_taint [] asp (by simp) ⟨_,by taint_decide⟩) (enter a ca) (enter b cb) ?_
  intro t u ht hu
  have ta : (sharedBoundedContract 96).pre (view t.callEntry) := ⟨ht.pre ca,ht.within ra.1 ra.2.1 ra.2.2⟩
  have ub : (sharedBoundedContract 96).pre (view u.callEntry) := ⟨hu.pre cb,hu.within rb.1 rb.2.1 rb.2.2⟩
  obtain ⟨tr,tw⟩ := ht.covers ca
  obtain ⟨ur,uw⟩ := hu.covers cb
  exact callReturn_rel hash ta ub (ht.public hu pub (ht.dit.trans (dit.trans hu.dit.symm))) tr tw ur uw

/-- The shared short leaf's in-place caller observes the normal seal output. -/
def shortCallerContract : Contract isa where
  pre o := Caller o ∧ boundedArgs o
  post := (sealAArch64).post
  pub a b := onePub 2 a b ∧ a.dit = b.dit

open VG.AArch64.Scrub VG.Impl.Scrub.AArch64

theorem scrubbedCall {k : Contract isa} {raw : Prog isa}
    (verified : Verified target raw k) (cleanup : ScrubAllOk k 400 0)
    (side : scrubSide raw 400 0 Impl.AesGcm.AArch64.Fn.own [] = true) :
    VerifiedScrubbed target (scrubAll 400 0 Impl.AesGcm.AArch64.Fn.own raw) k 0 := by
  obtain ⟨wf,kp,dit,rb⟩ := keeps_of_side side
  refine ⟨Verified.scrubAllOfV verified cleanup side,?_⟩
  simp only [scrubSide,show (400 : Nat) ≠ 0 by decide,↓reduceIte,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at side
  refine noResidue_scrubAll wf kp verified (by decide) cleanup.sp side.1.1.1.1.1.2 dit ?_ rb
  intro _ _ _ n hn
  exact False.elim (List.not_mem_nil (of_decide_eq_true (List.all_eq_true.mp side.1.1.1.1.2 n hn)))

theorem shortCaller_verified (hash : HashEightOk) (sat : ∃ s, shortCallerContract.pre s) :
    VerifiedScrubbed target (boundedSeal setup) shortCallerContract 0 := by
  let raw := callFrame setup shortName Impl.AesGcm.AArch64.DirectGather.shortWork
    Impl.AesGcm.AArch64.DirectGather.shortBody
  have verified : Verified target raw shortCallerContract := by
    refine ⟨fun _ p => shortFrame_ok hash p.1 p.2.1 p.2.2.1 p.2.2.2,ct_of ?_,sat⟩
    intro a b pa pb pub
    exact shortFrame_rel hash pa.1 pb.1 pa.2 pb.2 pub.1 pub.2
  have cleanup : ScrubAllOk shortCallerContract 400 0 := by
    refine ⟨fun s ps => by have := ps.1.room; omega,fun s t u ps res eq _ =>
      ps.1.postFrame res (bytes := 400) (by decide) ?_, fun _ _ p => p.1.2.2.2.2.2.2.2.2.1⟩
    intro a h
    exact eq a fun bad => h _ (List.mem_singleton_self _) (by change (a-(below s.sp 400).base).toNat+1 ≤ 400; exact bad)
  exact scrubbedCall verified cleanup (by decide +kernel)

namespace Forward
open VG.Proof.AesGcm.AArch64.Gather

/-- A gather caller already has its descriptor vector. It forwards only the
three outgoing stack arguments and preserves the return address. -/
structure Entered (o t : State) : Prop where
  args : ∀ j < 3, stackArg t j = stackArg o j
  regs : ∀ r, r ∉ [.x9,.x10,.x11] → t.gpr r = o.gpr r
  sp : t.sp = o.sp-32
  rd : t.rd = o.rd
  wr : t.wr = below o.sp 32 :: o.wr
  dit : t.dit = o.dit
  link : t.mem.readW (t.sp+24#64) 64 = o.gpr .x30
  frame : Frame [below o.sp 32] o.mem t.mem

theorem enter (o : State) (lay : Gather.Lay .plain o) :
    WP isa (.block gatherSetup) (allocated 32 o) (Entered o) := by
  let u := allocated 32 o
  have high (n : Nat) : slot u.sp (32+n) = slot o.sp n := by
    simp only [slot,BitVec.ofNat_add,← BitVec.add_assoc]; rw [show u.sp + 32#64 = o.sp from BitVec.sub_add_cancel _ _]
  have read (n j : Nat) (hj : j < 3) (eq : n=32+8*j) : InRegions (u.rd++u.wr) (slot u.sp n) 8 := by
    rw [eq,high]
    refine ⟨argR o,List.mem_append_left _ (by change _ ∈ o.rd; rw [lay.pre.1]; simp),stackArg_contains o j hj⟩
  have write (n : Nat) (hn : n+8 ≤ 32) : InRegions u.wr (slot u.sp n) 8 :=
    ⟨⟨u.sp,32⟩,List.mem_cons_self ..,Offset.contains_base _ hn (by omega)⟩
  have r32 := read 32 0 (by decide) (by decide)
  have r40 := read 40 1 (by decide) (by decide)
  have r48 := read 48 2 (by decide) (by decide)
  have w0 := write 0 (by decide)
  have w8 := write 8 (by decide)
  have w16 := write 16 (by decide)
  have w24 := write 24 (by decide)
  let m := saveWords u.mem u.sp (stackArg o 0) (stackArg o 1) (stackArg o 2) (o.gpr .x30)
  obtain ⟨d,n,tag,lr⟩ := saveWords_slots u.mem u.sp (stackArg o 0) (stackArg o 1) (stackArg o 2) (o.gpr .x30)
  have argv (j : Nat) : u.mem.readW (slot u.sp (32+8*j)) 64 = stackArg o j := by rw [high]; rfl
  have run : WP isa (.block gatherSetup) u fun t => t.mem = m ∧ t.sp = u.sp ∧
      (∀ r, r ∉ [.x9,.x10,.x11] → t.gpr r = u.gpr r) ∧ t.rd=u.rd ∧ t.wr=u.wr ∧ t.dit=u.dit := by
    unfold slot at r32 r40 r48 w0 w8 w16 w24
    apply WP.of_runBlock
    refine ⟨_,by arun [gatherSetup,r32,r40,r48,w0,w8,w16,w24],?_⟩
    have a0 := argv 0
    have a1 := argv 1
    have a2 := argv 2
    simp only [slot, Nat.reduceMul, Nat.reduceAdd, Mem.readW, BitVec.setWidth_eq] at a0 a1 a2
    simp only [m,saveWords,slot,State.write,BitVec.setWidth_eq,
      BitVec.add_zero,Size.bits,Mem.writeW,a0,a1,a2]
    refine ⟨rfl,trivial,?_,trivial,trivial,trivial⟩
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp [hr.1,hr.2.1,hr.2.2]
  refine run.mono ?_
  intro t ⟨hm,sp,g,rd,wr,dt⟩
  refine ⟨?_,g,sp,rd,wr,dt,?_,?_⟩
  · intro j hj
    have eq : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases eq with rfl|rfl|rfl
    · change t.mem.readW (slot t.sp 0) 64 = _; rw [hm,sp]; exact d
    · change t.mem.readW (slot t.sp 8) 64 = _; rw [hm,sp]; exact n
    · change t.mem.readW (slot t.sp 16) 64 = _; rw [hm,sp]; exact tag
  · rw [hm,sp]; exact lr
  · rw [hm]; exact saveWords_frame _ _ _ _ _ _

abbrev local32 {o t : State} (h : Entered o t) : Compact.LocalMem ⟨32,by decide⟩ o t := ⟨h.frame,h.rd,h.wr⟩

theorem Entered.g {o t : State} (h : Entered o t) (r : Reg) (hr : r ∉ [.x9,.x10,.x11]) (hl : r ∉ linkRegs) :
    t.callEntry.gpr r = o.gpr r := (State.callEntry_gpr _ hl).trans (h.regs _ hr)

structure Facts (o s : State) : Prop where
  k : kR .plain s = kR .plain o
  n : nR s = nR o
  aad : aR s = aR o
  ds : dsR s = dsR o
  ls : lsR s = lsR o
  d : dR s = dR o
  tag : tgR s = tgR o
  gl : gl s (Cnt s) = gl o (Cnt o)
  pt : pt s (Cnt s) = pt o (Cnt o)

theorem Entered.facts {o t : State} (h : Entered o t) (l : Gather.Lay .plain o) : Facts o t.callEntry := by
  have g := h.g
  have agr := (local32 h).descriptors (BoundedLay.ofGather l)
  have d := h.args 0 (by decide); have n := h.args 1 (by decide); have tag := h.args 2 (by decide)
  have ls := (Proof.AesGcm.listed_congr_le (Nat.le_refl _) agr).1
  have gl := Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) agr
  have pt := Proof.AesGcm.gathered_congr_le (Nat.le_refl _) agr
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact congrArg (fun (addr : Addr) => (⟨addr,256⟩ : Region)) (g .x0 (by decide) (by decide))
  · simp only [nR,Nn,NL,g .x2 (by decide) (by decide),g .x3 (by decide) (by decide)]
  · simp only [aR,Ad,AL,g .x4 (by decide) (by decide),g .x5 (by decide) (by decide)]
  · simp only [dsR,Src,Cnt,g .x6 (by decide) (by decide),g .x7 (by decide) (by decide)]
  · simpa only [lsR,Src,Cnt,State.callEntry_mem,g .x6 (by decide) (by decide),g .x7 (by decide) (by decide)] using ls
  · change (⟨stackArg t 0,(stackArg t 1).toNat⟩ : Region) = _; rw [d,n]
  · change (⟨stackArg t 2,16⟩ : Region) = _; rw [tag]
  · simpa only [Gather.gl,Src,Cnt,State.callEntry_mem,g .x6 (by decide) (by decide),g .x7 (by decide) (by decide)] using gl
  · simpa only [Gather.pt,Src,Cnt,State.callEntry_mem,g .x6 (by decide) (by decide),g .x7 (by decide) (by decide)] using pt

theorem Entered.pre {o t : State} (h : Entered o t) (l : Gather.Lay .plain o) : BoundedLay (view t.callEntry) := by
  have f := h.facts l
  have orig := BoundedLay.ofGather l
  have sub : (boundedStack t.callEntry).Sub (stkR o) := by
    change (⟨t.sp-752,752⟩ : Region).Sub (stkR o)
    rw [h.sp,BitVec.sub_sub]; exact Offset.sub_below _ (a := 784) (b := 2592) (by decide) (by decide)
  have arg : argR t.callEntry = ⟨t.sp,24⟩ := by simp [argR,stackArgAddr]
  have argSub : (argR t.callEntry).Sub (stkR o) := by
    rw [arg,h.sp]; exact Offset.sub_below _ (a := 32) (b := 2592) (by decide) (by decide)
  refine ⟨rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change (kR .plain t.callEntry).Disjoint (dR t.callEntry); rw [f.k,f.d]; exact orig.kd
  · change (dsR t.callEntry).Disjoint (dR t.callEntry); rw [f.ds,f.d]; exact orig.dsDst
  · change (dR t.callEntry).Disjoint (tgR t.callEntry); rw [f.d,f.tag]; exact orig.dt
  · change (dR t.callEntry).Disjoint (argR t.callEntry); rw [f.d]; exact (l.bd.sub_left argSub).symm
  · change (boundedStack t.callEntry).Disjoint (kR .plain t.callEntry); rw [f.k]; exact l.bk.sub_left sub
  · change (boundedStack t.callEntry).Disjoint (nR t.callEntry); rw [f.n]; exact l.bn.sub_left sub
  · change (boundedStack t.callEntry).Disjoint (aR t.callEntry); rw [f.aad]; exact l.ba.sub_left sub
  · change (boundedStack t.callEntry).Disjoint (dsR t.callEntry); rw [f.ds]; exact l.bds.sub_left sub
  · change ∀ r ∈ lsR t.callEntry, (boundedStack t.callEntry).Disjoint r
    rw [f.ls]; exact fun r hr => (l.bl r hr).sub_left sub
  · change (boundedStack t.callEntry).Disjoint (argR t.callEntry); rw [arg]; exact (Offset.base_disjoint_below _ (by decide)).symm
  · change (boundedStack t.callEntry).Disjoint (dR t.callEntry); rw [f.d]; exact l.bd.sub_left sub
  · change (boundedStack t.callEntry).Disjoint (tgR t.callEntry); rw [f.tag]; exact l.bt.sub_left sub
  · change 752 ≤ t.sp.toNat
    rw [h.sp,show (32 : Addr) = BitVec.ofNat 64 32 from rfl,Offset.toNat_sub_ofNat]; have := l.w₁; have := o.sp.isLt; omega
  · change rounds (t.callEntry.gpr .x1); rw [h.g .x1 (by decide) (by decide)]; exact l.hR
  · change gl t.callEntry (Cnt t.callEntry) = (stackArg t 1).toNat; rw [f.gl,h.args 1 (by decide)]; exact l.hgl
  · change (Src t.callEntry).toNat + Cnt t.callEntry*16 ≤ 2^64
    simpa only [Src,Cnt,h.g .x6 (by decide) (by decide),h.g .x7 (by decide) (by decide)] using l.ods
  · apply Or.inl
    change ∀ r ∈ lsR t.callEntry, r.Disjoint (dR t.callEntry)
    rw [f.ls,f.d]
    obtain ⟨_,_,_,_,_,_,_,_,_,_,slices,_⟩ := l.pre
    exact fun r hr => (slices r hr).1

theorem Entered.covers {o t : State} (h : Entered o t) (l : Gather.Lay .plain o) :
    Covers ((view t.callEntry).rd ++ (view t.callEntry).wr) (t.rd ++ t.wr) ∧ Covers (view t.callEntry).wr t.wr := by
  have f := h.facts l
  have orig := BoundedLay.ofGather l
  have out : Covers [dR t.callEntry,tgR t.callEntry] t.wr := by
    rw [f.d,f.tag,h.wr,orig.wr]; apply Covers.of_mem; simp
  refine ⟨Covers.append_left ?_ out.right,out⟩
  change Covers (([kR .plain t.callEntry,nR t.callEntry,aR t.callEntry,dsR t.callEntry] ++ lsR t.callEntry) ++ [argR t.callEntry]) _
  rw [f.k,f.n,f.aad,f.ds,f.ls]
  apply Covers.append_left
  · apply Covers.left; apply Covers.of_mem
    intro r hr; rw [h.rd,orig.rd]; exact List.mem_append_left _ hr
  · change Covers [⟨t.sp + BitVec.ofNat 64 (8*0),24⟩] _
    simp only [Nat.mul_zero,BitVec.add_zero]
    apply Covers.right; apply Covers.one; refine ⟨below o.sp 32,by rw [h.wr]; simp,?_⟩
    change (t.sp - (o.sp - 32)).toNat+24 ≤ 32
    simp [h.sp]

theorem Entered.post {o t v : State} (h : Entered o t) (l : Gather.Lay .plain o)
    (out : gatherPost (view t.callEntry) v) : gatherPost o v := by
  have f := h.facts l
  have sub : (below o.sp 32).Sub (stkR o) := Offset.sub_below _ (by decide) (by decide)
  have apart {r : Region} (hr : (stkR o).Disjoint r) : ∀ w ∈ [below o.sp 32], r.Disjoint w := by
    simpa only [List.mem_singleton,forall_eq] using (hr.sub_left sub).symm
  have cip : Spec.Gcm.ctxCiph t.mem (K o) (o.gpr .x1).toNat = Spec.Gcm.ctxCiph o.mem (K o) (o.gpr .x1).toNat :=
    ciph_frame h.frame (apart l.bk) l.hR
  have hs : Spec.Gcm.ctxH t.mem (K o) = Spec.Gcm.ctxH o.mem (K o) :=
    blockAt_frame h.frame (fun w hw => (apart l.bk w hw).sub_left (Lay.ctxSub (by decide)))
  have n := bytesAt_frame h.frame (apart l.bn) (Nat.le_of_lt (o.gpr .x3).isLt)
  have aad := bytesAt_frame h.frame (apart l.ba) (Nat.le_of_lt (o.gpr .x5).isLt)
  change gatherPost t.callEntry v at out
  unfold gatherPost at out ⊢
  rw [f.pt] at out
  change (Spec.Gcm.encryptWith _ _ _ _ _ _ = (Spec.Aes.bytesAt v.mem (stackArg t 0) (stackArg t 1).toNat,Spec.Aes.bytesAt v.mem (stackArg t 2) 16)) at out
  simp only [K,Nn,NL,Ad,AL,State.callEntry_mem,h.g .x0 (by decide) (by decide),h.g .x1 (by decide) (by decide),
    h.g .x2 (by decide) (by decide),h.g .x3 (by decide) (by decide),h.g .x4 (by decide) (by decide),h.g .x5 (by decide) (by decide),
    h.args 0 (by decide),h.args 1 (by decide),h.args 2 (by decide)] at out
  rw [cip,hs,n,aad] at out
  exact out

theorem postFrame {o t v : State} (l : Gather.Lay .plain o) (out : gatherPost o t) {bytes : Nat} (hb : bytes ≤ 2592)
    (f : Frame [below o.sp bytes] t.mem v.mem) : gatherPost o v := by
  have sub : (below o.sp bytes).Sub (stkR o) := Offset.sub_below _ hb (by omega)
  have apart {r : Region} (h : (stkR o).Disjoint r) : ∀ w ∈ [below o.sp bytes], r.Disjoint w := by
    simpa only [List.mem_singleton,forall_eq] using (h.sub_left sub).symm
  unfold gatherPost at out ⊢
  rwa [bytesAt_frame f (apart l.bd) (Nat.le_of_lt (stackArg o 1).isLt),bytesAt_frame f (apart l.bt) (by decide)]

theorem Entered.within {o t : State} (h : Entered o t) {lim : Nat} (rr : recordWithin lim o) :
    recordWithin lim (view t.callEntry) := by
  change (t.callEntry.gpr .x3).toNat = 12 ∧ (t.callEntry.gpr .x5).toNat ≤ 16 ∧ (stackArg t 1).toNat ≤ lim
  rw [h.g .x3 (by decide) (by decide),h.g .x5 (by decide) (by decide),h.args 1 (by decide)]
  exact rr

theorem shortFrame_ok (hash : HashEightOk) {o : State} (l : Gather.Lay .plain o) (rr : shortRecord o) :
    WP isa (callFrame gatherSetup shortName Impl.AesGcm.AArch64.DirectGather.shortWork
      Impl.AesGcm.AArch64.DirectGather.shortBody) o fun v => abiPreserved o v ∧ gatherPost o v := by
  apply callReady_ok hash (by have := l.w₁; omega) _ (by decide +kernel)
  refine (enter o l).mono ?_
  intro t h
  obtain ⟨read,write⟩ := h.covers l
  have f := h.facts l
  have sub : (⟨t.sp,32⟩ : Region).Sub (stkR o) := by
    rw [h.sp]; exact Offset.sub_below _ (by decide) (by decide)
  refine ⟨⟨h.pre l,h.within rr⟩,read,write,h.sp,h.wr,?_,h.link,?_,?_,
    fun u p _ fr => postFrame l (h.post l p) (by decide) fr⟩
  · exact fun r hr => h.regs r ((by decide : ∀ x ∈ preserved, x ∉ [.x9,.x10,.x11]) r hr)
  · rw [f.d]; exact l.bd.sub_left sub
  · rw [f.tag]; exact l.bt.sub_left sub

theorem Entered.public {a b t u : State} (ha : Entered a t) (hb : Entered b u)
    (la : Gather.Lay .plain a) (lb : Gather.Lay .plain b) (pub : gatherPub a b) :
    gatherPub (view t.callEntry) (view u.callEntry) := by
  obtain ⟨g0,g1,g2,g3,g4,g5,g6,g7,sp,dit,a0,a1,a2,bytes⟩ := pub
  have g (r : Reg) (hr : r ∉ [.x9,.x10,.x11]) (hl : r ∉ linkRegs) (eq : a.gpr r = b.gpr r) :
      t.callEntry.gpr r = u.callEntry.gpr r := (ha.g r hr hl).trans (eq.trans (hb.g r hr hl).symm)
  refine ⟨g .x0 (by decide) (by decide) g0,g .x1 (by decide) (by decide) g1,
    g .x2 (by decide) (by decide) g2,g .x3 (by decide) (by decide) g3,g .x4 (by decide) (by decide) g4,
    g .x5 (by decide) (by decide) g5,g .x6 (by decide) (by decide) g6,g .x7 (by decide) (by decide) g7,
    by change t.sp=u.sp; rw [ha.sp,hb.sp,sp],ha.dit.trans (dit.trans hb.dit.symm),
    (ha.args 0 (by decide)).trans (a0.trans (hb.args 0 (by decide)).symm),
    (ha.args 1 (by decide)).trans (a1.trans (hb.args 1 (by decide)).symm),
    (ha.args 2 (by decide)).trans (a2.trans (hb.args 2 (by decide)).symm),?_⟩
  change ∀ i < Cnt t.callEntry*16, t.mem (t.callEntry.gpr .x6 + BitVec.ofNat 64 i) =
    u.mem (t.callEntry.gpr .x6 + BitVec.ofNat 64 i)
  rw [Cnt,ha.g .x6 (by decide) (by decide),ha.g .x7 (by decide) (by decide)]
  intro i hi
  have inA : (dsR a).Contains (Src a+BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by change i+1 ≤ (a.gpr .x7).toNat*16; omega)
      (by have lim := descriptors_lt (BoundedLay.ofGather la); change 16*(a.gpr .x7).toNat < 2^64 at lim; omega)
  have inB : (dsR b).Contains (Src a+BitVec.ofNat 64 i) 1 := by simpa only [dsR,Cnt,Src,←g6,←g7] using inA
  exact ((local32 ha).agree (BoundedLay.ofGather la).bds inA).trans ((bytes i hi).trans
    ((local32 hb).agree (BoundedLay.ofGather lb).bds inB).symm)

theorem shortFrame_rel (hash : HashEightOk) {a b : State} (la : Gather.Lay .plain a) (lb : Gather.Lay .plain b)
    (ra : shortRecord a) (rb : shortRecord b) (pub : gatherPub a b) :
    RelCT isa (Eq2 a b) (callFrame gatherSetup shortName Impl.AesGcm.AArch64.DirectGather.shortWork
      Impl.AesGcm.AArch64.DirectGather.shortBody) TT := by
  have sp := pub.2.2.2.2.2.2.2.2.1
  apply RelCT.alloc (R := TT)
  suffices body : RelCT isa (Eq2 (allocated 32 a) (allocated 32 b)) _ TT from
    body.mono (by rintro x y ⟨_,_,⟨rfl,rfl⟩,rfl,rfl⟩; exact ⟨rfl,rfl⟩) (fun _ _ h => h)
  have asp : (allocated 32 a).sp = (allocated 32 b).sp := by simp only [allocated,sp]
  refine rel_seq (rel_taint [] asp (by simp) ⟨_,by taint_decide⟩) (enter a la) (enter b lb) ?_
  intro t u ht hu
  obtain ⟨tr,tw⟩ := ht.covers la
  obtain ⟨ur,uw⟩ := hu.covers lb
  exact callReturn_rel hash ⟨ht.pre la,ht.within ra⟩ ⟨hu.pre lb,hu.within rb⟩ (ht.public hu la lb pub) tr tw ur uw

theorem shortCaller_verified (hash : HashEightOk) : VerifiedScrubbed target (boundedSeal gatherSetup) shortContract 0 := by
  let raw := callFrame gatherSetup shortName Impl.AesGcm.AArch64.DirectGather.shortWork Impl.AesGcm.AArch64.DirectGather.shortBody
  have checked : Verified target raw shortContract := by
    refine ⟨fun _ h => shortFrame_ok hash (Gather.lay h.1) h.2,ct_of ?_,boundSat_pre 96⟩
    intro a b pa pb pub
    exact shortFrame_rel hash (Gather.lay pa.1) (Gather.lay pb.1) pa.2 pb.2 pub
  have cleanup : ScrubAllOk shortContract 400 0 := by
    refine ⟨fun _ h => by have := (Gather.lay h.1).w₁; omega,fun s t v ps res eq _ =>
      postFrame (Gather.lay ps.1) res (bytes := 400) (by decide) ?_, fun _ _ p => p.2.2.2.2.2.2.2.2.1⟩
    intro a ha
    exact eq a fun bad => ha _ (List.mem_singleton_self _) (by change (a-(below s.sp 400).base).toNat+1 ≤ 400; exact bad)
  exact scrubbedCall checked cleanup (by decide +kernel)

end Forward

namespace Selection
open VG.Proof.AesGcm.AArch64 VG.AArch64.RegUpd

abbrev changed : List Reg := [.x9,.x10,.x11]

structure View (o t : State) : Prop where
  keep : Regs changed o t
  vec : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (o.v r).extractLsb' 0 64
  dit : t.dit = o.dit
  taken : t.gpr .x10 = 0 ↔ boundedArgs o

theorem guard_ok (s : State) : WP isa (.block guard) s (View s) := by
  have run : WP isa (.block guard) s fun t => (t.gpr .x10 = 0 ↔ boundedArgs s) ∧ Regs changed s t := by
    refine WP.of_runBlock ⟨_,by unfold VG.Impl.AesGcm.AArch64.DirectGather.Contiguous.guard; arun [gpr_addWithCarry,sp_addWithCarry,rd_addWithCarry,wr_addWithCarry,mem_addWithCarry],?_,?_⟩
    · simp only [gpr_write,gpr_addWithCarry,c_addWithCarry,Size.bits,BitVec.setWidth_eq,ite_true,ite_false,
        reduceCtorEq,Bool.toNat_true,BitVec.shiftLeft_zero,decide_eq_true_eq,boundedArgs]
      have aad : (~~~BitVec.setWidth 64 17#16).toNat = 2^64-18 := by decide
      have len : (~~~BitVec.setWidth 64 97#16).toNat = 2^64-98 := by decide
      simp only [aad,len]
      split
      · simp; omega
      · split
        · simp; omega
        · have eq := BitVec.sub_eq_iff_eq_add (x := s.gpr .x3) (y := 12) (z := 0)
          simp at eq
          have size : (s.gpr .x3 = 12) ↔ (s.gpr .x3).toNat = 12 := by
            constructor
            · intro h; rw [h]; decide
            · intro h; exact BitVec.eq_of_toNat_eq h
          exact ⟨fun h => ⟨size.mp (eq.mp h),by omega,by omega⟩,fun h => eq.mpr (size.mpr h.1)⟩
    · refine ⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩
      simp only [changed,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      simp [gpr_write,gpr_addWithCarry,hr.1,hr.2.1,hr.2.2]
  obtain ⟨tr,t,exec,hit,keep⟩ := run
  exact ⟨tr,t,exec,keep,Exec.preservedV exec (by lit_decide),Exec.dit (by lit_decide) exec,hit⟩

abbrev whole := Spec.Gcm.sealWithPowersContract abi 1056

abbrev inputs (s : State) : List Addr := argRegs.map s.gpr ++ (List.range 2).map (stackArg s)

theorem View.values_eq {o t : State} (v : View o t) : inputs t = inputs o := by
  unfold inputs; congr 1
  · apply List.map_congr_left
    intro r hr
    exact v.keep.others r ((by decide : ∀ r ∈ argRegs, r ∉ changed) r hr)
  · apply List.map_congr_left
    intro j _
    simp only [stackArg,stackArgAddr,v.keep.mem,v.keep.sp]


abbrev widths := (Spec.Gcm.sealWithPowersSig.words abi.ptrBits).map (·.bits abi.ptrBits)
theorem argValues : abi.args widths = some inputs := rfl

theorem View.pre {o t : State} (v : View o t) (hp : whole.pre o) : whole.pre t := by
  simp only [whole,Spec.Gcm.sealWithPowersContract,Sig.contract,argValues] at hp ⊢
  simpa only [v.values_eq,abi,stackArgAddr,v.keep.sp,v.keep.rd,v.keep.wr,v.keep.mem] using hp

theorem View.post {o t u : State} (v : View o t) (hp : whole.post t u) : whole.post o u := by
  simp only [whole,Spec.Gcm.sealWithPowersContract,Sig.contract,argValues] at hp ⊢
  simpa only [v.values_eq,abi,v.keep.mem] using hp

theorem View.pub {a b t u : State} (v : View a t) (w : View b u) (p : whole.pub a b) : whole.pub t u := by
  simp only [whole,Spec.Gcm.sealWithPowersContract,Sig.contract,argValues] at p ⊢
  simpa only [v.values_eq,w.values_eq,abi,v.keep.sp,w.keep.sp,v.dit,w.dit,v.keep.mem,w.keep.mem] using p

theorem View.abi {o t u : State} (v : View o t) (h : abiPreserved t u) : abiPreserved o u :=
  ⟨fun r hr => (h.1 r hr).trans (v.keep.others _ ((by decide : ∀ r ∈ preserved, r ∉ changed) _ hr)),
    h.2.1.trans v.keep.sp, fun r hr => (h.2.2 r hr).trans (v.vec r hr)⟩

theorem View.bounded {o t : State} (v : View o t) (h : boundedArgs o) : boundedArgs t := by
  simpa only [boundedArgs,v.keep.others .x3 (by decide),v.keep.others .x5 (by decide),v.keep.others .x7 (by decide)] using h

theorem View.eval {o t : State} (v : View o t) : isa.eval (.zero .x .x10) t = some (decide (boundedArgs o)) := by
  change some (t.gpr .x10 == (0 : Addr)) = _
  congr 1
  by_cases e : boundedArgs o
  · simp [e,v.taken.mpr e]
  · simp [e]; exact fun h => e (v.taken.mp h)

theorem sealPub {a b : State} (p : whole.pub a b) : onePub 2 a b ∧ a.dit = b.dit := by
  sig_pub_keep [whole,Spec.Gcm.sealWithPowersContract,Spec.Gcm.sealWithPowersSig,Spec.Gcm.sealSig,
    Spec.Gcm.withPowersParam,abi,argRegs,stackWords,List.cons_append,List.nil_append] at p
  simp only [List.getD_cons_succ,List.getD_cons_zero] at p
  obtain ⟨sp,dit,p0,p1,p2,p3,p4,p5,p6,p7,a0,a1⟩ := p
  refine ⟨⟨p0,p1,p2,p3,p4,p5,p6,p7,sp,?_⟩,dit⟩
  intro j hj
  have ij : j=0 ∨ j=1 := by omega
  rcases ij with rfl|rfl
  · exact a0
  · exact a1

theorem sealResult {o u : State} (out : (sealAArch64).post o u) : whole.post o u := by
  sig_post [whole,Spec.Gcm.sealWithPowersContract,Spec.Gcm.sealWithPowersSig,Spec.Gcm.sealSig,
    Spec.Gcm.withPowersParam,Spec.Gcm.sealWithPowersPost,Spec.Gcm.sealPost,abi,argRegs,stackWords,
    List.cons_append,List.nil_append]
  exact Proof.AesGcm.sealPost_imp 64 _ _ _ _ _ _ _ _ _ _ _ (0 : BitVec 0) (fun _ => out)

theorem sameKind {a b : State} (p : whole.pub a b) : boundedArgs a ↔ boundedArgs b := by
  obtain ⟨⟨_,_,_,x3,_,x5,_,x7,_,_⟩,_⟩ := sealPub p
  simp only [boundedArgs,x3,x5,x7]

theorem selected_ok {other : Prog isa} (hash : HashEightOk) (hv : Verified target other whole)
    {o : State} (hp : whole.pre o) : WP isa (selectSeal other) o fun u => abiPreserved o u ∧ whole.post o u := by
  refine WP.seq ((guard_ok o).mono ?_)
  intro t v
  have hpt := v.pre hp
  apply WP.ite (b := decide (boundedArgs o)) v.eval
  · intro yes
    have short : shortCallerContract.pre t := ⟨caller_of_pre hpt,v.bounded (of_decide_eq_true yes)⟩
    exact (show WP isa (boundedSeal setup) t _ from
      (shortCaller_verified hash ⟨t,short⟩).verified.1 t short).mono fun u out => ⟨v.abi out.1,v.post (sealResult out.2)⟩
  · intro _
    exact (show WP isa other t _ from hv.1 t hpt).mono fun u out => ⟨v.abi out.1,v.post out.2⟩

theorem selected_rel {other : Prog isa} (hash : HashEightOk) (hv : Verified target other whole)
    {a b : State} (pa : whole.pre a) (pb : whole.pre b) (pub : whole.pub a b) : RelCT isa (Eq2 a b) (selectSeal other) TT := by
  have pubs := sealPub pub
  refine rel_seq (rel_taint [.x3,.x5,.x7] pubs.1.2.2.2.2.2.2.2.2.1
    (by obtain ⟨⟨_,_,_,q3,_,q5,_,q7,_⟩,_⟩ := pubs; agree_tac [q3,q5,q7]) ⟨_,by taint_decide⟩)
    (guard_ok a) (guard_ok b) ?_
  intro t u v w
  have same := sameKind pub
  have e : decide (boundedArgs a) = decide (boundedArgs b) := by simp only [same]
  refine rel_ite v.eval (e ▸ w.eval) ?_ ?_
  · intro take
    have qa : shortCallerContract.pre t := ⟨caller_of_pre (v.pre pa),v.bounded (of_decide_eq_true take)⟩
    have qb : shortCallerContract.pre u := ⟨caller_of_pre (w.pre pb),w.bounded (same.mp (of_decide_eq_true take))⟩
    intro x y τ υ x' y' ⟨rfl,rfl⟩ ea eb
    exact ⟨(shortCaller_verified hash ⟨_,qa⟩).verified.2.1 _ _ _ _ _ _ qa qb (sealPub (v.pub w pub)) ea eb,trivial⟩
  · intro _
    intro x y τ υ x' y' ⟨rfl,rfl⟩ ea eb
    exact ⟨hv.2.1 _ _ _ _ _ _ (v.pre pa) (w.pre pb) (v.pub w pub) ea eb,trivial⟩

theorem selected_scrubbed (hash : HashEightOk) {other : Prog isa} (base : VerifiedScrubbed target other whole 0) :
    VerifiedScrubbed target (selectSeal other) whole 0 := by
  refine ⟨⟨fun _ => selected_ok hash base.verified,ct_of (fun _ _ => selected_rel hash base.verified),base.verified.2.2⟩,?_⟩
  intro a b τ υ x y pa pb pub outside unknown ea eb
  cases ea with | seq ga ba =>
   cases eb with | seq gb bb =>
    obtain ⟨_,_,xa,va⟩ := guard_ok a
    obtain ⟨_,_,xb,vb⟩ := guard_ok b
    obtain ⟨_,rfl⟩ := Exec.det xa ga
    obtain ⟨_,rfl⟩ := Exec.det xb gb
    have pu := va.pub vb pub
    have ou := Residue.noResidue_of_blind (c := (.block guard)) (by decide +kernel)
      (⟨fun _ => True,fun _ _ => True,fun _ _ => True,none⟩ : Contract isa) 0 _ _ _ _ _ _ trivial trivial trivial outside unknown ga gb
    obtain ⟨_,ua,ub⟩ := execBlock_unknowns (Exec.block_eq (T := target) ga) (Exec.block_eq (T := target) gb)
    have un := ua.trans (unknown.trans ub.symm)
    have same := sameKind pub
    cases ba with
    | iteT take yes =>
      have good := of_decide_eq_true (Option.some.inj (va.eval.symm.trans take))
      cases bb with
      | iteT _ yes' =>
        have ac : shortCallerContract.pre _ := ⟨caller_of_pre (va.pre pa),va.bounded good⟩
        have bc : shortCallerContract.pre _ := ⟨caller_of_pre (vb.pre pb),vb.bounded (same.mp good)⟩
        exact (shortCaller_verified hash ⟨_,ac⟩).noResidue _ _ _ _ _ _ ac bc (sealPub pu) ou un yes yes'
      | iteF no _ => rw [vb.eval,decide_eq_true (same.mp good)] at no; cases no
    | iteF skip no =>
      have bad := of_decide_eq_false (Option.some.inj (va.eval.symm.trans skip))
      cases bb with
      | iteT yes _ => rw [vb.eval,decide_eq_false (fun h => bad (same.mpr h))] at yes; cases yes
      | iteF _ no' => exact base.noResidue _ _ _ _ _ _ (va.pre pa) (vb.pre pb) pu ou un no no'

theorem withPowers_scrubbed (hash : HashEightOk) (c : Impl.AesGcm.AArch64.Calls) (w : Impl.AesGcm.AArch64.Fn)
    (base : VerifiedScrubbed target (Impl.AesGcm.AArch64.Fn.sealWithPowers c w)
      (Spec.Gcm.sealWithPowersContract abi (c.pwWn+32)) 0) :
    VerifiedScrubbed target (VG.Impl.AesGcm.AArch64.DirectGather.Contiguous.sealWithPowers c w)
      (Spec.Gcm.sealWithPowersContract abi (c.pwWn+32)) 0 := by
  unfold VG.Impl.AesGcm.AArch64.DirectGather.Contiguous.sealWithPowers
  split
  next enabled =>
    simp only [Bool.and_eq_true,beq_iff_eq] at enabled
    have size : c.pwWn = 1024 := by simp [Impl.AesGcm.AArch64.Calls.pwWn,enabled]
    rw [size] at base ⊢
    exact selected_scrubbed hash base
  next => exact base

end Selection

end VG.Proof.AesGcm.AArch64.DirectGather.Contiguous
