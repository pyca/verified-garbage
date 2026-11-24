module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Standalone
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.General
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GeneralFrame
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.LeafCT
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.DirectBody
public import VerifiedGarbage.Proof.AesGcm.AArch64.Crypt
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Standalone
import VerifiedGarbage.Proof.AesGcm.AArch64.OneEntry
public import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Set up the single contiguous plaintext and ciphertext ranges for arbitrary nonce lengths. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Standalone
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Impl.StackScratch.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous.Standalone
open DirectGather (genBase genWork genStack genState genArgAddr)
abbrev slotR (p : Addr) (n : Nat) : Region := ⟨p+BitVec.ofNat 64 n,8⟩
structure FrameIn (o s : State) (wn : Nat) : Prop where
  bound : wn ≤ 2560
  frame : Frame [⟨genBase o wn,32⟩] o.mem s.mem
  regs : ∀ r, r ≠ .x16 → r ≠ .x17 → s.gpr r = o.gpr r
  sp : s.sp = genBase o wn
  rd : s.rd = o.rd
  wr : s.wr = genStack o wn :: o.wr
  args : ∀ i < 2, s.mem.readW (s.sp+BitVec.ofNat 64 (8*i)) 64 = stackArg o i
  work : s.mem.readW (s.sp+16#64) 64 = genWork o wn

theorem pushed {o : State} {wn : Nat} (c : Caller o) (hb : wn ≤ 2560)
    (align : wn % 16 = 0) :
    let a := allocated (wn+32) o
    execBlock isa (setArgs (wn+32) 2) a =
      some (setArgsState (wn+32) 2 a,setArgsTrace (wn+32) a.sp 2) ∧
      FrameIn o (setArgsState (wn+32) 2 a) wn := by
  let a := allocated (wn+32) o
  have hr (i : Nat) (hi : i < 2) : InRegions (a.rd ++ a.wr) (a.sp+BitVec.ofNat 64 ((wn+32)+8*i)) 8 := by
    change InRegions (o.rd ++ a.wr) (genBase o wn + BitVec.ofNat 64 ((wn+32)+8*i)) 8
    rw [genArgAddr]
    obtain ⟨r,hr,loc⟩ := c.read _ _ ⟨callerArgs o,by simp,DirectGather.stackArg_contains o i (by omega)⟩
    exact ⟨r,by rcases List.mem_append.mp hr with l|w; exact List.mem_append_left _ l; exact List.mem_append_right _ (List.mem_cons_of_mem _ w),loc⟩
  have hw (i : Nat) (hi : i ≤ 2) : InRegions a.wr (a.sp+BitVec.ofNat 64 (8*i)) 8 :=
    ⟨_,List.mem_cons_self ..,Offset.contains_base _ (by change 8*i+8 ≤ wn+32; omega) (by omega)⟩
  obtain ⟨run,frame,args,work⟩ := setArgs_run (bytes := wn+32) (m := 2) (u := a)
    (by omega) (by omega) (by change 32 ≤ wn+32; omega) hr hw
  refine ⟨run,hb,frame.sub (fun r hr => ⟨_,.head _,List.mem_singleton.mp hr ▸ Region.sub_prefix (by decide : 24≤32)⟩),fun r h j => setArgsState_gpr _ _ _ h j,setArgsState_sp ..,
    setArgsState_rd ..,setArgsState_wr ..,?_,?_⟩
  · intro i hi
    rw [setArgsState_sp,args i hi]
    change o.mem.readW (genBase o wn + BitVec.ofNat 64 ((wn+32)+8*i)) 64 = _
    rw [genArgAddr]; rfl
  · rw [setArgsState_sp]; exact work

structure Inner (wn : Nat) (W : Addr) (o : State) : Prop where
  lay : Lay wn (o.gpr .x0) (W+16#64) W
  perm : Perm wn (o.gpr .x0) (W+16#64) W o
  hw : stackArg o 2 = W
  args : ∀ i < 3, InRegions (o.rd++o.wr) (stackArgAddr o i) 8
  apart : ∀ i < 2, (slotR o.sp (8*i)).Disjoint (workR wn W)
  nr : rounds (o.gpr .x1)
  iv : DataOk wn (W+16#64) W o (o.gpr .x2) (o.gpr .x3).toNat
  aad : DataOk wn (W+16#64) W o (o.gpr .x4) (o.gpr .x5).toNat
  src : DataOk wn (W+16#64) W o (o.gpr .x6) (stackArg o 0).toNat
  dst : DataW wn (o.gpr .x0) (W+16#64) W o (o.gpr .x7) (stackArg o 0).toNat
  mode : BufferLayout (o.gpr .x6) (o.gpr .x7) (stackArg o 0).toNat
  tag : Covers [tagR o] o.wr
  tagWork : (tagR o).Disjoint (workR wn W)
  dstTag : (dstR o).Disjoint (tagR o)
  tagData : DataW wn (o.gpr .x0) (W+16#64) W o (stackArg o 1) 16

theorem inner {o s : State} {wn : Nat} (c : Caller o) (e : FrameIn o s wn)
    (lo : 768 ≤ wn) : Inner wn (genWork o wn) s := by
  have lim := e.bound
  have sub : (genStack o wn).Sub (below o.sp 2640) := Offset.sub_below _ (by omega) (by omega)
  have wk : (workR wn (genWork o wn)).Sub (genStack o wn) := Offset.sub_base (genBase o wn) (by change 32+wn≤wn+32; omega)
  have st := DirectGather.genState_sub o lo
  have apart (r : Region) (hr : r ∈ externalRegions o) : r.Disjoint (workR wn (genWork o wn)) :=
    ((c.stack _ hr).symm.sub_right sub).sub_right wk
  have ctx := apart (Gather.kR .plain o) (by simp [externalRegions])
  have lay := DirectGather.recordLay lim lo ctx (c.nowrap (Gather.kR .plain o) (by simp [externalRegions]))
    (by have := c.room; omega)
  have widen : Covers (o.rd++o.wr) (s.rd++s.wr) := Covers.of_mem fun r hr => by
    rw [e.rd,e.wr]; rcases List.mem_append.mp hr with l|w
    · exact List.mem_append_left _ l
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ w)
  have widenW : Covers o.wr s.wr := Covers.of_mem fun r hr => by rw [e.wr]; exact List.mem_cons_of_mem _ hr
  have read (r : Region) (hr : r ∈ [Gather.kR .plain o,Gather.nR o,Gather.aR o,srcR o,callerArgs o]) : Covers [r] (s.rd++s.wr) :=
    (Covers.of_mem (by simpa only [List.mem_singleton,forall_eq] using hr)).trans (c.read.trans widen)
  have write (r : Region) (hr : r ∈ [dstR o,tagR o]) : Covers [r] s.wr :=
    (Covers.of_mem (by simpa only [List.mem_singleton,forall_eq] using hr)).trans (c.write.trans widenW)
  have cover : Covers [workR wn (genWork o wn)] s.wr := by
    rw [e.wr]; exact Covers.of_sub fun r hr => List.mem_singleton.mp hr ▸ ⟨_,List.mem_cons_self ..,32,rfl,by change 32+wn≤wn+32; omega⟩
  have perm : Perm wn (o.gpr .x0) (genState o wn) (genWork o wn) s :=
    ⟨read _ (by simp),covers_off cover (by omega) (by omega),cover,lo,lim⟩
  have arg (i : Nat) (hi : i < 3) : InRegions (s.rd++s.wr) (stackArgAddr s i) 8 := by
    rw [e.wr,stackArgAddr,e.sp]; exact ⟨_,List.mem_append_right _ (List.mem_cons_self ..),Offset.contains_base _
      (by change 8*i+8≤wn+32; omega) (by omega)⟩
  have argSep {i : Nat} (hi : i+8 ≤ 32) : (slotR s.sp i).Disjoint (workR wn (genWork o wn)) := by
    rw [e.sp]; exact Offset.disjoint (genBase o wn) (e := 32) (.inl hi) (by omega) (by omega)
  have data (r : Region) (hr : r ∈ externalRegions o) (lt : r.len < 2^64) (rd : Covers [r] (s.rd++s.wr)) :
      DataOk wn (genState o wn) (genWork o wn) s r.base r.len :=
    ⟨rd,lt,c.nowrap _ hr,(apart r hr).sub_right st,apart r hr⟩
  have nonce := data (Gather.nR o) (by simp [externalRegions]) (o.gpr .x3).isLt (read _ (by simp))
  have aad := data (Gather.aR o) (by simp [externalRegions]) (o.gpr .x5).isLt (read _ (by simp))
  have source := data (srcR o) (by simp [externalRegions]) (stackArg o 0).isLt (read _ (by simp))
  have dst := data (dstR o) (by simp [externalRegions]) (stackArg o 0).isLt (covers_left (write _ (by simp)))
  have regs : ∀ r ∈ [Reg.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7], s.gpr r = o.gpr r :=
    fun r hr => e.regs _ (by intro h; subst r; contradiction) (by intro h; subst r; contradiction)
  have args (i : Nat) (h : i<2) : stackArg s i = stackArg o i := e.args i h
  have mode : BufferLayout (o.gpr .x6) (o.gpr .x7) (stackArg o 0).toNat :=
    c.sd.elim Or.inr (fun h => Or.inl h.symm)
  constructor <;> try simp only [regs .x0 (by decide),regs .x1 (by decide),regs .x2 (by decide),regs .x3 (by decide),regs .x4 (by decide),
    regs .x5 (by decide),regs .x6 (by decide),regs .x7 (by decide),tagR,dstR,
    args 0 (by decide),args 1 (by decide)]
  · exact lay
  · exact perm
  · exact e.work
  · exact arg
  · intro i hi; exact argSep (by omega)
  · exact c.rounds
  · simpa only [genState,Gather.nR,Gather.NL,Gather.Nn] using nonce
  · exact aad
  · exact source
  · exact ⟨dst,write (dstR o) (by simp),c.kd⟩
  · exact mode
  · exact write (tagR o) (by simp)
  · exact apart (tagR o) (by simp [externalRegions])
  · exact c.dt
  · exact ⟨data (tagR o) (by simp [externalRegions]) (by change 16<2^64; decide) (covers_left (write _ (by simp))),write _ (by simp),c.kt⟩


structure Entry (wn : Nat) (W : Addr) (s u : State) : Prop where
  env : Env wn (s.gpr .x0) (W+16#64) W s.sp u
  x22 : u.gpr .x22 = s.gpr .x1
  x23 : u.gpr .x23 = s.gpr .x2
  x24 : u.gpr .x24 = s.gpr .x3
  x26 : u.gpr .x26 = s.gpr .x3
  x27 : u.gpr .x27 = 0
  x28 : u.gpr .x28 = stackArg s 1
  aad : u.mem.readW (W+216#64) 64 = s.gpr .x4
  alen : u.mem.readW (W+224#64) 64 = s.gpr .x5
  src : u.mem.readW (W+232#64) 64 = s.gpr .x6
  len : u.mem.readW (W+240#64) 64 = stackArg s 0
  tag : u.mem.readW (W+248#64) 64 = stackArg s 1
  dst : u.mem.readW (W+336#64) 64 = s.gpr .x7
  saved : SavedAt u.mem W s
  frame : Frame [workR wn W] s.mem u.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr

theorem entry_ok {wn : Nat} {W : Addr} {s : State} (c : Inner wn W s) :
    WP isa (.block entry) s (Entry wn W s) := by
  obtain bounds := c.lay.hWn
  unfold entry
  rw [List.append_assoc,WP.block_append_iff]
  refine (oneEntry_args (k := 16) (by decide) c.hw (c.args 2 (by decide)) rfl c.perm).mono ?_
  intro a ⟨env,ar,an,al,ac,az,aad,alen,src,_,f,saved,rd,wr,_,a7⟩
  have fa : Frame [workR wn W] s.mem a.mem :=
    f.sub fun r hr => ⟨_,.head _,entryR_work W bounds r hr⟩
  let q := a.mem.writeW (W+336#64) (s.gpr .x7)
  let b := {(a.write .x .x9 (stackArg s 0)) with mem := q.writeW (W+240#64) (stackArg s 0)}
  have sw (m : Mem) (d : Nat) (hd : d+8 ≤ wn) (v : Addr) :
      Frame [workR wn W] m (m.writeW (W+BitVec.ofNat 64 d) v) :=
    (Frame.refl _ _).writeW (.head _) _ (Offset.contains_base _ hd (by omega))
  have fq : Frame [workR wn W] s.mem q := fa.trans (sw _ 336 (by omega) _)
  have fb : Frame [workR wn W] s.mem b.mem := fq.trans (sw _ 240 (by omega) _)
  have arg0 : q.read a.sp 8 = stackArg s 0 := by
    rw [env.sp]
    have read : q.readW (s.sp+0#64) 64 = s.mem.readW (s.sp+0#64) 64 := fq.readW (r := slotR s.sp 0) (Region.contains_self _ _)
      (by simpa only [List.mem_singleton,forall_eq] using c.apart 0 (by decide)) (by decide : 64/8<2^64)
    simpa [Mem.readW,stackArg,stackArgAddr] using read
  have ir0 : InRegions (a.rd++a.wr) a.sp 8 := by
    rw [rd,wr,env.sp]; simpa [stackArgAddr] using c.args 0 (by decide)
  have wa (d : Nat) (hd : d+8≤wn) : InRegions a.wr (W+BitVec.ofNat 64 d) 8 := in_off env.perm.w hd (by omega)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨b,?_,?_⟩
  · simp only [q,Mem.writeW,BitVec.setWidth_eq] at arg0
    arun [b,q,BitVec.add_zero,env.x19,a7,DirectGather.descO,lenO,wa 336 (by omega),wa 240 (by omega),ir0,arg0,Mem.writeW]
  have arg1 : b.mem.readW (b.sp+8#64) 64 = stackArg s 1 := by
    change b.mem.readW (a.sp+8#64) 64 = _; rw [env.sp]
    exact fb.readW (r := slotR s.sp 8) (Region.contains_self _ _)
      (by simpa only [List.mem_singleton,forall_eq] using c.apart 1 (by decide)) (by decide)
  refine (stashArg_ok (k := 8) (by decide) (s := b) (by simpa [b,gpr_write] using env.x19) env.perm.w
    (by change InRegions (a.rd++a.wr) (a.sp+8#64) 8; rw [rd,wr,env.sp];exact c.args 1 (by decide))
    arg1 bounds).mono ?_
  intro u ⟨tag,um,ug,us,ur,uw⟩
  have regs (r : Reg) (hr : r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x28) : u.gpr r = a.gpr r :=
    (ug r (by simp [hr.2.1,hr.2.2])).trans (by simp [b,gpr_write,hr.1])
  have U : u.mem = (q.writeW (W+240#64) (stackArg s 0)).writeW (W+248#64) (stackArg s 1) := um
  have old (d : Nat) (hd : d+8≤240) : u.mem.readW (W+BitVec.ofNat 64 d) 64 = a.mem.readW (W+BitVec.ofNat 64 d) 64 := by
    rw [U]; unfold q; repeat rw [readW_writeW_other _ W _ (.inl (by omega)) (by omega) (by decide)]
  refine ⟨env.keep (fun r hr => regs r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr;rcases hr with rfl|rfl|rfl <;> decide))
    us ur uw,(regs _ (by decide)).trans ar,(regs _ (by decide)).trans an,(regs _ (by decide)).trans al,
    (regs _ (by decide)).trans ac,(regs _ (by decide)).trans az,tag,(old 216 (by decide)).trans aad,
    (old 224 (by decide)).trans alen,(old 232 (by decide)).trans src,?_,?_,?_,?_,?_,ur.trans rd,uw.trans wr⟩
  · rw [U,readW_writeW_other _ W _ (.inl (by decide)) (by decide) (by decide),Mem.readW_writeW_self64]
  · rw [U,Mem.readW_writeW_self64]
  · rw [U,readW_writeW_other _ W _ (.inr (by decide)) (by decide) (by decide),
      readW_writeW_other _ W _ (.inr (by decide)) (by decide) (by decide)]
    exact Mem.readW_writeW_self64 ..
  · intro d hd
    rw [old _ (by
      simp only [VG.Impl.AesGcm.AArch64.saved,List.mem_cons,List.not_mem_nil,or_false] at hd
      rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
    exact saved _ hd
  · rw [U]; exact fb.trans (sw _ 248 (by omega) _)

theorem entry_rel {wn : Nat} {W : Addr} {a b : State} (ca : Inner wn W a) (cb : Inner wn W b) (sp : a.sp=b.sp) :
    RelCT isa (Eq2 a b) (.block entry) TT := by
  let head : List Instr := [.ldrSp .x9 16]
  have run {o : State} (c : Inner wn W o) : WP isa (.block head) o fun z => z.gpr .x9 = W ∧ z.sp=o.sp := by
    have read : o.mem.read (o.sp+16#64) 8 = W := c.hw
    have slot : InRegions (o.rd++o.wr) (o.sp+16#64) 8 := c.args 2 (by decide)
    refine WP.of_runBlock ⟨o.write .x .x9 W,by arun [head,slot,read],?_,rfl⟩
    simp [gpr_write]
  change RelCT isa _ (.block (head ++ ((oneEntry 16).tail ++ [.str .x .x7 .x19 DirectGather.descO,
      .ldrSp .x9 0,.str .x .x9 .x19 lenO] ++ stashArg 8))) _
  apply VG.RelCT.block_append
  refine rel_seq (rel_taint [] sp (by agree_tac []) ⟨.block [] 256,by decide⟩) (run ca) (run cb) ?_
  intro x y ⟨hx,sx⟩ ⟨hy,sy⟩
  exact rel_taint [.x9] (sx.trans (sp.trans sy.symm)) (by agree_tac [hx,hy]) ⟨_,by taint_decide⟩

theorem entryResult {o s z : State} {wn : Nat} (e : FrameIn o s wn) (c : Caller o) (post : result s z) :
    result o z := by
  have hi := e.bound
  have sub : (genStack o wn).Sub (below o.sp 2640) := Offset.sub_below _ (by omega) (by omega)
  have localSub : (⟨genBase o wn,32⟩ : Region).Sub (genStack o wn) := Region.sub_prefix (by omega)
  have apart {r : Region} (hr : r ∈ externalRegions o) : ∀ w ∈ [⟨genBase o wn,32⟩], r.Disjoint w :=
    by simpa only [List.mem_singleton,forall_eq] using (((c.stack _ hr).symm.sub_right sub).sub_right localSub)
  have key : Spec.Gcm.ctxCiph s.mem (o.gpr .x0) (o.gpr .x1).toNat = Spec.Gcm.ctxCiph o.mem (o.gpr .x0) (o.gpr .x1).toNat :=
    ciph_frame e.frame (apart (r := Gather.kR .plain o) (by simp [externalRegions])) c.rounds
  have hash := blockAt_frame e.frame (fun r hr => (apart (r := Gather.kR .plain o) (by simp [externalRegions]) r hr).sub_left
    (Lay.ctxSub (d := 240) (n := 16) (by decide)))
  change Spec.Gcm.ctxH s.mem (o.gpr .x0) = Spec.Gcm.ctxH o.mem (o.gpr .x0) at hash
  have bytes (r : Region) (hr : r ∈ externalRegions o) (lt : r.len ≤ 2^64) := bytesAt_frame e.frame (apart hr) lt
  have keep : ∀ r ∈ [Reg.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7], s.gpr r = o.gpr r :=
    fun r hr => e.regs _ (by intro h; subst r; contradiction) (by intro h; subst r; contradiction)
  have args (i : Nat) (h : i<2) : stackArg s i = stackArg o i := e.args i h
  unfold result at post ⊢
  rw [keep _ (by decide),keep .x1 (by decide),keep .x2 (by decide),keep .x3 (by decide),keep .x4 (by decide),
    keep .x5 (by decide),keep .x6 (by decide),keep .x7 (by decide),args 0 (by decide),args 1 (by decide),key,hash] at post
  rw [bytes (Gather.nR o) (by simp [externalRegions]) (Nat.le_of_lt (o.gpr .x3).isLt),
    bytes (Gather.aR o) (by simp [externalRegions]) (Nat.le_of_lt (o.gpr .x5).isLt),
    bytes (srcR o) (by simp [externalRegions]) (Nat.le_of_lt (stackArg o 0).isLt)] at post
  exact post

end VG.Proof.AesGcm.AArch64.Contiguous.Standalone
