module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.PreparedSeal
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.General
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Calls
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GeneralFrame
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.LeafCT
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.DirectBody
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.PreparedCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Prepared

/-! The whole prepared machine body. Input, destination, tag and the cached
powers have the same positions for exact alias and disjoint execution. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared
open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous
open VG.Spec.Gcm (ctxH blockAt)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm.AArch64.Pmull (MulKey)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

abbrev nBytes (o : State) := (stackArg o 0).toNat

structure Inner (wn : Nat) (W : Addr) (o : State) : Prop where
  lay : Lay wn (o.gpr .x0) (word W 16) W
  perm : Perm wn (o.gpr .x0) (word W 16) W o
  hw : stackArg o 3 = W
  args : ∀ i < 4, InRegions (o.rd++o.wr) (stackArgAddr o i) 8
  argsWork : (slotR o.sp 8).Disjoint (workR wn W)
  powers : GhWCall o (o.gpr .x0) (word (word W 16) 16) (word W 512) (stackArg o 2)
  ext : External wn (nBytes o) W (o.gpr .x7) (stackArg o 2) o
  nr : rounds (o.gpr .x1)
  iv : DataOk wn (word W 16) W o (o.gpr .x2) 12
  aad : DataOk wn (word W 16) W o (o.gpr .x4) (o.gpr .x5).toNat
  src : DataOk wn (word W 16) W o (o.gpr .x6) (nBytes o)
  dst : DataW wn (o.gpr .x0) (word W 16) W o (o.gpr .x7) (nBytes o)
  mode : BufferLayout (o.gpr .x6) (o.gpr .x7) (nBytes o)
  tag : Covers [tagR o] o.wr
  tagWork : (tagR o).Disjoint (workR wn W)
  dstTag : (dstR o).Disjoint (tagR o)

abbrev Aad (o : State) := bytesAt o.mem (o.gpr .x4) (o.gpr .x5).toNat
abbrev Iv (o : State) := bytesAt o.mem (o.gpr .x2) 12
abbrev PreparedFront (wn : Nat) (W : Addr) (o a t : State) :=
  Fast.FFront wn (o.gpr .x0) (word W 16) W o.sp (ctxH o.mem (o.gpr .x0))
    (Iv o) (Aad o) (o.gpr .x6) (nBytes o) a t

theorem frontWork {wn : Nat} {W : Addr} (lim : 768 ≤ wn) :
    ∀ r ∈ Fast.frontFrame' (word W 16) W, r.Sub (workR wn W) := by
  intro r hr
  simp only [Fast.frontFrame',j0Frame,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with (rfl|rfl|rfl)|rfl
  · exact Lay.wSub (by omega)
  · exact Lay.wSub (by omega)
  · exact Lay.wSub (by omega)
  · exact Lay.wSub (by change 288+32≤wn; omega)

theorem frontSlots {wn : Nat} {Ctx W : Addr} (L : Lay wn Ctx (word W 16) W) {d : Nat} (lo : 216 ≤ d)
    (hi : d+8 ≤ 288 ∨ 320 ≤ d ∧ d+8 ≤ 512) :
    ∀ r ∈ Fast.frontFrame' (word W 16) W, (slotR W d).Disjoint r := by
  have lim := L.hWn
  intro r hr
  simp only [Fast.frontFrame',j0Frame,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with (rfl|rfl|rfl)|rfl
  · exact Offset.disjoint W (.inr (by omega)) (by omega) (by decide)
  · exact Offset.disjoint W (.inr (by omega)) (by omega) (by decide)
  · exact Offset.disjoint W (.inl (by omega)) (by omega) (by decide)
  · exact Offset.disjoint W (by change d+8≤288 ∨ 320≤d; omega) (by omega) (by decide)

theorem fromFront {wn : Nat} {W : Addr} {o a t : State} (c : Inner wn W o) (e : Entry wn o a W)
    (f : PreparedFront wn W o a t) :
    Ready wn (o.gpr .x1).toNat (nBytes o) (o.gpr .x0) W (o.gpr .x6) (o.gpr .x7) (stackArg o 2) (Aad o) (Iv o) t ∧
      External wn (nBytes o) W (o.gpr .x7) (stackArg o 2) t ∧ SavedAt t.mem W o ∧
      Frame [workR wn W] o.mem t.mem := by
  have lim := c.lay.hWn
  have fr := e.frame.trans (f.frame.sub fun r hr => ⟨_,List.mem_singleton_self _,frontWork lim.1 r hr⟩)
  have keep {r : Region} (h : r.Disjoint (workR wn W)) : ∀ w ∈ [workR wn W], r.Disjoint w := by simpa
  have hH : ctxH t.mem (o.gpr .x0) = ctxH o.mem (o.gpr .x0) := f.hH
  have rd := f.rd.trans e.rd
  have wr := f.wr.trans e.wr
  have sp := f.env.sp
  have get (d : Nat) (lo : 216 ≤ d) (hi : d+8 ≤ 288 ∨ 320 ≤ d ∧ d+8 ≤ 512) :=
    f.frame.readW (r := slotR W d) (Region.contains_self _ _) (frontSlots c.lay lo hi) (by decide : 64/8<2^64)
  have call : GhWCall t (o.gpr .x0) (word (word W 16) 16) (word W 512) (stackArg o 2) := by
    refine ⟨by rw [rd,wr]; exact c.powers.reads,c.powers.yp,c.powers.sp,?_⟩
    rw [f.hH]; exact Proof.AesGcm.powers8Repr_congr (fun i hi => fr.bytes (R := ⟨stackArg o 2,128⟩)
      (keep c.ext.powersWork) (show 128≤2^64 by decide) hi) c.powers.repr
  refine ⟨?_,?_,?_,fr⟩
  · refine ⟨sp ▸ f.env,by simpa using f.x22.trans e.x22,f.x23,f.x26,c.nr,
      c.src.of_eq rd wr,c.dst.of_eq rd wr,c.mode,call,?_,?_,(get 232 (by decide) (by decide)).trans e.src,
      (get 320 (by decide) (by decide)).trans e.dst,?_,?_,?_,?_,?_,?_⟩
    · rw [sp]; exact fr.readW (r := slotR o.sp 16) (Region.contains_self _ _) (keep c.ext.slotWork) (by decide)
    · rw [rd,wr,sp]; exact c.args 2 (by decide)
    · simpa only [lenO,nBytes,BitVec.ofNat_toNat,BitVec.setWidth_eq] using (get 240 (by decide) (by decide)).trans e.len
    · simp only [Aad,length_bytesAt,BitVec.ofNat_toNat]; exact (get 224 (by decide) (by decide)).trans e.alen
    · rw [hH]; exact f.j0
    · rw [hH]; exact f.cb
    · rw [hH]; exact f.y
    · rw [hH]; exact f.key
  · exact ⟨c.ext.powersWork,c.ext.powersOut,sp ▸ c.ext.slotWork,sp ▸ c.ext.slotOut⟩
  · apply e.saved.frame f.frame
    intro r hr
    rcases List.mem_append.mp hr with h|h
    · exact saved_j0Frame c.lay r h
    · simp only [List.mem_singleton] at h; subst r
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)

theorem body_ok {wn : Nat} {W : Addr} {o : State} (v : GcmImpl) (g : GhashWithImpl) (fused : Bool)
    (gh : Gh8Ok) (mk : MulKey) (c : Inner wn W o) (hv : v.ctr.scratch ≤ wn-512)
    (hn : (o.gpr .x3).toNat = 12) (ha : (o.gpr .x5).toNat ≤ 16) (hb : fused = true → 128 ≤ nBytes o) :
    WP isa (preparedBody v.callees g.fn fused) o fun z => GprAbi o z ∧ result o z := by
  refine WP.seq ((entry_ok c.hw c.args c.argsWork c.perm).mono ?_)
  intro a e
  refine WP.seq ((front_ok c.lay mk e hn ha c.iv c.aad).mono ?_)
  intro t f
  obtain ⟨q,ext,saved,fr⟩ := fromFront c e f
  have rd := f.rd.trans e.rd
  have wr := f.wr.trans e.wr
  have sp := f.env.sp
  have aLen : (Aad o).length < 2^64 := by rw [Aad,length_bytesAt]; exact (o.gpr .x5).isLt
  have verified := (afterFront_ok v g fused gh mk c.lay q ext hb aLen hv saved sp (by rw [wr]; exact c.tag)
    (f.x28.trans e.x28) c.tagWork c.dstTag).mono (Q' := fun z => GprAbi o z ∧ result o z) (by
      intro z ⟨abi,_,enc⟩
      have key := ciph_frame fr (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact c.lay.cw') c.nr
      have text := bytesAt_frame fr (by simpa only [List.mem_singleton,forall_eq] using c.src.w) (Nat.le_of_lt c.src.lt)
      have hh : ctxH t.mem (o.gpr .x0) = ctxH o.mem (o.gpr .x0) := f.hH
      rw [key,hh,text] at enc
      exact ⟨abi,by unfold result; rw [hn]; exact enc⟩)
  simpa only [afterFront,encPart,finalPart,finishProgram,WP.seq_iff (M := isa)] using verified

end VG.Proof.AesGcm.AArch64.Contiguous.Prepared

/-! ## The prepared seal uses one native call frame, for either buffer layout. -/

namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared
open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous
open VG.Impl.StackScratch.AArch64
open VG.Proof.AesGcm.AArch64.DirectGather (genBase genStack genWork genState RecordEntry)
open VG.Proof.Gcm.AArch64.Pmull (MulKey)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)
open VG.Spec.Aes (bytesAt)

theorem pushed {o : State} {wn : Nat} (c : Caller o) (hi : wn ≤ 2560) (align : wn%16=0) :
    let a := allocated (wn+32) o
    execBlock isa (setArgs (wn+32) 3) a = some (setArgsState (wn+32) 3 a,setArgsTrace (wn+32) a.sp 3) ∧
    RecordEntry o (setArgsState (wn+32) 3 a) wn := by
  apply DirectGather.recordEntry_run o hi _ align
  intro i h
  obtain ⟨r,hr,loc⟩ := c.read _ _ ⟨callerArgs o,by simp,DirectGather.stackArg_contains o i h⟩
  exact ⟨r,by rcases List.mem_append.mp hr with l|w; exact List.mem_append_left _ l; exact List.mem_append_right _ (List.mem_cons_of_mem _ w),loc⟩

theorem inner {o s : State} {wn : Nat} (c : Caller o) (p : Powers o) (e : RecordEntry o s wn)
    (lo : 768 ≤ wn) (iv : (o.gpr .x3).toNat = 12) : Inner wn (genWork o wn) s := by
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
  have arg (i : Nat) (hi : i < 4) : InRegions (s.rd++s.wr) (stackArgAddr s i) 8 := by
    rw [e.wr,stackArgAddr,e.sp]; exact ⟨_,List.mem_append_right _ (List.mem_cons_self ..),Offset.contains_base _
      (by change 8*i+8≤wn+32; omega) (by omega)⟩
  have argSep {i : Nat} (hi : i+8 ≤ 32) : (slotR s.sp i).Disjoint (workR wn (genWork o wn)) := by
    rw [e.sp]; exact Offset.disjoint (genBase o wn) (e := 32) (.inl hi) (by omega) (by omega)
  have localSub := Region.sub_prefix (base := genBase o wn) (show 32 ≤ wn+32 by omega)
  have frame : Frame [genStack o wn] o.mem s.mem := e.frame.sub fun r hr => ⟨_,List.mem_singleton_self _,
    List.mem_singleton.mp hr ▸ localSub⟩
  have powers := p.stack.sub_right sub
  have power : GhWCall s (o.gpr .x0) (word (genState o wn) 16) (word (genWork o wn) 512) (stackArg o 2) := by
    have w := powers.sub_right wk
    refine ⟨p.read.trans widen,(w.sub_right (fun x h => st x ((Lay.stSub (by decide : 16+16≤80)) x h))).symm,
      (w.sub_right (Lay.wSub (by omega))).symm,?_⟩
    rw [blockAt_frame frame (fun r hr => List.mem_singleton.mp hr ▸
      (((c.stack _ (by simp [externalRegions] : Gather.kR .plain o ∈ externalRegions o)).symm.sub_right sub).sub_left (Lay.ctxSub (by decide))))]
    exact Proof.AesGcm.powers8Repr_congr (fun i hi => frame.bytes (R := powerR o)
      (by simpa only [List.mem_singleton,forall_eq] using powers) (show 128≤2^64 by decide) hi) p.repr
  have data (r : Region) (hr : r ∈ externalRegions o) (lt : r.len < 2^64) (rd : Covers [r] (s.rd++s.wr)) :
      DataOk wn (genState o wn) (genWork o wn) s r.base r.len :=
    ⟨rd,lt,c.nowrap _ hr,(apart r hr).sub_right st,apart r hr⟩
  have nonce := data (Gather.nR o) (by simp [externalRegions]) (o.gpr .x3).isLt (read _ (by simp))
  have aad := data (Gather.aR o) (by simp [externalRegions]) (o.gpr .x5).isLt (read _ (by simp))
  have source := data (srcR o) (by simp [externalRegions]) (stackArg o 0).isLt (read _ (by simp))
  have dst := data (dstR o) (by simp [externalRegions]) (stackArg o 0).isLt (covers_left (write _ (by simp)))
  have regs : ∀ r ∈ [Reg.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7], s.gpr r = o.gpr r :=
    fun r hr => e.regs _ (by intro h; subst r; contradiction) (by intro h; subst r; contradiction)
  have args (i : Nat) (h : i<3) : stackArg s i = stackArg o i := e.args i h
  have ex : External wn (nBytes o) (genWork o wn) (o.gpr .x7) (stackArg o 2) s := by
    refine ⟨powers.sub_right wk,p.dst,argSep (by decide),?_⟩
    rw [e.sp]; exact (((c.stack (dstR o) (by simp [externalRegions])).sub_left sub).sub_left (Offset.sub_base _ (by change 16+8≤wn+32; omega)))
  have mode : BufferLayout (o.gpr .x6) (o.gpr .x7) (nBytes o) :=
    c.sd.elim Or.inr (fun h => Or.inl h.symm)
  constructor <;> try simp only [regs .x0 (by decide),regs .x1 (by decide),regs .x2 (by decide),regs .x4 (by decide),
    regs .x5 (by decide),regs .x6 (by decide),regs .x7 (by decide),tagR,dstR,nBytes,
    args 0 (by decide),args 1 (by decide),args 2 (by decide)]
  · exact lay
  · exact perm
  · exact e.work
  · exact arg
  · exact argSep (by decide)
  · exact power
  · exact ex
  · exact c.rounds
  · simpa only [Gather.nR,Gather.NL,Gather.Nn,iv] using nonce
  · exact aad
  · exact source
  · exact ⟨dst,write (dstR o) (by simp),c.kd⟩
  · exact mode
  · exact write (tagR o) (by simp)
  · exact apart (tagR o) (by simp [externalRegions])
  · exact c.dt

theorem entryResult {o s z : State} {wn : Nat} (e : RecordEntry o s wn) (c : Caller o) (post : result s z) :
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
  have args (i : Nat) (h : i<3) : stackArg s i = stackArg o i := e.args i h
  unfold result at post ⊢
  rw [keep _ (by decide),keep .x1 (by decide),keep .x2 (by decide),keep .x3 (by decide),keep .x4 (by decide),
    keep .x5 (by decide),keep .x6 (by decide),keep .x7 (by decide),args 0 (by decide),args 1 (by decide),key,hash] at post
  rw [bytes (Gather.nR o) (by simp [externalRegions]) (Nat.le_of_lt (o.gpr .x3).isLt),
    bytes (Gather.aR o) (by simp [externalRegions]) (Nat.le_of_lt (o.gpr .x5).isLt),
    bytes (srcR o) (by simp [externalRegions]) (Nat.le_of_lt (stackArg o 0).isLt)] at post
  exact post

theorem frame_ok {o : State} (v : GcmImpl) (g : GhashWithImpl) (fused : Bool) (gh : Gh8Ok) (mk : MulKey)
    (c : Caller o) (p : Powers o) (iv : (o.gpr .x3).toNat = 12) (ha : (o.gpr .x5).toNat ≤ 16)
    (hn : fused = true → 128 ≤ nBytes o) (lo : 768 ≤ v.calls.pwWn) (hi : v.calls.pwWn ≤ 2560)
    (align : v.calls.pwWn % 16 = 0) (hv : v.ctr.scratch ≤ v.calls.pwWn-512)
    (keep : (preparedFrame v.calls g.fn fused).allInstrs keepsV = true) :
    WP isa (preparedFrame v.calls g.fn fused) o fun t => abiPreserved o t ∧ result o t := by
  apply WP.withPreservedV (hc := keep)
  obtain ⟨run,e⟩ := pushed c hi align
  have en := inner c p e lo iv
  apply WP.alloc ⟨by omega,by omega,by omega⟩ (by have := c.room; omega)
  refine WP.seq ⟨_,_,Exec.block run,?_⟩
  have nr := e.regs .x3 (by decide) (by decide)
  have al := e.regs .x5 (by decide) (by decide)
  have len := e.args 0 (by decide)
  refine (body_ok v g fused gh mk en hv (by rw [nr]; exact iv) (by rw [al]; exact ha)
    (by intro h; change 128 ≤ (stackArg _ 0).toNat; rw [show stackArg _ 0 = stackArg o 0 from len]; exact hn h)).mono ?_
  intro z ⟨abi,post⟩ m u fr
  have hold : ∀ r ∈ preserved, r ≠ .x16 ∧ r ≠ .x17 := by decide
  exact ⟨⟨fun r hr => (abi.1 r hr).trans (e.regs r (hold r hr).1 (hold r hr).2),
    by change z.sp+BitVec.ofNat 64 (v.calls.pwWn+32) = o.sp
       rw [abi.2,e.sp,genBase,BitVec.sub_add_cancel]⟩,
    result_frame c (by omega) (entryResult e c post) fr⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Prepared

/-! ## Public round counts, lengths and addresses fix the entire trace of
both prepared records, from stack setup through the final return. -/

namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.Contiguous
open VG.Proof.Gcm.AArch64.Pmull (MulKey)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

theorem entry_rel {wn : Nat} {W : Addr} {a b : State} (ca : Inner wn W a) (cb : Inner wn W b) (sp : a.sp = b.sp) :
    RelCT isa (Eq2 a b) (.block preparedArgs) TT := by
  let head : List Instr := [mov .x11 .x7,.ldrSp .x7 0,.ldrSp .x9 24]
  have run {o : State} (c : Inner wn W o) : WP isa (.block head) o fun s => s.gpr .x9 = W ∧ s.sp = o.sp := by
    have ir := c.args 0 (by decide)
    have wr := c.args 3 (by decide)
    change InRegions _ (o.sp+0#64) 8 at ir
    rw [BitVec.add_zero] at ir
    change InRegions _ (o.sp+24#64) 8 at wr
    have w : o.mem.read (o.sp+24#64) 8 = W := c.hw
    refine WP.of_runBlock ⟨((o.write .x .x11 (o.gpr .x7)).write .x .x7 (o.mem.read o.sp 8)).write .x .x9 W,by arun [head,ir,wr,BitVec.add_zero,w],?_,rfl⟩
    simp [gpr_write]
  change RelCT isa _ (.block (head ++ ((oneEntry 24).tail ++ [.str .x .x11 .x19 dstO] ++ stashArg 8))) _
  apply VG.RelCT.block_append
  refine rel_seq (rel_taint [] sp (by agree_tac []) ⟨.block [] 256,by decide⟩) (run ca) (run cb) ?_
  intro x y ⟨x9,sx⟩ ⟨y9,sy⟩
  exact rel_taint [.x9] (sx.trans (sp.trans sy.symm)) (by agree_tac [x9,y9]) ⟨_,by taint_decide⟩

theorem body_rel {wn : Nat} {W : Addr} {a b : State} (v : GcmImpl) (g : GhashWithImpl) (fused : Bool)
    (gh : Gh8Ok) (mk : MulKey) (ca : Inner wn W a) (cb : Inner wn W b) (hv : v.ctr.scratch ≤ wn-512)
    (ai : (a.gpr .x3).toNat = 12) (bi : (b.gpr .x3).toNat = 12)
    (aa : (a.gpr .x5).toNat ≤ 16) (ba : (b.gpr .x5).toNat ≤ 16)
    (hn : fused = true → 128 ≤ nBytes a) (pub : onePub 3 a b) :
    RelCT isa (Eq2 a b) (preparedBody v.callees g.fn fused) TT := by
  obtain ⟨q0,q1,q2,_,q4,q5,q6,q7,sp,stk⟩ := pub
  have size := congrArg BitVec.toNat (stk 0 (by decide))
  refine rel_seq (entry_rel ca cb sp) (entry_ok ca.hw ca.args ca.argsWork ca.perm)
    (entry_ok cb.hw cb.args cb.argsWork cb.perm) ?_
  intro u z e f
  refine rel_seq (rel_taint [.x4,.x5,.x6,.x7,.x19,.x20,.x21,.x23] (e.env.sp.trans (sp.trans f.env.sp.symm))
    (by agree_tac [e.x4,f.x4,e.x5,f.x5,e.x6,f.x6,e.x7,f.x7,e.env.x19,f.env.x19,e.env.x20,f.env.x20,
      e.env.x21,f.env.x21,e.x23,f.x23,q0,q2,q4,q5,q6,stk 0 (by decide)]) ⟨_,by taint_decide⟩)
    (front_ok ca.lay mk e ai aa ca.iv ca.aad) (front_ok cb.lay mk f bi ba cb.iv cb.aad) ?_
  intro t w ft fw
  obtain ⟨x,ex,_,_⟩ := fromFront ca e ft
  obtain ⟨y,ey,_,_⟩ := fromFront cb f fw
  have nr := congrArg BitVec.toNat q1
  have n : nBytes a = nBytes b := size
  have pp := stk 2 (by decide)
  rw [← nr,← n,← q0,← q6,← q7,← pp] at y
  rw [← n,← q7,← pp] at ey
  have x28 := (ft.x28.trans (e.x28.trans (stk 1 (by decide)))).trans (fw.x28.trans f.x28).symm
  have al (o : State) : (Aad o).length < 2^64 := by rw [Aad,length_bytesAt]; exact (o.gpr .x5).isLt
  exact record_rel v g fused gh mk ca.lay x y ex ey (ft.env.sp.trans (sp.trans fw.env.sp.symm)) x28 (al a) (al b) hn hv

theorem frame_rel {a b : State} (v : GcmImpl) (g : GhashWithImpl) (fused : Bool)
    (gh : Gh8Ok) (mk : MulKey) (ca : Caller a) (cb : Caller b) (pa : Powers a) (pb : Powers b)
    (ai : (a.gpr .x3).toNat = 12) (bi : (b.gpr .x3).toNat = 12)
    (aa : (a.gpr .x5).toNat ≤ 16) (ba : (b.gpr .x5).toNat ≤ 16)
    (hn : fused = true → 128 ≤ nBytes a) (lo : 768 ≤ v.calls.pwWn) (hi : v.calls.pwWn ≤ 2560)
    (align : v.calls.pwWn % 16 = 0) (hv : v.ctr.scratch ≤ v.calls.pwWn-512) (pub : onePub 3 a b) :
    RelCT isa (Eq2 a b) (preparedFrame v.calls g.fn fused) TT := by
  let wn := v.calls.pwWn
  let u := setArgsState (wn+32) 3 (allocated (wn+32) a)
  let z := setArgsState (wn+32) 3 (allocated (wn+32) b)
  obtain ⟨ra,e⟩ := pushed ca hi align
  obtain ⟨rb,f⟩ := pushed cb hi align
  obtain ⟨q0,q1,q2,q3,q4,q5,q6,q7,sp,stk⟩ := pub
  have base : DirectGather.genWork a wn = DirectGather.genWork b wn := by simp only [DirectGather.genWork,DirectGather.genBase,sp]
  have sp' : u.sp = z.sp := by rw [e.sp,f.sp,DirectGather.genBase,DirectGather.genBase,sp]
  have eq (r : Reg) (h16 : r ≠ .x16) (h17 : r ≠ .x17) (h : a.gpr r = b.gpr r) : u.gpr r = z.gpr r :=
    (e.regs _ h16 h17).trans (h.trans (f.regs _ h16 h17).symm)
  have pub' : onePub 3 u z :=
    ⟨eq _ (by decide) (by decide) q0,eq _ (by decide) (by decide) q1,eq _ (by decide) (by decide) q2,
      eq _ (by decide) (by decide) q3,eq _ (by decide) (by decide) q4,eq _ (by decide) (by decide) q5,
      eq _ (by decide) (by decide) q6,eq _ (by decide) (by decide) q7,sp',
      fun i hi => (e.args i hi).trans ((stk i hi).trans (f.args i hi).symm)⟩
  apply RelCT.alloc (P := Eq2 a b) (R := TT)
  apply RelCT.seq (R := Eq2 u z)
  · rintro x y tx ty x' y' ⟨_,_,⟨rfl,rfl⟩,rfl,rfl⟩ ex ey
    obtain ⟨rfl,rfl⟩ := Exec.det ex (.block ra)
    obtain ⟨rfl,rfl⟩ := Exec.det ey (.block rb)
    exact ⟨by simp only [allocated,sp],rfl,rfl⟩
  · have p := inner ca pa e lo ai
    have p' := inner cb pb f lo bi
    exact body_rel v g fused gh mk p (base ▸ p') hv (by rw [e.regs .x3 (by decide) (by decide)]; exact ai)
      (by rw [f.regs .x3 (by decide) (by decide)]; exact bi) (by rw [e.regs .x5 (by decide) (by decide)]; exact aa)
      (by rw [f.regs .x5 (by decide) (by decide)]; exact ba) (fun h => by
        change 128 ≤ (stackArg u 0).toNat; rw [show stackArg u 0 = stackArg a 0 from e.args 0 (by decide)]; exact hn h) pub'

end VG.Proof.AesGcm.AArch64.Contiguous.Prepared
