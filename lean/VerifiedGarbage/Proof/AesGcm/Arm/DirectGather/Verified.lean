module

public import VerifiedGarbage.Proof.AesGcm.Arm.ArgSlots
public import VerifiedGarbage.Proof.Framework.Arm.StackScratch
public import VerifiedGarbage.Impl.AesGcm.Arm.DirectGather
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.AesGcm.Arm.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.Arm.CTCrypt
import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.AesGcm.Arm.DirectGather.Loop
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.AesGcm.Arm.Crypt
import VerifiedGarbage.Proof.AesGcm.Arm.StreamFinish
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.AesGcm.Arm.CTOpen
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.AesGcm.Arm.DirectGather
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

/-! One-shot argument slots are filled directly from the gather caller's stack. -/


namespace VG.Proof.AesGcm.Arm.DirectGather
open VG VG.Arm VG.Impl.AesGcm.Arm.DirectGather

namespace Slot

def index (j : Nat) := ([0,1,4,5,6,2,3] : List Nat)[j]!
def slots : Args.Slots where
  count := 7
  bytes := 2608
  index := index
  indexLt := by
    intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
    rcases this with h|h|h|h|h|h|h <;> subst h <;> decide
  header := by decide
  imm := by decide
  small := by decide

abbrev source (j : Nat) := 2608 + 4 * index j
abbrev Layout := Args.Layout slots
abbrev Ready := Args.Ready slots
abbrev frameTrace := slots.frameTrace

theorem bound {j : Nat} (hj : j < 7) : 2608 ≤ source j ∧ source j + 4 ≤ 2636 :=
  slots.bound hj

theorem frameArgs_run {u : State} (L : Layout u) :
    ∃ t, execBlock isa frameArgs u = some (t, frameTrace u.sp) ∧ Ready u t :=
  Args.frameArgs_run L

end Slot
end VG.Proof.AesGcm.Arm.DirectGather

/-! Lay out the writable workspace and read-only private arguments inside the caller's stack allowance. -/

namespace VG.Proof.AesGcm.Arm.DirectGather
open VG VG.Arm VG.Arm.FrameStack
open Gather (K Nn NL Ad AL Src Cnt Dst L Tg kR nR aR dsR lsR dR tgR argR stkR gatherPre)

namespace Local

abbrev sp (o : State) := o.sp - 2608#32
abbrev work (o : State) := sp o+36#32
abbrev part (o : State) (d n : Nat) : Region := ⟨(stkR o).base+BitVec.ofNat 64 d,n⟩
abbrev workR (o : State) : Region := ⟨State.addr (work o),2560⟩
abbrev argsR (o : State) : Region := ⟨State.addr (sp o),32⟩

/-- The stack space and caller arguments fit without wrapping. -/
structure Fits (o : State) : Prop where
  down : 2640≤o.sp.toNat
  up : o.sp.toNat+28≤2^32

theorem fits {o : State} (h : gatherPre o) : Fits o :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem Fits.ptr {o : State} (h : Fits o) : (sp o).toNat=o.sp.toNat-2608 :=
  sub_toNat' (by have := h.down; omega)

theorem Fits.addr {o : State} (h : Fits o) : State.addr (sp o)=(stkR o).base+32#64 := by
  have a := addr_sub' (x:=o.sp) (k:=2608) (by have := h.down; omega)
  change State.addr (o.sp-BitVec.ofNat 32 2608) = State.addr o.sp-2640#64+32#64
  rw [a,BitVec.sub_eq_add_neg,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rfl

theorem Fits.workAddr {o : State} (h : Fits o) : State.addr (work o)=(stkR o).base+68#64 := by
  change sa (sp o) 36=_
  rw [sa_eq (by have := h.ptr; have := h.up; omega),h.addr,BitVec.add_assoc]; rfl

theorem Fits.workNat {o : State} (h : Fits o) : (work o).toNat=(sp o).toNat+36 := by
  have := h.ptr
  have := h.up
  rw [work,BitVec.toNat_add, Nat.mod_eq_of_lt (by change _+36<2^32; omega)]
  rfl

theorem Fits.argsEq {o : State} (h : Fits o) : argsR o=part o 32 32 := congrArg (fun p => Region.mk p 32) h.addr
theorem Fits.workEq {o : State} (h : Fits o) : workR o=part o 68 2560 := congrArg (fun p => Region.mk p 2560) h.workAddr

theorem Fits.belowEq {o : State} (h : Fits o) : below (sp o)=part o 24 8 := by
  change (Region.mk (State.addr _ - 8#64) 8)=_
  rw [h.addr]; congr 1
  exact Gather.add_ofNat_sub_ofNat _ (a:=32) (b:=8) (by decide)

theorem Fits.below12Eq {o : State} (h : Fits o) : below12 (sp o)=part o 20 12 := by
  change (Region.mk (State.addr _ - 12#64) 12)=_
  rw [h.addr]; congr 1
  exact Gather.add_ofNat_sub_ofNat _ (a:=32) (b:=12) (by decide)

theorem sub (o : State) {d n : Nat} (h : d+n≤2640) : (part o d n).Sub (stkR o) :=
  Offset.sub_base _ h

theorem disj (o : State) {d n e k : Nat} (sep : d+n≤e ∨ e+k≤d) (dn : d+n≤2640) (ek : e+k≤2640) :
    (part o d n).Disjoint (part o e k) := Offset.disjoint _ sep (by omega) (by omega)

theorem allocatedSlots {o : State} (h : gatherPre o) : Slot.Layout (allocState 2608 o) := by
  have g := fits h
  have n := g.ptr
  have up := g.up
  have down := g.down
  refine ⟨by change (sp o).toNat+2636≤2^32; omega,?_,?_⟩
  · intro j hj
    have ⟨low,high⟩ := Slot.bound hj
    have shift : sa (sp o) (Slot.source j) = State.addr o.sp + BitVec.ofNat 64 (4*Slot.index j) := by
      change State.addr (o.sp-2608#32 + BitVec.ofNat 32 (2608+4*Slot.index j))=_
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.sub_add_cancel]
      exact sa_eq (by unfold Slot.source at high; omega)
    refine ⟨argR o,List.mem_append_left _ (show argR o∈o.rd by rw [h.1]; simp),?_⟩
    change (argR o).Contains (sa (sp o) (Slot.source j)) 4
    rw [shift]
    change (Region.mk (State.addr (o.sp+BitVec.ofNat 32 (4*0))) 28).Contains _ _
    rw [Nat.mul_zero,show o.sp+BitVec.ofNat 32 0=o.sp from BitVec.add_zero _]
    exact Offset.contains_base _ (by unfold Slot.source at high; omega) (by unfold Slot.source at high; omega)
  · intro d hd
    change d + 4 ≤ 36 at hd
    refine ⟨_,List.mem_cons_self ..,?_⟩
    change (Region.mk (State.addr (sp o)) 2608).Contains (sa (sp o) d) 4
    rw [sa_eq (by omega)]
    exact Offset.contains_base _ (by omega) (by omega)

def narrow (o t : State) := t.withRegions (o.rd++[argsR o]) [dR o,tgR o,workR o]

abbrev Prepared (o t : State) := Slot.Ready (allocState 2608 o) t

theorem Prepared.word {o t : State} (p : Prepared o t) {i : Nat} (hi : i<7) :
    arg (narrow o t) i=stackArg o (Slot.index i) := by
  change t.mem.readW (sa t.sp (4*i)) 32 = o.mem.readW (sa o.sp (4*Slot.index i)) 32
  rw [p.sp,p.words i hi]
  change o.mem.readW (State.addr (o.sp-2608#32+BitVec.ofNat 32 (2608+4*Slot.index i))) 32 = _
  rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.sub_add_cancel]

theorem Prepared.workspace {o t : State} (p : Prepared o t) : arg (narrow o t) 7=work o := by
  change t.mem.readW (sa t.sp 28) 32=_
  rw [p.sp]
  exact p.scratch

theorem Prepared.one {o t : State} (p : Prepared o t) (h : gatherPre o) : onePre 8 7 (narrow o t) := by
  have f := fits h
  have fp := f.ptr
  have down := f.down
  have up := f.up
  have argsE : args (narrow o t) 8=argsR o := by
    change (Region.mk (State.addr (t.sp+BitVec.ofNat 32 0)) 32)=_
    rw [show t.sp+BitVec.ofNat 32 0=t.sp from BitVec.add_zero _,p.sp]; rfl
  have addr (i : Nat) (hi : i<7) := p.word hi
  have a0 := addr 0 (by decide); have a1 := addr 1 (by decide)
  have a2 := addr 2 (by decide); have a3 := addr 3 (by decide)
  change arg _ 0=Ad o at a0
  change arg _ 1=stackArg o 1 at a1
  change arg _ 2=Dst o at a2
  change arg _ 3=stackArg o 5 at a3
  have g (r : Reg) (hr : r≠.r12) : (narrow o t).gpr r=o.gpr r := p.regs _ hr
  have eSp : (narrow o t).sp=sp o := p.sp
  have eBel : bel (narrow o t)=part o 24 8 := by change below (narrow o t).sp=_; rw [eSp,f.belowEq]
  obtain ⟨rd,wr,kd,kt,nd,nt,ad,at',dd,dt,ls,dt',da,ta,bk,bn,ba,bdsc,bs,bar,bd,bt,
    fk,fn,fa,fdsc,fs,fd,ft,_,_,rounds,_⟩ := h
  have dsW := f.workEq ▸ sub o (d:=68) (n:=2560) (by decide)
  have dsA := f.argsEq ▸ sub o (d:=32) (n:=32) (by decide)
  have belowS := sub o (d:=24) (n:=8) (by decide)
  have aw : (argsR o).Disjoint (workR o) := by rw [f.argsEq,f.workEq]; exact disj _ (.inl (by decide)) (by decide) (by decide)
  have bw : (part o 24 8).Disjoint (workR o) := by rw [f.workEq]; exact disj _ (.inl (by decide)) (by decide) (by decide)
  simp only [onePre,roundsOk,g _ (by decide : Reg.r0≠.r12),g _ (by decide : Reg.r1≠.r12),g _ (by decide : Reg.r2≠.r12),
    g _ (by decide : Reg.r3≠.r12),a0,a1,a2,a3,p.workspace,argsE,eBel,eSp]
  refine ⟨?_,?_,fun _ => kd,(bk.sub_left dsW).symm,fun _ => nd,(bn.sub_left dsW).symm,
    fun _ => ad,(ba.sub_left dsW).symm,(bd.sub_left dsW).symm,fun _ => (bd.sub_left dsA).symm,aw.symm,
    bk.sub_left belowS,bn.sub_left belowS,ba.sub_left belowS,bd.sub_left belowS,bw,
    fk,fn,fa,fd,by rw [f.workNat]; omega,by omega,by omega,rounds⟩
  · change kR o∈o.rd++[argsR o] ∧ nR o∈o.rd++[argsR o] ∧ aR o∈o.rd++[argsR o] ∧ argsR o∈o.rd++[argsR o]
    simp [rd]
  · change dR o∈(o.rd++[argsR o])++[dR o,tgR o,workR o] ∧ workR o∈[dR o,tgR o,workR o] ∧ _
    refine ⟨by simp,by simp,?_⟩
    intro r hr
    change r∈[dR o,tgR o,workR o] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact bd.sub_left dsA
    · exact bt.sub_left dsA
    · exact aw

end Local
end VG.Proof.AesGcm.Arm.DirectGather

/-! Seed the public cursor and counters for the descriptor walk. -/

namespace VG.Proof.AesGcm.Arm.DirectGather
open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.Impl.AesGcm.Arm.DirectGather
open VG.Spec.Gcm (Block blockAt)
open VG.Proof.Gcm (Ctr)

structure Started (b s t : State) : Prop where
  env : Env (b.gpr .r0) (oSt b 7) (arg b 7) b.sp (arg b 5) (b.gpr .r1) t
  count : wordAt t (arg b 7) 256 = arg b 6
  offset : wordAt t (arg b 7) 260 = 0
  args : ArgsKeep 8 b t
  frame : Frame [⟨State.addr (arg b 7)+256#64,8⟩] s.mem t.mem

theorem setup_ok {b s : State} (p : onePre 8 7 b) (args' : ArgsKeep 8 b s) {k7 : BitVec 32}
    (env : Env (b.gpr .r0) (oSt b 7) (arg b 7) b.sp k7 (b.gpr .r1) s) :
    WP isa (.block setup) s (Started b s) := by
  let W := arg b 7
  have lay := oneLay p
  have fit := p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin := p.1.2.2.2
  obtain ⟨r5,a5⟩ := args'.at fit hin 5 (by decide) (show 4*5=20 from rfl)
  obtain ⟨r6,a6⟩ := args'.at fit hin 6 (by decide) (show 4*6=24 from rfl)
  have w256 : InRegions s.wr (State.addr (W+256#32)) 4 := by
    rw [lay.wA (d:=256) (by decide)]; exact env.perm.wW (by decide)
  have w260 : InRegions s.wr (State.addr (W+260#32)) 4 := by
    rw [lay.wA (d:=260) (by decide)]; exact env.perm.wW (by decide)
  dsimp only [W] at w256 w260

  refine WP.of_runBlock ⟨_,by arun [setup,rO,r5,r6,a5,a6,env.r11,w256,w260],?_⟩
  let M := s.mem.writeW (State.addr (W+256#32)) (arg b 6)
  have hf : Frame [⟨State.addr W+256#64,8⟩] s.mem
      (M.writeW (State.addr (W+260#32)) (0#32)) := by
    change Frame _ _ ((s.mem.writeW _ _).writeW _ _)
    rw [lay.wA (d:=256) (by decide),lay.wA (d:=260) (by decide)]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (d:=256) (e:=256) (n:=4) (k:=8) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ ?_
    exact Offset.contains _ (d:=260) (e:=256) (k:=8) (n:=4) (by decide) (by decide) (by decide)
  have sep : Mem.Sep (State.addr (W+256#32)) (32/8) (State.addr (W+260#32)) (32/8) := by
    rw [lay.wA (d:=256) (by decide),lay.wA (d:=260) (by decide)]
    exact Offset.sep _ (.inl (by decide)) (by decide) (by decide)
  constructor
  · refine ⟨?_,?_,?_,?_,?_,env.sp,env.perm.of_eq rfl rfl⟩
    · rfl
    · exact env.r8
    · exact env.r9
    · exact env.r10
    · exact env.r11
  · change ((s.mem.writeW _ _).writeW _ _).readW _ 32=_
    rw [Mem.readW_writeW_sep sep (by decide),Mem.readW_writeW_self32]
  · exact Mem.readW_writeW_self32 _ _ _
  · refine ArgsKeep.frame (s':=_) args' fit hf ?_ rfl rfl rfl
    intro q hq; obtain rfl := List.mem_singleton.mp hq
    exact (p.2.1.2.2 _ p.2.1.2.1).sub_right (Lay.wSub (by decide : 256+8≤2560))
  · exact hf

end VG.Proof.AesGcm.Arm.DirectGather

/-! Relate the original gather buffers to the direct descriptor walk. -/

namespace VG.Proof.AesGcm.Arm.DirectGather
open VG VG.Arm VG.Spec.Gcm
open Gather (K Nn NL Ad AL Src Cnt Dst L Tg kR nR aR dsR lsR dR tgR argR stkR gatherPre sb sl)
namespace Local

def stream (o b s : State) (cb : Block) : Stream :=
  ⟨b.gpr .r0,oSt b 7,arg b 7,b.sp,Src o,Dst o,Cnt o,(b.gpr .r1).toNat,s,cb⟩

theorem gatherAgree {o s : State} (h : gatherPre o) (f : Frame [stkR o] o.mem s.mem) :
    ∀ r∈Sig.descRegion 32 (State.addr (Src o)) (Cnt o)::lsR o, ∀ x, r.Contains x 1 → o.mem x=s.mem x := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hd,hl,_⟩ := h
  intro r hr x hx
  symm; apply f
  intro q hq; obtain rfl := List.mem_singleton.mp hq
  rcases List.mem_cons.mp hr with rfl|m
  · exact (hd.symm _ hx)
  · exact ((hl r m).symm _ hx)

theorem position {o b s : State} {cb : Block} (h : gatherPre o) (f : Frame [stkR o] o.mem s.mem)
    {i : Nat} (hi : i≤Cnt o) :
    (stream o b s cb).pos i=Gather.gl o i := VG.Proof.AesGcm.gatheredLen_congr_le hi (gatherAgree h f)

theorem plaintext {o b s : State} {cb : Block} (h : gatherPre o) (f : Frame [stkR o] o.mem s.mem)
    {i : Nat} (hi : i≤Cnt o) :
    (stream o b s cb).plain i=Gather.pt o i := VG.Proof.AesGcm.gathered_congr_le hi (gatherAgree h f)

variable {o t v s : State} {cb : Block}
theorem destEq (h : gatherPre o) (f : Frame [stkR o] o.mem s.mem) : (stream o (narrow o t) s cb).dstR=dR o := by
  have total := position (b:=(narrow o t)) (cb:=cb) h f (Nat.le_refl (Cnt o))
  have eq := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  change (Region.mk _ ((stream o (narrow o t) s cb).pos (Cnt o)))=_
  rw [total,eq]; rfl

theorem memChange (h : gatherPre o) (p : Prepared o t) {r : Region} (hr : r∈(stream o (narrow o t) s cb).changes) :
    r=(stream o (narrow o t) s cb).dstR ∨ r.Sub (stkR o) := by
  have f := fits h
  have eSp : (narrow o t).sp=sp o := p.sp
  have w : State.addr (arg (narrow o t) 7)=(stkR o).base+68#64 := p.workspace ▸ f.workAddr
  have st := oSt_addr (p.one h)
  simp only [Stream.changes,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
  · exact .inl rfl
  · right; change (Region.mk (State.addr (oSt (narrow o t) 7)+48#64) 32).Sub _
    rw [st,w,BitVec.add_assoc,BitVec.add_assoc]; exact sub o (d:=132) (by decide)
  · right; change (Region.mk (State.addr (arg (narrow o t) 7)+512#64) 2048).Sub _
    rw [w,BitVec.add_assoc]; exact sub o (d:=580) (by decide)
  · right; change (below (narrow o t).sp).Sub _; rw [eSp,f.belowEq]; exact sub o (by decide)
  · right; change (below12 (narrow o t).sp).Sub _; rw [eSp,f.below12Eq]; exact sub o (by decide)
  · right; change (Region.mk (State.addr (arg (narrow o t) 7)+256#64) 8).Sub _
    rw [w,BitVec.add_assoc]; exact sub o (d:=324) (by decide)

theorem safe (h : gatherPre o) (p : Prepared o t) (f : Frame [stkR o] o.mem s.mem) {r : Region}
    (hd : r.Disjoint (dR o)) (hs : r.Disjoint (stkR o)) : (stream o (narrow o t) s cb).safe r := by
  intro q hq
  rcases memChange h p hq with rfl|x
  · rwa [destEq h f]
  · exact hs.sub_right x

theorem changes (h : gatherPre o) (p : Prepared o t) (f : Frame [stkR o] o.mem s.mem) :
    (stream o (narrow o t) s cb).changes =
    [dR o,part o 132 32,part o 580 2048,part o 24 8,part o 20 12,part o 324 8] := by
  have g := fits h
  have es : (narrow o t).sp=sp o := p.sp
  have eW : State.addr (arg (narrow o t) 7) = (stkR o).base+68#64 := p.workspace ▸ g.workAddr
  rw [Stream.changes,destEq h f]
  dsimp only [Stream.ctrR,Stream.workR,Stream.countR,stream,Stream.st,Stream.w,Stream.sp]
  rw [oSt_addr (p.one h),eW,es,g.belowEq,g.below12Eq]
  simp only [BitVec.add_assoc]
  rfl

theorem safeSlot (h : gatherPre o) (p : Prepared o t) (f : Frame [stkR o] o.mem s.mem) {d n : Nat}
    (hd : (part o d n).Disjoint (dR o)) (within : d+n≤2640)
    (c : d+n≤132 ∨ 164≤d) (w : d+n≤580 ∨ 2628≤d)
    (b8 : d+n≤24 ∨ 32≤d) (b12 : d+n≤20 ∨ 32≤d) (cnt : d+n≤324 ∨ 332≤d) :
    (stream o (narrow o t) s cb).safe (part o d n) := by
  intro q hq
  rw [changes h p f] at hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  · exact hd
  · exact disj _ c within (by decide)
  · exact disj _ w within (by decide)
  · exact disj _ b8 within (by decide)
  · exact disj _ b12 within (by decide)
  · exact disj _ cnt within (by decide)

theorem layout (h : gatherPre o) (p : Prepared o t) (f : Frame [stkR o] o.mem s.mem)
    (args' : ArgsKeep 8 (narrow o t) s) : LoopLayout (stream o (narrow o t) s cb) := by
  have one := p.one h
  have fit := fits h
  have eSp : (narrow o t).sp=sp o := p.sp
  have belowS : (below (narrow o t).sp).Sub (stkR o) := by rw [eSp,fit.belowEq]; exact sub o (by decide)
  have below12S : (below12 (narrow o t).sp).Sub (stkR o) := by rw [eSp,fit.below12Eq]; exact sub o (by decide)
  have wS : (Region.mk (State.addr (arg (narrow o t) 7)) 2560).Sub (stkR o) := by
    rw [p.workspace,show (Region.mk (State.addr (work o)) 2560)=workR o from rfl,fit.workEq]; exact sub o (by decide)
  have zK : (narrow o t).gpr .r0=K o := p.regs _ (by decide)
  have zR : (narrow o t).gpr .r1=o.gpr .r1 := p.regs _ (by decide)
  have dst := destEq (t:=t) (cb:=cb) h f
  have ls := (VG.Proof.AesGcm.listed_congr_le (Nat.le_refl (Cnt o)) (gatherAgree h f)).1
  have orig := h
  obtain ⟨rd,wr,kd,kt,nd,nt,ad,at',dd,dt,ld,dt',da,ta,bk,bn,ba,bdsc,bs,bar,bd,bt,
    fk,fn,fa,fdsc,fs,fd,ft,_,_,rounds,total⟩ := h
  have leq : (stream o (narrow o t) s cb).pos (stream o (narrow o t) s cb).count=L o := (position (b:=(narrow o t)) (cb:=cb) orig f (Nat.le_refl _)).trans total
  have srcRegion (i : Nat) (hi : i<Cnt o) : (Region.mk (State.addr (sb s.mem (Src o) i)) (sl s.mem (Src o) i))∈lsR o := by
    change _∈Sig.listed 32 o.mem .u8 (State.addr (Src o)) (Cnt o); rw [←ls]; exact Gather.slice_mem _ fdsc hi
  have read (r : Region) (hr : r∈o.rd) : Covers [r] (s.rd++s.wr) := by
    rw [args'.rd]; exact covers_of_mem (List.mem_append_left _ (List.mem_append_left _ hr))
  have write : Covers [dR o] s.wr := by rw [args'.wr]; exact covers_of_mem (List.mem_cons_self ..)
  have d : DataOk (oSt (narrow o t) 7) (arg (narrow o t) 7) (narrow o t).sp s (Dst o) (L o) :=
    ⟨by exact covers_left write,(stackArg o 5).isLt,fd,oSt_disj one ((bd.sub_left wS).symm),(bd.sub_left wS).symm,bd.sub_left belowS⟩
  have srcO (i : Nat) (hi : i<Cnt o) :
      DataOk (oSt (narrow o t) 7) (arg (narrow o t) 7) (narrow o t).sp s (sb s.mem (Src o) i) (sl s.mem (Src o) i) := by
    have x := srcRegion i hi
    have y := bs _ x
    refine ⟨read _ (by rw [rd]; simp [x]), (s.mem.readW _ 32).isLt,?_,oSt_disj one (y.sub_left wS).symm,
      (y.sub_left wS).symm,y.sub_left belowS⟩
    simpa only [State.addr,BitVec.toNat_setWidth,Nat.mod_eq_of_lt (by have := (sb s.mem (Src o) i).isLt; omega : (sb s.mem (Src o) i).toNat<2^64)] using fs _ x
  have argFit := one.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨outRead,outArg⟩ := args'.at argFit one.1.2.2.2 2 (by decide) (show 4*2=8 from rfl)
  have outE : arg (narrow o t) 2=Dst o := p.word (i:=2) (by decide)
  have rBelow : State.addr ((narrow o t).sp+8#32)=(stkR o).base+40#64 := by
    rw [eSp,show State.addr (sp o+8#32)=sa (sp o) 8 from rfl,sa_eq (by have := fit.ptr; have := fit.up; omega),fit.addr,BitVec.add_assoc]; rfl
  have desc : (stream o (narrow o t) s cb).dsR = dsR o := by
    change Region.mk _ (8*Cnt o)=Region.mk _ (Cnt o*8); rw [Nat.mul_comm 8]; rfl
  have dr : Covers [(stream o (narrow o t) s cb).dsR] (s.rd++s.wr) := by
    rw [desc]; exact read _ (by rw [rd]; simp)
  have dsSafe : (stream o (narrow o t) s cb).safe (stream o (narrow o t) s cb).dsR := by
    rw [desc]; exact safe orig p f dd bdsc.symm
  refine ⟨oneLay (s₀:=narrow o t) one,by change roundsOk (narrow o t); rw [show roundsOk (narrow o t)=roundsOk o by unfold roundsOk; rw [zR]]; exact rounds,
    fdsc,by rw [leq]; exact (stackArg o 5).isLt,?_,dr,dsSafe,srcO,
    fun i hi => safe orig p f (ld _ (srcRegion i hi)).1 (bs _ (srcRegion i hi)).symm,?_,?_,?_,?_,
    by change 12≤(narrow o t).sp.toNat; rw [eSp]; have := fit.ptr; have := fit.down; omega,?_,?_,?_,?_,
    fun i hi => (bs _ (srcRegion i hi)).sub_left below12S⟩
  · change DataW _ _ _ _ _ _ _ _ ((stream o (narrow o t) s cb).pos (stream o (narrow o t) s cb).count)
    rw [leq]; refine ⟨d,write,?_⟩
    change (Region.mk (State.addr ((narrow o t).gpr .r0)) 256).Disjoint (dR o); rw [zK]; exact kd
  · change (stream o (narrow o t) s cb).safe (Region.mk (State.addr ((narrow o t).gpr .r0)) 256); rw [zK]; exact safe orig p f kd bk.symm
  · change InRegions (s.rd++s.wr) (State.addr ((narrow o t).sp+8#32)) 4
    simpa only [args'.sp] using outRead
  · change (stream o (narrow o t) s cb).safe (Region.mk (State.addr ((narrow o t).sp+8#32)) 4)
    rw [rBelow]
    exact safeSlot orig p f (bd.sub_left (sub o (d:=40) (n:=4) (by decide))) (by decide)
      (.inl (by decide)) (.inl (by decide)) (.inr (by decide)) (.inr (by decide)) (.inl (by decide))
  · change s.mem.readW (State.addr ((narrow o t).sp+8#32)) 32=Dst o
    rw [←args'.sp]; exact outArg.trans outE
  · change (below12 (narrow o t).sp).Disjoint (Region.mk (State.addr ((narrow o t).gpr .r0)) 256)
    rw [zK]; exact bk.sub_left below12S
  · change (below12 (narrow o t).sp).Disjoint (Region.mk (State.addr (oSt (narrow o t) 7)) 80)
    exact oSt_disj (s₀:=narrow o t) one (by rw [p.workspace, eSp,fit.below12Eq, show Region.mk (State.addr (work o)) 2560=workR o from rfl,fit.workEq]; exact disj o (.inl (by decide)) (by decide) (by decide))
  · change (below12 (narrow o t).sp).Disjoint (Region.mk (State.addr (arg (narrow o t) 7)) 2560)
    rw [p.workspace,eSp,fit.below12Eq,show Region.mk (State.addr (work o)) 2560=workR o from rfl,fit.workEq]
    exact disj o (.inl (by decide)) (by decide) (by decide)
  · rw [dst]; exact bd.sub_left below12S

end Local
end VG.Proof.AesGcm.Arm.DirectGather

/-! Connect the one-shot nonce/AAD setup to the descriptor walk. -/

namespace VG.Proof.AesGcm.Arm.DirectGather
open VG VG.Arm VG.Spec.Gcm
open VG.Spec.Aes (bytesAt)
open Gather (K Src Cnt Dst L stkR dR gatherPre)
namespace Local

abbrev icb (b : State) := inc32 (j0 (sealH b) (sealNonce b))
abbrev record (o t s : State) := stream o (narrow o t) s (icb (narrow o t))
abbrev J (b : State) := State.addr (oSt b 7)
abbrev W (b : State) := State.addr (arg b 7)

theorem Prepared.ofs {o t : State} (p : Prepared o t) (h : gatherPre o) (d : Nat) :
    W (narrow o t)+BitVec.ofNat 64 d=(stkR o).base+BitVec.ofNat 64 (68+d) := by
  rw [W,p.workspace,(fits h).workAddr,BitVec.add_assoc]; congr 1; exact (BitVec.ofNat_add ..).symm

theorem Prepared.stOfs {o t : State} (p : Prepared o t) (h : gatherPre o) (d : Nat) :
    J (narrow o t)+BitVec.ofNat 64 d=(stkR o).base+BitVec.ofNat 64 (84+d) := by
  rw [J,oSt_addr (p.one h),BitVec.add_assoc,←BitVec.ofNat_add]
  simpa only [← Nat.add_assoc] using p.ofs h (16+d)

theorem Prepared.jAddr {o t : State} (p : Prepared o t) (h : gatherPre o) :
    J (narrow o t)=(stkR o).base+84#64 := by
  simpa only [Nat.add_zero,BitVec.add_zero] using p.stOfs h 0

theorem Prepared.initialFrame {o t u v s : State} (p : Prepared o t) (h : gatherPre o)
    (entry : SO1 8 7 (narrow o t) u) (aad : OA 8 7 (narrow o t) u.mem v) (start : Started (narrow o t) v s) :
    Frame [stkR o] (narrow o t).mem s.mem := by
  have f := fits h
  have bSP : (narrow o t).sp=sp o := p.sp
  refine ((entry.frame.sub fun r hr => ?_).trans (aad.frame.sub fun r hr => ?_)).trans
    (start.frame.sub fun r hr => ?_)
  · obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_singleton_self _,?_⟩
    change (Region.mk (W (narrow o t)+128#64) 36).Sub _
    rw [p.ofs h]; exact sub o (by decide)
  · refine ⟨_,List.mem_singleton_self _,?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · change (Region.mk (J (narrow o t)) 80).Sub _; rw [p.jAddr h]; exact sub o (by decide)
    · change (Region.mk (W (narrow o t)+96#64) 16).Sub _; rw [p.ofs h]; exact sub o (by decide)
    · change (Region.mk (W (narrow o t)+512#64) 256).Sub _; rw [p.ofs h]; exact sub o (by decide)
    · rw [bSP,f.belowEq]; exact sub o (by decide)
  · obtain rfl := List.mem_singleton.mp hr; refine ⟨_,List.mem_singleton_self _,?_⟩
    change (Region.mk (W (narrow o t)+256#64) 8).Sub _; rw [p.ofs h]; exact sub o (by decide)

theorem Prepared.oldFrame {o t : State} (p : Prepared o t) (h : gatherPre o) :
    Frame [stkR o] o.mem (narrow o t).mem := by
  refine p.frame.sub fun r hr => ?_
  obtain rfl := List.mem_singleton.mp hr; refine ⟨_,List.mem_singleton_self _,?_⟩
  change (Region.mk (State.addr (sp o)) 36).Sub _
  rw [(fits h).addr]; exact sub o (by decide)

theorem Prepared.atZero {o t u v s : State} (p : Prepared o t) (h : gatherPre o)
    (aad : OA 8 7 (narrow o t) u.mem v) (start : Started (narrow o t) v s) :
    At (record o t s) 0 s := by
  have desc : arg (narrow o t) 5=Src o := p.word (i:=5) (by decide)
  have cnt : arg (narrow o t) 6=stackArg o 3 := p.word (i:=6) (by decide)
  have roll := start.env
  have same : blockAt s.mem (J (narrow o t)+48#64) = blockAt v.mem (J (narrow o t)+48#64) := by
    apply blockAt_frame start.frame
    intro q hq; obtain rfl := List.mem_singleton.mp hq
    change (Region.mk (J (narrow o t)+48#64) 16).Disjoint (Region.mk (W (narrow o t)+256#64) 8)
    rw [p.stOfs h,p.ofs h]; exact disj o (.inl (by decide)) (by decide) (by decide)
  have zero : (record o t s).pos 0=0 := rfl
  have empty : (record o t s).plain 0=[] := rfl
  have r8 : (record o t s).roundsW=(narrow o t).gpr .r1 := by
    change BitVec.ofNat 32 ((narrow o t).gpr .r1).toNat=_
    rw [BitVec.ofNat_toNat,BitVec.setWidth_eq]
  refine ⟨?_,?_,?_,?_,?_,Frame.refl _ _,rfl,rfl⟩
  · change Env _ _ _ _ (Src o+BitVec.ofNat 32 (8*0)) (record o t s).roundsW s
    rw [show (Src o+BitVec.ofNat 32 (8*0))=Src o from BitVec.add_zero _,r8,←desc]; exact roll
  · rw [zero]; exact start.offset
  · change wordAt s (arg (narrow o t) 7) 256 = BitVec.ofNat 32 ((Cnt o)-0)
    rw [Nat.sub_zero,start.count,cnt,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · change VG.Proof.Gcm.Ctr _ _ _ _ _ ((record o t s).pos 0)
    rw [zero]; exact VG.Proof.Gcm.ctr_zero _ _ _ _ (same.trans aad.cb)
  · rw [zero,empty]; rfl

end Local
end VG.Proof.AesGcm.Arm.DirectGather

/-! The descriptor loop changes ciphertext and CTR state while preserving the
AAD accumulator, initial nonce counter, caller arguments and saved registers. -/

namespace VG.Proof.AesGcm.Arm.DirectGather
open VG VG.Arm VG.Spec.Gcm
open VG.Spec.Aes (bytesAt)
open Gather (K Cnt Dst L stkR dR gatherPre)
namespace Local

variable {o t u v s z : State}

theorem safeLocal (h : gatherPre o) (p : Prepared o t) (f : Frame [stkR o] o.mem s.mem) {d n : Nat}
    (lo : 32≤d) (hi : d+n≤324) (counter : d+n≤132 ∨ 164≤d) : (record o t s).safe (part o d n) := by
  have out := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact safeSlot h p f (out.sub_left (sub o (by omega))) (by omega) counter (.inl (by omega)) (.inr lo) (.inr lo) (.inl hi)

theorem after (h : gatherPre o) (p : Prepared o t) (entry : SO1 8 7 (narrow o t) u)
    (aad : OA 8 7 (narrow o t) u.mem v) (start : Started (narrow o t) v s)
    (done : At (record o t s) (Cnt o) z) :
    TagReady 8 7 (narrow o t) z (Gather.pt o (Cnt o)) := by
  let b := narrow o t
  let a := record o t s
  have one := p.one h
  have fb := p.initialFrame h entry aad start
  have f := (p.oldFrame h).trans fb
  have l := layout (cb:=icb b) h p f start.args
  have all' : Frame a.changes v.mem z.mem :=
    (start.frame.mono fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))).trans done.frame
  have r8 : a.roundsW=b.gpr .r1 := by change BitVec.ofNat 32 (b.gpr .r1).toNat=_; rw [BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have lay := oneLay one
  have argsSafe : a.safe (args b 8) := by
    change a.safe (Region.mk (State.addr (t.sp+BitVec.ofNat 32 0)) 32)
    rw [show t.sp+BitVec.ofNat 32 0=t.sp from BitVec.add_zero _,p.sp]
    change a.safe (argsR o); rw [(fits h).argsEq]; exact safeLocal h p f (by decide) (by decide) (.inl (by decide))
  have ctx : a.safe (Region.mk (State.addr (b.gpr .r0)) 256) := l.ctxSafe
  have initKey : (⟨State.addr (b.gpr .r0),256⟩ : Region).Disjoint (stkR o) := by
    change (Region.mk (State.addr ((narrow o t).gpr .r0)) 256).Disjoint _
    rw [show (narrow o t).gpr .r0=K o from p.regs _ (by decide)]
    exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm
  have rds := one.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have cipher : a.cipher=sealCipher b := ciph_keep fb (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact initKey) rds
  have acc : a.safe (Region.mk (J b+16#64) 16) := by
    rw [p.stOfs h]; exact safeLocal h p f (by decide) (by decide) (.inl (by decide))
  have tailBuf (n : Nat) (hn : n≤16) : a.safe (Region.mk (J b+32#64) n) := by
    rw [p.stOfs h]; exact safeLocal h p f (by decide) (by omega) (.inl (by omega))
  have j : a.safe (Region.mk (J b) 16) := by
    rw [p.jAddr h]; exact safeLocal h p f (by decide) (by decide) (.inl (by decide))
  have saved : a.safe (savedR (arg b 7)) := by
    change a.safe (Region.mk (W b+128#64) 36)
    rw [p.ofs h]; exact safeLocal h p f (by decide) (by decide) (.inr (by decide))
  have en := done.env
  rw [r8] at en
  refine ⟨⟨_,en⟩,?_,?_,?_,?_,?_,?_,
    (entry.saved.frame aad.frame (saved_j0Frame lay)).frame all' saved⟩
  · exact ArgsKeep.frame (s':=z) start.args one.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      done.frame argsSafe (done.env.sp.trans start.env.sp.symm) done.rd done.wr
  · rw [blockAt_frame all' (fun r hr => (ctx r hr).sub_left (Lay.ctxSub (by decide)))]; exact aad.hH
  · exact aad.abs.congr (blockAt_frame all' acc) (bytesAt_frame all' (tailBuf _ (Nat.le_of_lt (Nat.mod_lt _ (by decide)))) (by omega))
  · rw [blockAt_frame all' j]; exact aad.j
  · exact (ciph_frame done.frame ctx rds).trans cipher
  · have result := done.encrypted
    have pos : a.pos (Cnt o)=L o :=
      (position (b:=b) (cb:=icb b) h f (Nat.le_refl (Cnt o))).trans h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have plain : a.plain (Cnt o)=Gather.pt o (Cnt o) := plaintext h f (Nat.le_refl _)
    change bytesAt z.mem (State.addr (Dst o)) (a.pos (Cnt o)) = gctr a.cipher (icb b) (a.plain (Cnt o)) at result
    rw [pos,plain,cipher] at result
    change bytesAt z.mem (State.addr (arg b 2)) (arg b 3).toNat=_
    rw [show arg b 2=Dst o from p.word (i:=2) (by decide),show arg b 3=stackArg o 5 from p.word (i:=3) (by decide)]
    exact result

end Local
end VG.Proof.AesGcm.Arm.DirectGather

/-! Functional correctness of the caller-facing direct gather operation. -/

namespace VG.Proof.AesGcm.Arm.DirectGather
open VG VG.Arm VG.Arm.FrameStack
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm
open VG.Impl.AesGcm.Arm.DirectGather
open Gather (K Nn NL Ad AL Cnt Dst L Tg kR nR aR stkR dR tgR gatherPre gatherPost)
namespace Local

theorem body_wp [VG.Proof.Gcm.Arm.GhashLaw] {o t : State} (h : gatherPre o) (p : Prepared o t) :
    WP isa body (narrow o t) fun z => abiPreserved (narrow o t) z ∧ gatherPost o z := by
  let b := narrow o t
  have one := p.one h
  have fit := fits h
  have fOld := p.oldFrame h
  have tag : arg b 4=Tg o := p.word (i:=4) (by decide)
  have dst : arg b 2=Dst o := p.word (i:=2) (by decide)
  have len : arg b 3=stackArg o 5 := p.word (i:=3) (by decide)
  have ad : arg b 0=Ad o := p.word (i:=0) (by decide)
  have al : arg b 1=stackArg o 1 := p.word (i:=1) (by decide)
  have reg (r : Reg) (hr : r≠.r12) : b.gpr r=o.gpr r := p.regs _ hr
  have wk : (workR o).Sub (stkR o) := by rw [fit.workEq]; exact sub o (by decide)
  have orig := h
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,dt,_,_,bk,bn,ba,_,_,_,_,bt,_,_,_,_,_,_,ft,_,_,rounds,_⟩ := h
  have cutoff (r : Region) (hr : (stkR o).Disjoint r) : ∀ q∈[stkR o], r.Disjoint q :=
    fun q hq => List.mem_singleton.mp hq ▸ hr.symm
  have cipher : sealCipher b=sealCipher o := by
    change ctxCiph b.mem (State.addr (b.gpr .r0)) (b.gpr .r1).toNat=_
    rw [reg _ (by decide),reg _ (by decide)]; exact ciph_keep fOld (cutoff _ bk) rounds
  have hash : sealH b=sealH o := by
    change ctxH b.mem (State.addr (b.gpr .r0))=_
    rw [reg _ (by decide),ctxH_eq]; exact ctxH_keep fOld (cutoff _ bk)
  have nonce : sealNonce b=sealNonce o := by
    change bytesAt b.mem (State.addr (b.gpr .r2)) (b.gpr .r3).toNat=_
    rw [reg _ (by decide),reg _ (by decide)]
    exact bytesAt_frame fOld (cutoff _ bn) (by have := (o.gpr .r3).isLt; omega)
  have aadE : sealAad b=bytesAt o.mem (State.addr (Ad o)) (AL o) := by
    change bytesAt b.mem (State.addr (arg b 0)) (arg b 1).toNat=_
    rw [ad,al]; exact bytesAt_frame fOld (cutoff _ ba) (by have := (stackArg o 1).isLt; omega)
  refine WP.seq (one1_wp one (by decide) (by decide) fun u entry => WP.seq ((oneAad_ok one (by decide) entry).mono fun v aad => ?_))
  obtain ⟨k7,env⟩ := aad.env
  refine WP.seq ((setup_ok one aad.args env).mono fun s start => ?_)
  have f := fOld.trans (p.initialFrame orig entry aad start)
  have loop := layout (cb:=icb b) orig p f start.args
  refine WP.seq ((loop.pieces_ok (p.atZero orig aad start)).mono fun z done => ?_)
  have T := after orig p entry aad start done
  refine (seal_tag_wp one (by decide) ?_ ?_ ?_ ?_ T).mono fun q ⟨abi,res⟩ => ⟨abi,?_⟩
  · change Region.mk (State.addr (arg b 4)) 16 ∈ [dR o,tgR o,workR o]
    rw [tag]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · change (Region.mk (State.addr (arg b 2)) (arg b 3).toNat).Disjoint ⟨State.addr (arg b 4),16⟩
    rw [dst,len,tag]; exact dt
  · change (Region.mk (State.addr (arg b 4)) 16).Disjoint (Region.mk (State.addr (arg b 7)) 2560)
    rw [tag,p.workspace]; exact (bt.sub_left wk).symm
  · change (arg b 4).toNat+16≤2^32; rw [tag]; exact ft
  · change encryptWith (sealCipher b) (sealH b) 16 (sealNonce b) _ (sealAad b) =
      (bytesAt q.mem (State.addr (arg b 2)) (arg b 3).toNat,bytesAt q.mem (State.addr (arg b 4)) 16) at res
    rw [cipher,hash,nonce,aadE,dst,len,tag] at res
    exact res

theorem widen {o t : State} (h : gatherPre o) (p : Prepared o t) :
    Covers ((narrow o t).rd++(narrow o t).wr) (t.rd++t.wr) ∧ Covers (narrow o t).wr t.wr := by
  have f := fits h
  have rd : t.rd=o.rd := p.rd
  have wr : t.wr=⟨State.addr (sp o),2608⟩::[dR o,tgR o] := p.wr.trans (by rw [allocState_wr,h.2.1])
  have frame : Covers [⟨State.addr (sp o),2608⟩] t.wr := covers_of_mem (by rw [wr]; exact List.mem_cons_self ..)
  have w : Covers [workR o] t.wr := by
    change Covers [Region.mk (State.addr (work o)) 2560] _
    change Covers [Region.mk (sa (sp o) 36) 2560] _
    rw [sa_eq (by have := f.ptr; have := f.up; omega)]
    exact covers_off frame (by decide) (by decide)
  have out : Covers (narrow o t).wr t.wr := by
    apply covers_cons (covers_of_mem (by rw [wr]; simp))
    apply covers_cons (covers_of_mem (by rw [wr]; simp))
    exact w
  refine ⟨covers_append' (covers_append' ?_ (covers_left (covers_prefix frame (by decide : 32≤2608)))) (covers_left out),out⟩
  intro x n hx
  obtain ⟨r,hr,inside⟩ := hx
  exact ⟨r,List.mem_append_left _ (rd ▸ hr),inside⟩

theorem direct_wp [VG.Proof.Gcm.Arm.GhashLaw] {o : State} (h : gatherPre o) :
    WP isa sealGather o fun z => abiPreserved o z ∧ gatherPost o z := by
  have f := fits h
  refine WP.alloc ⟨by decide,by decide,by decide,by decide⟩ (by have := f.down; omega) ?_
  obtain ⟨t,head,p⟩ := Slot.frameArgs_run (allocatedSlots h)
  refine WP.seq ⟨_,t,Exec.block head,?_⟩
  obtain ⟨tr,z,run,abi,res⟩ := body_wp h p
  obtain ⟨r,w⟩ := widen h p
  have wide := VG.Arm.Exec.widen run r w
  refine ⟨tr,z.withRegions t.rd t.wr,?_,?_⟩
  · exact wide
  intro m u fm
  have frSub : (Region.mk (State.addr (sp o)) 2608).Sub (stkR o) := by rw [f.addr]; exact sub o (by decide)
  have hd := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have mem (r : Region) (out : (stkR o).Disjoint r) (fit : r.len ≤ 2^64) :
      bytesAt m r.base r.len = bytesAt z.mem r.base r.len := bytesAt_frame fm
        (fun q hq => List.mem_singleton.mp hq ▸ (out.sub_left frSub).symm) fit
  refine ⟨⟨fun r hr => (abi.1 r hr).trans (p.regs _ (by intro eq; subst eq; exact (by decide : Reg.r12 ∉ preserved) hr)),?_⟩,?_⟩
  · change z.sp+2608#32 = o.sp
    rw [abi.2]; change t.sp+2608#32=o.sp
    rw [p.sp]; exact BitVec.sub_add_cancel _ _
  · change _=(bytesAt m (State.addr (Dst o)) (L o),bytesAt m (State.addr (Tg o)) 16)
    rw [mem (dR o) hd (by change (stackArg o 5).toNat≤2^64; have := (stackArg o 5).isLt; omega),
      mem (tgR o) ht (by decide : 16≤2^64)]
    exact res

end Local
end VG.Proof.AesGcm.Arm.DirectGather

/-! Only public pointer/length words pass from the entry frame to text processing. -/

namespace VG.Proof.AesGcm.Arm.DirectGather
open VG VG.Arm
open Gather (Src Cnt Dst stkR dR gatherPre gatherPub)
namespace Local

theorem one_public {o o' t t' : State} (p : Prepared o t) (p' : Prepared o' t') (pub : gatherPub o o') :
    onePub 8 (narrow o t) (narrow o' t') := by
  obtain ⟨r0,r1,r2,r3,spE,args,_⟩ := pub
  have reg (r : Reg) (ne : r≠.r12) (eq : o.gpr r=o'.gpr r) :
      (narrow o t).gpr r=(narrow o' t').gpr r := (p.regs _ ne).trans (eq.trans (p'.regs _ ne).symm)
  have ptr : sp o=sp o' := by unfold sp; rw [spE]
  refine ⟨p.sp.trans (ptr.trans p'.sp.symm),reg _ (by decide) r0,reg _ (by decide) r1,
    reg _ (by decide) r2,reg _ (by decide) r3,fun j hj => ?_⟩
  by_cases lt : j<7
  · rw [p.word lt,p'.word lt]
    have hi := (Slot.bound lt).2
    apply args; unfold Slot.source at hi; omega
  · obtain rfl : j=7 := by omega
    rw [p.workspace,p'.workspace]; exact congrArg (·+36#32) ptr

theorem stackPublic {o t s : State} (h : gatherPre o) (p : Prepared o t)
    (args' : ArgsKeep 8 (narrow o t) s) :
    ∀ r∈s.wr, (Region.mk (State.addr ((narrow o t).sp)) 12).Disjoint r := by
  have one := p.one h
  intro r hr; rw [args'.wr] at hr
  apply (one_hw one r hr).sub_left
  change (Region.mk (State.addr t.sp) 12).Sub (Region.mk (State.addr (t.sp+BitVec.ofNat 32 0)) 32)
  rw [show t.sp+BitVec.ofNat 32 0=t.sp from BitVec.add_zero _]
  exact Region.sub_prefix (by decide : 12≤32)

theorem same {o o' t t' s s' : State} (h : gatherPre o) (h' : gatherPre o') (p : Prepared o t) (p' : Prepared o' t')
    (pub : gatherPub o o') (f : Frame [stkR o] o.mem s.mem) (f' : Frame [stkR o'] o'.mem s'.mem)
    (k : ArgsKeep 8 (narrow o t) s) (k' : ArgsKeep 8 (narrow o' t') s') :
    Same (record o t s) (record o' t' s') := by
  have b := one_public p p' pub
  obtain ⟨bs,k0,k1,k2,k3,args⟩ := b
  obtain ⟨_,_,_,_,os,words,mem⟩ := pub
  have src : Src o=Src o' := words 2 (by decide)
  have cnt : Cnt o=Cnt o' := congrArg BitVec.toNat (words 3 (by decide))
  have dst : Dst o=Dst o' := words 4 (by decide)
  have dw := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have dBytes {o s : State} (h : gatherPre o) (f : Frame [stkR o] o.mem s.mem) (j : Nat) (hj : j<Cnt o*8) :
      s.mem (State.addr (Src o)+BitVec.ofNat 64 j)=o.mem (State.addr (Src o)+BitVec.ofNat 64 j) := by
    have dw := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact f.bytes (R:=Gather.dsR o) (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm)
      (by change Cnt o*8≤2^64; omega) hj
  have dEq (j : Nat) (hj : j<Cnt o*8) :
      s.mem (State.addr (Src o)+BitVec.ofNat 64 j)=s'.mem (State.addr (Src o)+BitVec.ofNat 64 j) := by
    rw [dBytes h f j hj,mem j hj,src,dBytes h' f' j (cnt ▸ hj)]
  have safe {o t s : State} (h : gatherPre o) (p : Prepared o t) (f : Frame [stkR o] o.mem s.mem) :
      (record o t s).safe (Region.mk (State.addr (narrow o t).sp) 12) := by
    change (record o t s).safe (Region.mk (State.addr t.sp) 12); rw [p.sp]
    change (record o t s).safe (Region.mk (State.addr (sp o)) 12); rw [(fits h).addr]
    exact safeLocal h p f (by decide) (by decide) (.inl (by decide))
  have fit := (p.one h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have agree := k.agree k' bs fit args (one_hw (p.one h)) (one_hw (p'.one h'))
    (rs:=[]) (by simp)
  refine ⟨k0,congrArg (·+16#32) (args 7 (by decide)),args 7 (by decide),bs,src,dst,congrArg BitVec.toNat k1,cnt,?_,?_,
    by change (narrow o t).sp.toNat+12≤2^32; omega,stackPublic (t:=t) h p k,stackPublic (t:=t') h' p' k',
    safe h p f,safe h' p' f',?_,?_⟩
  · intro i hi
    change Gather.sb s.mem (Src o) i=Gather.sb s'.mem (Src o') i
    rw [←src]; exact Gather.sb_agree dw dEq hi
  · intro i hi
    change Gather.sl s.mem (Src o) i=Gather.sl s'.mem (Src o') i
    rw [←src]; exact Gather.sl_agree dw dEq hi
  · intro j hj
    change s.mem (State.addr (narrow o t).sp+BitVec.ofNat 64 j)=s'.mem (State.addr (narrow o' t').sp+BitVec.ofNat 64 j)
    have eq := agree.argMem (k:=j) (by change j<4*8; omega)
    simpa only [VG.Arm.Taint.argByte,k.sp,k'.sp] using eq
  · intro i hi
    change VG.Spec.Gcm.gatheredLen 32 s.mem (State.addr (Src o)) i=VG.Spec.Gcm.gatheredLen 32 s'.mem (State.addr (Src o')) i
    rw [←src]; exact Gather.gl_agree dEq hi

end Local
end VG.Proof.AesGcm.Arm.DirectGather

/-! Constant-time composition of the one-shot stages around the direct walk. -/

namespace VG.Proof.AesGcm.Arm.DirectGather
open VG VG.Arm VG.Impl.AesGcm.Arm VG.Impl.AesGcm.Arm.DirectGather
open Gather (Src Cnt Tg stkR dR tgR gatherPre gatherPub Eq2 TT rel_seq)
namespace Local

theorem out_public {o t : State} (p : Prepared o t) (h : gatherPre o) :
    (⟨State.addr (arg (narrow o t) 4),16⟩ : Region) ∈ (narrow o t).wr ∧
    (arg (narrow o t) 4).toNat+16≤2^32 ∧
    (⟨State.addr (arg (narrow o t) 4),16⟩ : Region).Disjoint ⟨State.addr (arg (narrow o t) 7),16⟩ := by
  rw [show arg (narrow o t) 4=Tg o from p.word (i:=4) (by decide),p.workspace]
  have fit := fits h
  have bt := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ft := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨List.mem_cons_of_mem _ (List.mem_cons_self ..),ft,(bt.sub_left ?_).symm⟩
  rw [fit.workAddr]; exact sub o (by decide)

theorem tag_rel [VG.Proof.Gcm.Arm.GhashLaw] {o o' t t' z z' : State} (h : gatherPre o) (h' : gatherPre o')
    (p : Prepared o t) (p' : Prepared o' t') (pub : gatherPub o o') {plain plain' : List Byte}
    (r : TagReady 8 7 (narrow o t) z plain) (r' : TagReady 8 7 (narrow o' t') z' plain') :
    RelCT isa (Eq2 z z') (.seq (oneTag 0) (.seq (.block tagOut) (.block restore))) TT := by
  let b := narrow o t
  let b' := narrow o' t'
  have one := p.one h
  have one' := p'.one h'
  have q := one_public p p' pub
  have eqW := q.2.2.2.2.2 7 (by decide)
  have eqS : oSt b 7=oSt b' 7 := congrArg (·+16#32) eqW
  have fit := one.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have fit' := one'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ⟨tagW,tf,sep⟩ := out_public p h
  have ⟨tagW',tf',sep'⟩ := out_public p' h'
  let P (s : State) := s.gpr .r11=arg b 7
  have out := rel_agree (F:=OF 8 7 b b) (F':=OF 8 7 b b') (G:=P) (G':=P) (argTaint [.r11] 32)
    (c:=.block tagOut) (fun s s' ⟨_,en,k⟩ ⟨_,en',k'⟩ => k.agree k' q.1 fit q.2.2.2.2.2 (one_hw one) (one_hw one')
      fun reg mr => by obtain rfl := List.mem_singleton.mp mr; exact en.r11.trans en'.r11.symm)
    ⟨_,by taint_decide⟩ (fun s ⟨_,en,k⟩ => tagOut_wp (oneLay one) (by decide) en k fit one.1.2.2.2 tagW tf sep)
    (fun s ⟨_,en,k⟩ => tagOut_wp (oneLay one) (by decide) en k fit' one'.1.2.2.2 tagW' tf'
      (by rw [eqW]; exact sep'))
  have ret : RelCT isa (fun s s' => P s ∧ P s') (.block restore) TT := by
    exact RelCT.taint (A:=taint) (Taint.ofRegs [.r11]) (fun _ _ hh => Taint.agree_ofRegs fun reg mr => by
      obtain rfl := List.mem_singleton.mp mr; exact hh.1.trans hh.2.symm) (hc:=_) (by taint_decide)
  refine ((oneTag_rel one one' q (by decide) (by decide) (.inl rfl)).seq (out.seq ret)).mono ?_ (fun _ _ _ => trivial)
  rintro _ _ ⟨rfl,rfl⟩
  have round (w : BitVec 32) : BitVec.ofNat 32 w.toNat=w := by rw [BitVec.ofNat_toNat,BitVec.setWidth_eq]
  obtain ⟨k7,en⟩ := r.env
  obtain ⟨k7',en'⟩ := r'.env
  refine ⟨⟨k7,?_,r.args⟩,⟨k7',?_,r'.args⟩⟩
  · rw [round]; exact en
  · rw [round,q.2.1,eqS,eqW,q.1,q.2.2.1]; exact en'

theorem body_rel [VG.Proof.Gcm.Arm.GhashLaw] {o o' t t' : State} (h : gatherPre o) (h' : gatherPre o')
    (p : Prepared o t) (p' : Prepared o' t') (pub : gatherPub o o') :
    RelCT isa (Eq2 (narrow o t) (narrow o' t')) body TT := by
  let b := narrow o t
  let b' := narrow o' t'
  have one := p.one h
  have one' := p'.one h'
  have q := one_public p p' pub
  have entry : RelCT isa (Eq2 b b') (.block (oneEntry 28)) TT := RelCT.taint (A:=taint)
    (argTaint [.r0,.r1,.r2,.r3] 32) (fun _ _ ⟨e,e'⟩ => one_entry_agree (by simp) one one' q _ _ e e')
    (hc:=_) (by taint_decide)
  refine rel_seq entry (one1_wp one (by decide) (by decide) fun _ x => x)
    (one1_wp one' (by decide) (by decide) fun _ x => x) ?_
  intro u u' en en'
  refine rel_seq ((oneAad_rel one one' q (by decide) (by decide)).mono
    (by rintro _ _ ⟨rfl,rfl⟩; exact ⟨en,en'⟩) (fun _ _ _ => trivial))
    (oneAad_ok one (by decide) en) (oneAad_ok one' (by decide) en') ?_
  intro v v' aad aad'
  have ⟨k7,ev⟩ := aad.env
  have ⟨k7',ev'⟩ := aad'.env
  have fit := one.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have prep : RelCT isa (Eq2 v v') (.block setup) TT := by
    refine RelCT.taint (A:=taint) (argTaint [.r11] 32) ?_ (hc:=_) (by taint_decide)
    rintro _ _ ⟨rfl,rfl⟩
    exact aad.args.agree aad'.args q.1 fit q.2.2.2.2.2 (one_hw one) (one_hw one') fun reg mr => by
      obtain rfl := List.mem_singleton.mp mr; rw [ev.r11,ev'.r11,q.2.2.2.2.2 7 (by decide)]
  refine rel_seq prep (setup_ok one aad.args ev) (setup_ok one' aad'.args ev') ?_
  intro s s' start start'
  have f := (p.oldFrame h).trans (p.initialFrame h en aad start)
  have f' := (p'.oldFrame h').trans (p'.initialFrame h' en' aad' start')
  have left := layout (cb:=icb b) h p f start.args
  have right := layout (cb:=icb b') h' p' f' start'.args
  have zero := p.atZero h aad start
  have zero' := p'.atZero h' aad' start'
  refine rel_seq (left.pieces_rel right (same h h' p p' pub f f' start.args start'.args) zero zero')
    (left.pieces_ok zero) (right.pieces_ok zero') ?_
  intro z z' done done'
  exact tag_rel h h' p p' pub (after h p en aad start done) (after h' p' en' aad' start' done')

end Local
end VG.Proof.AesGcm.Arm.DirectGather

/-! The allocation, fixed argument permutation, and direct encryption implement
the existing public gather/rounds contract. -/

namespace VG.Proof.AesGcm.Arm.DirectGather
open VG VG.Arm VG.Impl.AesGcm.Arm.DirectGather
open Gather (gatherPre gatherPub Eq2 TT)
namespace Local

theorem frame_rel [VG.Proof.Gcm.Arm.GhashLaw] {o o' : State} (h : gatherPre o) (h' : gatherPre o') (pub : gatherPub o o') :
    RelCT isa (Eq2 o o') sealGather TT := by
  apply Gather.rel_alloc
  obtain ⟨t,run,p⟩ := Slot.frameArgs_run (allocatedSlots h)
  obtain ⟨t',run',p'⟩ := Slot.frameArgs_run (allocatedSlots h')
  have spEq : (allocState 2608 o).sp=(allocState 2608 o').sp := by
    simp only [allocState_sp,pub.2.2.2.2.1]
  have argsCt : RelCT isa (Eq2 (allocState 2608 o) (allocState 2608 o')) (.block frameArgs) TT := by
    rintro _ _ _ _ _ _ ⟨rfl,rfl⟩ ex ex'
    exact ⟨(ex.det (.block run)).1.trans ((congrArg Slot.frameTrace spEq).trans (ex'.det (.block run')).1.symm),trivial⟩
  have v : WP isa (.block frameArgs) (allocState 2608 o) (fun z => z=t) := ⟨_,_,Exec.block run,rfl⟩
  have v' : WP isa (.block frameArgs) (allocState 2608 o') (fun z => z=t') := ⟨_,_,Exec.block run',rfl⟩
  refine Gather.rel_seq argsCt v v' ?_
  rintro _ _ rfl rfl
  have ct := body_rel h h' p p' pub
  obtain ⟨_,z,exec,_⟩ := body_wp h p
  obtain ⟨_,z',exec',_⟩ := body_wp h' p'
  obtain ⟨r,w⟩ := widen h p
  obtain ⟨r',w'⟩ := widen h' p'
  have wide := VG.Arm.Exec.widen exec r w
  have wide' := VG.Arm.Exec.widen exec' r' w'
  rintro _ _ _ _ _ _ ⟨rfl,rfl⟩ ex ex'
  exact ⟨(ex.det wide).1.trans ((ct _ _ _ _ _ _ ⟨rfl,rfl⟩ exec exec').1.trans (ex'.det wide').1.symm),trivial⟩

theorem verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified target sealGather (VG.Proof.AesGcm.sealGatherRoundsContract abi 2640) :=
  by
    refine Verified.of_correct (k:=Gather.gatherArm) ?_ ?_ Gather.gather_implies
    · intro s h
      obtain ⟨tr,z,run,abi,res⟩ := direct_wp h
      exact ⟨tr,z,run,abi,res⟩
    · intro _ _ _ _ _ _ h h' pub ex ex'
      exact (frame_rel h h' pub _ _ _ _ _ _ ⟨rfl,rfl⟩ ex ex').1

end Local
end VG.Proof.AesGcm.Arm.DirectGather
