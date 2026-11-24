module

public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Step
import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.HeadCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Impl.AesGcm.X86.DirectGather
meta import VerifiedGarbage.Proof.AesGcm.X86.Callee
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State

/-! Gather descriptors are public. Their lengths determine the stream offset
and all branches in the IA-32 descriptor loop. Source bytes may differ. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.DirectGather

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Impl.AesGcm.X86.DirectGather (descriptor setCursors nextPiece partialHead pieces)
open VG.Spec.Gcm (Block)

variable {N : Nat}

def DescEq (a : Text) (m u : Mem) : Prop :=
  ∀ i<a.count, a.source m i = a.source u i ∧ a.size m i = a.size u i

private theorem offEq {a : Text} {m u : Mem} (fit : a.Src.toNat+a.count*8 ≤ 2^32) (h : DescEq a m u)
    {i : Nat} (hi : i≤a.count) : a.off m i = a.off u i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi' : i<a.count := by omega_using [hi]
    have left : a.off m (i+1) = a.off m i+a.size m i := Gather.gl_succ fit hi'
    have right : a.off u (i+1) = a.off u i+a.size u i := Gather.gl_succ fit hi'
    rw [left,right,ih (Nat.le_of_lt hi'),(h i hi').2]

private def AtI (N : Nat) (a : Text) (m : Mem) (i : Nat) (t : State) : Prop :=
  ∃ s icb, TextInput N a s ∧ DescEq a s.mem m ∧ TextAt N a s icb i t

private def LoadedI (N : Nat) (a : Text) (m : Mem) (i : Nat) (t : State) : Prop :=
  ∃ s icb, TextInput N a s ∧ DescEq a s.mem m ∧ TextInput.Loaded N a s icb i t

private def AdvancedI (N : Nat) (a : Text) (m : Mem) (i : Nat) (t : State) : Prop :=
  ∃ s icb, TextInput N a s ∧ DescEq a s.mem m ∧ TextInput.Advanced N a s icb i t

private theorem load_ct {a : Text} {m : Mem} {i : Nat} : CT (AtI N a m i) (.block nextPiece) := by
  apply RelCT.block_append (M:=isa) (l₁:=[.mov .edx (slot rO)]) (l₂:=descriptor.tail++setCursors)
  refine CT.seq (J:=fun s => s.gpr .ebp=a.W ∧ s.gpr .esp=a.SP ∧ s.gpr .edx=a.desc i)
    (CT.taint [.ebp] (fun _ _ ⟨_,_,_,_,x⟩ ⟨_,_,_,_,y⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact x.env.ebp.trans y.env.ebp.symm) (by taint_decide)) ?_ ?_
  · rintro t ⟨s,icb,p,hd,h⟩
    refine WP.of_runBlock ⟨_,by xrun [h.env.ebp,p.lay.aW,h.env.wIn',h.ptr],?_⟩
    exact ⟨h.env.ebp,h.env.esp,rfl⟩
  exact CT.taint [.ebp,.esp,.edx] (fun _ _ ⟨a,b,c⟩ ⟨d,e,f⟩ r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [a.trans d.symm,b.trans e.symm,c.trans f.symm]) (by taint_decide)

private theorem advance_ct (v : GcmImpl) [WSize N v.ctr.scr] {a : Text} {m : Mem} {i : Nat} (hi : i<a.count) :
    CT (LoadedI N a m i) (.seq (.ite .e (.block []) partialHead) (Open.decTo v.callees v.callees.ctr)) := by
  intro y z l₁ l₂ y' z' ⟨⟨s,icb,p,agree,h⟩,⟨s',iv,q,agree',h'⟩⟩ e₁ e₂
  have shape : a.source s'.mem i = a.source s.mem i := (agree' _ hi).1.trans (agree _ hi).1.symm
  have n : a.size s'.mem i = a.size s.mem i := (agree' _ hi).2.trans (agree _ hi).2.symm
  have off : a.off s'.mem i = a.off s.mem i :=
    (offEq q.descFit agree' (Nat.le_of_lt hi)).trans (offEq p.descFit agree (Nat.le_of_lt hi)).symm
  by_cases nz : a.size s.mem i=0
  · have args := h.args
    have args' := h'.args
    rw [nz] at args
    rw [shape,n,off,nz] at args'
    exact emptyPiece_ct v p.lay y z l₁ l₂ y' z' ⟨args,args'⟩ e₁ e₂
  · have nz' : a.size s'.mem i≠0 := by rwa [n]
    have pre (t z : State) {iv : Block} (q : TextInput N a t) (w : TextInput.Loaded N a t iv i z)
        (pos : a.size t.mem i ≠ 0) :
        StreamPiecePre N a.C a.st a.W a.SP (a.source t.mem i) (atByte a.O (a.off t.mem i)) (a.size t.mem i)
          a.rounds (a.off t.mem i) z := by
      have le := q.off_le (Nat.le_of_lt hi)
      have r : RoundsAt z.mem a.W a.rounds :=
        ⟨(slot_frame w.frame (q.frameSlot le (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))).trans
          q.rounds.1,q.rounds.2⟩
      obtain c := ciph_frame w.frame (q.outsideCtx.frame q.lay (q.ctxDst.sub_right (Region.sub_prefix le))) r.2
      exact ⟨w.args,q.accesses hi pos w.rd w.wr w.dest,r,
        by rw [w.wr]; exact q.spW _ _ ⟨_,List.mem_singleton_self _,Region.contains_self _ _⟩,iv,by rw [c]; exact w.ctr⟩
    obtain hy := pre s y p h nz
    obtain hz := pre s' z q h' nz'
    rw [shape,n,off] at hz
    have lim:=p.lenLt
    have span:=p.span hi
    exact processPiece_ct v p.lay rfl (p.input i hi nz) (by omega_using [span,lim]) p.argCtx y z l₁ l₂ y' z'
      ⟨hy,hz⟩ e₁ e₂

private abbrev stepCode (v : GcmImpl) : Prog isa := .seq (.block nextPiece) (.seq (.ite .e (.block []) partialHead)
  (.seq (Open.decTo v.callees v.callees.ctr)
    (.block [.mov .ecx (slot tglO),.alu .sub .ecx (imm 1),.store (at_ .ebp tglO) .ecx])))

private abbrev nextI (N : Nat) (a : Text) (m : Mem) (i : Nat) (z : State) :=
  AtI N a m (i+1) z ∧ z.zf=some (decide (i+1=a.count))

private theorem step_rel (v : GcmImpl) [WSize N v.ctr.scr] {a : Text} {m : Mem} {i : Nat} (hi : i<a.count) :
    RelCT isa (fun x y => AtI N a m i x ∧ AtI N a m i y) (stepCode v)
      (fun x y => nextI N a m i x ∧ nextI N a m i y) := by
  have loads : ∀ t, AtI N a m i t → WP isa (.block nextPiece) t (LoadedI N a m i) := by
    rintro t ⟨s,iv,p,eq,h⟩
    exact WP.mono (p.load_ok hi h) fun _ g => ⟨s,iv,p,eq,g⟩
  have procs : ∀ t, LoadedI N a m i t → WP isa
      (.seq (.ite .e (.block []) partialHead) (Open.decTo v.callees v.callees.ctr)) t (AdvancedI N a m i) := by
    rintro t ⟨s,iv,p,eq,h⟩
    exact WP.mono (p.advance_ok v hi h) fun _ g => ⟨s,iv,p,eq,g⟩
  have ct : CT (AtI N a m i) (stepCode v) :=
    CT.seq load_ct loads (RelCT.assoc (CT.seq (advance_ct v hi) procs (CT.taint [.ebp] (fun _ _ ⟨_,_,_,_,x⟩ ⟨_,_,_,_,y⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact x.env.ebp.trans y.env.ebp.symm) (by taint_decide))))
  have wp : ∀ u, AtI N a m i u → WP isa (stepCode v) u (nextI N a m i) := by
    intro u h
    refine WP.seq (WP.mono (loads u h) ?_)
    intro x hx
    refine WP.assoc (WP.seq (WP.mono (procs x hx) ?_))
    rintro z ⟨s,iv,p,eq,g⟩
    exact WP.mono (p.countdown hi g) fun t ⟨q,zf⟩ => ⟨⟨s,iv,p,eq,q⟩,zf⟩
  exact (ct.wp (F₁:=nextI N a m i) (F₂:=nextI N a m i) fun u t h => ⟨wp u h.1,wp t h.2⟩).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem loop_ct (v : GcmImpl) [WSize N v.ctr.scr] {a : Text} {m : Mem} (nonzero : a.count ≠ 0) :
    CT (AtI N a m 0) (.loop (stepCode v) .ne) := by
  refine (RelCT.loop (Q:=fun _ _ => True)
    (fun n x y => ∃ i, n=a.count-i ∧ i<a.count ∧ AtI N a m i x ∧ AtI N a m i y) (fun n => ?_) (a.count-0)).mono
    (fun x y h => ⟨0,rfl,Nat.pos_of_ne_zero nonzero,h⟩) (fun _ _ h => h)
  refine RelCT.exists_ fun i => ?_
  by_cases next : n=a.count-i ∧ i<a.count
  · obtain ⟨rfl,hi⟩ := next
    refine (step_rel (m:=m) v hi).mono (fun _ _ h => h.2.2) ?_
    rintro x y ⟨⟨px,zx⟩,⟨py,zy⟩⟩
    have ex : isa.eval .ne x=some (!decide (i+1=a.count)) := by show x.zf.map (!·)=_; rw [zx]; rfl
    have ey : isa.eval .ne y=some (!decide (i+1=a.count)) := by show y.zf.map (!·)=_; rw [zy]; rfl
    refine ⟨ex.trans ey.symm,fun _ => trivial,fun go => ?_⟩
    rw [ex] at go
    have lt : i+1<a.count := by simp at go; omega_using [go,hi]
    exact ⟨a.count-(i+1),by omega_using [hi],i+1,rfl,lt,px,py⟩
  · exact RelCT.of_false fun _ _ h => next ⟨h.1,h.2.1⟩

private theorem pieces_ct (v : GcmImpl) [WSize N v.ctr.scr] {a : Text} {m : Mem} :
    CT (AtI N a m 0) (pieces v.callees) := by
  refine CT.seq (J:=fun z => AtI N a m 0 z ∧ z.zf=some (decide (a.count=0))) (CT.taint [.ebp]
    (fun _ _ ⟨_,_,_,_,x⟩ ⟨_,_,_,_,y⟩ r hr => by simp only [List.mem_singleton] at hr; subst hr; exact x.env.ebp.trans y.env.ebp.symm)
    (by taint_decide)) ?_ ?_
  · rintro z ⟨s,iv,p,eq,h⟩
    have cnt : slotv z.mem a.W tglO=BitVec.ofNat 32 a.count := h.count
    refine WP.of_runBlock ⟨_,by xrun [h.env.ebp,p.lay.aW,h.env.wIn',cnt],?_⟩
    exact ⟨⟨s,iv,p,eq,⟨⟨h.env.ebp,h.env.esi,h.env.esp,h.env.ctxR,h.env.stW,h.env.wW,h.env.ctx⟩,
      h.rd,h.wr,h.ptr,h.count,h.off,h.frame,h.ctr,h.out⟩⟩,congrArg some (and_self_beq32 p.countLt)⟩
  refine CT.ite (decide (a.count=0)) (fun _ h => h.2) (fun _ => CT.nil) (fun nz => ?_)
  exact (loop_ct v (by simpa using nz)).mono (fun _ h => h.1)

theorem pieces_rel (v : GcmImpl) [WSize N v.ctr.scr] {a : Text} {s t : State} {iv jv : Block}
    (p : TextInput N a s) (q : TextInput N a t) (desc : DescEq a s.mem t.mem)
    (hs : TextAt N a s iv 0 s) (ht : TextAt N a t jv 0 t) :
    RelCT isa (fun x y => x=s ∧ y=t) (pieces v.callees) (fun _ _ => True) :=
  RelCT.mono (pieces_ct (a:=a) (m:=t.mem) v) (fun x y h => by
    rw [h.1,h.2]
    exact ⟨⟨s,iv,p,desc,hs⟩,⟨t,jv,q,fun _ _ => ⟨rfl,rfl⟩,ht⟩⟩) (fun _ _ h => h)

end VG.Proof.AesGcm.X86.DirectGather
