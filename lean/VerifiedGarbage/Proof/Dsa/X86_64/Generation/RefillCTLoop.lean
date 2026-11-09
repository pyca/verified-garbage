module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTAttempt
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTSeed
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputPlan
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTAttempt
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTSeed
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputPlan
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.Registration

/-! # Timing of the refillable-tape search's controller

The controller's public state between seeds (`LoopPublic`): the search's
context and its current `h` tape, the octets of the witness tape consumed,
the seeds it may still reject and the pointers to `used` and `state`. Each
seed's attempt leaves a public `h` tape (`refillHs`), status and cursor, all
functions of the tape's octets (`LoopPublic.res`), so two runs of the
controller with the same public state take the same branches and leave the
same public state (`DonePublic` when it stops). -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.MillerRabin.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

variable {checkName : String}

/-- Where the controller's words and the pointers it holds are, apart from
the search's other memory. -/
structure CtlOK (c : GenerationContext) (c0 c1 : BitVec 64) : Prop where
  changed : ∀ r ∈ c.changed, (Refill.ctlRegion c.geo.F).Disjoint r
  rand : (⟨c.rand.ptr, c.rand.bytes.length⟩ : Region).Disjoint (Refill.ctlRegion c.geo.F)
  seeds : (⟨c.seeds.ptr, c.seeds.bytes.length⟩ : Region).Disjoint (Refill.ctlRegion c.geo.F)
  hash : (Refill.ctlRegion c.geo.F).Disjoint ⟨c.geo.hash, oRsa⟩
  bound : c.geo.F.toNat + 328 ≤ 2 ^ 64

theorem CtlOK.gm {c : GenerationContext} {c0 c1 : BitVec 64} (ok : CtlOK c c0 c1) {hs : GenerationTape c.geo}
    (hin : Region.Sub ⟨hs.ptr, hs.bytes.length⟩ ⟨c.rand.ptr, c.rand.bytes.length⟩)
    {W : Nat → BitVec 64} {s t : State} (hm : GenerationMemory (c.withHs hs) W s)
    (hf : Frame [Refill.ctlRegion c.geo.F] s.mem t.mem) (hsp : t.gpr .rsp = s.gpr .rsp)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) : GenerationMemory (c.withHs hs) W t := by
  obtain ⟨V, R⟩ := hm.rep
  have Rt : Rep t.mem c.geo.F c.geo.hash V W :=
    rep_of_disjoint_frame R hf (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact (Refill.ctl_frame _).symm)
      (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact ok.hash.symm)
  exact ⟨lay_of_rep hm.layout R Rt rfl hsp hw, ⟨V, Rt⟩, hm.slots, hm.scratch.congr hw,
    Refill.tapeMemory_ctl hm.seeds hf ok.seeds hr hw, Refill.tapeMemory_ctl hm.hs hf (ok.rand.sub_left hin) hr hw,
    Refill.tapeMemory_ctl hm.rand hf ok.rand hr hw⟩

theorem CtlOK.word {c : GenerationContext} {c0 c1 : BitVec 64} (ok : CtlOK c c0 c1) {m m' : Mem}
    (hf : Frame c.changed m m') {k : Nat} (hk : k < 4) :
    Refill.ctlWord m' c.geo.F k = Refill.ctlWord m c.geo.F k :=
  Refill.ctlWord_frame hf ok.changed hk

theorem refillHs_sub (p : GenerationContext) (seed rest : List Byte)
    (hin : Region.Sub ⟨p.hs.ptr, p.hs.bytes.length⟩ ⟨p.rand.ptr, p.rand.bytes.length⟩) :
    Region.Sub ⟨(refillHs p seed rest).ptr, (refillHs p seed rest).bytes.length⟩ ⟨p.rand.ptr, p.rand.bytes.length⟩ := by
  unfold refillHs
  split
  · split
    · rw [GenerationTape.window_length]
      exact Offset.sub_base p.rand.ptr (by omega)
    · exact hin
  · exact hin

/-- Where the buffers the search's end writes are, apart from its other memory. -/
structure EndOK (c : GenerationContext) (c0 c1 : BitVec 64) (wr : List Region) : Prop where
  stIn : (⟨c1, 32⟩ : Region) ∈ wr
  usIn : (⟨c0, 8⟩ : Region) ∈ wr
  stBound : c1.toNat + 32 ≤ 2 ^ 64
  usBound : c0.toNat + 8 ≤ 2 ^ 64
  stChanged : ∀ r ∈ c.changed, (⟨c1, 32⟩ : Region).Disjoint r
  usChanged : ∀ r ∈ c.changed, (⟨c0, 8⟩ : Region).Disjoint r
  stRand : (⟨c1, 32⟩ : Region).Disjoint ⟨c.rand.ptr, c.rand.bytes.length⟩
  usRand : (⟨c0, 8⟩ : Region).Disjoint ⟨c.rand.ptr, c.rand.bytes.length⟩
  stSeeds : (⟨c1, 32⟩ : Region).Disjoint ⟨c.seeds.ptr, c.seeds.bytes.length⟩
  usSeeds : (⟨c0, 8⟩ : Region).Disjoint ⟨c.seeds.ptr, c.seeds.bytes.length⟩
  stHash : (⟨c1, 32⟩ : Region).Disjoint ⟨c.geo.hash, oRsa⟩
  usHash : (⟨c0, 8⟩ : Region).Disjoint ⟨c.geo.hash, oRsa⟩
  stCtl : (⟨c1, 32⟩ : Region).Disjoint (Refill.ctlRegion c.geo.F)
  usCtl : (⟨c0, 8⟩ : Region).Disjoint (Refill.ctlRegion c.geo.F)
  out : OutputPlan c
  outIn : (⟨c.saved 6, 2 * c.geo.pLen + c.geo.qLen⟩ : Region) ∈ wr
  lenBound : c.rand.bytes.length < 2 ^ 32

/-! ## The public state -/

structure LoopPublic where
  ctx : GenerationContext
  hs : GenerationTape ctx.geo
  start : Nat
  left : Nat
  c0 : BitVec 64
  c1 : BitVec 64
  ws : List Region
  wr : List Region
  header : PrimeHeaderLayout ctx.geo.B wr
  startBound : start ≤ ctx.rand.bytes.length
  leftBound : left ≤ Spec.Dsa.parameterSeeds
  hsIn : Region.Sub ⟨hs.ptr, hs.bytes.length⟩ ⟨ctx.rand.ptr, ctx.rand.bytes.length⟩
  ok : CtlOK ctx c0 c1
  ends : EndOK ctx c0 c1 wr

def LoopPublic.context (P : LoopPublic) : GenerationContext := P.ctx.withHs P.hs

/-- The seed's octets and the witness tape after them. -/
def LoopPublic.seedBytes (P : LoopPublic) : List Byte :=
  (P.ctx.rand.bytes.drop P.start).take P.ctx.geo.qLen

def LoopPublic.rest (P : LoopPublic) : List Byte := P.ctx.rand.bytes.drop (P.start + P.ctx.geo.qLen)

/-- The seed's result. -/
def LoopPublic.res (P : LoopPublic) : Option (Option Spec.Dsa.Params × List Byte) :=
  VG.Proof.Dsa.Generation.refillAttempt P.ctx.geo.pLen P.ctx.geo.qLen P.seedBytes P.rest

def LoopPublic.hsNext (P : LoopPublic) : GenerationTape P.ctx.geo := refillHs P.context P.seedBytes P.rest

def LoopPublic.after (P : LoopPublic) : Nat :=
  match P.res with
  | some (_, r) => P.ctx.rand.bytes.length - r.length
  | none => P.start

def LoopPublic.status (P : LoopPublic) : BitVec 64 :=
  match P.res with
  | none => 0
  | some (none, _) => 3
  | some (some _, _) => 1

def LoopPublic.next (P : LoopPublic) : LoopPublic where
  ctx := P.ctx
  hs := P.hsNext
  start := P.after
  left := P.left - 1
  c0 := P.c0
  c1 := P.c1
  ws := P.ws
  wr := P.wr
  header := P.header
  startBound := by
    unfold LoopPublic.after; split
    · exact Nat.sub_le _ _
    · exact P.startBound
  leftBound := by have := P.leftBound; omega
  hsIn := refillHs_sub P.context _ _ P.hsIn
  ok := P.ok
  ends := P.ends

/-- The controller's state when it stops. -/
structure DonePublic where
  ctx : GenerationContext
  hs : GenerationTape ctx.geo
  status : BitVec 64
  cursor : Nat
  left : Nat
  used : Nat
  c0 : BitVec 64
  c1 : BitVec 64
  ws : List Region
  wr : List Region
  cursorBound : cursor ≤ ctx.rand.bytes.length
  hsIn : Region.Sub ⟨hs.ptr, hs.bytes.length⟩ ⟨ctx.rand.ptr, ctx.rand.bytes.length⟩
  ok : CtlOK ctx c0 c1
  ends : EndOK ctx c0 c1 wr

def LoopPublic.stop (P : LoopPublic) (status : BitVec 64) : DonePublic :=
  ⟨P.ctx, P.hs, status, P.start, P.left, 0, P.c0, P.c1, P.ws, P.wr, P.startBound, P.hsIn, P.ok, P.ends⟩

def LoopPublic.done (P : LoopPublic) : DonePublic :=
  ⟨P.ctx, P.hsNext, P.status, P.start, P.left, P.after, P.c0, P.c1, P.ws, P.wr, P.startBound,
    refillHs_sub P.context _ _ P.hsIn, P.ok, P.ends⟩

/-! ## The predicates -/

def CtlAt (F : Addr) (c0 c1 : BitVec 64) (left : Nat) (t : State) : Prop :=
  Refill.ctlWord t.mem F 0 = c0 ∧ Refill.ctlWord t.mem F 1 = c1 ∧
  Refill.ctlWord t.mem F 2 = BitVec.ofNat 64 left ∧ Refill.ctlRegion F ∈ t.wr

def RefillLoopBefore (n pLen qLen : Nat) (P : LoopPublic) (t : State) : Prop :=
  (∃ W, GenerationMemory P.context W t ∧ W 16 = BitVec.ofNat 64 P.start ∧ W 10 = 0) ∧
  CtlAt P.ctx.geo.F P.c0 P.c1 P.left t ∧ FrV n P.ctx.geo.F P.ws t ∧ t.wr = P.wr ∧
  P.ctx.geo.pLen = pLen ∧ P.ctx.geo.qLen = qLen

def DoneAt (n pLen qLen : Nat) (D : DonePublic) (t : State) : Prop :=
  (∃ W, GenerationMemory (D.ctx.withHs D.hs) W t ∧ W 19 = D.status ∧
    (D.status = 1 → W 16 = BitVec.ofNat 64 D.used)) ∧
  CtlAt D.ctx.geo.F D.c0 D.c1 D.left t ∧ Refill.ctlWord t.mem D.ctx.geo.F 3 = BitVec.ofNat 64 D.cursor ∧
  FrV n D.ctx.geo.F D.ws t ∧ t.wr = D.wr ∧ (D.status = 0 ∨ D.status = 1 ∨ D.status = 2) ∧
  D.ctx.geo.pLen = pLen ∧ D.ctx.geo.qLen = qLen

/-- Before the iteration's last status test. -/
def LoopMid (n pLen qLen m : Nat) : LoopPublic ⊕ DonePublic → State → Prop
  | .inl P, t => RefillLoopBefore n pLen qLen P t ∧ (∃ W, GenerationMemory P.context W t ∧ W 19 = 3) ∧ P.left < m
  | .inr D, t => DoneAt n pLen qLen D t

def LoopPost (n pLen qLen m : Nat) : LoopPublic ⊕ DonePublic → State → Prop
  | .inl P, t => isa.eval .e t = some true ∧ RefillLoopBefore n pLen qLen P t ∧ P.left < m
  | .inr D, t => isa.eval .e t = some false ∧ DoneAt n pLen qLen D t

theorem two_image {α β : Type} {Φ : β → State → Prop} (f : α → β) {s t : State}
    (h : Two (fun a s => Φ (f a) s) s t) : Two Φ s t :=
  let ⟨a, h₁, h₂⟩ := h; ⟨f a, h₁, h₂⟩

theorem loopBefore_rsp {n pLen qLen : Nat} {P : LoopPublic} {t : State} (h : RefillLoopBefore n pLen qLen P t) :
    t.gpr .rsp = P.ctx.geo.F := h.2.2.1.rsp

/-- `RefillLoopBefore` across a step that keeps the memory but `rax` and `rcx`. -/
theorem loopBefore_keep {n pLen qLen : Nat} {P : LoopPublic} {s t : State} (h : RefillLoopBefore n pLen qLen P s)
    (hm : t.mem = s.mem) (hk : Keep [.rax, .rcx] s t) : RefillLoopBefore n pLen qLen P t := by
  obtain ⟨⟨W, hW, h16, h10⟩, ⟨c0, c1, c2, cw⟩, hf, hw, hp, hq⟩ := h
  refine ⟨⟨W, hW.congr2 hm hk, h16, h10⟩, ⟨?_, ?_, ?_, hk.2.2 ▸ cw⟩, hf.congr (hk.gpr (by decide)) hk.2.2,
    hk.2.2.trans hw, hp, hq⟩
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c0
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c1
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c2

end VG.Proof.Dsa.X86_64.Generation
