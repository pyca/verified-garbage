module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTLoop
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
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTLoop
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

/-! # Timing of one step of the refillable-tape search's controller -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.MillerRabin.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

variable {checkName : String}

/-! ## The iteration's public states -/

def Begun (n pLen qLen : Nat) (P : LoopPublic) (t : State) : Prop :=
  LoopBefore n pLen qLen P t ∧ Refill.ctlWord t.mem P.ctx.geo.F 3 = BitVec.ofNat 64 P.start ∧
  t.gpr .rax = BitVec.ofNat 64 P.start

def Started (n pLen qLen : Nat) (P : LoopPublic) (t : State) : Prop :=
  Begun n pLen qLen P t ∧ isa.eval .e t = some (decide (P.left = 0))

def Roomed (n pLen qLen : Nat) (P : LoopPublic) (t : State) : Prop :=
  Begun n pLen qLen P t ∧ P.left ≠ 0 ∧
  isa.eval .b t = some (decide (P.ctx.rand.bytes.length - P.start < P.ctx.geo.qLen))

/-- The seed's public inputs. -/
def LoopPublic.seedPub (P : LoopPublic) (room : P.start + P.ctx.geo.qLen ≤ P.ctx.rand.bytes.length) :
    SeedPublic where
  context := P.context
  seed := P.ctx.rand.slice P.start P.ctx.geo.qLen room
  length := by
    show ((P.ctx.rand.bytes.drop P.start).take P.ctx.geo.qLen).length = P.ctx.geo.qLen
    simp only [List.length_take, List.length_drop]; omega
  used := P.start + P.ctx.geo.qLen
  seedCursor := 0
  bound := room
  ws := P.ws
  wr := P.wr
  header := P.header

def Seeded (n pLen qLen : Nat) (P : LoopPublic) (t : State) : Prop :=
  (∃ room, SeedAttemptBefore n pLen qLen (P.seedPub room) t) ∧
  CtlAt P.ctx.geo.F P.c0 P.c1 P.left t ∧ Refill.ctlWord t.mem P.ctx.geo.F 3 = BitVec.ofNat 64 P.start ∧
  P.left ≠ 0

def Attempted (n pLen qLen : Nat) (P : LoopPublic) (t : State) : Prop :=
  (∃ W used, GenerationMemory (P.ctx.withHs P.hsNext) W t ∧ used ≤ P.ctx.rand.bytes.length ∧
    W 16 = BitVec.ofNat 64 used ∧ W 10 = 0 ∧ SeedOutcome P.context P.res W used t) ∧
  CtlAt P.ctx.geo.F P.c0 P.c1 P.left t ∧ Refill.ctlWord t.mem P.ctx.geo.F 3 = BitVec.ofNat 64 P.start ∧
  FrV n P.ctx.geo.F P.ws t ∧ t.wr = P.wr ∧ P.left ≠ 0 ∧ P.ctx.geo.pLen = pLen ∧ P.ctx.geo.qLen = qLen

def Tested (n pLen qLen : Nat) (P : LoopPublic) (t : State) : Prop :=
  Attempted n pLen qLen P t ∧ isa.eval .e t = some (P.status == 3)

/-! ## Each piece -/

theorem head_ready {n pLen qLen : Nat} {P : LoopPublic} {s : State} (h : LoopBefore n pLen qLen P s) :
    WP isa (.block [.mov .rax (.mem (sp 128)), .store (Impl.Dsa.X86_64.Generation.Refill.ctl 3) .rax,
        .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 2)), .alu .test .rcx (.reg .rcx)]) s
      (Started n pLen qLen P) := by
  obtain ⟨⟨W, hm, h16, h10⟩, ⟨c0, c1, c2, cw⟩, hf, hw, hp, hq⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  have h2 : (s.mem.writeW (off P.ctx.geo.F 320) (BitVec.ofNat 64 P.start)).readW (off P.ctx.geo.F 312) 64 =
      BitVec.ofNat 64 P.left := by
    rw [← c2]; exact Refill.ctlWord_write_other s.mem _ (j := 2) (k := 3) (by decide) (by decide) (by decide) _
  have ln : P.left < 2 ^ 64 := by have := P.leftBound; unfold Spec.Dsa.parameterSeeds at this; omega
  refine WP.mono (Refill.iterStart_ok hm.layout R cw P.ok.bound h16 ln h2) fun t ⟨rax, zf, mt, kt⟩ => ?_
  have fr : Frame [Refill.ctlRegion P.ctx.geo.F] s.mem t.mem := by
    rw [mt]; exact Refill.ctl_write s.mem _ (k := 3) (by decide) _
  have hmt := P.ok.gm P.hsIn hm fr (kt.gpr (by decide)) kt.2.1 kt.2.2
  refine ⟨⟨⟨⟨W, hmt, h16, h10⟩, ⟨?_, ?_, ?_, kt.2.2 ▸ cw⟩, hf.congr (kt.gpr (by decide)) kt.2.2,
    kt.2.2.trans hw, hp, hq⟩, ?_, rax⟩, by simp only [eval, zf]⟩
  · rw [mt]; exact (Refill.ctlWord_write_other s.mem _ (j := 0) (k := 3) (by decide) (by decide) (by decide) _).trans c0
  · rw [mt]; exact (Refill.ctlWord_write_other s.mem _ (j := 1) (k := 3) (by decide) (by decide) (by decide) _).trans c1
  · rw [mt]; exact (Refill.ctlWord_write_other s.mem _ (j := 2) (k := 3) (by decide) (by decide) (by decide) _).trans c2
  · rw [mt]; exact Refill.ctlWord_write_self s.mem _ 3 _

/-- A status word stored, with the controller's words kept. -/
theorem stopped_ready {n pLen qLen m : Nat} {P : LoopPublic} {t : State} (h : Begun n pLen qLen P t)
    (status : Nat) (hs : status = 0 ∨ status = 2) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.stackStatus status)) t
      (LoopMid n pLen qLen m (.inr (P.stop (BitVec.ofNat 64 status)))) := by
  obtain ⟨⟨⟨W, hm, _, _⟩, ⟨c0, c1, c2, cw⟩, hf, hw, hp, hq⟩, c3, _⟩ := h
  refine WP.mono (Refill.statusMem_ok hm status (by omega)) fun u ⟨mu, fu, ku⟩ => ?_
  have cwd : ∀ k < 4, Refill.ctlWord u.mem P.ctx.geo.F k = Refill.ctlWord t.mem P.ctx.geo.F k :=
    fun k hk => P.ok.word fu hk
  refine ⟨⟨_, mu, by simp [upd, LoopPublic.stop], fun h1 => ?_⟩,
    ⟨(cwd 0 (by decide)).trans c0, (cwd 1 (by decide)).trans c1, (cwd 2 (by decide)).trans c2, ku.2.2 ▸ cw⟩,
    (cwd 3 (by decide)).trans c3, hf.congr (ku.gpr (by decide)) ku.2.2, ku.2.2.trans hw, ?_, hp, hq⟩
  · rcases hs with rfl | rfl <;> simp [LoopPublic.stop] at h1
  · rcases hs with rfl | rfl <;> simp [LoopPublic.stop]

theorem room_ready {n pLen qLen : Nat} {P : LoopPublic} {t : State} (h : Started n pLen qLen P t)
    (he : isa.eval .e t = some false) :
    WP isa (.block [.mov .rcx (.mem (sp 120)), .alu .sub .rcx (.reg .rax),
        .alu .cmp .rcx (.imm (BitVec.ofNat 32 qLen))]) t (Roomed n pLen qLen P) := by
  obtain ⟨hb, hz⟩ := h
  obtain ⟨hl, c3, rax⟩ := id hb
  obtain ⟨⟨W, hm, _, _⟩, _, _, _, _, hq⟩ := id hl
  obtain ⟨V, R⟩ := hm.rep
  have ne : P.left ≠ 0 := by
    intro e; have := hz.symm.trans he; simp [e] at this
  have h15 : W 15 = BitVec.ofNat 64 P.ctx.rand.bytes.length :=
    (hm.slots 15 (by simp [generationSlots])).trans (P.ctx.withHs P.hs).randLengthSlot
  have q31 : qLen < 2 ^ 31 := by rcases P.ctx.geo.qWidth with hh | hh <;> omega
  refine WP.mono (Refill.roomCheck_ok hm.layout R rax h15 P.startBound P.ctx.rand.size q31)
    fun u ⟨cf, mu, ku⟩ => ?_
  refine ⟨⟨loopBefore_keep hl mu (ku.mono (by decide)), by rw [Refill.ctlWord_eq_of_mem mu]; exact c3,
    (ku.gpr (by decide)).trans rax⟩, ne, by simp only [eval, cf, hq]⟩

theorem seedStart_ready {n pLen qLen : Nat} {P : LoopPublic} {t : State} (h : Roomed n pLen qLen P t)
    (hb : isa.eval .b t = some false) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.Refill.seedStart qLen)) t (Seeded n pLen qLen P) := by
  obtain ⟨⟨⟨⟨W, hm, _, h10⟩, ⟨c0, c1, c2, cw⟩, hf, hw, hp, hq⟩, c3, rax⟩, ne, hc⟩ := h
  have room : P.start + P.ctx.geo.qLen ≤ P.ctx.rand.bytes.length := by
    have h1 := hc.symm.trans hb; have := P.startBound
    simp only [Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt] at h1; omega
  obtain ⟨V, R⟩ := hm.rep
  have h13 : W 13 = P.ctx.rand.ptr :=
    (hm.slots 13 (by simp [generationSlots])).trans (P.ctx.withHs P.hs).randSlot
  have q31 : qLen < 2 ^ 31 := by rcases P.ctx.geo.qWidth with hh | hh <;> omega
  refine WP.mono (Refill.seedStart_ok hm.layout R rax h13 q31) fun u ⟨Lu, Ru, fu, ku⟩ => ?_
  have hmu : GenerationMemory P.context (upd (upd W 1 (off P.ctx.rand.ptr P.start)) 16
      (BitVec.ofNat 64 (P.start + qLen))) u := by
    refine hm.frame Lu ⟨V, Ru⟩ ?_ (GenerationContext.frame_single fu) ku.2.1 ku.2.2
    intro k hk
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have cwd : ∀ k < 4, Refill.ctlWord u.mem P.ctx.geo.F k = Refill.ctlWord t.mem P.ctx.geo.F k := fun k hk =>
    Refill.ctlWord_frame fu (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact Refill.ctl_frame _) hk
  subst hq
  refine ⟨⟨room, ⟨⟨_, hmu, by simp [upd, LoopPublic.seedPub, GenerationTape.slice], by simp [upd, LoopPublic.seedPub],
    by simpa [upd, LoopPublic.seedPub] using h10⟩, hmu.rand.slice room, hf.congr (ku.gpr (by decide)) ku.2.2,
    ku.2.2.trans hw, rfl⟩, hp⟩,
    ⟨(cwd 0 (by decide)).trans c0, (cwd 1 (by decide)).trans c1, (cwd 2 (by decide)).trans c2, ku.2.2 ▸ cw⟩,
    (cwd 3 (by decide)).trans c3, ne⟩

theorem attempt_ready (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    {n pLen qLen : Nat} {P : LoopPublic} {t : State} (h : Seeded n pLen qLen P t) :
    WP isa (Impl.Dsa.X86_64.Generation.Refill.refillAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm
      T.run pLen qLen) t (Attempted n pLen qLen P) := by
  obtain ⟨⟨room, ⟨⟨W, hm, h1, h16, h10⟩, seed, hf, hw, hq⟩, hp⟩, ⟨c0, c1, c2, cw⟩, c3, ne⟩ := h
  have call := ctAttempt_ok (checkName := checkName) H M Sq T hm (P.seedPub room).seed (P.seedPub room).length
    seed h1 h16 room
  change P.ctx.geo.pLen = pLen at hp
  change P.ctx.geo.qLen = qLen at hq
  subst hp; subst hq
  refine WP.mono call fun u ⟨W', used, mu, hu, u16, slots, outcome, fu, ru, wu⟩ => ?_
  have cwd : ∀ k < 4, Refill.ctlWord u.mem P.ctx.geo.F k = Refill.ctlWord t.mem P.ctx.geo.F k :=
    fun k hk => P.ok.word fu hk
  have mu' : GenerationMemory (P.ctx.withHs P.hsNext) W' u := Refill.withHs_withHs P.ctx P.hs _ ▸ mu
  refine ⟨⟨W', used, mu', hu, u16, ?_, outcome⟩,
    ⟨(cwd 0 (by decide)).trans c0, (cwd 1 (by decide)).trans c1, (cwd 2 (by decide)).trans c2, wu ▸ cw⟩,
    (cwd 3 (by decide)).trans c3, hf.congr (mu.layout.rsp.trans hm.layout.rsp.symm) wu, wu.trans hw, ne, rfl, rfl⟩
  rw [slots 10 (by simp [refillSlots]), h10]; rfl

theorem LoopPublic.status_cases (P : LoopPublic) : P.status = 0 ∨ P.status = 1 ∨ P.status = 3 := by
  unfold LoopPublic.status; split <;> simp

theorem outcome_public {P : LoopPublic} {W : Nat → BitVec 64} {used : Nat} {t : State}
    (h : SeedOutcome P.context P.res W used t) (hu : used ≤ P.ctx.rand.bytes.length) :
    W 19 = P.status ∧ (P.status ≠ 0 → used = P.after) := by
  rcases h with ⟨h19, hr⟩ | ⟨h19, hr⟩ | ⟨h19, a, hr, _⟩
  · exact ⟨by rw [h19]; simp [LoopPublic.status, hr], fun h0 => by simp [LoopPublic.status, hr] at h0⟩
  · refine ⟨by rw [h19]; simp [LoopPublic.status, hr], fun _ => ?_⟩
    simp only [LoopPublic.after, hr]
    change used = P.ctx.rand.bytes.length - (P.ctx.rand.bytes.drop used).length
    rw [List.length_drop]; omega
  · refine ⟨by rw [h19]; simp [LoopPublic.status, hr], fun _ => ?_⟩
    simp only [LoopPublic.after, hr]
    change used = P.ctx.rand.bytes.length - (P.ctx.rand.bytes.drop used).length
    rw [List.length_drop]; omega

theorem attempted_keep {n pLen qLen : Nat} {P : LoopPublic} {s t : State} (h : Attempted n pLen qLen P s)
    (hm : t.mem = s.mem) (hk : Keep [.rax] s t) : Attempted n pLen qLen P t := by
  obtain ⟨⟨W, used, hW, hu, h16, h10, outcome⟩, ⟨c0, c1, c2, cw⟩, c3, hf, hw, rest⟩ := h
  refine ⟨⟨W, used, hW.congr hm hk, hu, h16, h10, ?_⟩, ⟨?_, ?_, ?_, hk.2.2 ▸ cw⟩, ?_,
    hf.congr (hk.gpr (by decide)) hk.2.2, hk.2.2.trans hw, rest⟩
  · rcases outcome with o | o | ⟨h19, a, hr, bytes⟩
    · exact Or.inl o
    · exact Or.inr (Or.inl o)
    · exact Or.inr (Or.inr ⟨h19, a, hr, hm ▸ bytes⟩)
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c0
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c1
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c2
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c3

theorem test_ready {n pLen qLen : Nat} {P : LoopPublic} {t : State} (h : Attempted n pLen qLen P t) :
    WP isa (.block Impl.Dsa.X86_64.Generation.tapeStatus) t (Tested n pLen qLen P) := by
  obtain ⟨⟨W, used, hm, hu, _, _, outcome⟩, _⟩ := id h
  have h19 := (outcome_public outcome hu).1
  refine WP.mono (Refill.statusTest_ok hm) fun u ⟨z, _, mu, ku⟩ => ?_
  exact ⟨attempted_keep h mu ku, by rw [z, h19]⟩

theorem reject_ready {n pLen qLen m : Nat} {P : LoopPublic} {t : State} (h : Tested n pLen qLen P t)
    (he : isa.eval .e t = some true) (hl : P.left = m) :
    WP isa (.block Impl.Dsa.X86_64.Generation.Refill.rejected) t (LoopMid n pLen qLen m (.inl P.next)) := by
  obtain ⟨⟨⟨W, used, hm, hu, h16, h10, outcome⟩, ⟨c0, c1, c2, cw⟩, c3, hf, hw, ne, hp, hq⟩, hs⟩ := h
  have s3 : P.status = 3 := by
    have := hs.symm.trans he; simpa using this
  obtain ⟨h19, hafter⟩ := outcome_public outcome hu
  have uafter := hafter (by rw [s3]; decide)
  have ln : P.left - 1 + 1 < 2 ^ 64 := by have := P.leftBound; unfold Spec.Dsa.parameterSeeds at this; omega
  have h2 : t.mem.readW (off P.ctx.geo.F 312) 64 = BitVec.ofNat 64 (P.left - 1 + 1) := by
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero ne)]; exact c2
  refine WP.mono (Refill.rejected_ok hm.layout.rsp cw P.ok.bound ln h2) fun u ⟨mu, ku⟩ => ?_
  have fr : Frame [Refill.ctlRegion P.ctx.geo.F] t.mem u.mem := by
    rw [mu]; exact Refill.ctl_write t.mem _ (k := 2) (by decide) _
  have hmu := P.ok.gm (refillHs_sub P.context _ _ P.hsIn) hm fr (ku.gpr (by decide)) ku.2.1 ku.2.2
  refine ⟨⟨⟨W, hmu, by rw [h16, uafter]; rfl, h10⟩, ⟨?_, ?_, ?_, ku.2.2 ▸ cw⟩,
    hf.congr (ku.gpr (by decide)) ku.2.2, ku.2.2.trans hw, hp, hq⟩, ⟨W, hmu, h19.trans s3⟩, ?_⟩
  · rw [mu]; exact (Refill.ctlWord_write_other t.mem _ (j := 0) (k := 2) (by decide) (by decide) (by decide) _).trans c0
  · rw [mu]; exact (Refill.ctlWord_write_other t.mem _ (j := 1) (k := 2) (by decide) (by decide) (by decide) _).trans c1
  · rw [mu]; exact Refill.ctlWord_write_self t.mem _ 2 _
  · show P.left - 1 < m; omega

theorem stop_ready {n pLen qLen m : Nat} {P : LoopPublic} {t : State} (h : Tested n pLen qLen P t)
    (he : isa.eval .e t = some false) :
    WP isa (.block []) t (LoopMid n pLen qLen m (.inr P.done)) := by
  obtain ⟨⟨⟨W, used, hm, hu, h16, _, outcome⟩, ⟨c0, c1, c2, cw⟩, c3, hf, hw, _, hp, hq⟩, hs⟩ := h
  have s3 : P.status ≠ 3 := by
    intro e; have := hs.symm.trans he; simp [e] at this
  obtain ⟨h19, hafter⟩ := outcome_public outcome hu
  refine WP.block_nil ⟨⟨W, hm, h19, fun h1 => ?_⟩, ⟨c0, c1, c2, cw⟩, c3, hf, hw, ?_, hp, hq⟩
  · change W 16 = BitVec.ofNat 64 P.after
    rw [h16, hafter (by change P.status = 1 at h1; rw [h1]; decide)]
  · rcases P.status_cases with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact absurd e s3

theorem doneAt_keep {n pLen qLen : Nat} {D : DonePublic} {s t : State} (h : DoneAt n pLen qLen D s)
    (hm : t.mem = s.mem) (hk : Keep [.rax] s t) : DoneAt n pLen qLen D t := by
  obtain ⟨⟨W, hW, rest⟩, ⟨c0, c1, c2, cw⟩, c3, hf, hw, more⟩ := h
  refine ⟨⟨W, hW.congr hm hk, rest⟩, ⟨?_, ?_, ?_, hk.2.2 ▸ cw⟩, ?_, hf.congr (hk.gpr (by decide)) hk.2.2,
    hk.2.2.trans hw, more⟩
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c0
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c1
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c2
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c3

theorem final_ready {n pLen qLen m : Nat} (x : LoopPublic ⊕ DonePublic) {t : State}
    (h : LoopMid n pLen qLen m x t) :
    WP isa (.block Impl.Dsa.X86_64.Generation.tapeStatus) t (LoopPost n pLen qLen m x) := by
  cases x with
  | inl P =>
    obtain ⟨hl, ⟨W, hm, h19⟩, hlt⟩ := h
    refine WP.mono (Refill.statusTest_ok hm) fun u ⟨z, _, mu, ku⟩ => ?_
    exact ⟨by rw [z, h19]; rfl, loopBefore_keep hl mu (ku.mono (by decide)), hlt⟩
  | inr D =>
    obtain ⟨⟨W, hm, h19, _⟩, _, _, _, _, hs, _⟩ := id h
    refine WP.mono (Refill.statusTest_ok hm) fun u ⟨z, _, mu, ku⟩ => ?_
    refine ⟨by rw [z, h19]; rcases hs with e | e | e <;> rw [e] <;> rfl, doneAt_keep h mu ku⟩

/-! ## The step -/

theorem pins_of {α : Type} {Φ : α → State → Prop} (F : α → Addr) (h : ∀ a s, Φ a s → s.gpr .rsp = F a) :
    Pins Φ [.rsp] := by
  intro a s t hs ht r hr
  obtain rfl := List.mem_singleton.mp hr
  exact (h a s hs).trans (h a t ht).symm

theorem loopMid_rsp {n pLen qLen m : Nat} : ∀ (x : LoopPublic ⊕ DonePublic) (s : State),
    LoopMid n pLen qLen m x s → s.gpr .rsp = (match x with | .inl P => P.ctx.geo.F | .inr D => D.ctx.geo.F)
  | .inl _, _, h => loopBefore_rsp h.1
  | .inr _, _, h => h.2.2.2.1.rsp

theorem iteration_ct_of {n pLen qLen : Nat} (m : Nat) {attempt : Prog isa}
    (hct : RelCT isa (Two (SeedAttemptBefore n pLen qLen)) attempt (fun _ _ => True))
    (hwp : ∀ P t, Seeded n pLen qLen P t → WP isa attempt t (Attempted n pLen qLen P))
    (troom : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rcx (.mem (sp 120)), .alu .sub .rcx (.reg .rax),
        .alu .cmp .rcx (.imm (BitVec.ofNat 32 qLen))]) hc).isSome = true)
    (tseed : ∃ hc, (taint.check (Taint.ofRegs [.rsp])
        (.block (Impl.Dsa.X86_64.Generation.Refill.seedStart qLen)) hc).isSome = true) :
    RelCT isa (Two fun P s => LoopBefore n pLen qLen P s ∧ P.left = m)
      (Impl.Dsa.X86_64.Generation.Refill.iteration attempt qLen) (Two (LoopPost n pLen qLen m)) := by
  unfold Impl.Dsa.X86_64.Generation.Refill.iteration
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq (two_piece (Ψ := fun P s => Started n pLen qLen P s ∧ P.left = m) [.rsp]
    (pins_of (fun P => P.ctx.geo.F) fun _ _ h => loopBefore_rsp h.1) (by taint_decide)
    fun P s h => WP.mono (head_ready h.1) fun _ ht => ⟨ht, h.2⟩) ?_
  refine RelCT.seq (R := Two (LoopMid n pLen qLen m)) ?_ (two_piece [.rsp]
    (pins_of _ fun x s h => loopMid_rsp x s h) (by taint_decide) fun x s h => final_ready x h)
  refine two_ite (fun P s t hs ht => hs.1.2.trans ht.1.2.symm) ?_ ?_
  · exact (two_piece (Ψ := fun P s => LoopMid n pLen qLen m (.inr (P.stop (BitVec.ofNat 64 2))) s) [.rsp]
      (pins_of (fun P => P.ctx.geo.F) fun _ _ h => loopBefore_rsp h.1.1.1.1) (by taint_decide)
      fun P s h => stopped_ready h.1.1.1 2 (Or.inr rfl)).mono (fun _ _ h => h) fun _ _ h => two_image _ h
  refine RelCT.seq (two_piece (Ψ := fun P s => Roomed n pLen qLen P s ∧ P.left = m) [.rsp]
    (pins_of (fun P => P.ctx.geo.F) fun _ _ h => loopBefore_rsp h.1.1.1.1) troom.choose_spec
    fun P s h => WP.mono (room_ready h.1.1 h.2) fun _ ht => ⟨ht, h.1.2⟩) ?_
  refine two_ite (fun P s t hs ht => hs.1.2.2.trans ht.1.2.2.symm) ?_ ?_
  · exact (two_piece (Ψ := fun P s => LoopMid n pLen qLen m (.inr (P.stop (BitVec.ofNat 64 0))) s) [.rsp]
      (pins_of (fun P => P.ctx.geo.F) fun _ _ h => loopBefore_rsp h.1.1.1.1) (by taint_decide)
      fun P s h => stopped_ready h.1.1.1 0 (Or.inl rfl)).mono (fun _ _ h => h) fun _ _ h => two_image _ h
  refine RelCT.seq (two_piece (Ψ := fun P s => Seeded n pLen qLen P s ∧ P.left = m) [.rsp]
    (pins_of (fun P => P.ctx.geo.F) fun _ _ h => loopBefore_rsp h.1.1.1.1) tseed.choose_spec
    fun P s h => WP.mono (seedStart_ready h.1.1 h.2) fun _ ht => ⟨ht, h.1.2⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun P s => Attempted n pLen qLen P s ∧ P.left = m)
    (hct.mono (fun s t h => by
      obtain ⟨P, ⟨⟨⟨r, a⟩, _⟩, _⟩, ⟨⟨⟨_, b⟩, _⟩, _⟩⟩ := h
      exact ⟨P.seedPub r, a, b⟩) fun _ _ h => h)
    fun P s h => WP.mono (hwp P s h.1) fun _ ht => ⟨ht, h.2⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun P s => Tested n pLen qLen P s ∧ P.left = m) [.rsp]
    (pins_of (fun P => P.ctx.geo.F) fun _ _ h => h.1.2.2.2.1.rsp) (by taint_decide)
    fun P s h => WP.mono (test_ready h.1) fun _ ht => ⟨ht, h.2⟩) ?_
  refine two_ite (fun P s t hs ht => hs.1.2.trans ht.1.2.symm) ?_ ?_
  · exact (two_piece (Ψ := fun P s => LoopMid n pLen qLen m (.inl P.next) s) [.rsp]
      (pins_of (fun P => P.ctx.geo.F) fun _ _ h => h.1.1.1.2.2.2.1.rsp) (by taint_decide)
      fun P s h => reject_ready h.1.1 h.2 h.1.2).mono (fun _ _ h => h) fun _ _ h => two_image _ h
  · exact (two_post (Ψ := fun P s => LoopMid n pLen qLen m (.inr P.done) s)
      (two_taint [] (by intro _ _ _ _ _ r hr; simp at hr) (by taint_decide))
      fun P s h => stop_ready h.1.1 h.2).mono (fun _ _ h => h) fun _ _ h => two_image _ h

theorem loop_ct_of {n pLen qLen : Nat} {attempt : Prog isa}
    (hstep : ∀ m, RelCT isa (Two fun P s => LoopBefore n pLen qLen P s ∧ P.left = m)
      (Impl.Dsa.X86_64.Generation.Refill.iteration attempt qLen) (Two (LoopPost n pLen qLen m))) :
    RelCT isa (Two (LoopBefore n pLen qLen))
      (.loop (Impl.Dsa.X86_64.Generation.Refill.iteration attempt qLen) .e) (Two (DoneAt n pLen qLen)) := by
  have step : ∀ m, RelCT isa (Two fun P s => LoopBefore n pLen qLen P s ∧ P.left = m)
      (Impl.Dsa.X86_64.Generation.Refill.iteration attempt qLen) fun s t =>
        isa.eval .e s = isa.eval .e t ∧ (isa.eval .e s = some false → Two (DoneAt n pLen qLen) s t) ∧
        (isa.eval .e s = some true → ∃ k < m, Two (fun P s => LoopBefore n pLen qLen P s ∧ P.left = k) s t) := by
    intro m
    refine (hstep m).mono (fun _ _ h => h) ?_
    rintro s t ⟨x, hs, ht⟩
    cases x with
    | inl P =>
      refine ⟨hs.1.trans ht.1.symm, fun hf => absurd (hs.1.symm.trans hf) (by simp), fun _ => ?_⟩
      exact ⟨P.left, hs.2.2, P, ⟨hs.2.1, rfl⟩, ⟨ht.2.1, rfl⟩⟩
    | inr D =>
      exact ⟨hs.1.trans ht.1.symm, fun _ => ⟨D, hs.2, ht.2⟩, fun hf => absurd (hs.1.symm.trans hf) (by simp)⟩
  rintro s t a b s' t' ⟨P, hs, ht⟩ es et
  exact RelCT.loop (fun m => Two fun P s => LoopBefore n pLen qLen P s ∧ P.left = m) step P.left
    s t a b s' t' ⟨P, ⟨hs, rfl⟩, ⟨ht, rfl⟩⟩ es et

theorem controller_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (LoopBefore 6 pLen qLen))
      (Impl.Dsa.X86_64.Generation.Refill.controller (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pLen qLen)
      (Two (DoneAt 6 pLen qLen)) := by
  have width : qLen = 20 ∨ qLen = 32 := by
    rcases sizes with h | h | h <;> simp [h.2]
  have troom : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rcx (.mem (sp 120)),
      .alu .sub .rcx (.reg .rax), .alu .cmp .rcx (.imm (BitVec.ofNat 32 qLen))]) hc).isSome = true := by
    rcases width with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have tseed : ∃ hc, (taint.check (Taint.ofRegs [.rsp])
      (.block (Impl.Dsa.X86_64.Generation.Refill.seedStart qLen)) hc).isSome = true := by
    rcases width with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  unfold Impl.Dsa.X86_64.Generation.Refill.controller
  exact loop_ct_of fun m => iteration_ct_of m
    (refillAttempt_ct (checkName := checkName) H M Sq T 6 (Or.inr (Or.inr rfl)) pLen qLen sizes)
    (fun P t h => attempt_ready (checkName := checkName) H M Sq T h) troom tseed

end VG.Proof.Dsa.X86_64.Generation
