module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillLoop
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillCTAttempt
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillAttempt
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSlice
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillLoop
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillCTAttempt
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Timing of the refillable-tape search's controller on AArch64

The controller's public state between seeds (`LoopPub`): the search's
context, the seeds it may still reject and the seed's start. Whether an
iteration stops, and where the next seed starts, are functions of it
(`ctxContinues`, `ctxNext`), so two runs from the same public state take
the same branches and reach the same public state (`controller_ct`). -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation.Refill
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 (upd)
open VG.Proof.Dsa.AArch64.Generation

/-! ## The public state -/

structure LoopPub where
  ctx : GenerationContext
  n : Nat
  c : Nat

/-- Fewer octets than a seed's are left from `c`. -/
def ctxShort (p : GenerationContext) (c : Nat) : Prop := p.rand.bytes.length - c < p.geo.qLen

instance (p : GenerationContext) (c : Nat) : Decidable (ctxShort p c) := by unfold ctxShort; infer_instance

/-- The seed at `c`'s result. -/
def ctxResult (p : GenerationContext) (c : Nat) : Option (Option Spec.Dsa.Params × List Byte) :=
  VG.Proof.Dsa.Generation.refillAttempt p.geo.pLen p.geo.qLen ((p.rand.bytes.drop c).take p.geo.qLen)
    (p.rand.bytes.drop (c + p.geo.qLen))

def ctxContinues (p : GenerationContext) (n c : Nat) : Bool :=
  n != 0 && !decide (ctxShort p c) &&
    match ctxResult p c with
    | some (none, _) => true
    | _ => false

def ctxNext (p : GenerationContext) (c : Nat) : Nat :=
  match ctxResult p c with
  | some (_, rest) => p.rand.bytes.length - rest.length
  | none => c

/-- The status a seed's attempt with result `res` leaves. -/
def resStatus (res : Option (Option Spec.Dsa.Params × List Byte)) : BitVec 64 :=
  match res with
  | none => 0
  | some (none, _) => 3
  | some (some _, _) => 1

def ctxStatus (p : GenerationContext) (c : Nat) : BitVec 64 := resStatus (ctxResult p c)

section
variable {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀)

theorem continues_eq (n c : Nat) : continues h n c = ctxContinues (refillContext h) n c := rfl

theorem nextUsed_eq (c : Nat) : nextUsed h c = ctxNext (refillContext h) c := rfl

end

/-- The controller's state, for some entry of the search. -/
def LoopAt (pBytes : Nat) (P : LoopPub) (t : State) : Prop :=
  ∃ (s₀ : State) (h : RefillABI pBytes s₀) (v : State), refillContext h = P.ctx ∧
    v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr ∧ LoopState h v P.n P.c t

/-- How the controller ended. -/
def DoneAt (pBytes : Nat) (P : LoopPub) (t : State) : Prop :=
  ∃ (s₀ : State) (h : RefillABI pBytes s₀) (v : State), refillContext h = P.ctx ∧
    v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr ∧ LoopDone h v P.n P.c t

/-! ## One iteration -/

theorem two_sp {α : Type} {Φ : α → State → Prop} {c : Prog isa} (hct : RelCT isa (Two Φ) c fun _ _ => True) :
    RelCT isa (Two Φ) c (Two fun (_ : Unit) (_ : State) => True) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨_, -, -, hsp⟩ := hp
  exact ⟨ht, (), True.intro, True.intro, by rw [(Exec.rdwr e₁).2.2, (Exec.rdwr e₂).2.2, hsp]⟩

def Started (pBytes : Nat) (P : LoopPub) (t : State) : Prop :=
  ∃ (s₀ : State) (h : RefillABI pBytes s₀) (v : State), refillContext h = P.ctx ∧
    v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr ∧ LoopState h v P.n P.c t ∧
    ctlWord t.mem (refillBase s₀) 3 = BitVec.ofNat 64 P.c ∧ t.gpr .x0 = BitVec.ofNat 64 P.c ∧
    t.gpr .x3 = BitVec.ofNat 64 P.n

theorem started_wp {pBytes : Nat} {P : LoopPub} {t : State} (hl : LoopAt pBytes P t) :
    WP isa (.block Impl.Dsa.AArch64.Generation.Refill.iterStart) t (Started pBytes P) := by
  obtain ⟨s₀, h, v, hc, hv, hi⟩ := hl
  exact WP.mono (iterStart_ok h (by rw [hv]; exact List.mem_cons_self ..) hi) fun t₁ ⟨a, b, c, d⟩ =>
    ⟨s₀, h, v, hc, hv, a, b, c, d⟩

def Roomed (pBytes : Nat) (P : LoopPub) (t : State) : Prop :=
  ∃ (s₀ : State) (h : RefillABI pBytes s₀) (v : State), refillContext h = P.ctx ∧
    v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr ∧ LoopState h v P.n P.c t ∧
    ctlWord t.mem (refillBase s₀) 3 = BitVec.ofNat 64 P.c ∧ t.gpr .x0 = BitVec.ofNat 64 P.c ∧
    t.gpr .x3 = BitVec.ofNat 64 (if ctxShort P.ctx P.c then 1 else 0)

theorem roomed_wp {pBytes : Nat} {P : LoopPub} {t : State} (hl : Started pBytes P t) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.roomCheck (Spec.Dsa.generationQLen pBytes))) t
      (Roomed pBytes P) := by
  obtain ⟨ctx, n, c⟩ := P
  obtain ⟨s₀, h, v, hc, hv, hi, c3, x0, -⟩ := hl
  subst hc
  exact WP.mono (roomCheck_ok h hi x0) fun t₂ ⟨hi₂, mem₂, x0₂, x3₂⟩ =>
    ⟨s₀, h, v, rfl, hv, hi₂, by rw [ctlWord_eq_of_mem mem₂]; exact c3, x0₂, x3₂⟩

def LoopPub.seedPub (P : LoopPub) (room : P.c + P.ctx.geo.qLen ≤ P.ctx.rand.bytes.length) : SeedPublic where
  context := P.ctx
  seed := P.ctx.rand.slice P.c P.ctx.geo.qLen room
  length := slice_length _ room
  used := P.c + P.ctx.geo.qLen
  seedCursor := 0
  bound := room

/-- Before the seed's attempt. -/
def SeededPub (pBytes : Nat) (P : LoopPub) (t : State) : Prop :=
  (∃ room, RefillAttemptBefore pBytes (Spec.Dsa.generationQLen pBytes) (P.seedPub room) t) ∧
    Region.Sub ⟨P.ctx.hs.ptr, P.ctx.hs.bytes.length⟩ ⟨P.ctx.rand.ptr, P.ctx.rand.bytes.length⟩

theorem seeded_wp {pBytes : Nat} {P : LoopPub} {t : State}
    (hl : Roomed pBytes P t ∧ isa.eval (.nonzero .x .x3) t = some false) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.seedStart (Spec.Dsa.generationQLen pBytes))) t
      (SeededPub pBytes P) := by
  obtain ⟨ctx, n, c⟩ := P
  obtain ⟨⟨s₀, h, v, hc, hv, hi, c3, x0, x3⟩, ev⟩ := hl
  subst hc
  have hq2 : Spec.Dsa.generationQLen pBytes = 20 ∨ Spec.Dsa.generationQLen pBytes = 32 := by
    unfold Spec.Dsa.generationQLen; split <;> simp
  have hs : ¬ ctxShort (refillContext h) c := by
    intro hs
    simp only [eval, State.read, x3, BitVec.setWidth_eq, hs, ite_true] at ev
    cases ev
  have room : c + Spec.Dsa.generationQLen pBytes ≤ (randTape h).bytes.length := by
    unfold ctxShort at hs
    change ¬ (randTape h).bytes.length - c < Spec.Dsa.generationQLen pBytes at hs
    omega
  refine WP.mono (seedStart_ok h hi c3 x0 room) fun t₃ ⟨room', W, hm, w1, w16, w10, seed, _⟩ => ?_
  refine ⟨⟨room', ⟨⟨W, hm, w1, w16, w10⟩, seed, rfl⟩, rfl⟩, ?_⟩
  intro a ha
  simp [Region.Contains, refillContext, GenerationTape.slice] at ha

/-- The status the seed's attempt leaves. -/
theorem outcome_status {p : GenerationContext} {res : Option (Option Spec.Dsa.Params × List Byte)}
    {W : Nat → BitVec 64} {used : Nat} {t : State} (h : SeedOutcome p res W used t) : W 19 = resStatus res := by
  rcases h with ⟨h19, hr⟩ | ⟨h19, hr⟩ | ⟨h19, a, hr, _⟩ <;> subst hr <;> exact h19

def AfterAttempt (P : LoopPub) (t : State) : Prop :=
  ∃ (p : GenerationContext) (W : Nat → BitVec 64), GenerationMemory p W t ∧ W 19 = ctxStatus P.ctx P.c

theorem attempt_wp (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) {pBytes : Nat} {P : LoopPub}
    {t : State} (hl : SeededPub pBytes P t) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run pBytes
      (Spec.Dsa.generationQLen pBytes)) t (AfterAttempt P) := by
  obtain ⟨ctx, n, c⟩ := P
  obtain ⟨⟨room, ⟨⟨W, hm, h1, h16, _⟩, seed, hq⟩, hp⟩, hsub⟩ := hl
  change ctx.geo.pLen = pBytes at hp
  change ctx.geo.qLen = Spec.Dsa.generationQLen pBytes at hq
  subst hp
  rw [← hq]
  refine WP.mono (refillAttempt_ok H G T hm hsub _ (slice_length _ room) seed h1 h16 room) fun t' hf => ?_
  obtain ⟨hs, W', used, -, hm', -, -, -, outcome, -⟩ := hf
  change SeedOutcome _ (ctxResult ctx c) W' used t' at outcome
  exact ⟨_, W', hm', outcome_status outcome⟩

def StatusTested (P : LoopPub) (t : State) : Prop :=
  isa.eval (.zero .x .x0) t = some (ctxStatus P.ctx P.c == 3)

theorem tested_wp {P : LoopPub} {t : State} (hl : AfterAttempt P t) :
    WP isa (.block Impl.Dsa.AArch64.Generation.tapeStatus) t (StatusTested P) := by
  obtain ⟨p, W, hm, h19⟩ := hl
  exact WP.mono (statusTest_ok hm) fun t' ⟨z, _⟩ => by
    show isa.eval _ t' = some (ctxStatus P.ctx P.c == 3)
    rw [← h19]; exact z

theorem nopin {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ hr => nomatch hr

theorem iteration_ct_of (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) (pBytes : Nat)
    (sizes : GenerationSizes pBytes (Spec.Dsa.generationQLen pBytes))
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [])
      (.block (Impl.Dsa.AArch64.Generation.Refill.roomCheck (Spec.Dsa.generationQLen pBytes))) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [])
      (.block (Impl.Dsa.AArch64.Generation.Refill.seedStart (Spec.Dsa.generationQLen pBytes))) hc₂).isSome = true) :
    RelCT isa (Two (LoopAt pBytes))
      (Impl.Dsa.AArch64.Generation.Refill.iteration
        (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run pBytes
          (Spec.Dsa.generationQLen pBytes)) (Spec.Dsa.generationQLen pBytes)) (fun _ _ => True) := by
  simp only [Impl.Dsa.AArch64.Generation.Refill.iteration, VG.Impl.Bignum.AArch64.seqs]
  refine RelCT.seq (two_piece [] (nopin _) (by taint_decide) fun _ _ h => started_wp h) ?_
  refine RelCT.seq (R := Two fun (_ : Unit) (_ : State) => True) ?_ (two_taint [] (nopin _) (by taint_decide))
  refine two_ite (fun P s t ⟨_, _, _, _, _, _, _, _, hs⟩ ⟨_, _, _, _, _, _, _, _, ht⟩ => by
    simp only [eval, State.read, hs, ht]) (two_sp (two_taint [] (nopin _) (by taint_decide))) ?_
  refine RelCT.seq (two_piece [] (nopin _) ht₁ fun _ _ h => roomed_wp h.1) ?_
  refine two_ite (fun P s t ⟨_, _, _, _, _, _, _, _, hs⟩ ⟨_, _, _, _, _, _, _, _, ht⟩ => by
    simp only [eval, State.read, hs, ht]) (two_sp (two_taint [] (nopin _) (by taint_decide))) ?_
  refine RelCT.seq (two_piece [] (nopin _) ht₂ fun _ _ h => seeded_wp h) ?_
  refine RelCT.seq (two_post ?_ fun _ _ h => attempt_wp H G T h) ?_
  · refine (refillAttempt_ct H G T pBytes _ sizes).mono ?_ fun _ _ h => h
    rintro s t ⟨P, ⟨⟨room, hs⟩, _⟩, ⟨⟨room', ht⟩, _⟩, hsp⟩
    exact ⟨P.seedPub room, hs, ht, hsp⟩
  refine RelCT.seq (two_piece [] (nopin _) (by taint_decide) fun _ _ h => tested_wp h) ?_
  exact two_ite (fun P s t hs ht => hs.trans ht.symm) (two_sp (two_taint [] (nopin _) (by taint_decide)))
    (two_sp (two_taint [] (nopin _) (by taint_decide)))

theorem iteration_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) (pBytes : Nat)
    (sizes : GenerationSizes pBytes (Spec.Dsa.generationQLen pBytes)) :
    RelCT isa (Two (LoopAt pBytes))
      (Impl.Dsa.AArch64.Generation.Refill.iteration
        (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run pBytes
          (Spec.Dsa.generationQLen pBytes)) (Spec.Dsa.generationQLen pBytes)) (fun _ _ => True) := by
  have hq : Spec.Dsa.generationQLen pBytes = 20 ∨ Spec.Dsa.generationQLen pBytes = 32 := by
    unfold Spec.Dsa.generationQLen; split <;> simp
  rcases hq with hq | hq <;>
    exact iteration_ct_of H G T pBytes sizes (by rw [hq]; taint_decide) (by rw [hq]; taint_decide)

/-! ## The loop -/

/-- After an iteration from `k` seeds left. -/
def StepAt (pBytes k : Nat) (P : LoopPub) (t : State) : Prop :=
  ∃ (s₀ : State) (h : RefillABI pBytes s₀) (v : State),
    refillContext h = P.ctx ∧ v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr ∧ P.n = k ∧ StepPost h v P.n P.c t

/-- The loop's invariant with `k` seeds left. -/
def LoopInv (pBytes k : Nat) : State → State → Prop := Two fun P t => P.n = k ∧ LoopAt pBytes P t

theorem controller_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) (pBytes : Nat)
    (sizes : GenerationSizes pBytes (Spec.Dsa.generationQLen pBytes)) :
    RelCT isa (Two (LoopAt pBytes))
      (Impl.Dsa.AArch64.Generation.Refill.controller H.sha1 H.sha256 G.run T.run pBytes
        (Spec.Dsa.generationQLen pBytes)) (Two (DoneAt pBytes)) := by
  have step : ∀ k, RelCT isa (LoopInv pBytes k)
      (Impl.Dsa.AArch64.Generation.Refill.iteration
        (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run pBytes
          (Spec.Dsa.generationQLen pBytes)) (Spec.Dsa.generationQLen pBytes))
      (fun s t => isa.eval (.zero .x .x0) s = isa.eval (.zero .x .x0) t ∧
        (isa.eval (.zero .x .x0) s = some false → Two (DoneAt pBytes) s t) ∧
        (isa.eval (.zero .x .x0) s = some true → ∃ m < k, LoopInv pBytes m s t)) := by
    intro k
    have hA : ∀ {s₀ : State} (h : RefillABI pBytes s₀), AttemptOk h
        (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run pBytes
          (Spec.Dsa.generationQLen pBytes)) :=
      fun _ hs W t seed hin hm hlen hseed h1 used h16 hu => refillAttempt_ok H G T hm hin seed hlen hseed h1 h16 hu
    have hw : ∀ (P : LoopPub) (t : State), P.n = k ∧ LoopAt pBytes P t →
        WP isa (Impl.Dsa.AArch64.Generation.Refill.iteration
          (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run pBytes
            (Spec.Dsa.generationQLen pBytes)) (Spec.Dsa.generationQLen pBytes)) t
          (StepAt pBytes k P) := by
      intro P t ⟨hk, s₀, h, v, hc, hv, hi⟩
      refine WP.mono (step_ok h (hA h) ?_ P.n P.c t hi) fun t' hp => ⟨s₀, h, v, hc, hv, hk, hp⟩
      rw [hv]; exact List.mem_cons_self ..
    have post := two_post (two_map (Φ := fun P t => P.n = k ∧ LoopAt pBytes P t) id (fun _ _ h => h.2)
      (iteration_ct H G T pBytes sizes)) hw
    refine RelCT.mono (P' := LoopInv pBytes k) post (fun _ _ h => h) ?_
    rintro s t ⟨⟨ctx, n, c⟩, ⟨s₀, h, v, hc, hv, hk, e, d, k'⟩, ⟨s₀', h', v', hc', hv', -, e', d', k''⟩, hsp⟩
    change refillContext h = ctx at hc
    change refillContext h' = ctx at hc'
    have es : isa.eval (.zero .x .x0) s = some (ctxContinues ctx n c) := by
      rw [← hc]; exact e
    have et : isa.eval (.zero .x .x0) t = some (ctxContinues ctx n c) := by
      rw [← hc']; exact e'
    refine ⟨es.trans et.symm, fun ef => ?_, fun et' => ?_⟩
    · have hf : ctxContinues ctx n c = false := Option.some.inj (es.symm.trans ef)
      exact ⟨⟨ctx, n, c⟩, ⟨s₀, h, v, hc, hv, d (by rw [continues_eq, hc]; exact hf)⟩,
        ⟨s₀', h', v', hc', hv', d' (by rw [continues_eq, hc']; exact hf)⟩, hsp⟩
    · have ht : ctxContinues ctx n c = true := Option.some.inj (es.symm.trans et')
      obtain ⟨m, hm, st⟩ := k' (by rw [continues_eq, hc]; exact ht)
      obtain ⟨m', hm', st'⟩ := k'' (by rw [continues_eq, hc']; exact ht)
      have e₁ : m' = m := by simp only at hm hm'; omega
      rw [e₁] at st'
      refine ⟨m, by simp only at hk hm; omega, ⟨ctx, m, ctxNext ctx c⟩, ⟨rfl, s₀, h, v, hc, hv, ?_⟩,
        ⟨rfl, s₀', h', v', hc', hv', ?_⟩, hsp⟩
      · rw [nextUsed_eq, hc] at st; exact st
      · rw [nextUsed_eq, hc'] at st'; exact st'
  rintro s t a b s' t' ⟨P, hs, ht, hsp⟩ es et
  exact RelCT.loop (LoopInv pBytes) step P.n s t a b s' t' ⟨P, ⟨rfl, hs⟩, ⟨rfl, ht⟩, hsp⟩ es et

end VG.Proof.Dsa.AArch64.Generation.Refill
