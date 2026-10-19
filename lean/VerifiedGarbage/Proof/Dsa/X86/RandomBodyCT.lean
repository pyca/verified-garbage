module

public import VerifiedGarbage.Proof.Dsa.X86.RandomAttemptCT
public import VerifiedGarbage.Proof.Dsa.X86.RandomAttempt
public import VerifiedGarbage.Proof.Dsa.X86.RandomFinish
public import VerifiedGarbage.Proof.Dsa.X86.RandomPrepare
public import VerifiedGarbage.Proof.Dsa.X86.RandomSampleCT
import VerifiedGarbage.Proof.Dsa.X86.RandomPrepareCT
import VerifiedGarbage.Proof.Dsa.X86.RandomBody
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Spec.Weierstrass
meta import VerifiedGarbage.Proof.Dsa.X86.RandomAttemptCT
meta import VerifiedGarbage.Proof.Dsa.X86.RandomAttempt
meta import VerifiedGarbage.Proof.Dsa.X86.RandomFinish
meta import VerifiedGarbage.Proof.Dsa.X86.RandomPrepare
meta import VerifiedGarbage.Proof.Dsa.X86.RandomSampleCT
meta import VerifiedGarbage.Proof.Dsa.X86.RandomPrepareCT
meta import VerifiedGarbage.Proof.Dsa.X86.RandomBody
meta import VerifiedGarbage.Proof.Dsa.RandomTraceResult
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Spec.Weierstrass

/-!
# The randomized signer's body leaks only its public data (x86)

The attempts continue after a retry with attempts left, which the signing
trace records (`AttPub.cont`); the next attempt's trace is the rest of it.
`finish` branches on the overall status, and writes through the public
`out` and `used` pointers.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random VG.Impl.Dsa.X86.RandomSign
open VG.Proof.Dsa (randomSignRemaining randomSamplingTrace randomSigningTrace)

/-! ## The attempts -/

/-- Whether another attempt follows: a retry, with attempts left. -/
def AttPub.cont (a : AttPub) : Bool := ((randomSigningTrace a.tr).head? == some 6) && decide (2 ≤ a.fuel)

def AttPub.next (a : AttPub) : AttPub :=
  ⟨a.pub, a.leak, a.used + a.pub.width * (randomSamplingTrace a.tr).countP (· ≤ 1), a.fuel - 1,
    (randomSigningTrace a.tr).tail, a.status⟩

/-- The test of the attempt's status. -/
abbrev attTest : Prog isa := .block [.mov .eax (.mem (sp oStatus)), .alu .cmp .eax (.imm 4)]

theorem AttemptOut.ready {s₀ u : State} {used f : Nat} (h : AttemptOut s₀ used f u) : Ready s₀ u := by
  rcases h with ⟨_, _, T, _⟩ | ⟨_, D, _⟩
  · obtain ⟨_, S⟩ := T.smp; exact S.ready
  · obtain ⟨_, S⟩ := D.smp; exact S.ready

/-- After an attempt and its test. -/
def AStep (a : AttPub) (s₀ t : State) : Prop :=
  Ready s₀ t ∧ t.zf = some a.cont ∧ (a.cont = true → AttAt a.next s₀ t) ∧ (a.cont = false → Fin s₀ t)

theorem astep_ok (F : SignFn) {a : AttPub} {s₀ t : State} (A : RandomSignABI s₀) (e : pubOf s₀ = a.pub)
    (L : AttAt a s₀ t) : WP isa (.seq (attempt F.name F.code) attTest) t (AStep a s₀) := by
  obtain ⟨Fa, T⟩ := L
  obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by have := Fa.pos; omega⟩
  have hf8 : f + 1 ≤ 8 := hf ▸ Fa.le
  rw [hf] at T
  refine WP.seq (WP.mono (attempt_ok F A T hf8 Fa.q) fun v hv => ?_)
  have hrv := hv.ready
  refine wp_movS (hrv.rf.readSlot (by decide)) fun v₁ uv₁ _ => wp_cmpi fun v₂ fv₂ _ zv₂ => WP.block_nil ?_
  have hv₂ := (hrv.upd uv₁ (by decide)).fupd fv₂
  have mv₂ : v₂.mem = v.mem := by rw [fv₂.mem, uv₁.mem]
  rw [uv₁.gpr] at zv₂
  have htr := Fa.tr
  rw [hf] at htr
  rcases hv with ⟨st, h1f, T', hs⟩ | ⟨st, D, hh⟩
  · have hc : a.cont = true := by
      simp only [AttPub.cont, ← htr, hs, List.head?_cons, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
      omega
    have st' : v.mem.readW (off (rBase s₀) oStatus) 32 = 4 := st
    refine ⟨hv₂, by rw [zv₂, st', hc]; rfl, fun _ => ?_, fun h => Bool.noConfusion (hc.symm.trans h)⟩
    have hu : a.pub.width * (randomSamplingTrace a.tr).countP (· ≤ 1) = (spl s₀ 128 a.used).used := by
      rw [(VG.Proof.Dsa.Random.sample_trace_result _ _ _).1, Fa.spl_trace, pub_width e, rWidth_eq]
    refine ⟨⟨Fa.q, by show 1 ≤ a.fuel - 1; omega, by show a.fuel - 1 ≤ 8; omega, Fa.leak, ?_⟩, ?_⟩
    · show (randomSignRemaining (rInput s₀) (a.used + a.pub.width * _) (a.fuel - 1)).trace =
        (randomSigningTrace a.tr).tail
      rw [hu, hf, Nat.add_sub_cancel, ← htr, hs]; rfl
    · show Att s₀ (a.used + a.pub.width * _) (a.fuel - 1) v₂
      rw [hu, hf, Nat.add_sub_cancel]; exact T'.mem A hv₂ mv₂
  · have hc : a.cont = false := by
      simp only [AttPub.cont, ← htr, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
        decide_eq_false_iff_not]
      by_cases h6 : (randomSigningTrace (randomSignRemaining (rInput s₀) a.used (f + 1)).trace).head? = some 6
      · exact .inr fun h2 => hh ⟨h6, by omega⟩
      · exact .inl h6
    exact ⟨hv₂, by rw [zv₂, sub_four_ne st, hc], fun h => Bool.noConfusion (hc.symm.trans h),
      fun _ => (D.mem A hv₂ mv₂).fin⟩

/-- At the end: the frame's slots, and the overall status `p.2`. -/
def FinAt (p : Pub × Nat) : State → Prop := At (fun s₀ t => Fin s₀ t ∧ (rResult s₀).status = p.2) p.1

/-- Before an attempt, with the overall status. -/
def LoopAt' (a : AttPub) : State → Prop := At (fun s₀ t => AttAt a s₀ t ∧ (rResult s₀).status = a.status) a.pub

theorem attemptLoop_ct (F : SignFn) (n : Nat) :
    RelCT isa (Two fun a t => a.fuel = n ∧ LoopAt' a t) (.loop (.seq (attempt F.name F.code) attTest) .e)
      (Two FinAt) := by
  refine RelCT.loop (M := isa) (fun n => Two fun a t => a.fuel = n ∧ LoopAt' a t) (fun n => ?_) n
  have hct : RelCT isa (Two fun a t => a.fuel = n ∧ LoopAt' a t) (.seq (attempt F.name F.code) attTest)
      fun _ _ => True := by
    refine RelCT.seq (two_post (Ψ := fun a => At (fun s₀ t => Ready s₀ t) a.pub)
      (two_map id (fun a t ⟨_, s₀, A, e, L, _⟩ => ⟨s₀, A, e, L⟩) (attempt_ct F))
      (fun a t ⟨_, s₀, A, e, ⟨Fa, T⟩, _⟩ => ?_)) ?_
    · obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by have := Fa.pos; omega⟩
      have hf8 : f + 1 ≤ 8 := hf ▸ Fa.le
      rw [hf] at T
      exact WP.mono (attempt_ok F A T hf8 Fa.q) fun u h => ⟨s₀, A, e, h.ready⟩
    · exact two_taint [.esp] (pins_at (P := fun _ s₀ t => Ready s₀ t) AttPub.pub fun _ _ _ h => h)
        (by taint_decide)
  have hp := two_post (Ψ := fun a t => a.fuel = n ∧ At (fun s₀ t => AStep a s₀ t ∧
      (rResult s₀).status = a.status) a.pub t) hct
    fun a t ⟨hn, s₀, A, e, L, st⟩ => WP.mono (astep_ok F A e L) fun u h => ⟨hn, s₀, A, e, h, st⟩
  refine hp.mono (fun _ _ h => h) ?_
  rintro t₁ t₂ ⟨a, ⟨hn, s₁, A₁, e₁, ⟨r₁, z₁, c₁, d₁⟩, st₁⟩, ⟨_, s₂, A₂, e₂, ⟨r₂, z₂, c₂, d₂⟩, st₂⟩⟩
  refine ⟨by simp only [eval, z₁, z₂], fun hc => ?_, fun hc => ?_⟩
  · have hc' : a.cont = false := by simpa only [eval, z₁, Option.some.injEq] using hc
    exact ⟨(a.pub, a.status), ⟨s₁, A₁, e₁, d₁ hc', st₁⟩, ⟨s₂, A₂, e₂, d₂ hc', st₂⟩⟩
  · have hc' : a.cont = true := by simpa only [eval, z₁, Option.some.injEq] using hc
    have h2 : 2 ≤ a.fuel := by
      simp only [AttPub.cont, Bool.and_eq_true, decide_eq_true_eq] at hc'; exact hc'.2
    exact ⟨n - 1, by omega, a.next, ⟨by show a.fuel - 1 = n - 1; omega, s₁, A₁, e₁, c₁ hc', st₁⟩,
      ⟨by show a.fuel - 1 = n - 1; omega, s₂, A₂, e₂, c₂ hc', st₂⟩⟩

/-! ## The end -/

/-- Test the overall status. -/
theorem finTest_ok {s₀ t : State} (A : RandomSignABI s₀) (Fi : Fin s₀ t) :
    WP isa (.block [.mov .eax (.mem (sp oStatus)), .alu .cmp .eax (.imm 1)]) t fun u =>
      Ready s₀ u ∧ u.zf = some (decide ((rResult s₀).status = 1)) := by
  have hR := rResult_status_le A
  refine wp_movS (v := BitVec.ofNat 32 (rResult s₀).status)
    (by rw [Fi.ready.rf.readSlot (by decide)]; exact congrArg some Fi.status)
    fun t₁ u₁ _ => wp_cmpi fun t₂ f₂ _ z₂ => WP.block_nil ⟨(Fi.ready.upd u₁ (by decide)).fupd f₂, ?_⟩
  rw [z₂, u₁.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega) (by decide)]

/-- The output's address and length. -/
theorem zeroHead_ok {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) :
    WP isa (.block [.mov .esi (.mem (Random.arg aOut)), .mov .ecx (.mem (Random.arg aOutLen)), .mov .eax (.imm 0)])
      t fun u => Ready s₀ u ∧ u.gpr .esi = X86.arg s₀ 0 ∧ u.gpr .ecx = X86.arg s₀ 1 := by
  refine wp_movS (h.argSrc A (j := 0) (by decide)) fun t₁ u₁ _ => ?_
  have h₁ := h.upd u₁ (by decide)
  refine wp_movS (h₁.argSrc A (j := 1) (by decide)) fun t₂ u₂ _ => wp_movS rfl fun t₃ u₃ _ => WP.block_nil ?_
  exact ⟨(h₁.upd u₂ (by decide)).upd u₃ (by decide), by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
    by rw [u₃.other _ (by decide), u₂.gpr]⟩

/-- The nonce cleared, and the address of `used`. -/
theorem finPrefix_ok {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) :
    WP isa (.block (clearNonce ++ ([.mov .edx (.mem (Random.arg aUsed))] : List Instr))) t fun u =>
      Ready s₀ u ∧ u.gpr .edx = X86.arg s₀ 2 := by
  refine clearNonce_ok h.rf fun t₁ _ m₁ k₁ _ => ?_
  have h₁ : Ready s₀ t₁ := h.congr k₁ (by rw [m₁]; exact clearMem_frame s₀ _ 8 (by decide))
  exact wp_movS (h₁.argSrc A (j := 2) (by decide)) fun t₂ u₂ _ => WP.block_nil ⟨h₁.upd u₂ (by decide), u₂.gpr⟩

/-- Ready, with public data `p.1`. -/
def ReadyAt (p : Pub × Nat) : State → Prop := At (fun s₀ t => Ready s₀ t) p.1

theorem zeroOut_ct : RelCT isa (Two fun p s => ReadyAt p s ∧ isa.eval .ne s = some true) zeroOut
    fun _ _ => True := by
  unfold zeroOut
  refine RelCT.seq (two_piece (Ψ := fun p => At (fun s₀ t => Ready s₀ t ∧ t.gpr .esi = X86.arg s₀ 0 ∧
      t.gpr .ecx = X86.arg s₀ 1) p.1) [.esp] (pins_at' (P := fun _ s₀ t => Ready s₀ t) Prod.fst
      fun _ _ _ h => h) (by taint_decide)
    fun p t ⟨⟨s₀, A, e, h⟩, _⟩ => WP.mono (zeroHead_ok A h) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine two_taint [.esi, .ecx] (fun p t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, _, x₁, c₁⟩ := h₁
  obtain ⟨s₂, _, e₂, _, x₂, c₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [x₁, x₂, pub_arg e 0 (by decide)]
  · rw [c₁, c₂, pub_arg e 1 (by decide)]

theorem finalBlock_ct : RelCT isa (Two ReadyAt)
    (.block (clearNonce ++ ([.mov .edx (.mem (Random.arg aUsed)), .mov .eax (.mem (sp oUsed)),
      .store (at_ .edx 0) .eax, .mov .eax (.imm 0), .store (at_ .edx 4) .eax,
      .mov .ebx (.mem (sp oSaveEbx)), .mov .esi (.mem (sp oSaveEsi)),
      .mov .edi (.mem (sp oSaveEdi)), .mov .ebp (.mem (sp oSaveEbp)),
      .mov .eax (.mem (sp oStatus))] : List Instr))) fun _ _ => True := by
  show RelCT isa _ (.block ((clearNonce ++ [.mov .edx (.mem (Random.arg aUsed))]) ++
    [.mov .eax (.mem (sp oUsed)), .store (at_ .edx 0) .eax, .mov .eax (.imm 0), .store (at_ .edx 4) .eax,
      .mov .ebx (.mem (sp oSaveEbx)), .mov .esi (.mem (sp oSaveEsi)),
      .mov .edi (.mem (sp oSaveEdi)), .mov .ebp (.mem (sp oSaveEbp)),
      .mov .eax (.mem (sp oStatus))])) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun p => At (fun s₀ t => Ready s₀ t ∧ t.gpr .edx = X86.arg s₀ 2) p.1)
    [.esp] (pins_at (P := fun _ s₀ t => Ready s₀ t) Prod.fst fun _ _ _ h => h) (by taint_decide)
    fun p t ⟨s₀, A, e, h⟩ => WP.mono (finPrefix_ok A h) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine two_taint [.esp, .edx] (fun p t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, r₁, d₁⟩ := h₁
  obtain ⟨s₂, _, e₂, r₂, d₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact esp_of_rf r₁.rf (pub_rBase e ▸ r₂.rf)
  · rw [d₁, d₂, pub_arg e 2 (by decide)]

theorem finish_ct : RelCT isa (Two FinAt) finish fun _ _ => True := by
  unfold finish
  refine RelCT.seq (two_piece (Ψ := fun (p : Pub × Nat) => At (fun s₀ t => Ready s₀ t ∧
      t.zf = some (decide (p.2 = 1))) p.1) [.esp]
    (pins_at (P := fun p s₀ t => Fin s₀ t ∧ (rResult s₀).status = p.2) Prod.fst fun _ _ _ h => h.1.ready)
    (by taint_decide) fun p t ⟨s₀, A, e, Fi, st⟩ => WP.mono (finTest_ok A Fi)
      fun u ⟨h, z⟩ => ⟨s₀, A, e, h, by rw [z, st]⟩) ?_
  refine RelCT.seq (R := Two ReadyAt) (two_ite (fun p t₁ t₂ ⟨_, _, _, _, z₁⟩ ⟨_, _, _, _, z₂⟩ => by
    simp only [eval, z₁, z₂]) ?_ ?_) finalBlock_ct
  · exact two_post (Ψ := ReadyAt) (two_map id (fun p t ⟨⟨s₀, A, e, h, _⟩, hb⟩ => ⟨⟨s₀, A, e, h⟩, hb⟩) zeroOut_ct)
      fun p t ⟨⟨s₀, A, e, h, _⟩, _⟩ => WP.mono (zeroOut_ok A h) fun u hu => ⟨s₀, A, e, hu.1⟩
  · exact two_post (Ψ := ReadyAt) (two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide))
      fun p t ⟨⟨s₀, A, e, h, _⟩, _⟩ => WP.block_nil ⟨s₀, A, e, h⟩

/-! ## The body -/

/-- What two runs of the body share: the public data and key bytes, and
the overall status and trace. -/
structure BodyPub where
  pub : Pub
  leak : List Nat
  status : Nat
  tr : List Nat

structure BodyFacts (b : BodyPub) (s₀ : State) : Prop where
  leak : keyLeak s₀ = b.leak
  status : (rResult s₀).status = b.status
  tr : (rResult s₀).trace = b.tr

/-- The body's entry, after the frame's allocation. -/
def BodyEntry (b : BodyPub) (s₀ t : State) : Prop := BodyFacts b s₀ ∧ t = allocated Random.frameBytes s₀

/-- After the entry block. -/
def Entered (b : BodyPub) (s₀ t : State) : Prop :=
  BodyFacts b s₀ ∧ Ready s₀ t ∧ Saved s₀ t.mem ∧ slot t.mem (rBase s₀) oUsed = 0 ∧
    slot t.mem (rBase s₀) oAttempts = 8

/-- After `prepare`. -/
structure Prepped (b : BodyPub) (s₀ t : State) : Prop where
  facts : BodyFacts b s₀
  ready : Ready s₀ t
  eax : t.gpr .eax = if 1 < rq s₀ then 1 else 0
  prep : 1 < rq s₀ → Prepared s₀ t
  saved : Saved s₀ t.mem
  used : slot t.mem (rBase s₀) oUsed = 0
  attempts : slot t.mem (rBase s₀) oAttempts = 8

theorem Prepped.fupd {b : BodyPub} {s₀ t u : State} (h : Prepped b s₀ t) (f : Fupd t u) : Prepped b s₀ u := by
  have hr := h.ready.fupd f
  have hm : u.mem = t.mem := f.mem
  refine ⟨h.facts, hr, by rw [f.gpr]; exact h.eax, fun hq => ?_, by rw [hm]; exact h.saved,
    by rw [hm]; exact h.used, by rw [hm]; exact h.attempts⟩
  have P := h.prep hq
  exact ⟨hr, by rw [hm]; exact P.q, by rw [hm]; exact P.width, by rw [hm]; exact P.mask,
    by rw [hm]; exact P.nonce⟩

theorem prepped_ok {b : BodyPub} {s₀ t : State} (A : RandomSignABI s₀) (E : Entered b s₀ t) :
    WP isa prepare t (Prepped b s₀) := by
  obtain ⟨Fb, h₁, sv₁, us₁, at₁⟩ := E
  refine WP.mono (prepare_ok A h₁) fun t₂ ⟨ax₂, P₂, h₂, o₂, _⟩ => ?_
  have lo₂ : ∀ d, d + 4 ≤ oQ → slot t₂.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd =>
    outs_low o₂ (by decide) hd (by unfold oQ at hd; omega)
  exact ⟨Fb, h₂, ax₂, P₂, sv₁.of_slots fun d _ hd => lo₂ d (by unfold oQ; omega),
    by rw [lo₂ _ (by decide)]; exact us₁, by rw [lo₂ _ (by decide)]; exact at₁⟩

/-- After the test of q. -/
def Checked (b : BodyPub) (s₀ t : State) : Prop := Prepped b s₀ t ∧ t.zf = some (!decide (1 < rq s₀))

/-- q ≤ 1: the status, and the end. -/
theorem small_fin {b : BodyPub} {s₀ t : State} (A : RandomSignABI s₀) (C : Checked b s₀ t) (hq : ¬ 1 < rq s₀) :
    WP isa (.block [.store (sp oStatus) .eax]) t fun u => Fin s₀ u ∧ (rResult s₀).status = b.status := by
  obtain ⟨Pp, _⟩ := C
  have hR := rResult_small A hq
  have ax₃ : t.gpr .eax = BitVec.ofNat 32 (rResult s₀).status := by
    rw [Pp.eax, hR]; simp only [hq, ↓reduceIte]; rfl
  refine wp_slot Pp.ready.rf (by decide) ax₃ fun t₄ f₄ m₄ g₄ r₄ w₄ _ _ => WP.block_nil ?_
  have h₄ : Ready s₀ t₄ := Pp.ready.congr (rs := []) ⟨fun r _ => by rw [g₄], r₄, w₄⟩
    (by rw [m₄]; exact frame_store s₀ _ (by decide) _)
  refine ⟨⟨h₄, ?_, by rw [m₄, slot_write_self], fun e => by rw [hR] at e; exact absurd e (by decide),
    Pp.saved.of_slots fun d _ hd => by rw [m₄, slot_write_ne _ _ _ (by unfold oStatus; omega) (by omega)
      (by decide)]⟩, Pp.facts.status⟩
  rw [m₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide), Pp.used, hR]; rfl

theorem body_ct (F : SignFn) :
    RelCT isa (Two fun b => At (BodyEntry b) b.pub) (body F.name F.code) fun _ _ => True := by
  unfold body
  refine RelCT.seq (two_piece (Ψ := fun b => At (Entered b) b.pub) [.esp]
    (fun b t₁ t₂ ⟨s₁, _, e₁, _, h₁⟩ ⟨s₂, _, e₂, _, h₂⟩ r hr => by
      rw [List.mem_singleton] at hr; subst hr h₁ h₂
      rw [allocated_esp, allocated_esp, pub_esp (e₁.trans e₂.symm)]) (by taint_decide)
    fun b t ⟨s₀, A, e, Fb, ht⟩ => ?_) ?_
  · subst ht
    exact WP.mono (entry_ok (alloc_ready A) (allocated_gpr _ _ (by decide)) (allocated_gpr _ _ (by decide))
      (allocated_gpr _ _ (by decide)) (allocated_gpr _ _ (by decide)))
      fun u ⟨h, sv, us, at₁, _⟩ => ⟨s₀, A, e, Fb, h, sv, us, at₁⟩
  refine RelCT.seq (two_post (Ψ := fun b => At (Prepped b) b.pub)
    (two_map BodyPub.pub (fun b t ⟨s₀, A, e, E⟩ => ⟨s₀, A, e, E.2.1⟩) prepare_ct)
    fun b t ⟨s₀, A, e, E⟩ => WP.mono (prepped_ok A E) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun b => At (Checked b) b.pub) [.esp]
    (pins_at BodyPub.pub fun _ _ _ h => h.ready) (by taint_decide)
    fun b t ⟨s₀, A, e, Pp⟩ => wp_cmpi fun u f _ z => WP.block_nil ⟨s₀, A, e, Pp.fupd f, ?_⟩) ?_
  · rw [z, Pp.eax]
    by_cases hq : 1 < rq s₀ <;> simp [hq]
  refine RelCT.seq (R := Two FinAt) (two_ite (fun b t₁ t₂ ⟨s₁, _, e₁, _, z₁⟩ ⟨s₂, _, e₂, _, z₂⟩ => by
    simp only [eval, z₁, z₂, pub_rq (e₁.trans e₂.symm)]) ?_ ?_) finish_ct
  · refine (two_post (Ψ := fun (b : BodyPub) => At (fun s₀ t => Fin s₀ t ∧ (rResult s₀).status = b.status) b.pub)
      (two_taint [.esp] (pins_at' BodyPub.pub fun _ _ _ h => h.1.ready) (by taint_decide))
      fun b t ⟨⟨s₀, A, e, C⟩, hb⟩ => WP.mono (small_fin A C (by
        have := C.2; simp only [eval, this, Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at hb
        exact hb)) fun u hu => ⟨s₀, A, e, hu⟩).mono (fun _ _ h => h)
      fun _ _ ⟨b, h₁, h₂⟩ => ⟨(b.pub, b.status), h₁, h₂⟩
  · refine two_map (fun b => (⟨b.pub, b.leak, 0, 8, b.tr, b.status⟩ : AttPub))
      (fun b t ⟨⟨s₀, A, e, Pp, z⟩, hb⟩ => ⟨rfl, s₀, A, e, ?_, Pp.facts.status⟩) (attemptLoop_ct F 8)
    have hq : 1 < rq s₀ := by
      simp only [eval, z, Option.some.injEq, Bool.not_eq_false', decide_eq_true_eq] at hb
      exact hb
    have P := Pp.prep hq
    have hql := rQBytes_le A
    have er : randomSignRemaining (rInput s₀) 0 8 = rResult s₀ := by rw [rResult_loop A]; rfl
    refine ⟨⟨hq, (by decide : 1 ≤ 8), (by decide : 8 ≤ 8), Pp.facts.leak, by
      show (randomSignRemaining (rInput s₀) 0 8).trace = b.tr; rw [er]; exact Pp.facts.tr⟩, ?_⟩
    refine ⟨⟨(slot t.mem (rBase s₀) oDraws).toNat, ⟨Pp.ready, P.q, P.width, P.mask, Pp.used,
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], fun i hi => P.nonce i (by omega), Nat.zero_le _⟩⟩,
      Pp.attempts, Pp.saved, ?_⟩
    exact ⟨by rw [er], by rw [er], by rw [er]⟩

end VG.Proof.Dsa.X86
