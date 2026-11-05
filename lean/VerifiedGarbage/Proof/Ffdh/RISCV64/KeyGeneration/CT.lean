module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.Correct
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.Correct
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The key search's timing depends on its public descriptor and statuses (RISC-V)

As on PPC64LE (`Proof/Ffdh/PPC64LE/KeyGeneration/`): two runs are related by
`Two` (`Proof/Bignum/RISCV64/PreCT.lean`) at each cut, both satisfying a
predicate for the same public point (`KeyPoint`): the public descriptor, the
octets consumed, the budgets left and the statuses of the attempts still to
come, which the search from there gives for each run's own tape. The blocks
between the branches are checked by the taint analysis from the registers a
predicate fixes (`s0`, the base of the controller's words); the branches
test what the point fixes: the budgets, the tape's length and the attempt's
status, the first of those still to come. The attempt leaks only its public
arguments, the domain and its status (`RelCT.callEx`, from its constant
time); its frame and the frame saving `ra` leak nothing of their own
(`relCT_alloc`, `relCT_pushRa`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.KeyGeneration

open VG VG.RISCV64 VG.RISCV64.Taint VG.Spec.Ffdh VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Proof.Ffdh.RISCV64.GenerateKey (gkContract gkLeak gkStatus)
open VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Ffdh.Control (writeController)
open VG.Impl.Ffdh.RISCV64.KeyGeneration.Search

/-! ## Relating two runs -/

theorem two_map {α β : Type} {Φ : α → State → Prop} {Φ' : β → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (g : α → β) (h : ∀ a s, Φ a s → Φ' (g a) s) (hct : RelCT isa (Two Φ') c Q) :
    RelCT isa (Two Φ) c Q :=
  hct.mono (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨g a, h _ _ h₁, h _ _ h₂, hsp⟩) fun _ _ h => h

/-- A branch whose condition `Φ a` fixes. -/
theorem two_ite {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el : Prog isa}
    {Q : State → State → Prop}
    (hc : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval cond s₁ = isa.eval cond s₂)
    (ht : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some true) th Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some false) el Q) :
    RelCT isa (Two Φ) (.ite cond th el) Q := by
  refine RelCT.ite (fun _ _ ⟨a, h₁, h₂, _⟩ => hc a _ _ h₁ h₂) (ht.mono ?_ fun _ _ h => h)
    (he.mono ?_ fun _ _ h => h)
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, ⟨h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩, hsp⟩
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, ⟨h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩, hsp⟩

/-- Allocating and freeing a buffer leaks nothing. -/
theorem relCT_alloc {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocd bytes s ∧ b = allocd bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocd bytes a := by
    intro a b h
    simp only [isa, VG.RISCV64.push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      exact ⟨rfl, trivial⟩

/-- A frame saving `ra` around a body proven with the permissions outside it
(as `WP.frameRegAny` runs it) leaks what the body does there: the body's run
in the frame is that run, with more permissions (`Exec.widen`). -/
theorem relCT_pushRa {body : Prog isa} {P : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp)
    (hwp : ∀ a b, P a b → (∃ t s', Exec isa body (framed .ra a) t s') ∧
      (∃ t s', Exec isa body (framed .ra b) t s'))
    (hct : RelCT isa (fun x y => ∃ a b, P a b ∧ x = framed .ra a ∧ y = framed .ra b) body
      fun _ _ => True) :
    RelCT isa P (.frame (.push .ra) body (.pop .ra)) fun a b => a.sp = b.sp := by
  refine RelCT.frame (R := fun _ _ => True) hsp ?_
  have widen : ∀ a, ∀ {t s'}, Exec isa body (framed .ra a) t s' →
      Exec isa body (pushed .ra a) t (s'.withRegions a.rd (⟨a.sp - 16, 16⟩ :: a.wr)) := by
    intro a t s' e
    have := Exec.widen e (rd := a.rd) (wr := ⟨a.sp - 16, 16⟩ :: a.wr)
      (Covers.of_mem fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact List.mem_append_left _ hr
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr))
      (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)
    exact this
  rintro x y tx ty x' y' ⟨a, b, hab, rfl, rfl⟩ ex ey
  obtain ⟨⟨ta, sa, ea⟩, ⟨tb, sb, eb⟩⟩ := hwp a b hab
  obtain ⟨rfl, -⟩ := Exec.det ex (widen a ea)
  obtain ⟨rfl, -⟩ := Exec.det ey (widen b eb)
  exact ⟨(hct _ _ _ _ _ _ ⟨a, b, hab, rfl, rfl⟩ ea eb).1, trivial⟩

/-! ## Public positions in the key search, and its exits and rejections -/

/-- Some loop state of the search with the public descriptor `p`. -/
def KeyAny (p : KeyPublic) (s : State) : Prop :=
  ∃ original used keys scalars, KeyLive p original used keys scalars s

structure KeyPoint where
  inputs : KeyPublic
  used : Nat
  keys : Nat
  scalars : Nat
  statuses : List Nat

def KeyCTL (q : KeyPoint) (s : State) : Prop :=
  ∃ original, KeyLive q.inputs original q.used q.keys q.scalars s ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses

theorem KeyCTL.any {q : KeyPoint} {s : State} (h : KeyCTL q s) : KeyAny q.inputs s :=
  let ⟨original, h, _⟩ := h; ⟨original, _, _, _, h⟩

theorem key_any_pins : Pins KeyAny [.s0] := by
  intro p s t ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.s0.trans h₂.s0.symm

theorem key_ctl_pins : Pins KeyCTL [.s0] :=
  fun _ _ _ h₁ h₂ => key_any_pins _ _ _ h₁.any h₂.any

theorem key_no_pins {α : Type} {Φ : α → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ h => by cases h

/-- Before a zeroing's loop: its pointer and count. -/
def KeyZeroCT (j : Nat) (p : KeyPublic) (s : State) : Prop :=
  KeyAny p s ∧ s.gpr .t0 = (if j = 5 then p.xp else p.yp) ∧ s.gpr .t1 = BitVec.ofNat 64 p.len

private theorem zero_header (j : Nat) (hj : j = 5 ∨ j = 6) (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block [ldf .t0 j, ldf .t1 2, .li .t2 0]) s (KeyZeroCT j p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  have a := h.access
  have hk : word s.mem p.control 16 = BitVec.ofNat 64 p.len :=
    h.header (j := 2) (by simp [KeyPublic.headers])
  simp only [Bignum.word] at hk
  rcases hj with rfl | rfl <;>
  refine WP.mono (WP.ctl (Q := fun t => (t.gpr .t0 = (if _ = 5 then p.xp else p.yp) ∧
    t.gpr .t1 = BitVec.ofNat 64 p.len) ∧ t.mem = s.mem) ?_ (by rfl))
    fun _ ⟨⟨hr, hm⟩, k, hsp⟩ => ⟨⟨original, used, keys, scalars, h.keep k hsp hm⟩, hr⟩
  · have hp : word s.mem p.control 40 = p.xp := h.header (j := 5) (by simp [KeyPublic.headers])
    simp only [Bignum.word] at hp
    brun [ldf, h.s0, hp, hk, a.ld 40 (by decide), a.ld 16 (by decide), a.al 40 (by decide) (by decide),
      a.al 16 (by decide) (by decide), fin64_exec_li_zero]
  · have hp : word s.mem p.control 48 = p.yp := h.header (j := 6) (by simp [KeyPublic.headers])
    simp only [Bignum.word] at hp
    brun [ldf, h.s0, hp, hk, a.ld 48 (by decide), a.ld 16 (by decide), a.al 48 (by decide) (by decide),
      a.al 16 (by decide) (by decide), fin64_exec_li_zero]

private theorem zero_ct (j : Nat) (hj : j = 5 ∨ j = 6) :
    RelCT isa (Two KeyAny) (zeroOut j) (fun _ _ => True) := by
  rcases hj with rfl | rfl <;> unfold zeroOut <;>
  · refine RelCT.seq (two_post (two_taint [.s0] key_any_pins (by taint_decide))
      (zero_header _ (by decide))) ?_
    exact two_taint [.t0, .t1] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm]) (by taint_decide)

private theorem zero_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (zeroOut 5) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  exact WP.mono (key_zero_out h (j := 5) (.inl rfl) (by simp [KeyPublic.headers]) h.input.x_mem
    h.input.x_ne_ctl) fun _ ⟨ht, _⟩ => ⟨original, used, keys, scalars, ht⟩

theorem key_zero_outputs_ct : RelCT isa (Two KeyAny) zeroOutputs (fun _ _ => True) := by
  unfold zeroOutputs
  exact RelCT.seq (two_post (zero_ct 5 (.inl rfl)) zero_ready) (zero_ct 6 (.inr rfl))

private theorem terminal_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block (terminal 3)) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  exact WP.mono (key_terminal_live h (.inr rfl)) fun _ ⟨ht, _⟩ => ⟨original, used, 0, 0, ht⟩

theorem key_exhausted_ct : RelCT isa (Two KeyAny) exhausted (fun _ _ => True) := by
  unfold exhausted
  exact RelCT.seq (two_post (two_taint [.s0] key_any_pins (by taint_decide)) terminal_ready)
    key_zero_outputs_ct

private theorem request_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block [ldf .t1 2, .li .t2 0, stf .t1 3, stf .t2 14]) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  exact WP.mono (key_request_live h) fun _ ⟨ht, _⟩ => ⟨original, used, keys, scalars, ht⟩

theorem key_request_ct : RelCT isa (Two KeyAny) request (fun _ _ => True) := by
  unfold request
  exact RelCT.seq (two_post (two_taint [.s0] key_any_pins (by taint_decide)) request_ready)
    key_zero_outputs_ct

theorem key_accepted_ct : RelCT isa (Two KeyAny) (.block (terminal 1)) (fun _ _ => True) :=
  two_taint [.s0] key_any_pins (by taint_decide)

theorem key_rejected_scalar_ct : RelCT isa (Two KeyAny) (.block rejectedScalar) (fun _ _ => True) :=
  two_taint [.s0] key_any_pins (by taint_decide)

theorem key_rejected_public_ct : RelCT isa (Two KeyAny) (.block rejectedPublic) (fun _ _ => True) :=
  two_taint [.s0] key_any_pins (by taint_decide)

/-! ## The attempt

The attempt's timing may depend on its arguments, the domain and its status
(`gkContract.pub`). Two runs at the same point agree on all of them: the
status is the first of the statuses still to come. -/

/-- A loop state at which the controller attempts a key. -/
def KeyReady (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen

def KeyAllocated (q : KeyPoint) (u : State) : Prop := ∃ s, KeyReady q s ∧ u = allocd 32 s

/-- The attempt's entry, before the call. -/
def KeyCallCT (q : KeyPoint) (u : State) : Prop :=
  ∃ original s, KeyLive q.inputs original q.used q.keys q.scalars s ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    KeyArgs q.inputs q.used u ∧
    u.mem = writeController (allocd 32 s).mem (callSp q.inputs) (callValues q.inputs) ∧
    Keep tmpRegs (allocd 32 s) u ∧ u.sp = (allocd 32 s).sp

/-- After the attempt. -/
def KeyAttempted (q : KeyPoint) (t : State) : Prop :=
  ∃ original, KeyLive q.inputs original q.used q.keys q.scalars t ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    AttemptPost q.inputs (keyRand original) q.used t

theorem key_allocated_pins : Pins KeyAllocated [.s0] := by
  rintro q _ _ ⟨a, ⟨⟨_, h₁, _⟩, _⟩, rfl⟩ ⟨b, ⟨⟨_, h₂, _⟩, _⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.s0.trans h₂.s0.symm

private theorem arguments_ready (q : KeyPoint) (u : State) (h : KeyAllocated q u) :
    WP isa (.block arguments) u (KeyCallCT q) := by
  obtain ⟨s, ⟨⟨original, h, hst⟩, hk, hs, hr⟩, rfl⟩ := h
  exact WP.mono (key_arguments_ok h) fun _ ⟨⟨ha, hm⟩, k, hsp⟩ =>
    ⟨original, s, h, hst, hk, hs, hr, ha, hm, k, hsp⟩

theorem key_attempt_ready (a : Attempt) (q : KeyPoint) (s : State) (h : KeyReady q s) :
    WP isa (attemptRun a.call) s (KeyAttempted q) := by
  obtain ⟨⟨original, h, hst⟩, hk, hs, hr⟩ := h
  exact WP.mono (key_attempt_run a h hr) fun _ ⟨ht, hp⟩ => ⟨original, ht, hst, hk, hs, hr, hp⟩

/-- The status of the attempt at a point: the first still to come. -/
def KeyPoint.status (q : KeyPoint) : Nat := q.statuses.head?.getD 0

/-- The attempt's status at a point, for each run's tape. -/
theorem attempt_status {q : KeyPoint} {original s : State}
    (h : KeyLive q.inputs original q.used q.keys q.scalars s)
    (hst : (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses)
    (hk : q.keys ≠ 0) (hs : q.scalars ≠ 0) (hr : q.used + q.inputs.len ≤ q.inputs.randLen) :
    attemptStatus q.inputs.a q.inputs.len ((keyRand original).drop q.used) = q.status := by
  have hhead := keyTail_statuses_head (a := q.inputs.a) (len := q.inputs.len)
    (rand := keyRand original) (used := q.used) hk hs (by rw [h.rand_length]; omega)
  rw [hst] at hhead
  simp only [KeyPoint.status, hhead, Option.getD_some]

/-- What the attempt sees at its entry, in terms of the point alone. -/
private theorem call_view {q : KeyPoint} {u : State} (h : KeyCallCT q u) :
    (callState q.inputs q.used u).sp = callSp q.inputs ∧
    gkLeak (callState q.inputs q.used u) = q.inputs.dom.map (·.toNat) ++ [q.status] ∧
    KeyArgs q.inputs q.used (callState q.inputs q.used u) ∧
    stackArg (callState q.inputs q.used u) 0 = BitVec.ofNat 64 q.inputs.len ∧
    stackArg (callState q.inputs q.used u) 1 = q.inputs.B ∧
    stackArg (callState q.inputs q.used u) 2 = BitVec.ofNat 64 (q.inputs.Z / 8) := by
  obtain ⟨original, s, h, hst, hk, hs, hr, ha, hm, k, husp⟩ := h
  have hu : u.sp = callSp q.inputs := husp.trans (allocd_sp h)
  have hf := h.callFacts hr
  obtain ⟨hdom, hrand, h6⟩ := call_inputs h hr hf hm hu ha
  have he := attempt_status h hst hk hs hr
  obtain ⟨h0, h1, h2⟩ := call_args hu hm
  refine ⟨by simp only [State.withRegions_sp, State.callEntry_sp, hu], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gkLeak, gkStatus, hdom, hrand, h6]
    rw [← he]
    rfl
  · obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
    exact ⟨(call_gpr (by decide)).trans r0, (call_gpr (by decide)).trans r1, (call_gpr (by decide)).trans r2,
      (call_gpr (by decide)).trans r3, (call_gpr (by decide)).trans r4, (call_gpr (by decide)).trans r5,
      (call_gpr (by decide)).trans r6, (call_gpr (by decide)).trans r7⟩
  · rw [call_stackArg, h0]
  · rw [call_stackArg, h1]
  · rw [call_stackArg, h2]

private theorem call_pub {q : KeyPoint} {u₁ u₂ : State} (h₁ : KeyCallCT q u₁) (h₂ : KeyCallCT q u₂) :
    gkContract.pub (callState q.inputs q.used u₁) (callState q.inputs q.used u₂) := by
  obtain ⟨a₁, b₁, ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩, d₀, d₁, d₂⟩ := call_view h₁
  obtain ⟨a₂, b₂, ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩, f₀, f₁, f₂⟩ := call_view h₂
  exact ⟨a₁.trans a₂.symm, c0.trans e0.symm, c1.trans e1.symm, c2.trans e2.symm, c3.trans e3.symm,
    c4.trans e4.symm, c5.trans e5.symm, c6.trans e6.symm, c7.trans e7.symm, d₀.trans f₀.symm,
    d₁.trans f₁.symm, d₂.trans f₂.symm, b₁.trans b₂.symm⟩

private theorem call_ready {q : KeyPoint} {u : State} (h : KeyCallCT q u) :
    gkContract.pre (callState q.inputs q.used u) ∧
      Covers (callRd q.inputs q.used ++ callWr q.inputs) (u.rd ++ u.wr) ∧
      Covers (callWr q.inputs) u.wr := by
  obtain ⟨original, s, h, _, _, _, hr, ha, hm, k, husp⟩ := h
  have hu : u.sp = callSp q.inputs := husp.trans (allocd_sp h)
  exact ⟨call_attempt_pre (h.callFacts hr) hu ha hm, call_covers_reads h hr k.2.1 k.2.2,
    call_covers_writes h k.2.2⟩

theorem key_attempt_call_ct (a : Attempt) :
    RelCT isa (Two KeyCallCT) a.call (fun _ _ => True) := by
  refine RelCT.callEx a.correct a.ct fun u₁ u₂ ⟨q, h₁, h₂, _⟩ => ?_
  obtain ⟨p₁, c₁, w₁⟩ := call_ready h₁
  obtain ⟨p₂, c₂, w₂⟩ := call_ready h₂
  exact ⟨_, _, _, _, p₁, p₂, call_pub h₁ h₂, c₁, w₁, c₂, w₂⟩

theorem key_attempt_run_ct (a : Attempt) :
    RelCT isa (Two KeyReady) (attemptRun a.call) (fun _ _ => True) := by
  unfold attemptRun
  apply relCT_alloc
  refine (RelCT.seq (two_post (two_taint [.s0] key_allocated_pins (by taint_decide)) arguments_ready)
    (key_attempt_call_ct a)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocd, hsp]⟩

/-! ## The classification

The attempt's classification branches on its status, the first of the
statuses still to come; the guards on the budgets and the tape, which the
point fixes. -/

theorem key_attempted_pins : Pins KeyAttempted [.s0] := by
  intro q s t ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.s0.trans h₂.s0.symm

/-- The status in `t0`, compared with `k` in `t1`. -/
def KeyGuard (k : Nat) (q : KeyPoint) (t : State) : Prop :=
  KeyAny q.inputs t ∧ t.gpr .t0 = BitVec.ofNat 64 q.status ∧
    isa.eval (.zero .t1) t = some (decide (q.status = k)) ∧ q.status < 4

private theorem first_ready (q : KeyPoint) (s : State) (h : KeyAttempted q s) :
    WP isa (.block (advance ++ test 1)) s (KeyGuard 1 q) := by
  obtain ⟨original, h, hst, hk, hs, hr, hp⟩ := h
  have he := attempt_status h hst hk hs hr
  have h4 : q.status < 4 := by
    rw [← he]
    rcases attemptStatus_cases q.inputs.a q.inputs.len ((keyRand original).drop q.used) with
      h | h | h <;> omega
  refine WP.mono (key_classify_head h hr hp) fun t ⟨ht, _, hax, hev⟩ => ?_
  exact ⟨⟨original, _, _, _, ht⟩, by rw [hax, he], by rw [hev, he], h4⟩

private theorem next_ready (j k : Nat) (hk : k = 1 ∨ k = 2 ∨ k = 3) (q : KeyPoint) (s : State)
    (h : KeyGuard j q s ∧ isa.eval (.zero .t1) s = some false) :
    WP isa (.block (test k)) s (KeyGuard k q) := by
  obtain ⟨⟨⟨o, u, a, c, hl⟩, ha, _, h4⟩, _⟩ := h
  refine WP.mono (test_ok ha h4 hk) fun t ⟨⟨he, hm⟩, kt, hsp⟩ => ?_
  exact ⟨⟨o, u, a, c, hl.keep kt hsp hm⟩, (kt.gpr (by decide)).trans ha, he, h4⟩

private theorem leaf {k : Nat} {b : Bool} {c : Prog isa} (hc : RelCT isa (Two KeyAny) c fun _ _ => True) :
    RelCT isa (Two fun q s => KeyGuard k q s ∧ isa.eval (.zero .t1) s = some b) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q.inputs, h₁.1.1, h₂.1.1, hsp⟩) fun _ _ h => h

private theorem guard_eq (k : Nat) (q : KeyPoint) (s₁ s₂ : State) (h₁ : KeyGuard k q s₁)
    (h₂ : KeyGuard k q s₂) : isa.eval (.zero .t1) s₁ = isa.eval (.zero .t1) s₂ :=
  h₁.2.2.1.trans h₂.2.2.1.symm

theorem key_classify_ct : RelCT isa (Two KeyAttempted) classify (fun _ _ => True) := by
  unfold classify
  refine RelCT.seq (two_post (two_taint [.s0] key_attempted_pins (by taint_decide)) first_ready) ?_
  refine two_ite (guard_eq 1) (leaf key_accepted_ct) ?_
  refine RelCT.seq (two_post (two_taint [] key_no_pins (by taint_decide))
    (next_ready 1 2 (.inr (.inl rfl)))) ?_
  refine two_ite (guard_eq 2) (leaf key_rejected_scalar_ct) ?_
  refine RelCT.seq (two_post (two_taint [] key_no_pins (by taint_decide))
    (next_ready 2 3 (.inr (.inr rfl)))) ?_
  exact two_ite (guard_eq 3) (leaf key_rejected_public_ct) (leaf key_exhausted_ct)

/-! ## The guards -/

/-- Whether the search goes on after an iteration from `q`: it attempts, and
the attempt is rejected. -/
def keyContinues (q : KeyPoint) : Prop :=
  q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.inputs.len ≤ q.inputs.randLen - q.used ∧ q.status ≠ 1

instance (q : KeyPoint) : Decidable (keyContinues q) := inferInstanceAs
  (Decidable (q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.inputs.len ≤ q.inputs.randLen - q.used ∧ q.status ≠ 1))

/-- The point after a rejected attempt. -/
def nextKeyPoint (q : KeyPoint) : KeyPoint :=
  if q.status = 2 then ⟨q.inputs, q.used + q.inputs.len, q.keys, q.scalars - 1, q.statuses.tail⟩
  else ⟨q.inputs, q.used + q.inputs.len, q.keys - 1, 128, q.statuses.tail⟩

theorem nextKeyPoint_inputs (q : KeyPoint) : (nextKeyPoint q).inputs = q.inputs := by
  unfold nextKeyPoint; split <;> rfl

theorem nextKeyPoint_measure {q : KeyPoint} (h : keyContinues q) :
    128 * (nextKeyPoint q).keys + (nextKeyPoint q).scalars < 128 * q.keys + q.scalars := by
  obtain ⟨hk, hs, -, -⟩ := h
  unfold nextKeyPoint; split <;> dsimp only <;> omega

/-- After the guards, the attempt and its classification. -/
def KeyBranchResult (q : KeyPoint) (t : State) : Prop :=
  if keyContinues q then KeyCTL (nextKeyPoint q) t ∧ word t.mem q.inputs.control 112 = 4
  else ∃ original r, KeyDone q.inputs original r t

theorem branch_s0 {q : KeyPoint} {t : State} (h : KeyBranchResult q t) :
    t.gpr .s0 = q.inputs.control := by
  by_cases hc : keyContinues q
  · simp only [KeyBranchResult, hc, ite_true] at h
    obtain ⟨⟨_, hl, _⟩, _⟩ := h
    rw [hl.s0, nextKeyPoint_inputs]
  · simp only [KeyBranchResult, hc, ite_false] at h
    obtain ⟨_, _, hd⟩ := h
    exact hd.s0

def KeysGuard (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ isa.eval (.zero .t0) s = some (decide (q.keys = 0))

def ScalarsGuard (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ isa.eval (.zero .t0) s = some (decide (q.scalars = 0))

def RoomGuard (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧
    isa.eval (.ltu .t0 .t1) s = some (decide (q.inputs.randLen - q.used < q.inputs.len))

theorem keys_ready (q : KeyPoint) (s : State) (h : KeyCTL q s) :
    WP isa (.block [ldf .t0 0]) s (KeysGuard q) := by
  obtain ⟨original, h, hst⟩ := h
  exact WP.mono (keys_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht, hst⟩, he⟩

theorem scalars_ready (q : KeyPoint) (s : State) (h : KeysGuard q s ∧ isa.eval (.zero .t0) s = some false) :
    WP isa (.block [ldf .t0 1]) s (ScalarsGuard q) := by
  obtain ⟨⟨⟨original, h, hst⟩, he⟩, hf⟩ := h
  have hk : q.keys ≠ 0 := of_decide_eq_false (Option.some.inj (he.symm.trans hf))
  exact WP.mono (scalars_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht, hst⟩, hk, he⟩

theorem room_ready (q : KeyPoint) (s : State) (h : ScalarsGuard q s ∧ isa.eval (.zero .t0) s = some false) :
    WP isa (.block room) s (RoomGuard q) := by
  obtain ⟨⟨⟨original, h, hst⟩, hk, he⟩, hf⟩ := h
  have hs : q.scalars ≠ 0 := of_decide_eq_false (Option.some.inj (he.symm.trans hf))
  exact WP.mono (room_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht, hst⟩, hk, hs, he⟩

theorem attempt_of_room {q : KeyPoint} {s : State}
    (h : RoomGuard q s ∧ isa.eval (.ltu .t0 .t1) s = some false) : KeyReady q s := by
  obtain ⟨⟨⟨original, hl, hst⟩, hk, hs, he⟩, hf⟩ := h
  have hr := of_decide_eq_false (Option.some.inj (he.symm.trans hf))
  exact ⟨⟨original, hl, hst⟩, hk, hs, by have := hl.used_le; omega⟩

theorem key_branch_ready (a : Attempt) (q : KeyPoint) (s : State) (h : KeysGuard q s) :
    WP isa (branch a.call) s (KeyBranchResult q) := by
  obtain ⟨⟨original, hl, hst⟩, he⟩ := h
  have done : ∀ (t : State) (r : KeySearchResult), ¬keyContinues q →
      KeyDone q.inputs original r t → KeyBranchResult q t := fun t r hn hd => by
    simp only [KeyBranchResult, hn, ite_false]; exact ⟨original, r, hd⟩
  unfold branch
  refine WP.ite (decide (q.keys = 0)) he ?_ ?_
  · intro hz
    exact WP.mono (key_exhausted hl) fun t ht => done t _ (fun hc => hc.1 (of_decide_eq_true hz)) ht
  intro hnz
  have hk : q.keys ≠ 0 := of_decide_eq_false hnz
  refine WP.seq (WP.mono (scalars_guard hl) fun u ⟨hu, he2⟩ => ?_)
  refine WP.ite (decide (q.scalars = 0)) he2 ?_ ?_
  · intro hz
    exact WP.mono (key_exhausted hu) fun t ht => done t _ (fun hc => hc.2.1 (of_decide_eq_true hz)) ht
  intro hnz2
  have hs : q.scalars ≠ 0 := of_decide_eq_false hnz2
  unfold attemptOrRequest
  refine WP.seq (WP.mono (room_guard hu) fun u ⟨hu3, hb⟩ => ?_)
  refine WP.ite _ hb ?_ ?_
  · intro hshort
    have := of_decide_eq_true hshort
    exact WP.mono (key_request hu3) fun t ht => done t _ (fun hc => by have := hc.2.2.1; omega) ht
  intro hlong
  have hroom : q.used + q.inputs.len ≤ q.inputs.randLen := by
    have := of_decide_eq_false hlong; have := hl.used_le; omega
  refine WP.seq (WP.mono (key_attempt_run a hu3 hroom) fun t ⟨ht, hp⟩ => ?_)
  refine WP.mono (key_classify ht hroom (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hs) hp)
    fun r hq => ?_
  have hstat := attempt_status hl hst hk hs hroom
  have hr : q.inputs.len ≤ (keyRand original).length - q.used := by rw [hl.rand_length]; omega
  rcases attemptStatus_cases q.inputs.a q.inputs.len ((keyRand original).drop q.used) with h1 | h2 | h3
  · simp only [KeyClassified, h1, ite_true] at hq
    exact done r _ (fun hc => hc.2.2.2 (by rw [← hstat, h1])) hq
  · simp only [KeyClassified, h2, Nat.reduceEqDiff, ite_true, ite_false] at hq
    have hc : keyContinues q := ⟨hk, hs, by omega, by rw [← hstat, h2]; decide⟩
    have hn : nextKeyPoint q = ⟨q.inputs, q.used + q.inputs.len, q.keys, q.scalars - 1, q.statuses.tail⟩ := by
      simp only [nextKeyPoint, ← hstat, h2, ite_true]
    simp only [KeyBranchResult, hc, ite_true, hn]
    refine ⟨⟨original, hq.1, ?_⟩, hq.2⟩
    rw [← hst]
    simp only [KeyPublic.tail, keyTail_scalar hk hs hr h2, List.tail_cons]
  · simp only [KeyClassified, h3, Nat.reduceEqDiff, ite_false] at hq
    have hc : keyContinues q := ⟨hk, hs, by omega, by rw [← hstat, h3]; decide⟩
    have hn : nextKeyPoint q = ⟨q.inputs, q.used + q.inputs.len, q.keys - 1, 128, q.statuses.tail⟩ := by
      simp only [nextKeyPoint, ← hstat, h3, Nat.reduceEqDiff, ite_false]
    simp only [KeyBranchResult, hc, ite_true, hn]
    refine ⟨⟨original, hq.1, ?_⟩, hq.2⟩
    rw [← hst]
    simp only [KeyPublic.tail, keyTail_public hk hs hr h3, List.tail_cons]

private theorem leafB {Φ : KeyPoint → State → Prop} {c : Prog isa}
    (hΦ : ∀ q s, Φ q s → KeyAny q.inputs s) (hc : RelCT isa (Two KeyAny) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q.inputs, hΦ q _ h₁, hΦ q _ h₂, hsp⟩) fun _ _ h => h

theorem key_branch_ct (a : Attempt) :
    RelCT isa (Two KeysGuard) (branch a.call) (fun _ _ => True) := by
  unfold branch
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (leafB (fun _ _ h => h.1.1.any) key_exhausted_ct) ?_
  refine RelCT.seq (two_post (two_taint [.s0] (fun q _ _ h₁ h₂ => key_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide)) scalars_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm)
    (leafB (fun _ _ h => h.1.1.any) key_exhausted_ct) ?_
  unfold attemptOrRequest
  refine RelCT.seq (two_post (two_taint [.s0] (fun q _ _ h₁ h₂ => key_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide)) room_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm)
    (leafB (fun _ _ h => h.1.1.any) key_request_ct) ?_
  exact RelCT.seq (two_post ((key_attempt_run_ct a).mono
      (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, attempt_of_room h₁, attempt_of_room h₂, hsp⟩) fun _ _ h => h)
    fun q s h => key_attempt_ready a q s (attempt_of_room h)) key_classify_ct

/-! ## The loop -/

theorem key_iteration_ct (a : Attempt) :
    RelCT isa (Two KeyCTL) (iteration a.call) (fun _ _ => True) := by
  unfold iteration
  refine RelCT.seq (two_post (two_taint [.s0] key_ctl_pins (by taint_decide)) keys_ready) ?_
  exact RelCT.seq (two_post (key_branch_ct a) (key_branch_ready a))
    (two_taint [.s0] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact (branch_s0 h₁).trans (branch_s0 h₂).symm) (by taint_decide))

def KeyCTStep (q : KeyPoint) (s : State) : Prop :=
  if keyContinues q then isa.eval (.zero .t0) s = some true ∧ KeyCTL (nextKeyPoint q) s
  else isa.eval (.zero .t0) s = some false

theorem key_ct_step (a : Attempt) (q : KeyPoint) (s : State) (h : KeyCTL q s) :
    WP isa (iteration a.call) s (KeyCTStep q) := by
  unfold iteration
  refine WP.seq (WP.mono (keys_ready q s h) fun u hu => ?_)
  refine WP.seq (WP.mono (key_branch_ready a q u hu) fun t ht => ?_)
  by_cases hc : keyContinues q
  · simp only [KeyBranchResult, hc, ite_true] at ht
    obtain ⟨⟨original, hl, hst⟩, hw⟩ := ht
    rw [← nextKeyPoint_inputs q] at hw
    refine WP.mono (live_loop_guard hl hw) fun z ⟨hz, hzl⟩ => ?_
    simp only [KeyCTStep, hc, ite_true]
    exact ⟨hz, original, hzl, hst⟩
  · simp only [KeyBranchResult, hc, ite_false] at ht
    obtain ⟨_, _, hd⟩ := ht
    refine WP.mono (done_loop_guard hd) fun z ⟨hz, _⟩ => ?_
    simp only [KeyCTStep, hc, ite_false]
    exact hz

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q, n = 128 * q.keys + q.scalars + 1 ∧ KeyCTL q s ∧ KeyCTL q t ∧ s.sp = t.sp

private theorem iteration_pair (a : Attempt) (n : Nat) :
    RelCT isa (LoopPair n) (iteration a.call) fun s t =>
      isa.eval (.zero .t0) s = isa.eval (.zero .t0) t ∧
      (isa.eval (.zero .t0) s = some false → True) ∧
      (isa.eval (.zero .t0) s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : KeyPoint) (s : State) (h : n = 128 * q.keys + q.scalars + 1 ∧ KeyCTL q s) :
      WP isa (iteration a.call) s fun t => n = 128 * q.keys + q.scalars + 1 ∧ KeyCTStep q t :=
    WP.mono (key_ct_step a q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((key_iteration_ct a).mono
    (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.2, h₂.2, hsp⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂, hsp⟩ => ⟨q, ⟨hn, h₁⟩, ⟨hn, h₂⟩, hsp⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, ⟨_, h₂⟩, hsp⟩
  by_cases hb : keyContinues q
  · simp only [KeyCTStep, hb, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ?_⟩
    refine ⟨128 * (nextKeyPoint q).keys + (nextKeyPoint q).scalars + 1, ?_, nextKeyPoint q, rfl,
      h₁.2, h₂.2, hsp⟩
    have := nextKeyPoint_measure hb
    omega
  · simp only [KeyCTStep, hb, ite_false] at h₁ h₂
    exact ⟨h₁.trans h₂.symm, fun _ => trivial, fun ht => absurd (ht.symm.trans h₁) (by decide)⟩

theorem key_loop_ct (a : Attempt) :
    RelCT isa (Two KeyCTL) (.loop (iteration a.call) (.zero .t0)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht, hsp⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration a.call) (c := .zero .t0)
    (Q := fun _ _ => True) LoopPair (iteration_pair a) (128 * q.keys + q.scalars + 1)
    _ _ _ _ _ _ ⟨q, rfl, hs, ht, hsp⟩ he₁ he₂

/-! ## Entry and return -/

/-- A run's entry, with its public descriptor and its result's statuses. -/
def KeyStart (a : KeyPublic × List Nat) (s : State) : Prop :=
  KeyInput a.1 s ∧ (keyResult s).statuses = a.2

private theorem entry_pointer (p : KeyPublic) (s : State) (h : KeyInput p s) :
    WP isa (.block (entry.take 2)) s fun t => t.gpr .t2 = p.control ∧ t.gpr .t1 = p.sp := by
  have hd : s.mem.readW (s.sp + BitVec.ofNat 64 32) 64 = p.control :=
    (show _ = stackArg s 4 from rfl).trans (congrArg KeyPublic.control h.2)
  have ha4 := input_args h 4 (by decide)
  have hsp : s.sp.toNat % 8 = 0 := by have := h.1.2.2.1; omega
  simp only [Nat.reduceMul] at ha4
  unfold entry
  simp only [List.take_succ_cons, List.take_zero]
  brun [exec_addSp (show 0 < 2048 by decide), add_ofNat_zero, hd, ha4, al8 hsp (d := 32) (by decide),
    h.sp_eq]

private theorem pins_E2 : Pins (fun (p : KeyPublic) (t : State) =>
    t.gpr .t2 = p.control ∧ t.gpr .t1 = p.sp) [.t1, .t2] := by
  rintro p s t ⟨a2, a1⟩ ⟨b2, b1⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a1, b1]
  · rw [a2, b2]

private theorem entry_ct : RelCT isa (Two KeyInput) (.block entry) (fun _ _ => True) := by
  change RelCT isa (Two KeyInput) (.block (entry.take 2 ++ entry.drop 2)) _
  exact RelCT.block_append (RelCT.seq (two_post (two_taint [] key_no_pins (by taint_decide)) entry_pointer)
    (two_taint _ pins_E2 (by taint_decide)))

/-- After the entry: the controller's words written. -/
def KeyEntered (a : KeyPublic × List Nat) (t : State) : Prop :=
  ∃ s, KeyStart a s ∧ t.gpr .s0 = a.1.control ∧
    t.mem = writeController s.mem a.1.control (entryValues s) ∧ Keep entryRegs s t ∧ t.sp = s.sp

private theorem entry_ready (a : KeyPublic × List Nat) (s : State) (h : KeyStart a s) :
    WP isa (.block entry) s (KeyEntered a) :=
  WP.mono (entry_ok h.1) fun _ ⟨⟨hx, hm⟩, k, hsp⟩ => ⟨s, h, hx, hm, k, hsp⟩

private def initialPoint (a : KeyPublic × List Nat) : KeyPoint := ⟨a.1, 0, a.1.keys, a.1.scalars, a.2⟩

private theorem entered_ctl {a : KeyPublic × List Nat} {t : State} (h : KeyEntered a t) :
    KeyCTL (initialPoint a) (framed .ra t) := by
  rcases a with ⟨p, l⟩
  obtain ⟨s, ⟨hi, hst⟩, hx, hm, k, hsp⟩ := h
  refine ⟨s, key_start hi hx hm k hsp, ?_⟩
  show (p.tail (keyRand s) 0 p.keys p.scalars).statuses = l
  change (keyResult s).statuses = l at hst
  change KeyInput p s at hi
  rw [← hst, hi.tail_eq]

def KeyCTDone (p : KeyPublic) (s : State) : Prop := ∃ original r, KeyDone p original r s

private theorem search_ct (a : Attempt) : RelCT isa (Two KeyEntered) (search a.call) (fun _ _ => True) := by
  unfold search
  refine (relCT_pushRa (fun _ _ ⟨_, _, _, hsp⟩ => hsp) ?_ ?_).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  · rintro x y ⟨q, h₁, h₂, _⟩
    obtain ⟨original, hl, -⟩ := entered_ctl h₁
    obtain ⟨original', hl', -⟩ := entered_ctl h₂
    obtain ⟨t, s', e, -⟩ := key_loop a (n := 128 * q.1.keys + q.1.scalars + 1)
      (expected := (initialPoint q).inputs.tail (keyRand original) 0 q.1.keys q.1.scalars)
      ⟨0, _, _, rfl, hl, rfl, rfl⟩
    obtain ⟨t', s'', e', -⟩ := key_loop a (n := 128 * q.1.keys + q.1.scalars + 1)
      (expected := (initialPoint q).inputs.tail (keyRand original') 0 q.1.keys q.1.scalars)
      ⟨0, _, _, rfl, hl', rfl, rfl⟩
    exact ⟨⟨t, s', e⟩, ⟨t', s'', e'⟩⟩
  · refine (key_loop_ct a).mono ?_ fun _ _ h => h
    rintro _ _ ⟨x, y, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
    exact ⟨initialPoint q, entered_ctl h₁, entered_ctl h₂, by simp only [framed, hsp]⟩

private theorem search_ready (a : Attempt) (q : KeyPublic × List Nat) (t : State) (h : KeyEntered q t) :
    WP isa (search a.call) t (KeyCTDone q.1) := by
  obtain ⟨s, ⟨hi, _⟩, hx, hm, k, hsp⟩ := h
  exact WP.mono (key_body a hi hx hm k hsp) fun _ ⟨hd, _, _⟩ => ⟨s, _, hd⟩

private theorem finish_pointer (p : KeyPublic) (s : State) (h : KeyCTDone p s) :
    WP isa (.block (finish.take 3)) s fun t => t.gpr .t0 = p.up ∧ t.gpr .s0 = p.control := by
  obtain ⟨original, r, h⟩ := h
  have a := CtlAccess.of_scr (h.input.control_scr (t := s) h.wr)
  have hu := h.usedPtr
  simp only [Bignum.word] at hu
  unfold finish
  simp only [List.take_succ_cons, List.take_zero]
  brun [ldf, h.s0, hu, a.ld 120 (by decide), a.ld 88 (by decide), a.ld 112 (by decide),
    a.al 120 (by decide) (by decide), a.al 88 (by decide) (by decide), a.al 112 (by decide) (by decide)]

private theorem finish_ct : RelCT isa (Two KeyCTDone) (.block finish) (fun _ _ => True) := by
  change RelCT isa (Two KeyCTDone) (.block (finish.take 3 ++ finish.drop 3)) _
  refine RelCT.block_append (RelCT.seq (two_post (two_taint [.s0] ?_ (by taint_decide)) finish_pointer) ?_)
  · intro p s t ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.s0.trans h₂.s0.symm
  · exact two_taint [.t0, .s0] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

theorem key_code_ct (a : Attempt) :
    RelCT isa (Two KeyStart) (code a.call) (fun _ _ => True) := by
  unfold code
  exact RelCT.seq (two_post (two_map Prod.fst (fun _ _ h => h.1) entry_ct) entry_ready)
    (RelCT.seq (two_post (search_ct a) (search_ready a))
      (two_map Prod.fst (fun _ _ h => h) finish_ct))

private theorem key_public_descriptor {s t : State} (h : keyPub s t) : keyOfState s = keyOfState t := by
  obtain ⟨hsp, hr, ha, hdom, hw, -⟩ := h
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨r0, -, r2, -, r4, r5, r6, r7⟩ := hr
  change [word s.mem (stackArg s 4) 0, word s.mem (stackArg s 4) 8, word s.mem (stackArg s 4) 16,
    word s.mem (stackArg s 4) 24] = [word t.mem (stackArg t 4) 0, word t.mem (stackArg t 4) 8,
      word t.mem (stackArg t 4) 16, word t.mem (stackArg t 4) 24] at hw
  have h0 : s.mem.readW (stackArg s 4) 64 = t.mem.readW (stackArg t 4) 64 := by
    simpa only [Bignum.word, off, BitVec.add_zero] using (List.cons.inj hw).1
  have h1 : s.mem.readW (stackArg s 4 + 8) 64 = t.mem.readW (stackArg t 4 + 8) 64 := by
    have := (List.cons.inj (List.cons.inj hw).2).1
    simp only [Bignum.word, off] at this
    exact this
  unfold keyOfState
  rw [keyRetries, keyRetries, h0, h1, hdom, hsp, r0, r2, r4, r5, keyLen, keyLen, r6, r7,
    ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)]

theorem key_constantTime (a : Attempt) :
    ConstantTime isa keyContract.pre keyContract.pub (code a.call) := by
  refine RelCT.constantTime ((key_code_ct a).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨(keyOfState s, (keyResult s).statuses), ⟨⟨hs, rfl⟩, rfl⟩,
    ⟨⟨ht, (key_public_descriptor hp).symm⟩, hp.2.2.2.2.2.symm⟩, hp.1⟩

end VG.Proof.Ffdh.RISCV64.KeyGeneration
