module

-- separate module: built alongside Correct
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Generation.Search.Correct
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.Generation.Search.Correct
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.CT
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.CT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ffdh.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.Syms

/-! # The parameter search's timing depends on its public data (RISC-V)

As the key search's (`Proof/Ffdh/RISCV64/KeyGeneration/CT.lean`): two runs
are related by `Two` (`Proof/Bignum/RISCV64/PreCT.lean`) at each cut, both
satisfying a predicate for the same public point (`SPoint`): the public data
(the tape included), the octets consumed and the attempts left. The blocks
between the branches are checked by the taint analysis from the registers a
predicate fixes (`s0`, the base of the controller's words, and the pointers
loaded from those words); the branches test what the point fixes: the
attempts, the candidate's status and the tape's length. The candidate leaks
only its public arguments and its tape (`RelCT.callEx`, from its constant
time); its frame and the frame saving `ra` leak nothing of their own
(`relCT_alloc`, `relCT_pushRa`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Generation

open VG VG.RISCV64 VG.RISCV64.Taint VG.Spec.Ffdh VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Spec.Rsa (bytesAt wordsAt)
open VG.Proof.Ffdh.Control (writeController)
open VG.Proof.Ffdh.RISCV64.KeyGeneration (CtlAccess tmpRegs two_ite two_map relCT_alloc relCT_pushRa al8)
open VG.Impl.Ffdh.RISCV64.Generation.Search

/-! ## Public positions in the search, and its exits -/

/-- Some loop state of the search with the public data `p`. -/
def SAny (p : SPub) (s : State) : Prop := ∃ original used k, SLive p original used k s

structure SPoint where
  inputs : SPub
  used : Nat
  k : Nat

/-- A loop state at a point, for a candidate using `S` bytes of stack. -/
def SCTL (S : Nat) (q : SPoint) (s : State) : Prop :=
  q.inputs.S = S ∧ ∃ original, SLive q.inputs original q.used q.k s

theorem SCTL.any {S : Nat} {q : SPoint} {s : State} (h : SCTL S q s) : SAny q.inputs s :=
  let ⟨_, original, h⟩ := h; ⟨original, _, _, h⟩

theorem any_pins : Pins SAny [.s0] := by
  intro p s t ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.s0.trans h₂.s0.symm

theorem ctl_pins (S : Nat) : Pins (SCTL S) [.s0] :=
  fun _ _ _ h₁ h₂ => any_pins _ _ _ h₁.any h₂.any

theorem no_pins {α : Type} {Φ : α → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ h => by cases h

/-- Before the zeroing's loop: its pointer and count. -/
def ZeroCT (p : SPub) (s : State) : Prop :=
  SAny p s ∧ s.gpr .t0 = p.op ∧ s.gpr .t1 = BitVec.ofNat 64 p.len

private theorem zero_header (p : SPub) (s : State) (h : SAny p s) :
    WP isa (.block [ldf .t0 5, ldf .t1 6, .li .t2 0]) s (ZeroCT p) := by
  obtain ⟨original, used, k, h⟩ := h
  have a := h.access
  have hv := h.header (j := 5) (v := p.op) (by simp [SPub.headers])
  have hv6 := h.header (j := 6) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers])
  simp only [Bignum.word, Nat.reduceMul] at hv hv6
  refine WP.mono_syms (KeyGeneration.WP.ctl (Q := fun t => (t.gpr .t0 = p.op ∧
    t.gpr .t1 = BitVec.ofNat 64 p.len) ∧ t.mem = s.mem) ?_ (by rfl))
    fun _ ⟨⟨hr, hm⟩, k, hsp⟩ hy => ⟨⟨original, used, _, h.keep k hsp hm hy⟩, hr⟩
  brun [ldf, h.s0, hv, hv6, a.ld 40 (by decide), a.ld 48 (by decide), a.al 40 (by decide) (by decide),
    a.al 48 (by decide) (by decide), fin64_exec_li_zero]

theorem zero_ct : RelCT isa (Two SAny) zeroOut (fun _ _ => True) := by
  unfold zeroOut
  refine RelCT.seq (two_post (two_taint [.s0] any_pins (by taint_decide)) zero_header) ?_
  exact two_taint [.t0, .t1] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm]) (by taint_decide)

private theorem terminal_ready (p : SPub) (s : State) (h : SAny p s) :
    WP isa (.block (terminal 3)) s (SAny p) := by
  obtain ⟨original, used, k, h⟩ := h
  exact WP.mono (terminal_live h (.inr rfl)) fun _ ⟨ht, _⟩ => ⟨original, used, 0, ht⟩

theorem exhausted_ct : RelCT isa (Two SAny) exhausted (fun _ _ => True) := by
  unfold exhausted
  exact RelCT.seq (two_post (two_taint [.s0] any_pins (by taint_decide)) terminal_ready) zero_ct

theorem accept_ct : RelCT isa (Two SAny) (.block accept) (fun _ _ => True) :=
  two_taint [.s0] any_pins (by taint_decide)

theorem reject_ct : RelCT isa (Two SAny) (.block reject) (fun _ _ => True) :=
  two_taint [.s0] any_pins (by taint_decide)

theorem request_ct : RelCT isa (Two SAny) (.block request) (fun _ _ => True) :=
  two_taint [.s0] any_pins (by taint_decide)

/-! ## The candidate

The candidate's timing may depend on its arguments and its tape. Two runs at
the same point agree on both: the tape is public. -/

/-- A loop state at which the controller runs a candidate. -/
def SReady (S : Nat) (q : SPoint) (s : State) : Prop := SCTL S q s ∧ q.k ≠ 0

def SAllocated (S : Nat) (q : SPoint) (u : State) : Prop := ∃ s, SReady S q s ∧ u = allocd 16 s

/-- The candidate's entry, before the call. -/
def SCallCT (S : Nat) (q : SPoint) (u : State) : Prop :=
  q.inputs.S = S ∧ ∃ original s, SLive q.inputs original q.used q.k s ∧
    SArgs q.inputs q.used u ∧
    u.mem = writeController (allocd 16 s).mem (callSp q.inputs) (callValues q.inputs) ∧
    Keep tmpRegs (allocd 16 s) u ∧ u.sp = (allocd 16 s).sp ∧ u.syms = s.syms

/-- After the candidate. -/
def SRan (S : Nat) (q : SPoint) (t : State) : Prop :=
  q.inputs.S = S ∧ q.k ≠ 0 ∧ ∃ original, SLive q.inputs original q.used q.k t ∧
    CandPost q.inputs q.used t

theorem allocated_pins (S : Nat) : Pins (SAllocated S) [.s0] := by
  rintro q _ _ ⟨a, ⟨⟨_, _, h₁⟩, _⟩, rfl⟩ ⟨b, ⟨⟨_, _, h₂⟩, _⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.s0.trans h₂.s0.symm

private theorem arguments_ready (S : Nat) (q : SPoint) (u : State) (h : SAllocated S q u) :
    WP isa (.block arguments) u (SCallCT S q) := by
  obtain ⟨s, ⟨⟨hS, original, h⟩, _⟩, rfl⟩ := h
  exact WP.mono_syms (search_arguments_ok h) fun _ ⟨⟨ha, hm⟩, k, hsp⟩ hy => ⟨hS, original, s, h, ha, hm, k, hsp, hy⟩

theorem cand_pub {p : SPub} {used : Nat} {t₁ t₂ : State} (hf : CallFacts p used)
    (he₁ : CandEntry p used t₁) (he₂ : CandEntry p used t₂)
    (hr₁ : bytesAt t₁.mem (p.rp + BitVec.ofNat 64 used) (p.randLen - used) = p.rand.drop used)
    (hr₂ : bytesAt t₂.mem (p.rp + BitVec.ofNat 64 used) (p.randLen - used) = p.rand.drop used) {S : Nat} :
    (candK S).pub t₁ t₂ := by
  have hrl : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
    toNat_ofNat_lt (by have := hf.randLen; omega)
  unfold candK Proof.Ffdh.sievedParameterCandidateContract
  rw [show tables = [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] from rfl]
  refine pub_consts.mpr ⟨?_, fun c hc => ?_⟩
  swap
  · rw [List.mem_singleton] at hc
    subst hc
    exact he₁.sy.trans he₂.sy.symm
  sig_pub [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs,
    stackArgs_one, List.append_eq]
  simp only [List.getD_cons_succ, List.getD_cons_zero, he₁.a0, he₁.a1, he₁.a2, he₁.a3, he₁.a4, he₁.a5,
    he₁.a6, he₁.a7, he₁.sp, he₁.arg, he₂.a0, he₂.a1, he₂.a2, he₂.a3, he₂.a4, he₂.a5, he₂.a6, he₂.a7,
    he₂.sp, he₂.arg, hrl, hr₁, hr₂, and_self]

private theorem call_ready {S : Nat} {q : SPoint} {u : State} (h : SCallCT S q u) :
    CallFacts q.inputs q.used ∧ CandEntry q.inputs q.used (callState q.inputs q.used u) ∧
      bytesAt (callState q.inputs q.used u).mem (q.inputs.rp + BitVec.ofNat 64 q.used)
        (q.inputs.randLen - q.used) = q.inputs.rand.drop q.used ∧
      Covers (callRd q.inputs q.used ++ callWr q.inputs) (u.rd ++ u.wr) ∧
      Covers (callWr q.inputs) u.wr := by
  obtain ⟨_, original, s, h, ha, hm, k, husp, hyu⟩ := h
  have hu : u.sp = callSp q.inputs := husp.trans (allocd_sp h)
  have hT : TabAt q.inputs.T u.mem := h.input.table_frame (frame_of_callChanges q.inputs.S original
    (candidate_frame (t := u) (d := 0) h (Nat.zero_le _) hm (fun _ _ => rfl))) h.table
  have hy : u.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = q.inputs.T := by
    rw [hyu, h.syms, ← h.input.2]; rfl
  exact ⟨h.callFacts, call_entry hu ha hm hy hT, by
    simp only [State.withRegions_mem, State.callEntry_mem]; exact call_rand h hm,
    call_covers_reads h k.2.1 k.2.2, call_covers_writes h k.2.2⟩

theorem cand_call_ct (c : Cand) : RelCT isa (Two (SCallCT c.S)) c.call (fun _ _ => True) := by
  refine RelCT.callEx c.correct c.ct fun u₁ u₂ ⟨q, h₁, h₂, _⟩ => ?_
  obtain ⟨hf, e₁, r₁, c₁, w₁⟩ := call_ready h₁
  obtain ⟨_, e₂, r₂, c₂, w₂⟩ := call_ready h₂
  have hS : q.inputs.S = c.S := h₁.1
  have hpos : 0 < q.inputs.S := by rw [hS]; exact c.pos
  refine ⟨_, _, _, _, ?_, ?_, cand_pub hf e₁ e₂ r₁ r₂, c₁, w₁, c₂, w₂⟩
  · rw [← hS]; exact cand_pre hf hpos e₁
  · rw [← hS]; exact cand_pre hf hpos e₂

theorem cand_run_ct (c : Cand) : RelCT isa (Two (SReady c.S)) (candidateRun c.call) (fun _ _ => True) := by
  unfold candidateRun
  apply relCT_alloc
  refine (RelCT.seq (two_post (two_taint [.s0] (allocated_pins c.S) (by taint_decide)) (arguments_ready c.S))
    (cand_call_ct c)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocd, hsp]⟩

theorem cand_run_ready (c : Cand) (q : SPoint) (s : State) (h : SReady c.S q s) :
    WP isa (candidateRun c.call) s (SRan c.S q) := by
  obtain ⟨⟨hS, original, h⟩, hk⟩ := h
  exact WP.mono (search_candidate_run c hS h) fun _ ⟨ht, hp⟩ => ⟨hS, hk, original, ht, hp⟩

/-! ## The classification

It branches on the candidate's status, and then on the tape's length, which
the point fixes. -/

/-- The candidate's status at a point. -/
abbrev SPoint.status (q : SPoint) : Nat := candidateStatus (q.inputs.cand q.used)

/-- After the status and the octets read: the pointer to `used`. -/
def SHead (S : Nat) (q : SPoint) (t : State) : Prop := SRan S q t ∧ t.gpr .t2 = q.inputs.up

theorem ran_pins (S : Nat) : Pins (SRan S) [.s0] := by
  intro q s t ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.s0.trans h₂.s0.symm

private theorem head_pointer (S : Nat) (q : SPoint) (s : State) (h : SRan S q s) :
    WP isa (.block ((head ++ test 1).take 3)) s (SHead S q) := by
  obtain ⟨hS, hk, original, h, hp⟩ := h
  have a := h.access
  have hv7 := h.header (j := 7) (v := q.inputs.up) (by simp [SPub.headers])
  simp only [Bignum.word, Nat.reduceMul] at hv7
  refine WP.mono_syms (WP.rdwr (WP.keep [.t0, .t2] (Q := fun t => t.gpr .t2 = q.inputs.up ∧ t.mem = s.mem) ?_
    (by rfl) rfl)) fun t ⟨⟨⟨h2, hm⟩, k⟩, _, _, hsp⟩ hy => ?_
  · unfold head test
    simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero]
    brun [ldf, h.s0, hv7, a.ld 56 (by decide), a.al 56 (by decide) (by decide)]
  refine ⟨⟨hS, hk, original, h.keep k hsp hm hy, ?_⟩, h2⟩
  unfold CandPost at hp ⊢
  rw [hm, k.gpr (by decide)]
  exact hp

private theorem head_ct (S : Nat) : RelCT isa (Two (SRan S)) (.block (head ++ test 1)) (fun _ _ => True) := by
  change RelCT isa (Two (SRan S)) (.block ((head ++ test 1).take 3 ++ (head ++ test 1).drop 3)) _
  refine RelCT.block_append (RelCT.seq (two_post (two_taint [.s0] (ran_pins S) (by taint_decide))
    (head_pointer S)) (two_taint [.t2] ?_ (by taint_decide)))
  intro q s t h₁ h₂ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.2.trans h₂.2.symm

/-- The status in `t0`, compared with `k` in `t1`. -/
def SGuard (S k : Nat) (q : SPoint) (t : State) : Prop :=
  SCTL S q t ∧ q.k ≠ 0 ∧ t.gpr .t0 = BitVec.ofNat 64 q.status ∧
    isa.eval (.zero .t1) t = some (decide (q.status = k)) ∧ CandPost q.inputs q.used t ∧
    t.gpr .t2 = BitVec.ofNat 64 (q.inputs.read q.used)

private theorem first_ready (S : Nat) (q : SPoint) (s : State) (h : SRan S q s) :
    WP isa (.block (head ++ test 1)) s (SGuard S 1 q) := by
  obtain ⟨hS, hk, original, h, hp⟩ := h
  exact WP.mono (search_head h hp) fun t ⟨ht, hpt, h0, h2, he⟩ => ⟨⟨hS, original, ht⟩, hk, h0, he, hpt, h2⟩

private theorem next_ready (S : Nat) (q : SPoint) (s : State)
    (h : SGuard S 1 q s ∧ isa.eval (.zero .t1) s = some false) :
    WP isa (.block (test 2)) s (SGuard S 2 q) := by
  obtain ⟨⟨⟨hS, o, hl⟩, hk, h0, _, hp, h2⟩, _⟩ := h
  refine WP.mono_syms (test_ok h0 (status_lt _) (.inr rfl)) fun t ⟨⟨he, hm⟩, kt, hsp⟩ hy => ?_
  refine ⟨⟨hS, o, hl.keep kt hsp hm hy⟩, hk, (kt.gpr (by decide)).trans h0, he, ?_, (kt.gpr (by decide)).trans h2⟩
  unfold CandPost at hp ⊢
  rw [hm, kt.gpr (by decide)]
  exact hp

private theorem leaf {S k : Nat} {b : Bool} {c : Prog isa} (hc : RelCT isa (Two SAny) c fun _ _ => True) :
    RelCT isa (Two fun q s => SGuard S k q s ∧ isa.eval (.zero .t1) s = some b) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q.inputs, h₁.1.1.any, h₂.1.1.any, hsp⟩) fun _ _ h => h

private theorem guard_eq (S k : Nat) (q : SPoint) (s₁ s₂ : State) (h₁ : SGuard S k q s₁)
    (h₂ : SGuard S k q s₂) : isa.eval (.zero .t1) s₁ = isa.eval (.zero .t1) s₂ :=
  h₁.2.2.2.1.trans h₂.2.2.2.1.symm

/-- Whether the tape is short of the entropy cap, at a point. -/
def SShort (S : Nat) (q : SPoint) (t : State) : Prop :=
  SCTL S q t ∧ isa.eval (.ltu .t0 .t1) t = some (decide (q.inputs.randLen - q.used < parameterEntropy q.inputs.bits))

private theorem short_ready (S : Nat) (q : SPoint) (s : State)
    (h : SGuard S 2 q s ∧ isa.eval (.zero .t1) s = some false) :
    WP isa (.block [ldf .t0 11, ldf .t1 2]) s (SShort S q) := by
  obtain ⟨⟨⟨hS, o, hl⟩, -⟩, -⟩ := h
  exact WP.mono (short_guard hl) fun _ ⟨⟨ht, _⟩, he⟩ => ⟨⟨hS, o, ht⟩, he⟩

private theorem leafS {S : Nat} {b : Bool} {c : Prog isa} (hc : RelCT isa (Two SAny) c fun _ _ => True) :
    RelCT isa (Two fun q s => SShort S q s ∧ isa.eval (.ltu .t0 .t1) s = some b) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q.inputs, h₁.1.1.any, h₂.1.1.any, hsp⟩) fun _ _ h => h

private theorem short_ct (S : Nat) :
    RelCT isa (Two fun q s => SGuard S 2 q s ∧ isa.eval (.zero .t1) s = some false) short fun _ _ => True := by
  unfold short
  refine RelCT.seq (two_post (two_taint [.s0] (fun q _ _ h₁ h₂ => ctl_pins S q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide)) (short_ready S)) ?_
  exact two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) (leafS request_ct) (leafS exhausted_ct)

theorem classify_ct (S : Nat) : RelCT isa (Two (SRan S)) classify (fun _ _ => True) := by
  unfold classify
  refine RelCT.seq (two_post (head_ct S) (first_ready S)) ?_
  refine two_ite (guard_eq S 1) (leaf accept_ct) ?_
  refine RelCT.seq (two_post (two_taint [] no_pins (by taint_decide)) (next_ready S)) ?_
  exact two_ite (guard_eq S 2) (leaf reject_ct) (short_ct S)

/-! ## The iteration -/

/-- Whether the search goes on after an iteration from `q`: it runs a
candidate, and the candidate is rejected. -/
def SContinues (q : SPoint) : Prop := q.k ≠ 0 ∧ q.status = 2

instance (q : SPoint) : Decidable (SContinues q) := inferInstanceAs (Decidable (q.k ≠ 0 ∧ q.status = 2))

/-- The point after a rejected candidate. -/
def nextPoint (q : SPoint) : SPoint := ⟨q.inputs, q.used + q.inputs.read q.used, q.k - 1⟩

/-- After the attempts' guard, the candidate and its classification. -/
def SBranchResult (S : Nat) (q : SPoint) (t : State) : Prop :=
  if SContinues q then SCTL S (nextPoint q) t ∧ word t.mem q.inputs.control 112 = 4
  else ∃ original r, SDone q.inputs original r t

theorem branch_s0 {S : Nat} {q : SPoint} {t : State} (h : SBranchResult S q t) :
    t.gpr .s0 = q.inputs.control := by
  by_cases hc : SContinues q
  · simp only [SBranchResult, hc, ite_true] at h
    obtain ⟨⟨_, _, hl⟩, _⟩ := h
    exact hl.s0
  · simp only [SBranchResult, hc, ite_false] at h
    obtain ⟨_, _, hd⟩ := h
    exact hd.s0

def AttemptsGuard (S : Nat) (q : SPoint) (s : State) : Prop :=
  SCTL S q s ∧ isa.eval (.zero .t0) s = some (decide (q.k = 0))

theorem attempts_ready (S : Nat) (q : SPoint) (s : State) (h : SCTL S q s) :
    WP isa (.block [ldf .t0 0]) s (AttemptsGuard S q) := by
  obtain ⟨hS, original, h⟩ := h
  exact WP.mono (attempts_guard h) fun _ ⟨ht, he⟩ => ⟨⟨hS, original, ht⟩, he⟩

theorem branch_ready (c : Cand) (q : SPoint) (s : State) (h : AttemptsGuard c.S q s) :
    WP isa (.ite (.zero .t0) exhausted (.seq (candidateRun c.call) classify)) s (SBranchResult c.S q) := by
  obtain ⟨⟨hS, original, hl⟩, he⟩ := h
  refine WP.ite (decide (q.k = 0)) he ?_ ?_
  · intro hz
    refine WP.mono (search_exhausted hl) fun t ht => ?_
    simp only [SBranchResult, show ¬SContinues q from fun hc => hc.1 (of_decide_eq_true hz), ite_false]
    exact ⟨original, _, ht⟩
  intro hnz
  have hk : q.k ≠ 0 := of_decide_eq_false hnz
  refine WP.seq (WP.mono (search_candidate_run c hS hl) fun t ⟨ht, hp⟩ => ?_)
  refine WP.mono (search_classify ht hk hp) fun r hq => ?_
  unfold SClassified at hq
  by_cases h2 : q.status = 2
  · have hc : SContinues q := ⟨hk, h2⟩
    simp only [SPoint.status] at h2
    simp only [h2, ite_true] at hq
    simp only [SBranchResult, hc, ite_true]
    exact ⟨⟨hS, original, hq.1⟩, hq.2⟩
  · have hc : ¬SContinues q := fun hc => h2 hc.2
    simp only [SPoint.status] at h2
    simp only [h2, ite_false] at hq
    simp only [SBranchResult, hc, ite_false]
    exact ⟨original, _, hq⟩

private theorem leafB {Φ : SPoint → State → Prop} {c : Prog isa}
    (hΦ : ∀ q s, Φ q s → SAny q.inputs s) (hc : RelCT isa (Two SAny) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q.inputs, hΦ q _ h₁, hΦ q _ h₂, hsp⟩) fun _ _ h => h

theorem branch_ct (c : Cand) :
    RelCT isa (Two (AttemptsGuard c.S)) (.ite (.zero .t0) exhausted (.seq (candidateRun c.call) classify))
      (fun _ _ => True) := by
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (leafB (fun _ _ h => h.1.1.any) exhausted_ct) ?_
  refine RelCT.seq (two_post ((cand_run_ct c).mono ?_ fun _ _ h => h) ?_) (classify_ct c.S)
  · rintro _ _ ⟨q, ⟨⟨h₁, he₁⟩, hf₁⟩, ⟨⟨h₂, _⟩, _⟩, hsp⟩
    have hk : q.k ≠ 0 := of_decide_eq_false (Option.some.inj (he₁.symm.trans hf₁))
    exact ⟨q, ⟨h₁, hk⟩, ⟨h₂, hk⟩, hsp⟩
  · rintro q s ⟨⟨h, he⟩, hf⟩
    exact cand_run_ready c q s ⟨h, of_decide_eq_false (Option.some.inj (he.symm.trans hf))⟩

theorem iteration_ct (c : Cand) : RelCT isa (Two (SCTL c.S)) (iteration c.call) (fun _ _ => True) := by
  unfold iteration
  refine RelCT.seq (two_post (two_taint [.s0] (ctl_pins c.S) (by taint_decide)) (attempts_ready c.S)) ?_
  exact RelCT.seq (two_post (branch_ct c) (branch_ready c))
    (two_taint [.s0] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact (branch_s0 h₁).trans (branch_s0 h₂).symm) (by taint_decide))

/-! ## The loop -/

def SCTStep (S : Nat) (q : SPoint) (s : State) : Prop :=
  if SContinues q then isa.eval (.zero .t0) s = some true ∧ SCTL S (nextPoint q) s
  else isa.eval (.zero .t0) s = some false

theorem ct_step (c : Cand) (q : SPoint) (s : State) (h : SCTL c.S q s) :
    WP isa (iteration c.call) s (SCTStep c.S q) := by
  unfold iteration
  refine WP.seq (WP.mono (attempts_ready c.S q s h) fun u hu => ?_)
  refine WP.seq (WP.mono (branch_ready c q u hu) fun t ht => ?_)
  by_cases hc : SContinues q
  · simp only [SBranchResult, hc, ite_true] at ht
    obtain ⟨⟨hS, original, hl⟩, hw⟩ := ht
    refine WP.mono (live_loop_guard hl hw) fun z ⟨hz, hzl⟩ => ?_
    simp only [SCTStep, hc, ite_true]
    exact ⟨hz, hS, original, hzl⟩
  · simp only [SBranchResult, hc, ite_false] at ht
    obtain ⟨_, _, hd⟩ := ht
    refine WP.mono (done_loop_guard hd) fun z ⟨hz, _⟩ => ?_
    simp only [SCTStep, hc, ite_false]
    exact hz

private def LoopPair (S : Nat) (n : Nat) (s t : State) : Prop :=
  ∃ q, n = q.k + 1 ∧ SCTL S q s ∧ SCTL S q t ∧ s.sp = t.sp

private theorem iteration_pair (c : Cand) (n : Nat) :
    RelCT isa (LoopPair c.S n) (iteration c.call) fun s t =>
      isa.eval (.zero .t0) s = isa.eval (.zero .t0) t ∧
      (isa.eval (.zero .t0) s = some false → True) ∧
      (isa.eval (.zero .t0) s = some true → ∃ m < n, LoopPair c.S m s t) := by
  have hw (q : SPoint) (s : State) (h : n = q.k + 1 ∧ SCTL c.S q s) :
      WP isa (iteration c.call) s fun t => n = q.k + 1 ∧ SCTStep c.S q t :=
    WP.mono (ct_step c q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((iteration_ct c).mono
    (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.2, h₂.2, hsp⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂, hsp⟩ => ⟨q, ⟨hn, h₁⟩, ⟨hn, h₂⟩, hsp⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, ⟨_, h₂⟩, hsp⟩
  by_cases hb : SContinues q
  · simp only [SCTStep, hb, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ?_⟩
    refine ⟨(nextPoint q).k + 1, ?_, nextPoint q, rfl, h₁.2, h₂.2, hsp⟩
    have := hb.1
    simp only [nextPoint]
    omega
  · simp only [SCTStep, hb, ite_false] at h₁ h₂
    exact ⟨h₁.trans h₂.symm, fun _ => trivial, fun ht => absurd (ht.symm.trans h₁) (by decide)⟩

theorem loop_ct (c : Cand) :
    RelCT isa (Two (SCTL c.S)) (.loop (iteration c.call) (.zero .t0)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht, hsp⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration c.call) (c := .zero .t0)
    (Q := fun _ _ => True) (LoopPair c.S) (iteration_pair c) (q.k + 1)
    _ _ _ _ _ _ ⟨q, rfl, hs, ht, hsp⟩ he₁ he₂

/-! ## Entry and return -/

/-- A run's entry, with its public data. -/
def SStart (S : Nat) (p : SPub) (s : State) : Prop := SInput p s ∧ p.S = S

private theorem entry_pointer (S : Nat) (p : SPub) (s : State) (h : SStart S p s) :
    WP isa (.block (entry.take 2)) s fun t => t.gpr .t2 = p.control ∧ t.gpr .t1 = p.sp := by
  have hi := h.1
  have hd : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = p.control :=
    (show _ = stackArg s 1 from rfl).trans (congrArg SPub.control hi.2)
  have ha1 := input_args hi 1 (by decide)
  have hsp : s.sp.toNat % 8 = 0 := by have := hi.1.2.2.1; omega
  simp only [Nat.reduceMul] at ha1
  unfold entry
  simp only [List.take_succ_cons, List.take_zero]
  brun [exec_addSp (show 0 < 2048 by decide), add_ofNat_zero, hd, ha1, al8 hsp (d := 8) (by decide),
    hi.sp_eq]

private theorem pins_E2 : Pins (fun (p : SPub) (t : State) =>
    t.gpr .t2 = p.control ∧ t.gpr .t1 = p.sp) [.t1, .t2] := by
  rintro p s t ⟨a2, a1⟩ ⟨b2, b1⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a1, b1]
  · rw [a2, b2]

private theorem entry_ct (S : Nat) : RelCT isa (Two (SStart S)) (.block entry) (fun _ _ => True) := by
  change RelCT isa (Two (SStart S)) (.block (entry.take 2 ++ entry.drop 2)) _
  exact RelCT.block_append (RelCT.seq (two_post (two_taint [] no_pins (by taint_decide)) (entry_pointer S))
    (two_taint _ pins_E2 (by taint_decide)))

/-- After the entry: the controller's words written. -/
def SEntered (S : Nat) (p : SPub) (t : State) : Prop :=
  ∃ s, SStart S p s ∧ t.gpr .s0 = p.control ∧
    t.mem = writeController s.mem p.control (entryValues s) ∧ Keep entryRegs s t ∧ t.sp = s.sp ∧
    t.syms = s.syms

private theorem entry_ready (S : Nat) (p : SPub) (s : State) (h : SStart S p s) :
    WP isa (.block entry) s (SEntered S p) :=
  WP.mono_syms (entry_ok h.1) fun _ ⟨⟨hx, hm⟩, k, hsp⟩ hy => ⟨s, h, hx, hm, k, hsp, hy⟩

private def initialPoint (p : SPub) : SPoint := ⟨p, 0, p.attempts⟩

private theorem entered_ctl {S : Nat} {p : SPub} {t : State} (h : SEntered S p t) :
    SCTL S (initialPoint p) (framed .ra t) := by
  obtain ⟨s, ⟨hi, hS⟩, hx, hm, k, hsp, hy⟩ := h
  exact ⟨hS, s, search_start hi hx hm k hsp hy⟩

def SCTDone (p : SPub) (s : State) : Prop := ∃ original r, SDone p original r s

private theorem search_ct (c : Cand) : RelCT isa (Two (SEntered c.S)) (search c.call) (fun _ _ => True) := by
  unfold search
  refine (relCT_pushRa (fun _ _ ⟨_, _, _, hsp⟩ => hsp) ?_ ?_).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  · rintro x y ⟨q, h₁, h₂, _⟩
    obtain ⟨hS, original, hl⟩ := entered_ctl h₁
    obtain ⟨-, original', hl'⟩ := entered_ctl h₂
    obtain ⟨t, s', e, -⟩ := search_loop c hS (n := q.attempts + 1)
      (expected := q.tail 0 q.attempts) ⟨0, _, rfl, hl, rfl⟩
    obtain ⟨t', s'', e', -⟩ := search_loop c hS (n := q.attempts + 1)
      (expected := q.tail 0 q.attempts) ⟨0, _, rfl, hl', rfl⟩
    exact ⟨⟨t, s', e⟩, ⟨t', s'', e'⟩⟩
  · refine (loop_ct c).mono ?_ fun _ _ h => h
    rintro _ _ ⟨x, y, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
    exact ⟨initialPoint q, entered_ctl h₁, entered_ctl h₂, by simp only [framed, hsp]⟩

private theorem search_ready (c : Cand) (q : SPub) (t : State) (h : SEntered c.S q t) :
    WP isa (search c.call) t (SCTDone q) := by
  obtain ⟨s, ⟨hi, hS⟩, hx, hm, k, hsp, hy⟩ := h
  exact WP.mono (search_body c hS hi hx hm k hsp hy) fun _ ⟨hd, _, _⟩ => ⟨s, _, hd⟩

private theorem finish_pointer (p : SPub) (s : State) (h : SCTDone p s) :
    WP isa (.block (finish.take 3)) s fun t => t.gpr .t0 = p.up ∧ t.gpr .s0 = p.control := by
  obtain ⟨original, r, h⟩ := h
  have a := CtlAccess.of_scr (h.input.control_scr (t := s) h.wr)
  have hu := h.usedPtr
  simp only [Bignum.word] at hu
  unfold finish
  simp only [List.take_succ_cons, List.take_zero]
  brun [ldf, h.s0, hu, a.ld 56 (by decide), a.ld 96 (by decide), a.ld 112 (by decide),
    a.al 56 (by decide) (by decide), a.al 96 (by decide) (by decide), a.al 112 (by decide) (by decide)]

private theorem finish_ct : RelCT isa (Two SCTDone) (.block finish) (fun _ _ => True) := by
  change RelCT isa (Two SCTDone) (.block (finish.take 3 ++ finish.drop 3)) _
  refine RelCT.block_append (RelCT.seq (two_post (two_taint [.s0] ?_ (by taint_decide)) finish_pointer) ?_)
  · intro p s t ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.s0.trans h₂.s0.symm
  · exact two_taint [.t0, .s0] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

theorem code_ct (c : Cand) : RelCT isa (Two (SStart c.S)) (code c.call) (fun _ _ => True) := by
  unfold code
  exact RelCT.seq (two_post (entry_ct c.S) (entry_ready c.S))
    (RelCT.seq (two_post (search_ct c) (search_ready c)) (two_map id (fun _ _ h => h) finish_ct))

theorem public_data {S : Nat} {s t : State} (h : searchPub s t) : sOfState S s = sOfState S t := by
  obtain ⟨hsp, hr, hw, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, hsy⟩ := h
  change [word s.mem (stackArg s 1) 0, word s.mem (stackArg s 1) 8, word s.mem (stackArg s 1) 16,
    word s.mem (stackArg s 1) 24] = [word t.mem (stackArg t 1) 0, word t.mem (stackArg t 1) 8,
      word t.mem (stackArg t 1) 16, word t.mem (stackArg t 1) 24] at hw
  have h0 : s.mem.readW (stackArg s 1) 64 = t.mem.readW (stackArg t 1) 64 := by
    simpa only [Bignum.word, off, BitVec.add_zero] using (List.cons.inj hw).1
  have hrand : genRand s = genRand t := by
    have hl : (genRand s).length = (genRand t).length := by
      simp only [genRand, Spec.Rsa.bytesAt, List.length_map, List.length_range, r6]
    exact (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hr
  unfold sOfState
  rw [genAttempts, genAttempts, h0, hrand, hsp, r0, r2, r5, r7, genLen, genLen, r1, genBits, genBits, r3,
    genGen, genGen, r4, r6, a0, a1, hsy]

theorem search_constantTime (c : Cand) :
    ConstantTime isa (searchContract c.S).pre (searchContract c.S).pub (code c.call) := by
  refine RelCT.constantTime ((code_ct c).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨sOfState c.S s, ⟨⟨hs, rfl⟩, rfl⟩, ⟨⟨ht, (public_data hp).symm⟩, rfl⟩, hp.1⟩

end VG.Proof.Ffdh.RISCV64.Generation
