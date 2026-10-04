import VerifiedGarbage.Proof.Framework.Taint

/-!
# Speculative constant time (Spectre v1), prototype

**Prototype, untrusted.** `SExec`, `SpecConstantTime` and `Spectre` are
definitions a reviewer has to trust (they would move to `TCB/Code.lean`);
the rest is checked.

The speculative semantics follows the directive-based definition of
Shivakumar et al., "Typing High-Speed Cryptography against Spectre v1"
(S&P 2023), §III (itself following Cauligi et al., PLDI 2020, with an
unbounded speculation window and no rollback):

* At every conditional (`ite`, and each evaluation of a `loop` condition)
  the attacker's next directive (`D`, a list of `Bool`) chooses the
  direction taken, whatever the condition evaluates to: `force b`. A
  directive that differs from the condition is a misprediction; nested
  mispredictions are allowed and nothing is ever rolled back, so the
  transient window is unbounded (a superset of any ROB-bounded window, see
  `Spectre.lean`'s report). The value of the condition (`M.eval`, `none` if
  it reads an undefined flag) leaks, as Jasmin's `branch b` observation.
* Execution stops after `n` instructions (the fuel), at any point the
  attacker chooses: so every prefix of a non-terminating or faulting
  transient execution is observed, as Jasmin's `n`-step executions.
* Instructions run with the speculative semantics `S.sexec`, where memory
  accesses outside the permitted regions do not fault (on x86-64: loads read
  any address, `X86_64/Spectre.lean`), and leak `S.saddrs`.
* A return goes back to its call site (`S.sret`), as the return stack
  buffer predicts, even if a transient store has overwritten the return
  address (which faults sequentially, `ISA.ret`). Calls and frames keep their
  sequential semantics: they only check the stack pointer and the regions,
  which no transient instruction changes (`ISA.writesSp`, `Artifact.spSafe`).

`SpecConstantTime`: for every directive list and fuel, two runs from states
that agree on public data leak the same trace.

The theorem: `Taint.check` is path-insensitive (it analyses both branches
of every `ite` and every loop body from an invariant, never refining
anything by a condition), so a successful check implies speculative
constant time, provided each instruction's transfer function is also
sound for the speculative semantics (`SpecSound`).
-/

namespace VG

/-- An observation of the speculative attacker. -/
inductive SLeak where
  | addr (a : Addr)
  /-- The value of a branch condition (`none`: it reads an undefined flag). -/
  | cond (v : Option Bool)
  deriving DecidableEq

/-- The speculative semantics of straight-line instructions: what an
instruction does, and the addresses it accesses, when executed transiently. -/
structure Spectre (M : ISA) where
  sexec : M.Instr → M.State → Option M.State
  saddrs : M.Instr → M.State → List Addr
  /-- The return instruction of a called function, executed transiently. -/
  sret : M.State → M.State → Option M.State

/-- How a speculative run ends: stopped (fuel or directives exhausted), or
done with the remaining directives and fuel. -/
inductive SOut (M : ISA) where
  | halt
  | done (s : M.State) (D : List Bool) (n : Nat)

variable {M : ISA} (S : Spectre M)

/-- Speculative run of a straight-line block with fuel `n`: `none` if it stopped. -/
inductive SBlock : List M.Instr → M.State → Nat → List SLeak → Option (M.State × Nat) → Prop
  | nil {s n} : SBlock [] s n [] (some (s, n))
  | stop {i is s} : SBlock (i :: is) s 0 [] none
  | cons {i is s s₁ n t r} : S.sexec i s = some s₁ → SBlock is s₁ n t r →
      SBlock (i :: is) s (n + 1) ((S.saddrs i s).map .addr ++ t) r

/-- Speculative big-step semantics under directives `D` and fuel `n`. -/
inductive SExec : Prog M → M.State → List Bool → Nat → List SLeak → SOut M → Prop
  | blockDone {is s s' D n n' t} : SBlock S is s n t (some (s', n')) →
      SExec (.block is) s D n t (.done s' D n')
  | blockHalt {is s D n t} : SBlock S is s n t none → SExec (.block is) s D n t .halt
  | seq {c₁ c₂ s s₁ D D₁ n n₁ t₁ t₂ o} : SExec c₁ s D n t₁ (.done s₁ D₁ n₁) →
      SExec c₂ s₁ D₁ n₁ t₂ o → SExec (.seq c₁ c₂) s D n (t₁ ++ t₂) o
  | seqHalt {c₁ c₂ s D n t} : SExec c₁ s D n t .halt → SExec (.seq c₁ c₂) s D n t .halt
  | iteEnd {c th el s n} : SExec (.ite c th el) s [] n [] .halt
  | iteT {c th el s D n t o} : SExec th s D n t o →
      SExec (.ite c th el) s (true :: D) n (.cond (M.eval c s) :: t) o
  | iteF {c th el s D n t o} : SExec el s D n t o →
      SExec (.ite c th el) s (false :: D) n (.cond (M.eval c s) :: t) o
  | loopHalt {body c s D n t} : SExec body s D n t .halt → SExec (.loop body c) s D n t .halt
  | loopEnd {body c s s' D n n' t} : SExec body s D n t (.done s' [] n') →
      SExec (.loop body c) s D n t .halt
  | loopExit {body c s s' D D' n n' t} : SExec body s D n t (.done s' (false :: D') n') →
      SExec (.loop body c) s D n (t ++ [.cond (M.eval c s')]) (.done s' D' n')
  | loopNext {body c s s' D D' n n' t t' o} : SExec body s D n t (.done s' (true :: D') n') →
      SExec (.loop body c) s' D' n' t' o →
      SExec (.loop body c) s D n (t ++ .cond (M.eval c s') :: t') o
  | callHalt {name body s s₁ D n t} : M.call s = some s₁ → SExec body s₁ D n t .halt →
      SExec (.call name body) s D n ((M.callAddrs s).map .addr ++ t) .halt
  | call {name body s s₁ s₂ s' D D' n n' t} : M.call s = some s₁ →
      SExec body s₁ D n t (.done s₂ D' n') → S.sret s₁ s₂ = some s' →
      SExec (.call name body) s D n
        ((M.callAddrs s).map .addr ++ t ++ (M.retAddrs s₂).map .addr) (.done s' D' n')
  | frameHalt {i j body s s₁ D n t} : M.push i s = some s₁ → SExec body s₁ D n t .halt →
      SExec (.frame i body j) s D n ((M.addrs i s).map .addr ++ t) .halt
  | frame {i j body s s₁ s₂ s' D D' n n' t} : M.push i s = some s₁ →
      SExec body s₁ D n t (.done s₂ D' n') → M.pop j s₁ s₂ = some s' →
      SExec (.frame i body j) s D n
        ((M.addrs i s).map .addr ++ t ++ (M.addrs j s₂).map .addr) (.done s' D' n')

/-- Speculative constant time: under any directives and fuel, two runs from
states agreeing on public data leak the same trace. -/
def SpecConstantTime (Pre : M.State → Prop) (Pub : M.State → M.State → Prop) (c : Prog M) : Prop :=
  ∀ s₁ s₂ D n t₁ t₂ o₁ o₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ →
    SExec S c s₁ D n t₁ o₁ → SExec S c s₂ D n t₂ o₂ → t₁ = t₂

namespace Taint

variable {S} {A : Taint M}

/-- The transfer functions of `A` are sound for the speculative semantics. -/
structure SpecSound (A : Taint M) (S : Spectre M) : Prop where
  step : ∀ {τ τ' i s₁ s₂ s₁' s₂'}, A.Agree τ s₁ s₂ → A.step τ i = some τ' →
    S.sexec i s₁ = some s₁' → S.sexec i s₂ = some s₂' →
    S.saddrs i s₁ = S.saddrs i s₂ ∧ A.Agree τ' s₁' s₂'
  ret : ∀ {τ τ' a₁ a₂ b₁ b₂ c₁ c₂}, A.Agree τ b₁ b₂ → A.ret τ = some τ' →
    S.sret a₁ b₁ = some c₁ → S.sret a₂ b₂ = some c₂ → M.retAddrs b₁ = M.retAddrs b₂ ∧ A.Agree τ' c₁ c₂

/-- How two runs end, related by the taint `τ`. -/
def BRel (A : Taint M) (τ : A.T) : Option (M.State × Nat) → Option (M.State × Nat) → Prop
  | none, none => True
  | some (a, k), some (b, l) => k = l ∧ A.Agree τ a b
  | _, _ => False

def ORel (A : Taint M) (τ : A.T) : SOut M → SOut M → Prop
  | .halt, .halt => True
  | .done a D k, .done b E l => D = E ∧ k = l ∧ A.Agree τ a b
  | _, _ => False

theorem sblock_sound (hs : SpecSound A S) {is : List M.Instr} {τ τ' : A.T} {s₁ s₂ : M.State}
    {n : Nat} {t₁ t₂ : List SLeak} {r₁ r₂ : Option (M.State × Nat)}
    (h : A.checkBlock τ is = some τ') (ha : A.Agree τ s₁ s₂)
    (e₁ : SBlock S is s₁ n t₁ r₁) (e₂ : SBlock S is s₂ n t₂ r₂) :
    t₁ = t₂ ∧ BRel A τ' r₁ r₂ := by
  induction e₁ generalizing τ s₂ t₂ r₂ with
  | nil =>
    cases e₂
    simp only [checkBlock, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl, ha⟩
  | stop => cases e₂; exact ⟨rfl, trivial⟩
  | cons x₁ _ ih =>
    cases e₂ with
    | cons x₂ b =>
      simp only [checkBlock, Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, hs₁, hr⟩ := h
      obtain ⟨hadd, ha₁⟩ := hs.step ha hs₁ x₁ x₂
      obtain ⟨ht, hr'⟩ := ih hr ha₁ b
      exact ⟨by rw [hadd, ht], hr'⟩

theorem sblock_append {xs ys : List M.Instr} {s : M.State} {n : Nat} {t : List SLeak}
    {r : Option (M.State × Nat)} (e : SBlock S (xs ++ ys) s n t r) :
    (∃ s₁ n₁ t₁ t₂, SBlock S xs s n t₁ (some (s₁, n₁)) ∧ SBlock S ys s₁ n₁ t₂ r ∧ t = t₁ ++ t₂) ∨
      (r = none ∧ SBlock S xs s n t none) := by
  induction xs generalizing s n t with
  | nil => exact .inl ⟨s, n, [], t, .nil, e, rfl⟩
  | cons i xs ih =>
    cases e with
    | stop => exact .inr ⟨rfl, .stop⟩
    | cons x b =>
      rcases ih b with ⟨s₁, n₁, t₁, t₂, b₁, b₂, rfl⟩ | ⟨rfl, b₁⟩
      · exact .inl ⟨s₁, n₁, _, t₂, .cons x b₁, b₂, by rw [List.append_assoc]⟩
      · exact .inr ⟨rfl, .cons x b₁⟩

theorem schunks_sound (hs : SpecSound A S) {ms : List A.T} {is : List M.Instr} {τ τ' : A.T}
    {s₁ s₂ : M.State} {n : Nat} {t₁ t₂ : List SLeak} {r₁ r₂ : Option (M.State × Nat)}
    (h : A.checkChunks τ is ms = some τ') (ha : A.Agree τ s₁ s₂)
    (e₁ : SBlock S is s₁ n t₁ r₁) (e₂ : SBlock S is s₂ n t₂ r₂) :
    t₁ = t₂ ∧ BRel A τ' r₁ r₂ := by
  induction ms generalizing τ is s₁ s₂ n t₁ t₂ with
  | nil => exact sblock_sound hs h ha e₁ e₂
  | cons m ms ih =>
    simp only [checkChunks, Option.bind_eq_some_iff] at h
    obtain ⟨τ₁, h₁, h₂⟩ := h
    split at h₂ <;> [rename_i hle; cases h₂]
    rw [← List.take_append_drop chunk is] at e₁ e₂
    rcases sblock_append e₁ with ⟨_, _, _, _, a₁, b₁, rfl⟩ | ⟨rfl, a₁⟩ <;>
    rcases sblock_append e₂ with ⟨_, _, _, _, a₂, b₂, rfl⟩ | ⟨rfl, a₂⟩
    · obtain ⟨rfl, rfl, hq⟩ := sblock_sound hs h₁ ha a₁ a₂
      obtain ⟨rfl, hr⟩ := ih h₂ (A.le_sound hle hq) b₁ b₂
      exact ⟨rfl, hr⟩
    · exact (sblock_sound hs h₁ ha a₁ a₂).2.elim
    · exact (sblock_sound hs h₁ ha a₁ a₂).2.elim
    · exact ⟨(sblock_sound hs h₁ ha a₁ a₂).1, trivial⟩

theorem ORel.mono {τ σ : A.T} {o₁ o₂ : SOut M} (hm : ∀ a b, A.Agree τ a b → A.Agree σ a b)
    (h : ORel A τ o₁ o₂) : ORel A σ o₁ o₂ := by
  cases o₁ <;> cases o₂ <;> simp only [ORel] at h ⊢
  exact ⟨h.1, h.2.1, hm _ _ h.2.2⟩

theorem specCheck_sound (hs : SpecSound A S) {c : Prog M} {τ τ' : A.T} {hc : Hint A.T}
    {s₁ s₂ : M.State} {D : List Bool} {n : Nat} {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M}
    (h : A.check τ c hc = some τ') (ha : A.Agree τ s₁ s₂)
    (e₁ : SExec S c s₁ D n t₁ o₁) (e₂ : SExec S c s₂ D n t₂ o₂) :
    t₁ = t₂ ∧ ORel A τ' o₁ o₂ := by
  induction e₁ generalizing τ τ' hc s₂ t₂ o₂ with
  | blockDone b₁ =>
    cases hc with
    | block ms =>
      have h : A.checkChunks τ _ ms = some τ' := h
      cases e₂ with
      | blockDone b₂ =>
        obtain ⟨rfl, rfl, hq⟩ := schunks_sound hs h ha b₁ b₂; exact ⟨rfl, rfl, rfl, hq⟩
      | blockHalt b₂ => exact (schunks_sound hs h ha b₁ b₂).2.elim
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | blockHalt b₁ =>
    cases hc with
    | block ms =>
      have h : A.checkChunks τ _ ms = some τ' := h
      cases e₂ with
      | blockDone b₂ => exact (schunks_sound hs h ha b₁ b₂).2.elim
      | blockHalt b₂ => exact ⟨(schunks_sound hs h ha b₁ b₂).1, trivial⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @seq c₁ c₂ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
    cases hc with
    | seq mid g₁ g₂ =>
      have h : ((A.check τ c₁ g₁).bind fun τ' => if A.le mid τ' then A.check mid c₂ g₂ else none) =
        some τ' := h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, h₂⟩ := h
      split at h₂ <;> [rename_i hle; cases h₂]
      cases e₂ with
      | seq a b =>
        obtain ⟨rfl, rfl, rfl, hq⟩ := ih₁ h₁ ha a
        obtain ⟨rfl, hr⟩ := ih₂ h₂ (A.le_sound hle hq) b
        exact ⟨rfl, hr⟩
      | seqHalt a => exact (ih₁ h₁ ha a).2.elim
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @seqHalt c₁ c₂ _ _ _ _ _ ih =>
    cases hc with
    | seq mid g₁ g₂ =>
      have h : ((A.check τ c₁ g₁).bind fun τ' => if A.le mid τ' then A.check mid c₂ g₂ else none) =
        some τ' := h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, -⟩ := h
      cases e₂ with
      | seq a _ => exact (ih h₁ ha a).2.elim
      | seqHalt a => exact ⟨(ih h₁ ha a).1, trivial⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | iteEnd => cases e₂; exact ⟨rfl, trivial⟩
  | @iteT cnd t e _ _ _ _ _ _ ih =>
    cases hc with
    | ite g₁ g₂ =>
      have h : (if A.condPub τ cnd then
          (A.check τ t g₁).bind fun τ₁ => (A.check τ e g₂).map fun τ₂ => A.meet τ₁ τ₂
        else none) = some τ' := h
      split at h <;> [rename_i hp; cases h]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, _, rfl⟩ := h
      cases e₂ with
      | iteT b =>
        obtain ⟨rfl, hq⟩ := ih h₁ ha b
        refine ⟨by rw [A.cond_sound ha hp], ?_⟩
        exact ORel.mono (fun _ _ => A.meet_left) hq
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @iteF cnd t e _ _ _ _ _ _ ih =>
    cases hc with
    | ite g₁ g₂ =>
      have h : (if A.condPub τ cnd then
          (A.check τ t g₁).bind fun τ₁ => (A.check τ e g₂).map fun τ₂ => A.meet τ₁ τ₂
        else none) = some τ' := h
      split at h <;> [rename_i hp; cases h]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨τ₁, _, τ₂, h₂, rfl⟩ := h
      cases e₂ with
      | iteF b =>
        obtain ⟨rfl, hq⟩ := ih h₂ ha b
        refine ⟨by rw [A.cond_sound ha hp], ?_⟩
        exact ORel.mono (fun _ _ => A.meet_right) hq
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @loopHalt body c _ _ _ _ _ ih =>
    cases hc with
    | loop σ hb =>
      have h : (if A.le σ τ then
          (A.check σ body hb).bind fun σ' => if A.le σ σ' && A.condPub σ' c then some σ' else none
        else none) = some τ' := h
      split at h <;> [rename_i hστ; cases h]
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨σ', hb', h'⟩ := h
      split at h' <;> [rename_i hl; cases h']
      cases h'
      simp only [Bool.and_eq_true] at hl
      have hσ := A.le_sound hστ ha
      cases e₂ with
      | loopHalt a => exact ⟨(ih hb' hσ a).1, trivial⟩
      | loopEnd a | loopExit a | loopNext a _ => exact (ih hb' hσ a).2.elim
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @loopEnd body c _ _ _ _ _ _ _ ih =>
    cases hc with
    | loop σ hb =>
      have h : (if A.le σ τ then
          (A.check σ body hb).bind fun σ' => if A.le σ σ' && A.condPub σ' c then some σ' else none
        else none) = some τ' := h
      split at h <;> [rename_i hστ; cases h]
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨σ', hb', h'⟩ := h
      split at h' <;> [rename_i hl; cases h']
      cases h'
      simp only [Bool.and_eq_true] at hl
      have hσ := A.le_sound hστ ha
      cases e₂ with
      | loopHalt a => exact (ih hb' hσ a).2.elim
      | loopEnd a => exact ⟨(ih hb' hσ a).1, trivial⟩
      | loopExit a | loopNext a _ => obtain ⟨h, -⟩ := (ih hb' hσ a).2; cases h
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @loopExit body c _ _ _ _ _ _ _ _ ih =>
    cases hc with
    | loop σ hb =>
      have h : (if A.le σ τ then
          (A.check σ body hb).bind fun σ' => if A.le σ σ' && A.condPub σ' c then some σ' else none
        else none) = some τ' := h
      split at h <;> [rename_i hστ; cases h]
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨σ', hb', h'⟩ := h
      split at h' <;> [rename_i hl; cases h']
      cases h'
      simp only [Bool.and_eq_true] at hl
      have hσ := A.le_sound hστ ha
      cases e₂ with
      | loopHalt a => exact (ih hb' hσ a).2.elim
      | loopEnd a | loopNext a _ => obtain ⟨h, -⟩ := (ih hb' hσ a).2; cases h
      | loopExit a =>
        obtain ⟨rfl, h, rfl, hq⟩ := ih hb' hσ a
        cases h
        exact ⟨by rw [A.cond_sound hq hl.2], rfl, rfl, hq⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @loopNext body c _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
    cases hc with
    | loop σ hb =>
      have h : (if A.le σ τ then
          (A.check σ body hb).bind fun σ' => if A.le σ σ' && A.condPub σ' c then some σ' else none
        else none) = some τ' := h
      split at h <;> [rename_i hστ; cases h]
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨σ', hb', h'⟩ := h
      split at h' <;> [rename_i hl; cases h']
      cases h'
      simp only [Bool.and_eq_true] at hl
      have hσ := A.le_sound hστ ha
      cases e₂ with
      | loopHalt a => exact (ih₁ hb' hσ a).2.elim
      | loopEnd a | loopExit a => obtain ⟨h, -⟩ := (ih₁ hb' hσ a).2; cases h
      | loopNext a b =>
        obtain ⟨rfl, h, rfl, hq⟩ := ih₁ hb' hσ a
        cases h
        have hloop : A.check τ' (.loop body c) (.loop σ hb) = some τ' := by
          show (if A.le σ τ' then
            (A.check σ body hb).bind fun σ' => if A.le σ σ' && A.condPub σ' c then some σ' else none
            else none) = some τ'
          simp only [hl.1, hl.2, hb', Option.bind_some, Bool.and_self, ite_true]
        obtain ⟨rfl, hr⟩ := ih₂ hloop hq b
        exact ⟨by rw [A.cond_sound hq hl.2], hr⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @callHalt _ body _ _ _ _ _ hc₁ _ ih =>
    cases hc with
    | call hb =>
      have h : ((A.call τ).bind fun τ₁ => (A.check τ₁ body hb).bind A.ret) = some τ' := h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, -⟩ := h
      cases e₂ with
      | callHalt hc₂ b =>
        obtain ⟨ha₁, ha₁'⟩ := A.call_sound ha h₁ hc₁ hc₂
        exact ⟨by rw [ha₁, (ih h₂ ha₁' b).1], trivial⟩
      | call hc₂ b _ =>
        exact (ih h₂ (A.call_sound ha h₁ hc₁ hc₂).2 b).2.elim
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @call _ body _ _ _ _ _ _ _ _ _ hc₁ _ hr ih =>
    cases hc with
    | call hb =>
      have h : ((A.call τ).bind fun τ₁ => (A.check τ₁ body hb).bind A.ret) = some τ' := h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      cases e₂ with
      | callHalt hc₂ b =>
        exact (ih h₂ (A.call_sound ha h₁ hc₁ hc₂).2 b).2.elim
      | call hc₂ b hr₂ =>
        obtain ⟨ha₁, ha₁'⟩ := A.call_sound ha h₁ hc₁ hc₂
        obtain ⟨rfl, rfl, rfl, ha₂⟩ := ih h₂ ha₁' b
        obtain ⟨ha₃, ha₃'⟩ := hs.ret ha₂ h₃ hr hr₂
        exact ⟨by rw [ha₁, ha₃], rfl, rfl, ha₃'⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @frameHalt i j body _ _ _ _ _ hp₁ _ ih =>
    cases hc with
    | frame hb =>
      have h : ((A.push τ i).bind fun τ₁ => (A.check τ₁ body hb).bind fun τ₂ => A.pop τ₂ j) =
        some τ' := h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, -⟩ := h
      cases e₂ with
      | frameHalt hp₂ b =>
        obtain ⟨ha₁, ha₁'⟩ := A.push_sound ha h₁ hp₁ hp₂
        exact ⟨by rw [ha₁, (ih h₂ ha₁' b).1], trivial⟩
      | frame hp₂ b _ =>
        exact (ih h₂ (A.push_sound ha h₁ hp₁ hp₂).2 b).2.elim
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @frame i j body _ _ _ _ _ _ _ _ _ hp₁ _ hq ih =>
    cases hc with
    | frame hb =>
      have h : ((A.push τ i).bind fun τ₁ => (A.check τ₁ body hb).bind fun τ₂ => A.pop τ₂ j) =
        some τ' := h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      cases e₂ with
      | frameHalt hp₂ b =>
        exact (ih h₂ (A.push_sound ha h₁ hp₁ hp₂).2 b).2.elim
      | frame hp₂ b hq₂ =>
        obtain ⟨ha₁, ha₁'⟩ := A.push_sound ha h₁ hp₁ hp₂
        obtain ⟨rfl, rfl, rfl, ha₂⟩ := ih h₂ ha₁' b
        obtain ⟨ha₃, ha₃'⟩ := A.pop_sound ha₂ h₃ hq hq₂
        exact ⟨by rw [ha₁, ha₃], rfl, rfl, ha₃'⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'

/-- A successful (sequential) taint check proves speculative constant time,
if the transfer function is sound for the speculative semantics. -/
theorem specConstantTime (hs : SpecSound A S) {Pre : M.State → Prop}
    {Pub : M.State → M.State → Prop} {c : Prog M}
    (τ : A.T) (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → A.Agree τ s₁ s₂) {hc : Hint A.T}
    (h : (A.check τ c hc).isSome = true) : SpecConstantTime S Pre Pub c := by
  intro s₁ s₂ D n t₁ t₂ o₁ o₂ h₁ h₂ hp e₁ e₂
  obtain ⟨τ', hc⟩ := Option.isSome_iff_exists.mp h
  exact (specCheck_sound hs hc (hpub _ _ h₁ h₂ hp) e₁ e₂).1

end Taint

end VG
