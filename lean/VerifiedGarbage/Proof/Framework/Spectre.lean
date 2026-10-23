import VerifiedGarbage.Proof.Framework.Taint

/-!
# Speculative constant time (Spectre v1), prototype

**Prototype, untrusted.** `Spectre`, `SBlock`, `SExec` and
`SpecConstantTime` are definitions a reviewer has to trust (they would move
to `TCB/Code.lean`); the rest is checked.

The speculative semantics follows the directive-based definition of
Shivakumar et al., "Typing High-Speed Cryptography against Spectre v1"
(S&P 2023), as restated in Baumann et al., "FSLH" (arXiv 2502.03203,
Definitions 2 and 3): a misspeculation flag, attacker directives, every
prefix of a run observed, and no rollback, so an unbounded speculation
window.

* At every conditional (`ite`, and each evaluation of a `loop` condition)
  the attacker's next directive (`D`, a list of `Bool`) chooses the
  direction taken, whatever the condition evaluates to: `force b`. A
  direction other than the condition's value sets the misspeculation flag
  `ms` (as does a condition on an undefined flag, `none`), which stays set:
  nested mispredictions are allowed and nothing is rolled back. The value of
  the condition leaks, as the observation `branch b`; it leaks too when no
  directive is left, and the run stops there.
* A run stops after `n` instructions (the fuel), wherever the attacker
  chooses, so every prefix of a non-terminating or faulting transient
  execution is observed, as in FSLH's Definition 2.
* While `ms` is clear, instructions run with the sequential semantics
  (`M.exec`, `M.addrs`). While it is set, they run with the speculative
  semantics `S.sexec`, where memory accesses outside the permitted regions
  do not fault (on x86-64: loads read any address and stores write any
  address, `X86_64/Spectre.lean`), and leak `S.saddrs`; and a speculation
  barrier (`S.fence`, `lfence` on x86-64) stops the run, as the transient
  execution ends when the misprediction resolves.
* A return goes back to its call site: while `ms` is set, even if a
  transient store has overwritten the return address (`S.sret`), as the
  return stack buffer predicts; while it is clear, as sequentially
  (`M.ret`). Calls and frames keep their sequential semantics: they only
  check the stack pointer and the regions, which no transient instruction
  changes (`ISA.writesSp`, `Artifact.spSafe`).

`SpecConstantTime`: for every directive list and fuel, two runs that start
before any misspeculation, from states that agree on public data, leak the
same trace.

Results:

* `Taint.specConstantTime`: `Taint.check` is path-insensitive (it analyses
  both branches of every `ite` and every loop body from an invariant, never
  refining anything by a condition), so a successful check implies
  speculative constant time, provided each instruction's transfer function
  is also sound for the speculative semantics (`SpecSound`).
* `Exec.sexec`: every sequential run is a speculative run (with the
  branches' own directions as directives, and its number of instructions as
  fuel) with the same trace.
-/

namespace VG

/-- An observation of the speculative attacker. -/
inductive SLeak where
  | addr (a : Addr)
  /-- The value of a branch condition (`none`: it reads an undefined flag). -/
  | cond (v : Option Bool)
  deriving DecidableEq

/-- The speculative semantics: what an instruction does, and the addresses
it accesses, when executed transiently; the transient return of a called
function; and which instructions are speculation barriers. -/
structure Spectre (M : ISA) where
  sexec : M.Instr → M.State → Option M.State
  saddrs : M.Instr → M.State → List Addr
  sret : M.State → M.State → Option M.State
  fence : M.Instr → Bool

variable {M : ISA} (S : Spectre M)

/-- An instruction, transiently if `ms`. -/
def Spectre.run (ms : Bool) (i : M.Instr) (s : M.State) : Option M.State :=
  if ms then S.sexec i s else M.exec i s

/-- The addresses an instruction accesses, transiently if `ms`. -/
def Spectre.leaks (ms : Bool) (i : M.Instr) (s : M.State) : List Addr :=
  if ms then S.saddrs i s else M.addrs i s

/-- A return, transiently if `ms`. -/
def Spectre.ret (ms : Bool) (s₁ s₂ : M.State) : Option M.State :=
  if ms then S.sret s₁ s₂ else M.ret s₁ s₂

/-- The misspeculation flag after following direction `b` at a condition of value `v`. -/
def Spectre.mis (ms : Bool) (v : Option Bool) (b : Bool) : Bool := ms || v != some b

/-- How a speculative run ends: stopped, or done with the misspeculation
flag and the remaining directives and fuel. -/
inductive SOut (M : ISA) where
  | halt
  | done (s : M.State) (ms : Bool) (D : List Bool) (n : Nat)

/-- Speculative run of a straight-line block, with misspeculation flag `ms`
and fuel `n`: `none` if it stopped. -/
inductive SBlock : List M.Instr → M.State → Bool → Nat → List SLeak → Option (M.State × Nat) → Prop
  | nil {s ms n} : SBlock [] s ms n [] (some (s, n))
  | stop {i is s ms} : SBlock (i :: is) s ms 0 [] none
  /-- A speculation barrier ends a transient run. -/
  | fence {i is s n} : S.fence i = true → SBlock (i :: is) s true (n + 1) [] none
  | cons {i is s s₁ ms n t r} : (ms && S.fence i) = false → S.run ms i s = some s₁ →
      SBlock is s₁ ms n t r →
      SBlock (i :: is) s ms (n + 1) ((S.leaks ms i s).map .addr ++ t) r

/-- Speculative big-step semantics, with misspeculation flag `ms`,
directives `D` and fuel `n`. -/
inductive SExec : Prog M → M.State → Bool → List Bool → Nat → List SLeak → SOut M → Prop
  | blockDone {is s s' ms D n n' t} : SBlock S is s ms n t (some (s', n')) →
      SExec (.block is) s ms D n t (.done s' ms D n')
  | blockHalt {is s ms D n t} : SBlock S is s ms n t none → SExec (.block is) s ms D n t .halt
  | seq {c₁ c₂ s s₁ ms ms₁ D D₁ n n₁ t₁ t₂ o} : SExec c₁ s ms D n t₁ (.done s₁ ms₁ D₁ n₁) →
      SExec c₂ s₁ ms₁ D₁ n₁ t₂ o → SExec (.seq c₁ c₂) s ms D n (t₁ ++ t₂) o
  | seqHalt {c₁ c₂ s ms D n t} : SExec c₁ s ms D n t .halt → SExec (.seq c₁ c₂) s ms D n t .halt
  | iteEnd {c th el s ms n} : SExec (.ite c th el) s ms [] n [.cond (M.eval c s)] .halt
  | iteT {c th el s ms D n t o} : SExec th s (Spectre.mis ms (M.eval c s) true) D n t o →
      SExec (.ite c th el) s ms (true :: D) n (.cond (M.eval c s) :: t) o
  | iteF {c th el s ms D n t o} : SExec el s (Spectre.mis ms (M.eval c s) false) D n t o →
      SExec (.ite c th el) s ms (false :: D) n (.cond (M.eval c s) :: t) o
  | loopHalt {body c s ms D n t} : SExec body s ms D n t .halt → SExec (.loop body c) s ms D n t .halt
  | loopEnd {body c s s' ms ms' D n n' t} : SExec body s ms D n t (.done s' ms' [] n') →
      SExec (.loop body c) s ms D n (t ++ [.cond (M.eval c s')]) .halt
  | loopExit {body c s s' ms ms' D D' n n' t} : SExec body s ms D n t (.done s' ms' (false :: D') n') →
      SExec (.loop body c) s ms D n (t ++ [.cond (M.eval c s')])
        (.done s' (Spectre.mis ms' (M.eval c s') false) D' n')
  | loopNext {body c s s' ms ms' D D' n n' t t' o} :
      SExec body s ms D n t (.done s' ms' (true :: D') n') →
      SExec (.loop body c) s' (Spectre.mis ms' (M.eval c s') true) D' n' t' o →
      SExec (.loop body c) s ms D n (t ++ .cond (M.eval c s') :: t') o
  | callHalt {name body s s₁ ms D n t} : M.call s = some s₁ → SExec body s₁ ms D n t .halt →
      SExec (.call name body) s ms D n ((M.callAddrs s).map .addr ++ t) .halt
  | call {name body s s₁ s₂ s' ms ms' D D' n n' t} : M.call s = some s₁ →
      SExec body s₁ ms D n t (.done s₂ ms' D' n') → S.ret ms' s₁ s₂ = some s' →
      SExec (.call name body) s ms D n
        ((M.callAddrs s).map .addr ++ t ++ (M.retAddrs s₂).map .addr) (.done s' ms' D' n')
  | frameHalt {i j body s s₁ ms D n t} : M.push i s = some s₁ → SExec body s₁ ms D n t .halt →
      SExec (.frame i body j) s ms D n ((M.addrs i s).map .addr ++ t) .halt
  | frame {i j body s s₁ s₂ s' ms ms' D D' n n' t} : M.push i s = some s₁ →
      SExec body s₁ ms D n t (.done s₂ ms' D' n') → M.pop j s₁ s₂ = some s' →
      SExec (.frame i body j) s ms D n
        ((M.addrs i s).map .addr ++ t ++ (M.addrs j s₂).map .addr) (.done s' ms' D' n')

/-- Speculative constant time: under any directives and fuel, two runs from
states agreeing on public data, starting before any misspeculation, leak
the same trace. -/
def SpecConstantTime (Pre : M.State → Prop) (Pub : M.State → M.State → Prop) (c : Prog M) : Prop :=
  ∀ s₁ s₂ D n t₁ t₂ o₁ o₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ →
    SExec S c s₁ false D n t₁ o₁ → SExec S c s₂ false D n t₂ o₂ → t₁ = t₂

namespace Taint

variable {S} {A : Taint M}

/-- The transfer functions of `A` are sound for the speculative semantics. -/
structure SpecSound (A : Taint M) (S : Spectre M) : Prop where
  step : ∀ {τ τ' i s₁ s₂ s₁' s₂'}, A.Agree τ s₁ s₂ → A.step τ i = some τ' →
    S.sexec i s₁ = some s₁' → S.sexec i s₂ = some s₂' →
    S.saddrs i s₁ = S.saddrs i s₂ ∧ A.Agree τ' s₁' s₂'
  ret : ∀ {τ τ' a₁ a₂ b₁ b₂ c₁ c₂}, A.Agree τ b₁ b₂ → A.ret τ = some τ' →
    S.sret a₁ b₁ = some c₁ → S.sret a₂ b₂ = some c₂ → M.retAddrs b₁ = M.retAddrs b₂ ∧ A.Agree τ' c₁ c₂

theorem SpecSound.run (hs : SpecSound A S) {ms : Bool} {τ τ' : A.T} {i : M.Instr}
    {s₁ s₂ s₁' s₂' : M.State} (ha : A.Agree τ s₁ s₂) (h : A.step τ i = some τ')
    (e₁ : S.run ms i s₁ = some s₁') (e₂ : S.run ms i s₂ = some s₂') :
    S.leaks ms i s₁ = S.leaks ms i s₂ ∧ A.Agree τ' s₁' s₂' := by
  cases ms
  · exact A.step_sound ha h e₁ e₂
  · exact hs.step ha h e₁ e₂

theorem SpecSound.sret (hs : SpecSound A S) {ms : Bool} {τ τ' : A.T} {a₁ a₂ b₁ b₂ c₁ c₂ : M.State}
    (ha : A.Agree τ b₁ b₂) (h : A.ret τ = some τ')
    (e₁ : S.ret ms a₁ b₁ = some c₁) (e₂ : S.ret ms a₂ b₂ = some c₂) :
    M.retAddrs b₁ = M.retAddrs b₂ ∧ A.Agree τ' c₁ c₂ := by
  cases ms
  · exact A.ret_sound ha h e₁ e₂
  · exact hs.ret ha h e₁ e₂

/-- How two runs end, related by the taint `τ`. -/
def BRel (A : Taint M) (τ : A.T) : Option (M.State × Nat) → Option (M.State × Nat) → Prop
  | none, none => True
  | some (a, k), some (b, l) => k = l ∧ A.Agree τ a b
  | _, _ => False

def ORel (A : Taint M) (τ : A.T) : SOut M → SOut M → Prop
  | .halt, .halt => True
  | .done a ms D k, .done b ms' E l => ms = ms' ∧ D = E ∧ k = l ∧ A.Agree τ a b
  | _, _ => False

theorem sblock_sound (hs : SpecSound A S) {is : List M.Instr} {τ τ' : A.T} {s₁ s₂ : M.State}
    {ms : Bool} {n : Nat} {t₁ t₂ : List SLeak} {r₁ r₂ : Option (M.State × Nat)}
    (h : A.checkBlock τ is = some τ') (ha : A.Agree τ s₁ s₂)
    (e₁ : SBlock S is s₁ ms n t₁ r₁) (e₂ : SBlock S is s₂ ms n t₂ r₂) :
    t₁ = t₂ ∧ BRel A τ' r₁ r₂ := by
  induction e₁ generalizing τ s₂ t₂ r₂ with
  | nil =>
    cases e₂
    simp only [checkBlock, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl, ha⟩
  | stop => cases e₂; exact ⟨rfl, trivial⟩
  | fence f =>
    cases e₂ with
    | fence => exact ⟨rfl, trivial⟩
    | cons hf => rw [f] at hf; cases hf
  | cons hf x₁ _ ih =>
    cases e₂ with
    | fence f => rw [f] at hf; cases hf
    | cons _ x₂ b =>
      simp only [checkBlock, Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, hs₁, hr⟩ := h
      obtain ⟨hadd, ha₁⟩ := hs.run ha hs₁ x₁ x₂
      obtain ⟨ht, hr'⟩ := ih hr ha₁ b
      exact ⟨by rw [hadd, ht], hr'⟩

theorem sblock_append {xs ys : List M.Instr} {s : M.State} {ms : Bool} {n : Nat} {t : List SLeak}
    {r : Option (M.State × Nat)} (e : SBlock S (xs ++ ys) s ms n t r) :
    (∃ s₁ n₁ t₁ t₂, SBlock S xs s ms n t₁ (some (s₁, n₁)) ∧ SBlock S ys s₁ ms n₁ t₂ r ∧
      t = t₁ ++ t₂) ∨ (r = none ∧ SBlock S xs s ms n t none) := by
  induction xs generalizing s n t with
  | nil => exact .inl ⟨s, n, [], t, .nil, e, rfl⟩
  | cons i xs ih =>
    cases e with
    | stop => exact .inr ⟨rfl, .stop⟩
    | fence f => exact .inr ⟨rfl, .fence f⟩
    | cons hf x b =>
      rcases ih b with ⟨s₁, n₁, t₁, t₂, b₁, b₂, rfl⟩ | ⟨rfl, b₁⟩
      · exact .inl ⟨s₁, n₁, _, t₂, .cons hf x b₁, b₂, by rw [List.append_assoc]⟩
      · exact .inr ⟨rfl, .cons hf x b₁⟩

theorem schunks_sound (hs : SpecSound A S) {ms : List A.T} {is : List M.Instr} {τ τ' : A.T}
    {s₁ s₂ : M.State} {f : Bool} {n : Nat} {t₁ t₂ : List SLeak} {r₁ r₂ : Option (M.State × Nat)}
    (h : A.checkChunks τ is ms = some τ') (ha : A.Agree τ s₁ s₂)
    (e₁ : SBlock S is s₁ f n t₁ r₁) (e₂ : SBlock S is s₂ f n t₂ r₂) :
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
  exact ⟨h.1, h.2.1, h.2.2.1, hm _ _ h.2.2.2⟩

theorem specCheck_sound (hs : SpecSound A S) {c : Prog M} {τ τ' : A.T} {hc : Hint A.T}
    {s₁ s₂ : M.State} {ms : Bool} {D : List Bool} {n : Nat} {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M}
    (h : A.check τ c hc = some τ') (ha : A.Agree τ s₁ s₂)
    (e₁ : SExec S c s₁ ms D n t₁ o₁) (e₂ : SExec S c s₂ ms D n t₂ o₂) :
    t₁ = t₂ ∧ ORel A τ' o₁ o₂ := by
  induction e₁ generalizing τ τ' hc s₂ t₂ o₂ with
  | blockDone b₁ =>
    cases hc with
    | block ms =>
      have h : A.checkChunks τ _ ms = some τ' := h
      cases e₂ with
      | blockDone b₂ =>
        obtain ⟨rfl, rfl, hq⟩ := schunks_sound hs h ha b₁ b₂; exact ⟨rfl, rfl, rfl, rfl, hq⟩
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
  | @seq c₁ c₂ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
    cases hc with
    | seq mid g₁ g₂ =>
      have h : ((A.check τ c₁ g₁).bind fun τ' => if A.le mid τ' then A.check mid c₂ g₂ else none) =
        some τ' := h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, h₂⟩ := h
      split at h₂ <;> [rename_i hle; cases h₂]
      cases e₂ with
      | seq a b =>
        obtain ⟨rfl, rfl, rfl, rfl, hq⟩ := ih₁ h₁ ha a
        obtain ⟨rfl, hr⟩ := ih₂ h₂ (A.le_sound hle hq) b
        exact ⟨rfl, hr⟩
      | seqHalt a => exact (ih₁ h₁ ha a).2.elim
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @seqHalt c₁ c₂ _ _ _ _ _ _ ih =>
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
  | @iteEnd cnd t e _ _ _ =>
    cases hc with
    | ite g₁ g₂ =>
      have h : (if A.condPub τ cnd then
          (A.check τ t g₁).bind fun τ₁ => (A.check τ e g₂).map fun τ₂ => A.meet τ₁ τ₂
        else none) = some τ' := h
      split at h <;> [rename_i hp; cases h]
      cases e₂; exact ⟨by rw [A.cond_sound ha hp], trivial⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @iteT cnd t e _ _ _ _ _ _ _ ih =>
    cases hc with
    | ite g₁ g₂ =>
      have h : (if A.condPub τ cnd then
          (A.check τ t g₁).bind fun τ₁ => (A.check τ e g₂).map fun τ₂ => A.meet τ₁ τ₂
        else none) = some τ' := h
      split at h <;> [rename_i hp; cases h]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, _, rfl⟩ := h
      have hv := A.cond_sound ha hp
      cases e₂ with
      | iteT b =>
        rw [← hv] at b
        obtain ⟨rfl, hq⟩ := ih h₁ ha b
        exact ⟨by rw [hv], ORel.mono (fun _ _ => A.meet_left) hq⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @iteF cnd t e _ _ _ _ _ _ _ ih =>
    cases hc with
    | ite g₁ g₂ =>
      have h : (if A.condPub τ cnd then
          (A.check τ t g₁).bind fun τ₁ => (A.check τ e g₂).map fun τ₂ => A.meet τ₁ τ₂
        else none) = some τ' := h
      split at h <;> [rename_i hp; cases h]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨τ₁, _, τ₂, h₂, rfl⟩ := h
      have hv := A.cond_sound ha hp
      cases e₂ with
      | iteF b =>
        rw [← hv] at b
        obtain ⟨rfl, hq⟩ := ih h₂ ha b
        exact ⟨by rw [hv], ORel.mono (fun _ _ => A.meet_right) hq⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @loopHalt body c _ _ _ _ _ _ ih =>
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
  | @loopEnd body c _ s' _ _ _ _ _ _ _ ih =>
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
      | loopEnd a =>
        obtain ⟨rfl, -, -, -, hq⟩ := ih hb' hσ a
        exact ⟨by rw [A.cond_sound hq hl.2], trivial⟩
      | loopExit a | loopNext a _ => obtain ⟨-, h, -⟩ := (ih hb' hσ a).2; cases h
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @loopExit body c _ s' _ _ _ _ _ _ _ _ ih =>
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
      | loopEnd a | loopNext a _ => obtain ⟨-, h, -⟩ := (ih hb' hσ a).2; cases h
      | loopExit a =>
        obtain ⟨rfl, rfl, h, rfl, hq⟩ := ih hb' hσ a
        cases h
        have hv := A.cond_sound hq hl.2
        rw [hv]
        exact ⟨rfl, rfl, rfl, rfl, hq⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @loopNext body c _ s' _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
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
      | loopEnd a | loopExit a => obtain ⟨-, h, -⟩ := (ih₁ hb' hσ a).2; cases h
      | loopNext a b =>
        obtain ⟨rfl, rfl, h, rfl, hq⟩ := ih₁ hb' hσ a
        cases h
        have hv := A.cond_sound hq hl.2
        rw [← hv] at b
        have hloop : A.check τ' (.loop body c) (.loop σ hb) = some τ' := by
          show (if A.le σ τ' then
            (A.check σ body hb).bind fun σ' => if A.le σ σ' && A.condPub σ' c then some σ' else none
            else none) = some τ'
          simp only [hl.1, hl.2, hb', Option.bind_some, Bool.and_self, ite_true]
        obtain ⟨rfl, hr⟩ := ih₂ hloop hq b
        exact ⟨by rw [hv], hr⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @callHalt _ body _ _ _ _ _ _ hc₁ _ ih =>
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
  | @call _ body _ _ _ _ _ _ _ _ _ _ _ hc₁ _ hr ih =>
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
        obtain ⟨rfl, rfl, rfl, rfl, ha₂⟩ := ih h₂ ha₁' b
        obtain ⟨ha₃, ha₃'⟩ := hs.sret ha₂ h₃ hr hr₂
        exact ⟨by rw [ha₁, ha₃], rfl, rfl, rfl, ha₃'⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @frameHalt i j body _ _ _ _ _ _ hp₁ _ ih =>
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
  | @frame i j body _ _ _ _ _ _ _ _ _ _ _ hp₁ _ hq ih =>
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
        obtain ⟨rfl, rfl, rfl, rfl, ha₂⟩ := ih h₂ ha₁' b
        obtain ⟨ha₃, ha₃'⟩ := A.pop_sound ha₂ h₃ hq hq₂
        exact ⟨by rw [ha₁, ha₃], rfl, rfl, rfl, ha₃'⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'

/-- A successful (sequential) taint check proves speculative constant time,
if the transfer functions are sound for the speculative semantics. -/
theorem specConstantTime (hs : SpecSound A S) {Pre : M.State → Prop}
    {Pub : M.State → M.State → Prop} {c : Prog M}
    (τ : A.T) (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → A.Agree τ s₁ s₂) {hc : Hint A.T}
    (h : (A.check τ c hc).isSome = true) : SpecConstantTime S Pre Pub c := by
  intro s₁ s₂ D n t₁ t₂ o₁ o₂ h₁ h₂ hp e₁ e₂
  obtain ⟨τ', hc⟩ := Option.isSome_iff_exists.mp h
  exact (specCheck_sound hs hc (hpub _ _ h₁ h₂ hp) e₁ e₂).1
/-- The same, for runs entered while already misspeculating (e.g. a
function called on a mispredicted path) and from any states agreeing on what
`τ` says is public, without a precondition. -/
theorem specConstantTime_any (hs : SpecSound A S) {c : Prog M} (τ : A.T) {hc : Hint A.T}
    (h : (A.check τ c hc).isSome = true) {s₁ s₂ : M.State} (ha : A.Agree τ s₁ s₂)
    {ms : Bool} {D : List Bool} {n : Nat} {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M}
    (e₁ : SExec S c s₁ ms D n t₁ o₁) (e₂ : SExec S c s₂ ms D n t₂ o₂) : t₁ = t₂ := by
  obtain ⟨τ', hc⟩ := Option.isSome_iff_exists.mp h
  exact (specCheck_sound hs hc ha e₁ e₂).1

end Taint

end VG
