module

public import VerifiedGarbage.Proof.Framework.Taint
public meta import VerifiedGarbage.Proof.Framework.Taint
public import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.Basic
public import Lean.Meta.Eval
public meta import Lean.Meta.Eval

/-!
# Taint tracking between two runs that leak the same

A `TaintCT M` is a taint analysis (`Taint M`) for two runs that are known to
leak the same trace: two runs of code proven constant time (`ConstantTime`),
from states its precondition and its `pub` relate, such as those
`NoResidue` compares. Each step of such runs accesses the same addresses,
and each branch goes the same way, in both, so the analysis never needs to
prove it: it takes each instruction's addresses as equal in the two runs
(`step_sound`), and may learn from it (a base register whose sum with an
offset is the same address is the same register), and it follows both
sides of every branch on any condition, public or not. What it proves is
only what the two runs leave in the state (`check_sound`): the kind of
analysis that `NoResidue` needs, where constant time is already proven.

`check` takes a `Hint` (`Taint.Hint`), as `Taint.check` does, which
`hint` computes in compiled code and `taint_decide_ct` passes to the kernel.

The proof that the two runs' traces agree step by step, given that they agree
as a whole, needs each step's trace to have a length that does not depend on
the state (`addrs_length`, `callAddrs_length`, `retAddrs_length`): two traces
that agree as a whole and whose first steps have the same length agree on
those steps, and on the rest (`List.append_inj`).
-/

@[expose] public section

namespace VG

structure TaintCT (M : ISA) where
  T : Type
  Agree : T → M.State → M.State → Prop
  step : T → M.Instr → Option T
  /-- An instruction run from agreeing states, accessing the same addresses
  in both, leaves states that agree. -/
  step_sound : ∀ {τ τ' i s₁ s₂ s₁' s₂'}, Agree τ s₁ s₂ → step τ i = some τ' →
    M.exec i s₁ = some s₁' → M.exec i s₂ = some s₂' → M.addrs i s₁ = M.addrs i s₂ →
    Agree τ' s₁' s₂'
  /-- How many addresses an instruction accesses does not depend on the state. -/
  addrs_length : ∀ i s₁ s₂, (M.addrs i s₁).length = (M.addrs i s₂).length
  meet : T → T → T
  meet_left : ∀ {τ₁ τ₂ s₁ s₂}, Agree τ₁ s₁ s₂ → Agree (meet τ₁ τ₂) s₁ s₂
  meet_right : ∀ {τ₁ τ₂ s₁ s₂}, Agree τ₂ s₁ s₂ → Agree (meet τ₁ τ₂) s₁ s₂
  le : T → T → Bool
  le_sound : ∀ {τ σ s₁ s₂}, le τ σ = true → Agree σ s₁ s₂ → Agree τ s₁ s₂
  call : T → Option T
  call_sound : ∀ {τ τ' s₁ s₂ s₁' s₂'}, Agree τ s₁ s₂ → call τ = some τ' →
    M.call s₁ = some s₁' → M.call s₂ = some s₂' → M.callAddrs s₁ = M.callAddrs s₂ →
    Agree τ' s₁' s₂'
  callAddrs_length : ∀ s₁ s₂, (M.callAddrs s₁).length = (M.callAddrs s₂).length
  ret : T → Option T
  ret_sound : ∀ {τ τ' a₁ a₂ b₁ b₂ c₁ c₂}, Agree τ b₁ b₂ → ret τ = some τ' →
    M.ret a₁ b₁ = some c₁ → M.ret a₂ b₂ = some c₂ → M.retAddrs b₁ = M.retAddrs b₂ →
    Agree τ' c₁ c₂
  retAddrs_length : ∀ s₁ s₂, (M.retAddrs s₁).length = (M.retAddrs s₂).length
  push : T → M.Instr → Option T
  push_sound : ∀ {τ τ' i s₁ s₂ s₁' s₂'}, Agree τ s₁ s₂ → push τ i = some τ' →
    M.push i s₁ = some s₁' → M.push i s₂ = some s₂' → M.addrs i s₁ = M.addrs i s₂ →
    Agree τ' s₁' s₂'
  pop : T → M.Instr → Option T
  pop_sound : ∀ {τ τ' j a₁ a₂ b₁ b₂ c₁ c₂}, Agree τ b₁ b₂ → pop τ j = some τ' →
    M.pop j a₁ b₁ = some c₁ → M.pop j a₂ b₂ = some c₂ → M.addrs j b₁ = M.addrs j b₂ →
    Agree τ' c₁ c₂

namespace TaintCT

open Taint (Hint)

variable {M : ISA} (A : TaintCT M)

/-- `checkBlock`, for compiled code. -/
def checkBlockC : A.T → List M.Instr → Option A.T
  | τ, [] => some τ
  | τ, i :: is => (A.step τ i).bind (checkBlockC · is)

/-- The analysis of a block, a `List.rec` as `Taint.checkBlock` is. -/
@[implemented_by checkBlockC] def checkBlock (τ : A.T) (is : List M.Instr) : Option A.T :=
  List.rec (motive := fun _ => A.T → Option A.T) some (fun i _ ih τ => (A.step τ i).bind ih) is τ

/-- The analysis of a block, weakened to `mids` after every `chunkSize` instructions. -/
def checkChunks (chunkSize : Nat) : A.T → List M.Instr → List A.T → Option A.T
  | τ, is, [] => A.checkBlock τ is
  | τ, is, m :: ms => (A.checkBlock τ (KList.take chunkSize is)).bind fun τ' =>
    if A.le m τ' then checkChunks chunkSize m (KList.drop chunkSize is) ms else none

/-- The analysis of structured code, given a hint: `Taint.check`, but that
the conditions need not be public. -/
def check : A.T → Prog M → Hint A.T → Option A.T
  | τ, .block is, .block ms chunkSize => checkChunks A chunkSize τ is ms
  | τ, .seq c₁ c₂, .seq mid h₁ h₂ =>
    (check τ c₁ h₁).bind fun τ' => if A.le mid τ' then check mid c₂ h₂ else none
  | τ, .ite _ t e, .ite h₁ h₂ =>
    (check τ t h₁).bind fun τ₁ => (check τ e h₂).map fun τ₂ => A.meet τ₁ τ₂
  | τ, .loop body _, .loop σ h =>
    if A.le σ τ then
      (check σ body h).bind fun σ' => if A.le σ σ' then some σ' else none
    else none
  | τ, .call _ body, .call h => (A.call τ).bind fun τ₁ => (check τ₁ body h).bind A.ret
  | τ, .frame i body j, .frame h =>
    (A.push τ i).bind fun τ₁ => (check τ₁ body h).bind fun τ₂ => A.pop τ₂ j
  | _, _, _ => none

/-! ## Computing hints

Nothing here needs to be sound: `check` checks the hint. -/

/-- The hints for a block: the analysis after every `chunkSize` instructions but the last. -/
def chunkHints (chunkSize : Nat) : A.T → List M.Instr → Nat → List A.T
  | _, _, 0 => []
  | τ, is, n + 1 =>
    if is.length ≤ chunkSize then [] else
    match A.checkBlock τ (is.take chunkSize) with
    | some τ' => τ' :: chunkHints chunkSize τ' (is.drop chunkSize) n
    | none => []

/-- The analysis of structured code, with its hint, as `Taint.hint`. -/
def hint (chunkSize : Nat) : A.T → Prog M → Option (A.T × Hint A.T)
  | τ, .block is => (A.checkBlock τ is).map fun τ' => (τ', .block (chunkHints A chunkSize τ is is.length) chunkSize)
  | τ, .seq c₁ c₂ =>
    (hint chunkSize τ c₁).bind fun (τ₁, h₁) => (hint chunkSize τ₁ c₂).map fun (τ₂, h₂) => (τ₂, .seq τ₁ h₁ h₂)
  | τ, .ite _ t e =>
    (hint chunkSize τ t).bind fun (τ₁, h₁) => (hint chunkSize τ e).map fun (τ₂, h₂) => (A.meet τ₁ τ₂, .ite h₁ h₂)
  | τ, .loop body _ => go (hint chunkSize · body) Taint.loopFuel τ
  | τ, .call _ body =>
    (A.call τ).bind fun τ₁ => (hint chunkSize τ₁ body).bind fun (τ₂, h) => (A.ret τ₂).map (·, .call h)
  | τ, .frame i body j =>
    (A.push τ i).bind fun τ₁ => (hint chunkSize τ₁ body).bind fun (τ₂, h) => (A.pop τ₂ j).map (·, .frame h)
  | _, .icall .. => none
where
  go (body : A.T → Option (A.T × Hint A.T)) : Nat → A.T → Option (A.T × Hint A.T)
    | 0, _ => none
    | n + 1, σ => (body σ).bind fun (σ', h) =>
      if A.le σ σ' then some (σ', .loop σ h) else go body n (A.meet σ σ')

/-- The hint for `c` from `τ` (any hint, if the analysis fails). -/
@[nospecialize] def hintOfSize (chunkSize : Nat) (τ : A.T) (c : Prog M) : Hint A.T :=
  ((hint A chunkSize τ c).map (·.2)).getD (.block [] chunkSize)

/-! ## Soundness -/

variable {A}

/-- Two traces that agree with what follows them, and whose first parts
have the same length, agree on those parts and on what follows. -/
theorem append_cancel {a₁ a₂ b₁ b₂ : List Leak} (h : a₁ ++ b₁ = a₂ ++ b₂)
    (hl : a₁.length = a₂.length) : a₁ = a₂ ∧ b₁ = b₂ :=
  List.append_inj h hl

theorem map_addr_inj : ∀ {a₁ a₂ : List Addr}, a₁.map Leak.addr = a₂.map Leak.addr → a₁ = a₂
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq, Leak.addr.injEq] at h
    rw [h.1, map_addr_inj h.2]

theorem checkBlock_sound {is : List M.Instr} {τ τ' : A.T} {s₁ s₂ s₁' s₂' : M.State}
    {t₁ t₂ r₁ r₂ : List Leak} (h : A.checkBlock τ is = some τ') (ha : A.Agree τ s₁ s₂)
    (e₁ : execBlock M is s₁ = some (s₁', t₁)) (e₂ : execBlock M is s₂ = some (s₂', t₂))
    (ht : t₁ ++ r₁ = t₂ ++ r₂) : t₁ = t₂ ∧ A.Agree τ' s₁' s₂' := by
  induction is generalizing τ s₁ s₂ t₁ t₂ with
  | nil =>
    simp only [checkBlock, Option.some.injEq] at h
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    obtain ⟨rfl, rfl⟩ := e₁; obtain ⟨rfl, rfl⟩ := e₂; subst h; exact ⟨rfl, ha⟩
  | cons i is ih =>
    simp only [checkBlock, Option.bind_eq_some_iff] at h
    obtain ⟨τ₁, hs, hr⟩ := h
    simp only [execBlock] at e₁ e₂
    split at e₁ <;> rename_i h₁ <;> [cases e₁; skip]
    split at e₂ <;> rename_i h₂ <;> [cases e₂; skip]
    simp only [Option.map_eq_some_iff, Prod.exists] at e₁ e₂
    obtain ⟨_, u₁, e₁, he₁⟩ := e₁
    obtain ⟨_, u₂, e₂, he₂⟩ := e₂
    simp only [Prod.mk.injEq] at he₁ he₂
    obtain ⟨rfl, rfl⟩ := he₁; obtain ⟨rfl, rfl⟩ := he₂
    rw [List.append_assoc, List.append_assoc] at ht
    obtain ⟨hadd, ht'⟩ := append_cancel ht (by
      rw [List.length_map, List.length_map]; exact A.addrs_length i _ _)
    obtain ⟨hu, ha'⟩ := ih hr (A.step_sound ha hs h₁ h₂ (map_addr_inj hadd)) e₁ e₂ ht'
    exact ⟨by rw [hadd, hu], ha'⟩

theorem execBlock_split {is : List M.Instr} {s s' : M.State} {t : List Leak} (n : Nat)
    (e : execBlock M is s = some (s', t)) :
    ∃ s₁ u₁ u₂, execBlock M (is.take n) s = some (s₁, u₁) ∧
      execBlock M (is.drop n) s₁ = some (s', u₂) ∧ t = u₁ ++ u₂ :=
  Taint.execBlock_split n e

/-- How many addresses a block accesses does not depend on the state. -/
theorem execBlock_length {is : List M.Instr} {s₁ s₂ s₁' s₂' : M.State} {t₁ t₂ : List Leak}
    (A : TaintCT M) (e₁ : execBlock M is s₁ = some (s₁', t₁))
    (e₂ : execBlock M is s₂ = some (s₂', t₂)) : t₁.length = t₂.length := by
  induction is generalizing s₁ s₂ s₁' s₂' t₁ t₂ with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2]
  | cons i is ih =>
    simp only [execBlock] at e₁ e₂
    split at e₁ <;> [cases e₁; skip]
    split at e₂ <;> [cases e₂; skip]
    simp only [Option.map_eq_some_iff, Prod.exists] at e₁ e₂
    obtain ⟨_, u₁, e₁, he₁⟩ := e₁
    obtain ⟨_, u₂, e₂, he₂⟩ := e₂
    simp only [Prod.mk.injEq] at he₁ he₂
    rw [← he₁.2, ← he₂.2, List.length_append, List.length_append, List.length_map,
      List.length_map, A.addrs_length i _ _, ih e₁ e₂]

theorem checkChunks_sound {chunkSize : Nat} {ms : List A.T} {is : List M.Instr} {τ τ' : A.T}
    {s₁ s₂ s₁' s₂' : M.State} {t₁ t₂ r₁ r₂ : List Leak}
    (h : A.checkChunks chunkSize τ is ms = some τ') (ha : A.Agree τ s₁ s₂)
    (e₁ : execBlock M is s₁ = some (s₁', t₁)) (e₂ : execBlock M is s₂ = some (s₂', t₂))
    (ht : t₁ ++ r₁ = t₂ ++ r₂) : t₁ = t₂ ∧ A.Agree τ' s₁' s₂' := by
  induction ms generalizing τ is s₁ s₂ t₁ t₂ with
  | nil => exact checkBlock_sound h ha e₁ e₂ ht
  | cons m ms ih =>
    simp only [checkChunks, KList.take_eq, KList.drop_eq, Option.bind_eq_some_iff] at h
    obtain ⟨τ₁, h₁, h₂⟩ := h
    split at h₂ <;> [rename_i hle; cases h₂]
    obtain ⟨_, _, _, a₁, b₁, rfl⟩ := execBlock_split chunkSize e₁
    obtain ⟨_, _, _, a₂, b₂, rfl⟩ := execBlock_split chunkSize e₂
    rw [List.append_assoc, List.append_assoc] at ht
    obtain ⟨hu, ht'⟩ := append_cancel ht (execBlock_length A a₁ a₂)
    obtain ⟨-, ha₁⟩ := checkBlock_sound h₁ ha a₁ a₂ (r₁ := []) (r₂ := []) (by rw [hu])
    obtain ⟨rfl, ha₂⟩ := ih h₂ (A.le_sound hle ha₁) b₁ b₂ ht'
    exact ⟨by rw [hu], ha₂⟩

/-- Two runs of code that the analysis checks, from states that agree on
what its taint says is public, and whose traces agree with what follows
them, have the same trace, and end in states that agree on what the final
taint says is public. -/
theorem check_sound {c : Prog M} {τ τ' : A.T} {hc : Hint A.T} {s₁ s₂ s₁' s₂' : M.State}
    {t₁ t₂ r₁ r₂ : List Leak} (h : A.check τ c hc = some τ') (ha : A.Agree τ s₁ s₂)
    (e₁ : Exec M c s₁ t₁ s₁') (e₂ : Exec M c s₂ t₂ s₂') (ht : t₁ ++ r₁ = t₂ ++ r₂) :
    t₁ = t₂ ∧ A.Agree τ' s₁' s₂' := by
  induction e₁ generalizing τ τ' hc s₂ t₂ s₂' r₁ r₂ with
  | block h₁ =>
    cases hc with
    | block ms chunkSize =>
      have h : A.checkChunks chunkSize τ _ ms = some τ' := h
      cases e₂ with
      | block h₂ => exact checkChunks_sound h ha h₁ h₂ ht
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @seq c₁ c₂ _ _ _ _ _ _ _ ih₁ ih₂ =>
    cases hc with
    | seq mid g₁ g₂ =>
      have h : ((A.check τ c₁ g₁).bind fun τ' => if A.le mid τ' then A.check mid c₂ g₂ else none) =
        some τ' := h
      cases e₂ with
      | seq a b =>
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨τ₁, h₁, h₂⟩ := h
        split at h₂ <;> [rename_i hle; cases h₂]
        rw [List.append_assoc, List.append_assoc] at ht
        obtain ⟨rfl, ha₁⟩ := ih₁ h₁ ha a ht
        obtain ⟨rfl, ha₂⟩ := ih₂ h₂ (A.le_sound hle ha₁) b (List.append_cancel_left ht)
        exact ⟨rfl, ha₂⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | iteT _ _ ih =>
    cases hc with
    | ite g₁ g₂ =>
      have h : ((A.check τ _ g₁).bind fun τ₁ => (A.check τ _ g₂).map fun τ₂ => A.meet τ₁ τ₂) =
        some τ' := h
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, _, rfl⟩ := h
      cases e₂ with
      | iteT _ b =>
        simp only [List.cons_append, List.cons.injEq, true_and] at ht
        obtain ⟨rfl, hq⟩ := ih h₁ ha b ht
        exact ⟨rfl, A.meet_left hq⟩
      | iteF _ _ => simp at ht
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | iteF _ _ ih =>
    cases hc with
    | ite g₁ g₂ =>
      have h : ((A.check τ _ g₁).bind fun τ₁ => (A.check τ _ g₂).map fun τ₂ => A.meet τ₁ τ₂) =
        some τ' := h
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨τ₁, _, τ₂, h₂, rfl⟩ := h
      cases e₂ with
      | iteT _ _ => simp at ht
      | iteF _ b =>
        simp only [List.cons_append, List.cons.injEq, true_and] at ht
        obtain ⟨rfl, hq⟩ := ih h₂ ha b ht
        exact ⟨rfl, A.meet_right hq⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @loopExit body c _ _ _ _ _ ih =>
    cases hc with
    | loop σ hb =>
      have h : (if A.le σ τ then
          (A.check σ body hb).bind fun σ' => if A.le σ σ' then some σ' else none
        else none) = some τ' := h
      split at h <;> [rename_i hστ; cases h]
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨σ', hb', h'⟩ := h
      split at h' <;> [skip; cases h']
      cases h'
      have hσ := A.le_sound hστ ha
      cases e₂ with
      | loopExit a _ =>
        rw [List.append_assoc, List.append_assoc] at ht
        obtain ⟨rfl, hq⟩ := ih hb' hσ a ht
        exact ⟨rfl, hq⟩
      | loopNext a _ _ =>
        rw [List.append_assoc, List.append_assoc] at ht
        obtain ⟨rfl, _⟩ := ih hb' hσ a ht
        simp at ht
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @loopNext body c _ _ _ _ _ _ _ _ ih₁ ih₂ =>
    cases hc with
    | loop σ hb =>
      have h : (if A.le σ τ then
          (A.check σ body hb).bind fun σ' => if A.le σ σ' then some σ' else none
        else none) = some τ' := h
      split at h <;> [rename_i hστ; cases h]
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨σ', hb', h'⟩ := h
      split at h' <;> [rename_i hl; cases h']
      cases h'
      have hσ := A.le_sound hστ ha
      cases e₂ with
      | loopExit a _ =>
        rw [List.append_assoc, List.append_assoc] at ht
        obtain ⟨rfl, _⟩ := ih₁ hb' hσ a ht
        simp at ht
      | loopNext a _ b =>
        rw [List.append_assoc, List.append_assoc] at ht
        obtain ⟨rfl, ha₁⟩ := ih₁ hb' hσ a ht
        have ht' := List.append_cancel_left ht
        simp only [List.cons_append, List.cons.injEq, true_and] at ht'
        have hloop : A.check τ' (.loop body c) (.loop σ hb) = some τ' := by
          show (if A.le σ τ' then
            (A.check σ body hb).bind fun σ' => if A.le σ σ' then some σ' else none
            else none) = some τ'
          simp only [hl, hb', Option.bind_some, ite_true]
        obtain ⟨rfl, ha₂⟩ := ih₂ hloop ha₁ b ht'
        exact ⟨rfl, ha₂⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @call _ body _ _ _ _ _ hc₁ _ hr ih =>
    cases hc with
    | call hb =>
      have h : ((A.call τ).bind fun τ₁ => (A.check τ₁ body hb).bind A.ret) = some τ' := h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      cases e₂ with
      | call hc₂ b hr₂ =>
        simp only [List.append_assoc] at ht
        obtain ⟨hca, ht₁⟩ := append_cancel ht (by
          rw [List.length_map, List.length_map]; exact A.callAddrs_length _ _)
        have ha₁ := A.call_sound ha h₁ hc₁ hc₂ (map_addr_inj hca)
        obtain ⟨rfl, ha₂⟩ := ih h₂ ha₁ b ht₁
        obtain ⟨hra, -⟩ := append_cancel (List.append_cancel_left ht₁) (by
          rw [List.length_map, List.length_map]; exact A.retAddrs_length _ _)
        exact ⟨by rw [hca, hra], A.ret_sound ha₂ h₃ hr hr₂ (map_addr_inj hra)⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @frame i j body _ _ _ _ _ hp₁ _ hq ih =>
    cases hc with
    | frame hb =>
      have h : ((A.push τ i).bind fun τ₁ => (A.check τ₁ body hb).bind fun τ₂ => A.pop τ₂ j) =
        some τ' := h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      cases e₂ with
      | frame hp₂ b hq₂ =>
        simp only [List.append_assoc] at ht
        obtain ⟨hpa, ht₁⟩ := append_cancel ht (by
          rw [List.length_map, List.length_map]; exact A.addrs_length i _ _)
        have ha₁ := A.push_sound ha h₁ hp₁ hp₂ (map_addr_inj hpa)
        obtain ⟨rfl, ha₂⟩ := ih h₂ ha₁ b ht₁
        obtain ⟨hqa, -⟩ := append_cancel (List.append_cancel_left ht₁) (by
          rw [List.length_map, List.length_map]; exact A.addrs_length j _ _)
        exact ⟨by rw [hpa, hqa], A.pop_sound ha₂ h₃ hq hq₂ (map_addr_inj hqa)⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | icall | icallNext => cases hc <;> (have h' : (none : Option A.T) = some τ' := h; cases h')

/-- Two runs of constant-time code that the analysis checks end in states
that agree on what the final taint says is public. -/
theorem agree_of_check {Pre : M.State → Prop} {Pub : M.State → M.State → Prop} {c : Prog M}
    (hct : ConstantTime M Pre Pub c) {τ τ' : A.T} {hc : Hint A.T} (h : A.check τ c hc = some τ')
    {s₁ s₂ s₁' s₂' : M.State} {t₁ t₂ : List Leak} (h₁ : Pre s₁) (h₂ : Pre s₂) (hp : Pub s₁ s₂)
    (ha : A.Agree τ s₁ s₂) (e₁ : Exec M c s₁ t₁ s₁') (e₂ : Exec M c s₂ t₂ s₂') :
    A.Agree τ' s₁' s₂' :=
  (check_sound h ha e₁ e₂ (r₁ := []) (r₂ := [])
    (by rw [List.append_nil, List.append_nil]; exact hct _ _ _ _ _ _ h₁ h₂ hp e₁ e₂)).2

end TaintCT

open Lean Meta Elab Tactic in
/-- `taint_decide` for a `TaintCT`: proves a decidable equation whose left
side contains `TaintCT.check A τ c ?hint`, computing the hint in compiled
code (`TaintCT.hintOfSize`) and having the kernel evaluate the goal. -/
meta def taintDecideCTAt (chunkSize : Expr) : TacticM Unit := do
  let g ← getMainGoal
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq?
    | throwError "taint_decide_ct: the goal is not an equation about `TaintCT.check A τ c h`"
  let some chk := lhs.find? (·.isAppOfArity ``TaintCT.check 5)
    | throwError "taint_decide_ct: the goal is not an equation about `TaintCT.check A τ c h`"
  let args := chk.getAppArgs
  let (m, a, τ, c, h) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  let tT ← whnfD (mkApp2 (mkConst ``TaintCT.T) m a)
  let hint := mkApp5 (mkConst ``TaintCT.hintOfSize) m a chunkSize τ c
  let instT ← synthInstance (mkApp (mkConst ``ToExpr [0]) tT)
  let hv ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``Taint.Hint.toExprNS) tT instT hint)
  if h.isMVar then h.mvarId!.assign hv
  evalTactic (← `(tactic| lit_decide))

open Lean Elab Tactic in
/-- Proves `(TaintCT.check A τ c ?hint)…`, as `taint_decide` does for a `Taint`. -/
elab "taint_decide_ct" : tactic => do
  let saved ← saveState
  try
    taintDecideCTAt (mkNatLit 1024)
  catch _ =>
    saved.restore
    taintDecideCTAt (mkConst ``Taint.chunk)

end VG
