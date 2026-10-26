module

public import VerifiedGarbage.Proof.Framework.Spectre
import VerifiedGarbage.Proof.Framework.Semantics
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.TCB.Artifact

/-!
# Fencing every branch target: constant time becomes speculative constant time

`Code.fence f c` puts the speculation barrier `f` (x86-64's `lfence`) at the
start of both branches of every `ite`, at the start of every loop body, and
after every loop: every place a mispredicted branch can lead. Sequentially
the barrier does nothing and leaks nothing (`exec f s = some s`,
`addrs f s = []`), so the fenced code has the same runs and traces as the
original (`Exec.fence_iff`), and so the same correctness and constant time
(`Verified.fence`).

Speculatively, a run with the barrier at every branch target stops at the
first instruction after any misprediction, before any instruction executes
transiently. So whatever the transient semantics (`S.sexec`, `S.saddrs`,
`S.sret` play no part), a speculative run of fenced code is a prefix of the
sequential run plus the value of the mispredicted condition, which the
sequential trace also leaks. Hence `specConstantTime_fence`: constant time,
however it was proven (taint analysis, `RelCT`, taint summaries), implies
speculative constant time of the fenced code, provided every run of an
instruction, call and return makes the same number of observations
(`LeakShape`), so that equal traces split equally between the parts of the
code.

`Code.fenceFn` also fences the function's entry, so that a run entered while
misspeculating (a call on a mispredicted path of the caller) leaks nothing
(`fenceFn_transient`), and no transient store of the function can reach
memory that its caller reads afterwards.
-/

@[expose] public section

namespace VG

/-- A branch target, starting with the barrier `f`. A cold `then` branch
(`Code.iteCold`) keeps its mark first, so that it stays out of line. -/
def Code.fenceArm {I C : Type} (f : I) : Code I C → Code I C
  | .seq (.seq (.block []) (.block [])) t => .seq (.seq (.block []) (.block [])) (.seq (.block [f]) t)
  | c => .seq (.block [f]) c

/-- `c` with the barrier `f` at every branch target: both branches of every
`ite`, every loop body, and after every loop. -/
def Code.fence {I C : Type} (f : I) : Code I C → Code I C
  | .block is => .block is
  | .seq a b => .seq (a.fence f) (b.fence f)
  | .ite c t e => .ite c ((t.fence f).fenceArm f) ((e.fence f).fenceArm f)
  | .loop b c => .seq (.loop ((b.fence f).fenceArm f) c) (.block [f])
  | .call n b => .call n (b.fence f)
  | .frame i b j => .frame i (b.fence f) j

/-- A function's code with the barrier `f` at its entry and every branch target. -/
def Code.fenceFn {I C : Type} (f : I) (c : Code I C) : Code I C :=
  .seq (.block [f]) (c.fence f)

variable {M : ISA}

/-- Every run of an instruction, call and return makes the same number of
observations, whatever the state. -/
structure LeakShape (M : ISA) : Prop where
  addrs : ∀ i s s', (M.addrs i s).length = (M.addrs i s').length
  callAddrs : ∀ s s', (M.callAddrs s).length = (M.callAddrs s').length
  retAddrs : ∀ s s', (M.retAddrs s).length = (M.retAddrs s').length

/-- `f` does nothing and leaks nothing sequentially. -/
structure Nop (M : ISA) (f : M.Instr) : Prop where
  exec : ∀ s, M.exec f s = some s
  addrs : ∀ s, M.addrs f s = []

/-! ## Sequential runs -/

section Seq

variable {f : M.Instr} (hn : Nop M f)
include hn

theorem Exec.fenceBlock_iff {s s' : M.State} {t : List Leak} :
    Exec M (.block [f]) s t s' ↔ s' = s ∧ t = [] := by
  rw [Exec.block_iff]
  simp only [execBlock, hn.exec, hn.addrs, List.map_nil, List.append_nil, Option.map_some,
    Option.some.injEq, Prod.mk.injEq]
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩, fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩⟩

theorem Exec.fenceSeq_iff {c : Prog M} {s s' : M.State} {t : List Leak} :
    Exec M (.seq (.block [f]) c) s t s' ↔ Exec M c s t s' := by
  constructor
  · intro h
    cases h with
    | seq a b =>
      obtain ⟨rfl, rfl⟩ := (Exec.fenceBlock_iff hn).mp a
      exact b
  · intro h
    exact (List.nil_append t) ▸ .seq ((Exec.fenceBlock_iff hn).mpr ⟨rfl, rfl⟩) h

theorem Exec.seqFence_iff {c : Prog M} {s s' : M.State} {t : List Leak} :
    Exec M (.seq c (.block [f])) s t s' ↔ Exec M c s t s' := by
  constructor
  · intro h
    cases h with
    | seq a b =>
      obtain ⟨rfl, rfl⟩ := (Exec.fenceBlock_iff hn).mp b
      rw [List.append_nil]; exact a
  · intro h
    exact (List.append_nil t) ▸ .seq h ((Exec.fenceBlock_iff hn).mpr ⟨rfl, rfl⟩)

omit hn in
theorem Exec.cold_iff {c : Prog M} {s s' : M.State} {t : List Leak} :
    Exec M (.seq (.seq (.block []) (.block [])) c) s t s' ↔ Exec M c s t s' := by
  have hb : ∀ {s s' : M.State} {t : List Leak}, Exec M (.block []) s t s' ↔ s' = s ∧ t = [] := by
    intro s s' t
    rw [Exec.block_iff]
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq]
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩, fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩⟩
  constructor
  · intro h
    cases h with
    | seq a b =>
      cases a with
      | seq x y =>
        obtain ⟨rfl, rfl⟩ := hb.mp x
        obtain ⟨rfl, rfl⟩ := hb.mp y
        exact b
  · intro h
    exact (List.nil_append t) ▸ .seq ((List.nil_append []) ▸
      .seq (hb.mpr ⟨rfl, rfl⟩) (hb.mpr ⟨rfl, rfl⟩)) h

theorem Exec.fenceArm_iff {c : Prog M} {s s' : M.State} {t : List Leak} :
    Exec M (c.fenceArm f) s t s' ↔ Exec M c s t s' := by
  unfold Code.fenceArm
  split
  · constructor
    · intro h
      exact (Exec.cold_iff).mpr ((Exec.fenceSeq_iff hn).mp ((Exec.cold_iff).mp h))
    · intro h
      exact (Exec.cold_iff).mpr ((Exec.fenceSeq_iff hn).mpr ((Exec.cold_iff).mp h))
  · exact Exec.fenceSeq_iff hn

omit hn in
theorem Exec.loop_congr {b b' : Prog M} {c : M.Cond}
    (h : ∀ s t s', Exec M b s t s' → Exec M b' s t s') {s s' : M.State} {t : List Leak}
    (e : Exec M (.loop b c) s t s') : Exec M (.loop b' c) s t s' := by
  generalize hl : Code.loop b c = l at e
  induction e with
  | loopExit a hc => cases hl; exact .loopExit (h _ _ _ a) hc
  | loopNext a hc _ _ ih₂ => cases hl; exact .loopNext (h _ _ _ a) hc (ih₂ rfl)
  | _ => cases hl

/-- The fenced code has the same runs as the original. -/
theorem Exec.fence_iff (c : Prog M) {s s' : M.State} {t : List Leak} :
    Exec M (c.fence f) s t s' ↔ Exec M c s t s' := by
  induction c generalizing s s' t with
  | block is => exact Iff.rfl
  | seq a b iha ihb =>
    constructor
    · intro h; cases h with | seq x y => exact .seq (iha.mp x) (ihb.mp y)
    · intro h; cases h with | seq x y => exact .seq (iha.mpr x) (ihb.mpr y)
  | ite c t e iht ihe =>
    constructor
    · intro h
      cases h with
      | iteT hc x => exact .iteT hc (iht.mp ((Exec.fenceArm_iff hn).mp x))
      | iteF hc x => exact .iteF hc (ihe.mp ((Exec.fenceArm_iff hn).mp x))
    · intro h
      cases h with
      | iteT hc x => exact .iteT hc ((Exec.fenceArm_iff hn).mpr (iht.mpr x))
      | iteF hc x => exact .iteF hc ((Exec.fenceArm_iff hn).mpr (ihe.mpr x))
  | loop b c ih =>
    show Exec M (.seq (.loop _ c) (.block [f])) s t s' ↔ _
    rw [Exec.seqFence_iff hn]
    exact ⟨Exec.loop_congr fun _ _ _ x => ih.mp ((Exec.fenceArm_iff hn).mp x),
      Exec.loop_congr fun _ _ _ x => (Exec.fenceArm_iff hn).mpr (ih.mpr x)⟩
  | call n b ih =>
    constructor
    · intro h; cases h with | call h₁ x h₂ => exact .call h₁ (ih.mp x) h₂
    · intro h; cases h with | call h₁ x h₂ => exact .call h₁ (ih.mpr x) h₂
  | frame i b j ih =>
    constructor
    · intro h; cases h with | frame h₁ x h₂ => exact .frame h₁ (ih.mp x) h₂
    · intro h; cases h with | frame h₁ x h₂ => exact .frame h₁ (ih.mpr x) h₂

theorem Exec.fenceFn_iff (c : Prog M) {s s' : M.State} {t : List Leak} :
    Exec M (c.fenceFn f) s t s' ↔ Exec M c s t s' :=
  (Exec.fenceSeq_iff hn).trans (Exec.fence_iff hn c)

theorem ConstantTime.fence {Pre : M.State → Prop} {Pub : M.State → M.State → Prop} {c : Prog M}
    (h : ConstantTime M Pre Pub c) : ConstantTime M Pre Pub (c.fenceFn f) :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ =>
    h _ _ _ _ _ _ h₁ h₂ hp ((Exec.fenceFn_iff hn c).mp e₁) ((Exec.fenceFn_iff hn c).mp e₂)

omit hn in
/-- Fencing keeps an artifact verified. -/
theorem Verified.fence {T : Target} {f : T.isa.Instr} (hn : Nop T.isa f) {c : Prog T.isa}
    {k : Contract T.isa} (h : Verified T c k) : Verified T (c.fenceFn f) k :=
  ⟨fun s hs => let ⟨t, s', e, h₁, h₂⟩ := h.1 s hs
    ⟨t, s', (Exec.fenceFn_iff hn c).mpr e, h₁, h₂⟩, h.2.1.fence hn, h.2.2⟩

end Seq

/-! ## Equal traces split equally -/

theorem execBlock_length (hs : LeakShape M) {is : List M.Instr} {s₁ s₂ s₁' s₂' : M.State}
    {t₁ t₂ : List Leak} (e₁ : execBlock M is s₁ = some (s₁', t₁))
    (e₂ : execBlock M is s₂ = some (s₂', t₂)) : t₁.length = t₂.length := by
  induction is generalizing s₁ s₂ s₁' s₂' t₁ t₂ with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2]
  | cons i is ih =>
    simp only [execBlock] at e₁ e₂
    split at e₁ <;> [cases e₁; rename_i a₁ x₁]
    split at e₂ <;> [cases e₂; rename_i a₂ x₂]
    simp only [Option.map_eq_some_iff, Prod.exists] at e₁ e₂
    obtain ⟨_, u₁, b₁, h₁⟩ := e₁
    obtain ⟨_, u₂, b₂, h₂⟩ := e₂
    simp only [Prod.mk.injEq] at h₁ h₂
    rw [← h₁.2, ← h₂.2, List.length_append, List.length_append, List.length_map,
      List.length_map, hs.addrs i s₁ s₂, ih b₁ b₂]

theorem map_addr_inj {a b : List Addr} (h : a.map Leak.addr = b.map Leak.addr) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.map_cons, List.cons.injEq, Leak.addr.injEq] at h
      rw [h.1, ih h.2]

theorem map_addr_append {a b : List Addr} {u v : List Leak}
    (h : a.map Leak.addr ++ u = b.map Leak.addr ++ v) (hl : a.length = b.length) :
    a = b ∧ u = v := by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp only [List.length_map, hl])
  exact ⟨map_addr_inj h₁, h₂⟩

/-- Two runs of the same code whose traces continue into equal traces
have equal traces. -/
theorem Exec.prefix_eq (hs : LeakShape M) {c : Prog M} {s₁ s₂ s₁' s₂' : M.State}
    {t₁ t₂ u₁ u₂ : List Leak} (e₁ : Exec M c s₁ t₁ s₁') (e₂ : Exec M c s₂ t₂ s₂')
    (h : t₁ ++ u₁ = t₂ ++ u₂) : t₁ = t₂ ∧ u₁ = u₂ := by
  induction e₁ generalizing s₂ t₂ s₂' u₁ u₂ with
  | block x₁ =>
    cases e₂ with
    | block x₂ => exact List.append_inj h (execBlock_length hs x₁ x₂)
  | seq _ _ ih₁ ih₂ =>
    cases e₂ with
    | seq a b =>
      simp only [List.append_assoc] at h
      obtain ⟨rfl, h'⟩ := ih₁ a h
      obtain ⟨rfl, rfl⟩ := ih₂ b h'
      exact ⟨rfl, rfl⟩
  | iteT _ _ ih =>
    cases e₂ with
    | iteT _ b =>
      simp only [List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := ih b h; exact ⟨rfl, rfl⟩
    | iteF _ _ => simp at h
  | iteF _ _ ih =>
    cases e₂ with
    | iteF _ b =>
      simp only [List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := ih b h; exact ⟨rfl, rfl⟩
    | iteT _ _ => simp at h
  | loopExit _ _ ih =>
    cases e₂ with
    | loopExit a _ =>
      simp only [List.append_assoc, List.cons_append, List.nil_append] at h
      obtain ⟨rfl, h'⟩ := ih a h
      simp only [List.cons.injEq, true_and] at h'
      exact ⟨rfl, h'⟩
    | loopNext a _ _ =>
      simp only [List.append_assoc, List.cons_append, List.nil_append] at h
      obtain ⟨rfl, h'⟩ := ih a h
      simp at h'
  | loopNext _ _ _ ih₁ ih₂ =>
    cases e₂ with
    | loopExit a _ =>
      simp only [List.append_assoc, List.cons_append, List.nil_append] at h
      obtain ⟨rfl, h'⟩ := ih₁ a h
      simp at h'
    | loopNext a _ b =>
      simp only [List.append_assoc, List.cons_append] at h
      obtain ⟨rfl, h'⟩ := ih₁ a h
      simp only [List.cons.injEq, true_and] at h'
      obtain ⟨rfl, rfl⟩ := ih₂ b h'
      exact ⟨rfl, rfl⟩
  | call _ _ _ ih =>
    cases e₂ with
    | call _ b _ =>
      simp only [List.append_assoc] at h
      obtain ⟨hc, h₁⟩ := map_addr_append h (hs.callAddrs _ _)
      obtain ⟨rfl, h₂⟩ := ih b h₁
      obtain ⟨hr, rfl⟩ := map_addr_append h₂ (hs.retAddrs _ _)
      rw [hc, hr]; exact ⟨rfl, rfl⟩
  | frame _ _ _ ih =>
    cases e₂ with
    | frame _ b _ =>
      simp only [List.append_assoc] at h
      obtain ⟨hc, h₁⟩ := map_addr_append h (hs.addrs _ _ _)
      obtain ⟨rfl, h₂⟩ := ih b h₁
      obtain ⟨hr, rfl⟩ := map_addr_append h₂ (hs.addrs _ _ _)
      rw [hc, hr]; exact ⟨rfl, rfl⟩

/-! ## Speculative runs -/

section Spec

variable {S : Spectre M} {f : M.Instr}

/-- How two speculative runs of fenced code end, given the final states of
the sequential runs: both stopped, or both done without misspeculating, in
those states. -/
def FRel (s₁' s₂' : M.State) : SOut M → SOut M → Prop
  | .halt, .halt => True
  | .done a ms D n, .done b ms' E m => a = s₁' ∧ b = s₂' ∧ ms = false ∧ ms' = false ∧ D = E ∧ n = m
  | _, _ => False

/-- As `FRel`, for a loop, which may end misspeculating (a mispredicted
exit); its states are then any. -/
def LRel (s₁' s₂' : M.State) : SOut M → SOut M → Prop
  | .halt, .halt => True
  | .done a ms D n, .done b ms' E m => ms = ms' ∧ D = E ∧ n = m ∧ (ms = false → a = s₁' ∧ b = s₂')
  | _, _ => False

theorem sblock_fence_true (hf : S.fence f = true) {is : List M.Instr} {s : M.State} {n : Nat}
    {t : List SLeak} {r : Option (M.State × Nat)} (e : SBlock S (f :: is) s true n t r) :
    t = [] ∧ r = none := by
  cases e with
  | stop => exact ⟨rfl, rfl⟩
  | fence _ => exact ⟨rfl, rfl⟩
  | cons h _ _ => simp [hf] at h

theorem sblock_fence_false (hn : Nop M f) {s : M.State} {n : Nat}
    {t : List SLeak} {r : Option (M.State × Nat)} (e : SBlock S [f] s false n t r) :
    t = [] ∧ (n = 0 ∧ r = none ∨ ∃ k, n = k + 1 ∧ r = some (s, k)) := by
  cases e with
  | stop => exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  | cons _ x b =>
    simp only [Spectre.run, Bool.false_eq_true, ↓reduceIte, hn.exec, Option.some.injEq] at x
    subst x
    cases b
    refine ⟨?_, .inr ⟨_, rfl, rfl⟩⟩
    simp only [Spectre.leaks, Bool.false_eq_true, ↓reduceIte, hn.addrs, List.map_nil,
      List.append_nil]

/-- A run reaching a fence while misspeculating stops there. -/
theorem sexec_fenceSeq_true (hf : S.fence f = true) {c : Prog M} {s : M.State} {D : List Bool}
    {n : Nat} {t : List SLeak} {o : SOut M} (e : SExec S (.seq (.block [f]) c) s true D n t o) :
    t = [] ∧ o = .halt := by
  cases e with
  | seq a _ => cases a with | blockDone b => exact absurd (sblock_fence_true hf b).2 nofun
  | seqHalt a => cases a with | blockHalt b => exact ⟨(sblock_fence_true hf b).1, rfl⟩

theorem sexec_fenceSeq_false (hn : Nop M f) {c : Prog M} {s : M.State} {D : List Bool}
    {n : Nat} {t : List SLeak} {o : SOut M} (e : SExec S (.seq (.block [f]) c) s false D n t o) :
    n = 0 ∧ t = [] ∧ o = .halt ∨ ∃ k, n = k + 1 ∧ SExec S c s false D k t o := by
  cases e with
  | seq a b =>
    cases a with
    | blockDone x =>
      obtain ⟨rfl, h⟩ := sblock_fence_false hn x
      rcases h with ⟨_, h⟩ | ⟨k, hk, h⟩
      · cases h
      · cases h; exact .inr ⟨_, hk, b⟩
  | seqHalt a =>
    cases a with
    | blockHalt x =>
      obtain ⟨rfl, h⟩ := sblock_fence_false hn x
      rcases h with ⟨hk, -⟩ | ⟨k, -, h⟩
      · exact .inl ⟨hk, rfl, rfl⟩
      · cases h

theorem sexec_cold {c : Prog M} {s : M.State} {ms : Bool} {D : List Bool} {n : Nat}
    {t : List SLeak} {o : SOut M} (e : SExec S (.seq (.seq (.block []) (.block [])) c) s ms D n t o) :
    SExec S c s ms D n t o := by
  cases e with
  | seq a b =>
    cases a with
    | seq x y =>
      cases x with
      | blockDone x =>
        cases x
        cases y with
        | blockDone y => cases y; exact b
  | seqHalt a =>
    cases a with
    | seq x y =>
      cases x with
      | blockDone x => cases x; cases y with | blockHalt y => cases y
    | seqHalt x => cases x with | blockHalt x => cases x

theorem sexec_fenceArm_true (hf : S.fence f = true) {c : Prog M} {s : M.State} {D : List Bool}
    {n : Nat} {t : List SLeak} {o : SOut M} (e : SExec S (c.fenceArm f) s true D n t o) :
    t = [] ∧ o = .halt := by
  unfold Code.fenceArm at e
  split at e
  · exact sexec_fenceSeq_true hf (sexec_cold e)
  · exact sexec_fenceSeq_true hf e

theorem sexec_fenceArm_false (hn : Nop M f) {c : Prog M} {s : M.State} {D : List Bool}
    {n : Nat} {t : List SLeak} {o : SOut M} (e : SExec S (c.fenceArm f) s false D n t o) :
    n = 0 ∧ t = [] ∧ o = .halt ∨ ∃ k, n = k + 1 ∧ SExec S c s false D k t o := by
  unfold Code.fenceArm at e
  split at e
  · rcases sexec_fenceSeq_false hn (sexec_cold e) with h | ⟨k, rfl, h⟩
    · exact .inl h
    · refine .inr ⟨k, rfl, ?_⟩
      exact (List.nil_append t) ▸ .seq ((List.nil_append []) ▸
        .seq (.blockDone .nil) (.blockDone .nil)) h
  · exact sexec_fenceSeq_false hn e

/-- Two runs of a fenced branch target, given the relation of runs of the
code it fences. -/
theorem fenceArm_rel (hn : Nop M f) {c : Prog M} {s₁ s₂ : M.State} {D : List Bool} {n : Nat}
    {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M} {R : SOut M → SOut M → Prop} (hR : R .halt .halt)
    (ih : ∀ k t₁ t₂ o₁ o₂, SExec S c s₁ false D k t₁ o₁ → SExec S c s₂ false D k t₂ o₂ →
      t₁ = t₂ ∧ R o₁ o₂)
    (e₁ : SExec S (c.fenceArm f) s₁ false D n t₁ o₁)
    (e₂ : SExec S (c.fenceArm f) s₂ false D n t₂ o₂) : t₁ = t₂ ∧ R o₁ o₂ := by
  rcases sexec_fenceArm_false hn e₁ with ⟨rfl, rfl, rfl⟩ | ⟨k, rfl, x₁⟩ <;>
  rcases sexec_fenceArm_false hn e₂ with ⟨h, rfl, rfl⟩ | ⟨k', h, x₂⟩
  · exact ⟨rfl, hR⟩
  · cases h
  · cases h
  · cases h; exact ih _ _ _ _ _ x₁ x₂

theorem sblock_seq (hs : LeakShape M) {is : List M.Instr} {s₁ s₂ s₁' s₂' : M.State}
    {T₁ T₂ : List Leak} (hT : T₁ = T₂) (x₁ : execBlock M is s₁ = some (s₁', T₁))
    (x₂ : execBlock M is s₂ = some (s₂', T₂)) {n : Nat} {t₁ t₂ : List SLeak}
    {r₁ r₂ : Option (M.State × Nat)} (e₁ : SBlock S is s₁ false n t₁ r₁)
    (e₂ : SBlock S is s₂ false n t₂ r₂) :
    t₁ = t₂ ∧ (r₁ = none ∧ r₂ = none ∨ ∃ k, r₁ = some (s₁', k) ∧ r₂ = some (s₂', k)) := by
  induction is generalizing s₁ s₂ T₁ T₂ n t₁ t₂ r₁ r₂ with
  | nil =>
    cases e₁; cases e₂
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at x₁ x₂
    rw [← x₁.1, ← x₂.1]
    exact ⟨rfl, .inr ⟨_, rfl, rfl⟩⟩
  | cons i is ih =>
    cases e₁ with
    | stop =>
      cases e₂ with
      | stop => exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
    | cons _ y₁ b₁ =>
      cases e₂ with
      | cons _ y₂ b₂ =>
        simp only [Spectre.run, Bool.false_eq_true, ↓reduceIte] at y₁ y₂
        simp only [execBlock, y₁, y₂, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at x₁ x₂
        obtain ⟨_, u₁, z₁, rfl, rfl⟩ := x₁
        obtain ⟨_, u₂, z₂, rfl, rfl⟩ := x₂
        obtain ⟨ha, hu⟩ := map_addr_append hT (hs.addrs _ _ _)
        obtain ⟨rfl, hr⟩ := ih hu z₁ z₂ b₁ b₂
        refine ⟨?_, hr⟩
        simp only [Spectre.leaks, Bool.false_eq_true, ↓reduceIte, ha]

/-- Two runs reaching the same barrier, with the same misspeculation flag
and fuel. -/
theorem fence_after (hn : Nop M f) (hf : S.fence f = true) {a b : M.State} {ms : Bool}
    {n : Nat} {t₁ t₂ : List SLeak} {r₁ r₂ : Option (M.State × Nat)}
    (y₁ : SBlock S [f] a ms n t₁ r₁) (y₂ : SBlock S [f] b ms n t₂ r₂) :
    t₁ = t₂ ∧ (r₁ = none ∧ r₂ = none ∨ ms = false ∧ ∃ k, r₁ = some (a, k) ∧ r₂ = some (b, k)) := by
  cases ms with
  | true =>
    obtain ⟨rfl, rfl⟩ := sblock_fence_true hf y₁
    obtain ⟨rfl, rfl⟩ := sblock_fence_true hf y₂
    exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  | false =>
    obtain ⟨rfl, h₁⟩ := sblock_fence_false hn y₁
    obtain ⟨rfl, h₂⟩ := sblock_fence_false hn y₂
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨k, rfl, rfl⟩ <;> rcases h₂ with ⟨h, rfl⟩ | ⟨k', h, rfl⟩
    · exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
    · cases h
    · cases h
    · cases h; exact ⟨rfl, .inr ⟨rfl, _, rfl, rfl⟩⟩

theorem sexec_loop_true (hf : S.fence f = true) {b : Prog M} {c : M.Cond} {s : M.State}
    {D : List Bool} {n : Nat} {t : List SLeak} {o : SOut M}
    (e : SExec S (.loop (b.fenceArm f) c) s true D n t o) : t = [] ∧ o = .halt := by
  cases e with
  | loopHalt a => exact sexec_fenceArm_true hf a
  | loopEnd a | loopExit a | loopNext a _ => exact absurd (sexec_fenceArm_true hf a).2 nofun

/-- The relation of two runs of fenced code, given equal traces of their
sequential runs. -/
theorem fence_rel (hs : LeakShape M) (hn : Nop M f) (hf : S.fence f = true) (c : Prog M) :
    ∀ {s₁ s₂ s₁' s₂' : M.State} {T₁ T₂ : List Leak} {D : List Bool} {n : Nat}
      {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M},
      Exec M c s₁ T₁ s₁' → Exec M c s₂ T₂ s₂' → T₁ = T₂ →
      SExec S (c.fence f) s₁ false D n t₁ o₁ → SExec S (c.fence f) s₂ false D n t₂ o₂ →
      t₁ = t₂ ∧ FRel s₁' s₂' o₁ o₂ := by
  induction c with
  | block is =>
    intro s₁ s₂ s₁' s₂' T₁ T₂ D n t₁ t₂ o₁ o₂ x₁ x₂ hT e₁ e₂
    rw [Exec.block_iff] at x₁ x₂
    cases e₁ with
    | blockDone b₁ =>
      cases e₂ with
      | blockDone b₂ =>
        obtain ⟨rfl, h⟩ := sblock_seq hs hT x₁ x₂ b₁ b₂
        rcases h with ⟨h, -⟩ | ⟨k, h₁, h₂⟩
        · cases h
        · cases h₁; cases h₂; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | blockHalt b₂ =>
        obtain ⟨-, h⟩ := sblock_seq hs hT x₁ x₂ b₁ b₂
        rcases h with ⟨h, -⟩ | ⟨k, -, h⟩ <;> cases h
    | blockHalt b₁ =>
      cases e₂ with
      | blockDone b₂ =>
        obtain ⟨-, h⟩ := sblock_seq hs hT x₁ x₂ b₁ b₂
        rcases h with ⟨-, h⟩ | ⟨k, h, -⟩ <;> cases h
      | blockHalt b₂ => exact ⟨(sblock_seq hs hT x₁ x₂ b₁ b₂).1, trivial⟩
  | seq a b iha ihb =>
    intro s₁ s₂ s₁' s₂' T₁ T₂ D n t₁ t₂ o₁ o₂ x₁ x₂ hT e₁ e₂
    cases x₁ with
    | seq xa₁ xb₁ =>
      cases x₂ with
      | seq xa₂ xb₂ =>
        obtain ⟨hA, hB⟩ := Exec.prefix_eq hs xa₁ xa₂ hT
        cases e₁ with
        | seq ea₁ eb₁ =>
          cases e₂ with
          | seq ea₂ eb₂ =>
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := iha xa₁ xa₂ hA ea₁ ea₂
            obtain ⟨rfl, hr⟩ := ihb xb₁ xb₂ hB eb₁ eb₂
            exact ⟨rfl, hr⟩
          | seqHalt ea₂ => exact (iha xa₁ xa₂ hA ea₁ ea₂).2.elim
        | seqHalt ea₁ =>
          cases e₂ with
          | seq ea₂ _ => exact (iha xa₁ xa₂ hA ea₁ ea₂).2.elim
          | seqHalt ea₂ => exact ⟨(iha xa₁ xa₂ hA ea₁ ea₂).1, trivial⟩
  | ite c t e iht ihe =>
    intro s₁ s₂ s₁' s₂' T₁ T₂ D n t₁ t₂ o₁ o₂ x₁ x₂ hT e₁ e₂
    -- The sequential runs take the same branch, and run it with equal traces.
    have key : ∃ v, M.eval c s₁ = some v ∧ M.eval c s₂ = some v ∧
        (v = true → ∃ U₁ U₂, Exec M t s₁ U₁ s₁' ∧ Exec M t s₂ U₂ s₂' ∧ U₁ = U₂) ∧
        (v = false → ∃ U₁ U₂, Exec M e s₁ U₁ s₁' ∧ Exec M e s₂ U₂ s₂' ∧ U₁ = U₂) := by
      cases x₁ with
      | iteT h₁ y₁ =>
        cases x₂ with
        | iteT h₂ y₂ =>
          simp only [List.cons.injEq, true_and] at hT
          exact ⟨true, h₁, h₂, fun _ => ⟨_, _, y₁, y₂, hT⟩, nofun⟩
        | iteF _ _ => simp at hT
      | iteF h₁ y₁ =>
        cases x₂ with
        | iteF h₂ y₂ =>
          simp only [List.cons.injEq, true_and] at hT
          exact ⟨false, h₁, h₂, nofun, fun _ => ⟨_, _, y₁, y₂, hT⟩⟩
        | iteT _ _ => simp at hT
    obtain ⟨v, hv₁, hv₂, kt, ke⟩ := key
    cases e₁ with
    | iteEnd =>
      cases e₂ with
      | iteEnd => rw [hv₁, hv₂]; exact ⟨rfl, trivial⟩
    | iteT a₁ =>
      cases e₂ with
      | iteT a₂ =>
        rw [hv₁] at a₁; rw [hv₂] at a₂; rw [hv₁, hv₂]
        cases v with
        | true =>
          obtain ⟨_, _, y₁, y₂, hU⟩ := kt rfl
          obtain ⟨rfl, hr⟩ := fenceArm_rel hn trivial
            (fun _ _ _ _ _ z₁ z₂ => iht y₁ y₂ hU z₁ z₂) a₁ a₂
          exact ⟨rfl, hr⟩
        | false =>
          obtain ⟨rfl, rfl⟩ := sexec_fenceArm_true hf a₁
          obtain ⟨rfl, rfl⟩ := sexec_fenceArm_true hf a₂
          exact ⟨rfl, trivial⟩
    | iteF a₁ =>
      cases e₂ with
      | iteF a₂ =>
        rw [hv₁] at a₁; rw [hv₂] at a₂; rw [hv₁, hv₂]
        cases v with
        | false =>
          obtain ⟨_, _, y₁, y₂, hU⟩ := ke rfl
          obtain ⟨rfl, hr⟩ := fenceArm_rel hn trivial
            (fun _ _ _ _ _ z₁ z₂ => ihe y₁ y₂ hU z₁ z₂) a₁ a₂
          exact ⟨rfl, hr⟩
        | true =>
          obtain ⟨rfl, rfl⟩ := sexec_fenceArm_true hf a₁
          obtain ⟨rfl, rfl⟩ := sexec_fenceArm_true hf a₂
          exact ⟨rfl, trivial⟩
  | loop b c ih =>
    intro s₁ s₂ s₁' s₂' T₁ T₂ D n t₁ t₂ o₁ o₂ x₁ x₂ hT e₁ e₂
    -- Runs of the fenced loop, before the barrier after it.
    have hloop : ∀ {s₁ s₂ s₁' s₂' : M.State} {T₁ T₂ : List Leak} {D : List Bool} {n : Nat}
        {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M},
        Exec M (.loop b c) s₁ T₁ s₁' → Exec M (.loop b c) s₂ T₂ s₂' → T₁ = T₂ →
        SExec S (.loop ((b.fence f).fenceArm f) c) s₁ false D n t₁ o₁ →
        SExec S (.loop ((b.fence f).fenceArm f) c) s₂ false D n t₂ o₂ →
        t₁ = t₂ ∧ LRel s₁' s₂' o₁ o₂ := by
      intro s₁ s₂ s₁' s₂' T₁ T₂ D n t₁ t₂ o₁ o₂ x₁ x₂ hT e₁ e₂
      generalize hl : Code.loop b c = l at x₁
      induction x₁ generalizing s₂ s₂' T₂ D n t₁ t₂ o₁ o₂ with
      | @loopExit _ _ _ y₁ U₁ xb₁ hc₁ =>
        cases hl
        cases x₂ with
        | loopExit xb₂ hc₂ =>
          obtain ⟨hU, -⟩ := Exec.prefix_eq hs xb₁ xb₂ hT
          have hb := fun {k t₁ t₂ o₁ o₂} => @fenceArm_rel _ _ _ hn _ _ _ D k t₁ t₂ o₁ o₂
            (FRel y₁ _) trivial (fun _ _ _ _ _ z₁ z₂ => ih xb₁ xb₂ hU z₁ z₂)
          cases e₁ with
          | loopHalt a₁ =>
            cases e₂ with
            | loopHalt a₂ => exact ⟨(hb a₁ a₂).1, trivial⟩
            | loopEnd a₂ | loopExit a₂ | loopNext a₂ _ => exact (hb a₁ a₂).2.elim
          | loopEnd a₁ =>
            cases e₂ with
            | loopHalt a₂ => exact (hb a₁ a₂).2.elim
            | loopEnd a₂ =>
              obtain ⟨rfl, rfl, rfl, -⟩ := hb a₁ a₂
              rw [hc₁, hc₂]; exact ⟨rfl, trivial⟩
            | loopExit a₂ | loopNext a₂ _ =>
              obtain ⟨-, -, -, -, h, -⟩ := (hb a₁ a₂).2; cases h
          | loopExit a₁ =>
            cases e₂ with
            | loopHalt a₂ => exact (hb a₁ a₂).2.elim
            | loopEnd a₂ | loopNext a₂ _ =>
              obtain ⟨-, -, -, -, h, -⟩ := (hb a₁ a₂).2; cases h
            | loopExit a₂ =>
              obtain ⟨rfl, rfl, rfl, rfl, rfl, h, rfl⟩ := hb a₁ a₂
              cases h
              rw [hc₁, hc₂]
              exact ⟨rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
          | loopNext a₁ r₁ =>
            cases e₂ with
            | loopHalt a₂ => exact (hb a₁ a₂).2.elim
            | loopEnd a₂ | loopExit a₂ =>
              obtain ⟨-, -, -, -, h, -⟩ := (hb a₁ a₂).2; cases h
            | loopNext a₂ r₂ =>
              obtain ⟨rfl, rfl, rfl, rfl, rfl, h, rfl⟩ := hb a₁ a₂
              cases h
              rw [hc₁] at r₁; rw [hc₂] at r₂; rw [hc₁, hc₂]
              obtain ⟨rfl, rfl⟩ := sexec_loop_true hf r₁
              obtain ⟨rfl, rfl⟩ := sexec_loop_true hf r₂
              exact ⟨rfl, trivial⟩
        | loopNext xb₂ _ _ =>
          obtain ⟨-, h'⟩ := Exec.prefix_eq hs xb₁ xb₂ hT
          simp at h'
      | @loopNext _ _ _ y₁ _ U₁ V₁ xb₁ hc₁ xl₁ _ ihl =>
        cases hl
        cases x₂ with
        | loopExit xb₂ _ =>
          obtain ⟨-, h'⟩ := Exec.prefix_eq hs xb₁ xb₂ hT
          simp at h'
        | loopNext xb₂ hc₂ xl₂ =>
          obtain ⟨hU, hV⟩ := Exec.prefix_eq hs xb₁ xb₂ hT
          simp only [List.cons.injEq, true_and] at hV
          have hb := fun {k t₁ t₂ o₁ o₂} => @fenceArm_rel _ _ _ hn _ _ _ D k t₁ t₂ o₁ o₂
            (FRel y₁ _) trivial (fun _ _ _ _ _ z₁ z₂ => ih xb₁ xb₂ hU z₁ z₂)
          cases e₁ with
          | loopHalt a₁ =>
            cases e₂ with
            | loopHalt a₂ => exact ⟨(hb a₁ a₂).1, trivial⟩
            | loopEnd a₂ | loopExit a₂ | loopNext a₂ _ => exact (hb a₁ a₂).2.elim
          | loopEnd a₁ =>
            cases e₂ with
            | loopHalt a₂ => exact (hb a₁ a₂).2.elim
            | loopEnd a₂ =>
              obtain ⟨rfl, rfl, rfl, -⟩ := hb a₁ a₂
              rw [hc₁, hc₂]; exact ⟨rfl, trivial⟩
            | loopExit a₂ | loopNext a₂ _ =>
              obtain ⟨-, -, -, -, h, -⟩ := (hb a₁ a₂).2; cases h
          | loopExit a₁ =>
            cases e₂ with
            | loopHalt a₂ => exact (hb a₁ a₂).2.elim
            | loopEnd a₂ | loopNext a₂ _ =>
              obtain ⟨-, -, -, -, h, -⟩ := (hb a₁ a₂).2; cases h
            | loopExit a₂ =>
              obtain ⟨rfl, rfl, rfl, rfl, rfl, h, rfl⟩ := hb a₁ a₂
              cases h
              rw [hc₁, hc₂]
              exact ⟨rfl, rfl, rfl, rfl, nofun⟩
          | loopNext a₁ r₁ =>
            cases e₂ with
            | loopHalt a₂ => exact (hb a₁ a₂).2.elim
            | loopEnd a₂ | loopExit a₂ =>
              obtain ⟨-, -, -, -, h, -⟩ := (hb a₁ a₂).2; cases h
            | loopNext a₂ r₂ =>
              obtain ⟨rfl, rfl, rfl, rfl, rfl, h, rfl⟩ := hb a₁ a₂
              cases h
              rw [hc₁] at r₁; rw [hc₂] at r₂; rw [hc₁, hc₂]
              obtain ⟨rfl, hr⟩ := ihl xl₂ hV r₁ r₂ rfl
              exact ⟨rfl, hr⟩
      | _ => cases hl
    -- The barrier after the loop.
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq a₂ b₂ =>
        obtain ⟨rfl, hms, rfl, rfl, hst⟩ := hloop x₁ x₂ hT a₁ a₂
        subst hms
        cases b₁ with
        | blockDone y₁ =>
          cases b₂ with
          | blockDone y₂ =>
            obtain ⟨rfl, h⟩ := fence_after hn hf y₁ y₂
            rcases h with ⟨h, -⟩ | ⟨rfl, k, h₁, h₂⟩
            · cases h
            · cases h₁; cases h₂
              obtain ⟨rfl, rfl⟩ := hst rfl
              exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          | blockHalt y₂ =>
            obtain ⟨-, h⟩ := fence_after hn hf y₁ y₂
            rcases h with ⟨h, -⟩ | ⟨-, k, -, h⟩ <;> cases h
        | blockHalt y₁ =>
          cases b₂ with
          | blockDone y₂ =>
            obtain ⟨-, h⟩ := fence_after hn hf y₁ y₂
            rcases h with ⟨-, h⟩ | ⟨-, k, h, -⟩ <;> cases h
          | blockHalt y₂ => exact ⟨by rw [(fence_after hn hf y₁ y₂).1], trivial⟩
      | seqHalt a₂ => exact (hloop x₁ x₂ hT a₁ a₂).2.elim
    | seqHalt a₁ =>
      cases e₂ with
      | seq a₂ _ => exact (hloop x₁ x₂ hT a₁ a₂).2.elim
      | seqHalt a₂ => exact ⟨(hloop x₁ x₂ hT a₁ a₂).1, trivial⟩
  | call nm b ih =>
    intro s₁ s₂ s₁' s₂' T₁ T₂ D n t₁ t₂ o₁ o₂ x₁ x₂ hT e₁ e₂
    cases x₁ with
    | call hc₁ xb₁ hr₁ =>
      cases x₂ with
      | call hc₂ xb₂ hr₂ =>
        simp only [List.append_assoc] at hT
        obtain ⟨hca, hT₁⟩ := map_addr_append hT (hs.callAddrs _ _)
        obtain ⟨hU, hT₂⟩ := Exec.prefix_eq hs xb₁ xb₂ hT₁
        have hra := map_addr_inj hT₂
        cases e₁ with
        | callHalt hc₁' a₁ =>
          rw [hc₁] at hc₁'; cases hc₁'
          cases e₂ with
          | callHalt hc₂' a₂ =>
            rw [hc₂] at hc₂'; cases hc₂'
            obtain ⟨rfl, -⟩ := ih xb₁ xb₂ hU a₁ a₂
            rw [hca]; exact ⟨rfl, trivial⟩
          | call hc₂' a₂ _ =>
            rw [hc₂] at hc₂'; cases hc₂'
            exact (ih xb₁ xb₂ hU a₁ a₂).2.elim
        | call hc₁' a₁ hr₁' =>
          rw [hc₁] at hc₁'; cases hc₁'
          cases e₂ with
          | callHalt hc₂' a₂ =>
            rw [hc₂] at hc₂'; cases hc₂'
            exact (ih xb₁ xb₂ hU a₁ a₂).2.elim
          | call hc₂' a₂ hr₂' =>
            rw [hc₂] at hc₂'; cases hc₂'
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih xb₁ xb₂ hU a₁ a₂
            simp only [Spectre.ret, Bool.false_eq_true, ↓reduceIte] at hr₁' hr₂'
            rw [hr₁] at hr₁'; cases hr₁'
            rw [hr₂] at hr₂'; cases hr₂'
            rw [hca, hra]
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | frame i b j ih =>
    intro s₁ s₂ s₁' s₂' T₁ T₂ D n t₁ t₂ o₁ o₂ x₁ x₂ hT e₁ e₂
    cases x₁ with
    | frame hp₁ xb₁ hq₁ =>
      cases x₂ with
      | frame hp₂ xb₂ hq₂ =>
        simp only [List.append_assoc] at hT
        obtain ⟨hpa, hT₁⟩ := map_addr_append hT (hs.addrs _ _ _)
        obtain ⟨hU, hT₂⟩ := Exec.prefix_eq hs xb₁ xb₂ hT₁
        have hqa := map_addr_inj hT₂
        cases e₁ with
        | frameHalt hp₁' a₁ =>
          rw [hp₁] at hp₁'; cases hp₁'
          cases e₂ with
          | frameHalt hp₂' a₂ =>
            rw [hp₂] at hp₂'; cases hp₂'
            obtain ⟨rfl, -⟩ := ih xb₁ xb₂ hU a₁ a₂
            rw [hpa]; exact ⟨rfl, trivial⟩
          | frame hp₂' a₂ _ =>
            rw [hp₂] at hp₂'; cases hp₂'
            exact (ih xb₁ xb₂ hU a₁ a₂).2.elim
        | frame hp₁' a₁ hq₁' =>
          rw [hp₁] at hp₁'; cases hp₁'
          cases e₂ with
          | frameHalt hp₂' a₂ =>
            rw [hp₂] at hp₂'; cases hp₂'
            exact (ih xb₁ xb₂ hU a₁ a₂).2.elim
          | frame hp₂' a₂ hq₂' =>
            rw [hp₂] at hp₂'; cases hp₂'
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih xb₁ xb₂ hU a₁ a₂
            rw [hq₁] at hq₁'; cases hq₁'
            rw [hq₂] at hq₂'; cases hq₂'
            rw [hpa, hqa]
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A run of fenced code entered while misspeculating leaks nothing: it
stops at the barrier at its entry. -/
theorem fenceFn_transient (hf : S.fence f = true) {c : Prog M} {s : M.State} {D : List Bool}
    {n : Nat} {t : List SLeak} {o : SOut M} (e : SExec S (c.fenceFn f) s true D n t o) :
    t = [] ∧ o = .halt :=
  sexec_fenceSeq_true hf e

/-- **Fencing every branch target makes constant-time code speculatively
constant time**, for any transient semantics in which `f` is a barrier. -/
theorem specConstantTime_fence (hs : LeakShape M) (hn : Nop M f) (hf : S.fence f = true)
    {Pre : M.State → Prop} {Pub : M.State → M.State → Prop} {c : Prog M}
    (hv : ∀ s, Pre s → ∃ t s', Exec M c s t s') (hct : ConstantTime M Pre Pub c) :
    SpecConstantTime S Pre Pub (c.fenceFn f) := by
  intro s₁ s₂ D n t₁ t₂ o₁ o₂ h₁ h₂ hp e₁ e₂
  obtain ⟨T₁, s₁', x₁⟩ := hv s₁ h₁
  obtain ⟨T₂, s₂', x₂⟩ := hv s₂ h₂
  have hT := hct _ _ _ _ _ _ h₁ h₂ hp x₁ x₂
  rcases sexec_fenceSeq_false hn e₁ with ⟨rfl, rfl, rfl⟩ | ⟨k, rfl, y₁⟩ <;>
  rcases sexec_fenceSeq_false hn e₂ with ⟨h, rfl, rfl⟩ | ⟨k', h, y₂⟩
  · rfl
  · cases h
  · cases h
  · cases h; exact (fence_rel hs hn hf c x₁ x₂ hT y₁ y₂).1

end Spec

/-- **A verified artifact, fenced, is verified and speculatively constant
time.** -/
theorem Verified.fence_spec {T : Target} {f : T.isa.Instr} (hs : LeakShape T.isa)
    (hn : Nop T.isa f) {S : Spectre T.isa} (hf : S.fence f = true) {c : Prog T.isa}
    {k : Contract T.isa} (h : Verified T c k) :
    Verified T (c.fenceFn f) k ∧ SpecConstantTime S k.pre k.pub (c.fenceFn f) :=
  ⟨h.fence hn, specConstantTime_fence hs hn hf
    (fun s hs => let ⟨t, s', e, _⟩ := h.1 s hs; ⟨t, s', e⟩) h.2.1⟩

end VG
