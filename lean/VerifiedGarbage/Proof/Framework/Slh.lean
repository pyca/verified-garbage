module

public import VerifiedGarbage.Proof.Framework.FenceMix
public import VerifiedGarbage.Proof.Framework.SpectreTaint
import VerifiedGarbage.Proof.Framework.Semantics

/-!
# Speculative load hardening at branch targets (prototype)

A barrier at a branch target (`Fence.lean`) stops a mispredicted run, at a
cost of tens of cycles at every branch. Hardening lets the mispredicted run
go on, but first makes what it computes addresses and conditions from the
same in both runs: at each branch target, a *prologue* (`pt c` where the
branch was taken because `c` holds, `pe c` where it was not) changes nothing
when the branch was predicted correctly, and when it was mispredicted
overwrites registers with values both runs agree on (on x86-64,
`cmov¬c r, rsp`, `X86_64/Slh.lean`).

* `Code.harden pt pe c`: the prologues at both branches of every `ite`; a
  loop `do b while c` becomes `b; if c then (do { pt c; b } while c); pe c`,
  so that every entry of the loop body (the first and each back edge) has
  the flags of the loop condition holding.
* `Exec.harden_iff`: the hardened code has the same runs, since the
  prologues change nothing where the condition is as the branch went.
* `scheck`: the analysis of the transient runs: the taint analysis of the
  hardened code, where each branch target starts from what both a run that
  was already misspeculating and one that has just mispredicted agree on:
  the meet of the taint after the prologue and `τR`, what the prologue
  establishes (`PrologueOk`).
* `slh_rel`, `specSafe_harden`: speculative safety from constant time, as
  `fence_rel` and `specSafe_fenceFn`, with `scheck` from no public data at
  all for the transient runs.
-/

@[expose] public section

namespace VG

/-- A branch target, starting with the prologue `is`. A cold `then` branch
keeps its mark first. -/
def Code.prefixArm {I C : Type} (is : List I) : Code I C → Code I C
  | .seq (.seq (.block []) (.block [])) t => .seq (.seq (.block []) (.block [])) (.seq (.block is) t)
  | c => .seq (.block is) c

/-- `c` with the prologues `pt c` and `pe c` at the branch targets of each
condition `c`. -/
def Code.harden {I C : Type} (pt pe : C → List I) : Code I C → Code I C
  | .block is => .block is
  | .seq a b => .seq (a.harden pt pe) (b.harden pt pe)
  | .ite c t e => .ite c ((t.harden pt pe).prefixArm (pt c)) (.seq (.block (pe c)) (e.harden pt pe))
  | .loop b c => .seq (b.harden pt pe)
      (.seq (.ite c (.loop (.seq (.block (pt c)) (b.harden pt pe)) c) (.block [])) (.block (pe c)))
  | .call n b => .call n (b.harden pt pe)
  | .frame i b j => .frame i (b.harden pt pe) j

variable {M : ISA}

theorem sblock_nil_inv {S : Spectre M} {s : M.State} {ms : Bool} {n : Nat} {t : List SLeak}
    {r : Option (M.State × Nat)} (e : SBlock S [] s ms n t r) : t = [] ∧ r = some (s, n) := by
  cases e; exact ⟨rfl, rfl⟩

theorem sblock_cons_inv {S : Spectre M} {i : M.Instr} {is : List M.Instr} {s : M.State} {ms : Bool}
    {n : Nat} {t : List SLeak} {r : Option (M.State × Nat)} (e : SBlock S (i :: is) s ms n t r) :
    (n = 0 ∧ t = [] ∧ r = none) ∨ (ms = true ∧ S.fence i = true ∧ t = [] ∧ r = none) ∨
      (∃ s₁ k t', (ms && S.fence i) = false ∧ n = k + 1 ∧ S.run ms i s = some s₁ ∧
        SBlock S is s₁ ms k t' r ∧ t = (S.leaks ms i s).map .addr ++ t') := by
  cases e with
  | stop => exact .inl ⟨rfl, rfl, rfl⟩
  | fence h => exact .inr (.inl ⟨rfl, h, rfl, rfl⟩)
  | cons h x b => exact .inr (.inr ⟨_, _, _, h, rfl, x, b, rfl⟩)

/-! ## Sequential runs -/

section Seq

variable {pt pe : M.Cond → List M.Instr}
  (hpt : ∀ c s, M.eval c s = some true → execBlock M (pt c) s = some (s, []))
  (hpe : ∀ c s, M.eval c s = some false → execBlock M (pe c) s = some (s, []))

theorem Exec.nopBlock_iff {is : List M.Instr} {s : M.State}
    (h : execBlock M is s = some (s, [])) {x : Prog M} {s' : M.State} {t : List Leak} :
    Exec M (.seq (.block is) x) s t s' ↔ Exec M x s t s' := by
  constructor
  · intro e
    cases e with
    | seq a b =>
      rw [Exec.block_iff, h] at a
      cases a
      exact b
  · intro e
    exact (List.nil_append t) ▸ .seq (Exec.block_iff.mpr h) e

theorem Exec.prefixArm_iff {is : List M.Instr} {s : M.State}
    (h : execBlock M is s = some (s, [])) {x : Prog M} {s' : M.State} {t : List Leak} :
    Exec M (x.prefixArm is) s t s' ↔ Exec M x s t s' := by
  unfold Code.prefixArm
  split
  · exact Exec.cold_iff.trans ((Exec.nopBlock_iff h).trans Exec.cold_iff.symm)
  · exact Exec.nopBlock_iff h

theorem Exec.loop_eval {b : Prog M} {c : M.Cond} {s s' : M.State} {t : List Leak}
    (e : Exec M (.loop b c) s t s') : M.eval c s' = some false := by
  generalize hl : Code.loop b c = l at e
  induction e with
  | loopExit _ hc => cases hl; exact hc
  | loopNext _ _ _ _ ih => exact ih hl
  | _ => cases hl

include hpt in
/-- The loop with the prologue at the start of its body, entered with the
condition holding, has the runs of the loop. -/
theorem Exec.loopPt_iff {b : Prog M} {c : M.Cond} {s s' : M.State} {t : List Leak}
    (hc : M.eval c s = some true) :
    Exec M (.loop (.seq (.block (pt c)) b) c) s t s' ↔ Exec M (.loop b c) s t s' := by
  constructor
  · intro e
    generalize hl : Code.loop (.seq (.block (pt c)) b) c = l at e
    induction e with
    | loopExit a hx =>
      cases hl
      exact .loopExit ((Exec.nopBlock_iff (hpt _ _ hc)).mp a) hx
    | loopNext a hx _ _ ih =>
      cases hl
      exact .loopNext ((Exec.nopBlock_iff (hpt _ _ hc)).mp a) hx (ih hx rfl)
    | _ => cases hl
  · intro e
    generalize hl : Code.loop b c = l at e
    induction e with
    | loopExit a hx =>
      cases hl
      exact .loopExit ((Exec.nopBlock_iff (hpt _ _ hc)).mpr a) hx
    | loopNext a hx _ _ ih =>
      cases hl
      exact .loopNext ((Exec.nopBlock_iff (hpt _ _ hc)).mpr a) hx (ih hx rfl)
    | _ => cases hl

include hpt hpe in
/-- The hardened code has the same runs as the original. -/
theorem Exec.harden_iff (c : Prog M) {s s' : M.State} {t : List Leak} :
    Exec M (c.harden pt pe) s t s' ↔ Exec M c s t s' := by
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
      | iteT hc x => exact .iteT hc (iht.mp ((Exec.prefixArm_iff (hpt _ _ hc)).mp x))
      | iteF hc x => exact .iteF hc (ihe.mp ((Exec.nopBlock_iff (hpe _ _ hc)).mp x))
    · intro h
      cases h with
      | iteT hc x => exact .iteT hc ((Exec.prefixArm_iff (hpt _ _ hc)).mpr (iht.mpr x))
      | iteF hc x => exact .iteF hc ((Exec.nopBlock_iff (hpe _ _ hc)).mpr (ihe.mpr x))
  | loop b c ih =>
    have hb : ∀ {s s' t}, Exec M (b.harden pt pe) s t s' → Exec M b s t s' := ih.mp
    have hb' : ∀ {s s' t}, Exec M b s t s' → Exec M (b.harden pt pe) s t s' := ih.mpr
    constructor
    · intro h
      cases h with
      | seq x y =>
        cases y with
        | seq i p =>
          rw [Exec.block_iff] at p
          cases i with
          | iteT hc l =>
            have hx := Exec.loop_eval l
            rw [hpe _ _ (by
              have := (Exec.loopPt_iff hpt hc).mp l
              exact Exec.loop_eval this)] at p
            cases p
            have l' := (Exec.loopPt_iff hpt hc).mp l
            have l'' : Exec M (.loop b c) _ _ _ := Exec.loop_congr (fun _ _ _ z => hb z) l'
            simpa [List.append_assoc] using Exec.loopNext (hb x) hc l''
          | iteF hc l =>
            rw [Exec.block_iff] at l
            simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at l
            obtain ⟨rfl, rfl⟩ := l
            rw [hpe _ _ hc] at p
            cases p
            simpa using Exec.loopExit (hb x) hc
    · intro h
      cases h with
      | loopExit a hc =>
        have p := hpe _ _ hc
        have := Exec.seq (hb' a) (Exec.seq (Exec.iteF (th := Code.loop (.seq (.block (pt c))
          (b.harden pt pe)) c) hc (Exec.block (is := []) (t := []) rfl)) (Exec.block p))
        simp only [List.append_nil] at this
        exact this
      | loopNext a hc r =>
        have r' := (Exec.loopPt_iff hpt hc).mpr (Exec.loop_congr (fun _ _ _ z => hb' z) r)
        have p := hpe _ _ (Exec.loop_eval r)
        have := Exec.seq (hb' a) (Exec.seq (Exec.iteT (el := Code.block []) hc r') (Exec.block p))
        simp only [List.append_nil] at this
        exact this
  | call n b ih =>
    constructor
    · intro h; cases h with | call h₁ x h₂ => exact .call h₁ (ih.mp x) h₂
    · intro h; cases h with | call h₁ x h₂ => exact .call h₁ (ih.mpr x) h₂
  | frame i b j ih =>
    constructor
    · intro h; cases h with | frame h₁ x h₂ => exact .frame h₁ (ih.mp x) h₂
    · intro h; cases h with | frame h₁ x h₂ => exact .frame h₁ (ih.mpr x) h₂

end Seq

/-! ## Transient runs -/

/-- The analysis of the transient runs of `c.harden pt pe`: the taint
analysis (`Taint.check`), but each branch target, after its prologue, starts
from the meet of the taint after the prologue (what runs already
misspeculating agree on) and `τR` (what runs that have just mispredicted
agree on, `PrologueOk`). A loop's hint is `.seq σ h₁ h₂`: `h₁` for its first
body, `σ` the invariant before the prologue at the start of the loop body,
`h₂` for the body in the loop. -/
def scheck (A : Taint M) (τR : A.T) (pt pe : M.Cond → List M.Instr) :
    A.T → Prog M → Taint.Hint A.T → Option A.T
  | τ, .block is, .block ms cs => A.checkChunks cs τ is ms
  | τ, .seq a b, .seq mid h₁ h₂ =>
    (scheck A τR pt pe τ a h₁).bind fun τ' => if A.le mid τ' then scheck A τR pt pe mid b h₂ else none
  | τ, .ite c t e, .ite h₁ h₂ =>
    if A.condPub τ c then
      (A.checkBlock τ (pt c)).bind fun τt => (A.checkBlock τ (pe c)).bind fun τe =>
        (scheck A τR pt pe (A.meet τt τR) t h₁).bind fun τ₁ =>
          (scheck A τR pt pe (A.meet τe τR) e h₂).map fun τ₂ => A.meet τ₁ τ₂
    else none
  | τ, .loop b c, .seq σ h₁ h₂ =>
    (scheck A τR pt pe τ b h₁).bind fun τ₀ =>
      if A.condPub τ₀ c && A.le σ τ₀ then
        (A.checkBlock σ (pt c)).bind fun σp =>
          (scheck A τR pt pe (A.meet σp τR) b h₂).bind fun σ' =>
            if A.le σ σ' && A.condPub σ' c then
              (A.checkBlock (A.meet σ' τ₀) (pe c)).map fun τx => A.meet τx τR
            else none
      else none
  | τ, .call _ b, .call h => (A.call τ).bind fun τ₁ => (scheck A τR pt pe τ₁ b h).bind A.ret
  | τ, .frame i b j, .frame h =>
    (A.push τ i).bind fun τ₁ => (scheck A τR pt pe τ₁ b h).bind fun τ₂ => A.pop τ₂ j
  | _, _, _ => none

section Transient

variable {S : Spectre M} {A : Taint M} {τR : A.T} {pt pe : M.Cond → List M.Instr}
  {Inv : M.State → M.State → Prop}

/-- The prologues establish `τR` in runs that have just mispredicted: in
states that agree on `Inv`, where the condition is the opposite of where
the branch went. -/
structure PrologueOk (S : Spectre M) (A : Taint M) (τR : A.T) (pt pe : M.Cond → List M.Instr)
    (Inv : M.State → M.State → Prop) : Prop where
  pt : ∀ {c s₁ s₂ n t₁ t₂ r₁ r₂}, Inv s₁ s₂ → M.eval c s₁ = some false → M.eval c s₂ = some false →
    SBlock S (pt c) s₁ true n t₁ r₁ → SBlock S (pt c) s₂ true n t₂ r₂ →
    t₁ = t₂ ∧ Taint.BRel A τR r₁ r₂
  pe : ∀ {c s₁ s₂ n t₁ t₂ r₁ r₂}, Inv s₁ s₂ → M.eval c s₁ = some true → M.eval c s₂ = some true →
    SBlock S (pe c) s₁ true n t₁ r₁ → SBlock S (pe c) s₂ true n t₂ r₂ →
    t₁ = t₂ ∧ Taint.BRel A τR r₁ r₂

theorem Taint.BRel.mono {τ σ : A.T} {r₁ r₂ : Option (M.State × Nat)}
    (hm : ∀ a b, A.Agree τ a b → A.Agree σ a b) (h : Taint.BRel A τ r₁ r₂) : Taint.BRel A σ r₁ r₂ := by
  rcases r₁ with _ | ⟨a, k⟩ <;> rcases r₂ with _ | ⟨b, l⟩ <;> simp only [Taint.BRel] at h ⊢
  exact ⟨h.1, hm _ _ h.2⟩

theorem sexec_cold_intro {x : Prog M} {s : M.State} {ms : Bool} {D : List Bool}
    {n : Nat} {t : List SLeak} {o : SOut M} (e : SExec S x s ms D n t o) :
    SExec S (.seq (.seq (.block []) (.block [])) x) s ms D n t o :=
  (List.nil_append t) ▸ .seq ((List.nil_append []) ▸ .seq (.blockDone .nil) (.blockDone .nil)) e

theorem sexec_prefixArm {is : List M.Instr} {x : Prog M} {s : M.State} {ms : Bool} {D : List Bool}
    {n : Nat} {t : List SLeak} {o : SOut M} (e : SExec S (x.prefixArm is) s ms D n t o) :
    SExec S (.seq (.block is) x) s ms D n t o := by
  unfold Code.prefixArm at e
  split at e
  · cases sexec_cold e with
    | seq a b => exact .seq a (sexec_cold_intro b)
    | seqHalt a => exact .seqHalt a
  · exact e

/-- Two runs of a block followed by code, given how the block's runs end and
how the code's runs from states related by `R` end. -/
theorem seqBlock_rel {is : List M.Instr} {x : Prog M} {s₁ s₂ : M.State} {ms : Bool} {D : List Bool}
    {n : Nat} {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M} {τ : A.T} {Q : SOut M → SOut M → Prop}
    (hQ : Q .halt .halt)
    (hb : ∀ {k t₁ t₂ r₁ r₂}, SBlock S is s₁ ms k t₁ r₁ → SBlock S is s₂ ms k t₂ r₂ →
      t₁ = t₂ ∧ Taint.BRel A τ r₁ r₂)
    (hx : ∀ {a b k t₁ t₂ o₁ o₂}, A.Agree τ a b → SExec S x a ms D k t₁ o₁ → SExec S x b ms D k t₂ o₂ →
      t₁ = t₂ ∧ Q o₁ o₂)
    (e₁ : SExec S (.seq (.block is) x) s₁ ms D n t₁ o₁) (e₂ : SExec S (.seq (.block is) x) s₂ ms D n t₂ o₂) :
    t₁ = t₂ ∧ Q o₁ o₂ := by
  cases e₁ with
  | seq a₁ b₁ =>
    cases a₁ with
    | blockDone y₁ =>
      cases e₂ with
      | seq a₂ b₂ =>
        cases a₂ with
        | blockDone y₂ =>
          obtain ⟨rfl, rfl, h⟩ := hb y₁ y₂
          obtain ⟨rfl, hq⟩ := hx h b₁ b₂
          exact ⟨rfl, hq⟩
      | seqHalt a₂ => cases a₂ with | blockHalt y₂ => exact (hb y₁ y₂).2.elim
  | seqHalt a₁ =>
    cases a₁ with
    | blockHalt y₁ =>
      cases e₂ with
      | seq a₂ _ => cases a₂ with | blockDone y₂ => exact (hb y₁ y₂).2.elim
      | seqHalt a₂ => cases a₂ with | blockHalt y₂ => exact ⟨(hb y₁ y₂).1, hQ⟩

theorem sexec_mono {c : Prog M} {s : M.State} {m : Bool} {D : List Bool} {n : Nat} {t : List SLeak}
    {o : SOut M} (e : SExec S c s m D n t o) :
    ∀ {s' ms D' n'}, o = .done s' ms D' n' → m = true → ms = true := by
  induction e with
  | blockDone _ => intro _ _ _ _ ho hm; cases ho; exact hm
  | seq _ _ ih₁ ih₂ => intro _ _ _ _ ho hm; exact ih₂ ho (ih₁ rfl hm)
  | iteT _ ih => intro _ _ _ _ ho hm; exact ih ho (by simp [Spectre.mis, hm])
  | iteF _ ih => intro _ _ _ _ ho hm; exact ih ho (by simp [Spectre.mis, hm])
  | loopExit _ ih => intro _ _ _ _ ho hm; cases ho; simp [Spectre.mis, ih rfl hm]
  | loopNext _ _ ih₁ ih₂ => intro _ _ _ _ ho hm; exact ih₂ ho (by simp [Spectre.mis, ih₁ rfl hm])
  | call _ _ _ ih => intro _ _ _ _ ho hm; cases ho; exact ih rfl hm
  | frame _ _ _ ih => intro _ _ _ _ ho hm; cases ho; exact ih rfl hm
  | _ => intro _ _ _ _ ho; cases ho

/-- A run that starts misspeculating ends misspeculating. -/
theorem sexec_true {c : Prog M} {s s' : M.State} {D D' : List Bool} {n n' : Nat} {t : List SLeak}
    {ms : Bool} (e : SExec S c s true D n t (.done s' ms D' n')) : ms = true :=
  sexec_mono e rfl rfl

/-- Two transient runs of code followed by more code. -/
theorem seq_orel {a b : Prog M} {τ₁ τ₂ : A.T} {s₁ s₂ : M.State} {D : List Bool} {n : Nat}
    {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M}
    (ha : ∀ {D n t₁ t₂ o₁ o₂}, SExec S a s₁ true D n t₁ o₁ → SExec S a s₂ true D n t₂ o₂ →
      t₁ = t₂ ∧ Taint.ORel A τ₁ o₁ o₂)
    (hb : ∀ {u₁ u₂ D n t₁ t₂ o₁ o₂}, A.Agree τ₁ u₁ u₂ → SExec S b u₁ true D n t₁ o₁ →
      SExec S b u₂ true D n t₂ o₂ → t₁ = t₂ ∧ Taint.ORel A τ₂ o₁ o₂)
    (e₁ : SExec S (.seq a b) s₁ true D n t₁ o₁) (e₂ : SExec S (.seq a b) s₂ true D n t₂ o₂) :
    t₁ = t₂ ∧ Taint.ORel A τ₂ o₁ o₂ := by
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      obtain ⟨rfl, rfl, rfl, rfl, h⟩ := ha a₁ a₂
      cases sexec_true a₁
      obtain ⟨rfl, hq⟩ := hb h b₁ b₂
      exact ⟨rfl, hq⟩
    | seqHalt a₂ => exact (ha a₁ a₂).2.elim
  | seqHalt a₁ =>
    cases e₂ with
    | seq a₂ _ => exact (ha a₁ a₂).2.elim
    | seqHalt a₂ => exact ⟨(ha a₁ a₂).1, trivial⟩

/-- How two transient runs of a block end, as `ORel`. -/
theorem block_orel (hs : Taint.SpecSound A S) {is : List M.Instr} {τ τ' : A.T}
    (h : A.checkBlock τ is = some τ') {s₁ s₂ : M.State} (ha : A.Agree τ s₁ s₂) {D : List Bool}
    {n : Nat} {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M}
    (e₁ : SExec S (.block is) s₁ true D n t₁ o₁) (e₂ : SExec S (.block is) s₂ true D n t₂ o₂) :
    t₁ = t₂ ∧ Taint.ORel A τ' o₁ o₂ := by
  cases e₁ with
  | blockDone b₁ =>
    cases e₂ with
    | blockDone b₂ =>
      obtain ⟨rfl, rfl, hq⟩ := Taint.sblock_sound hs h ha b₁ b₂; exact ⟨rfl, rfl, rfl, rfl, hq⟩
    | blockHalt b₂ => exact (Taint.sblock_sound hs h ha b₁ b₂).2.elim
  | blockHalt b₁ =>
    cases e₂ with
    | blockDone b₂ => exact (Taint.sblock_sound hs h ha b₁ b₂).2.elim
    | blockHalt b₂ => exact ⟨(Taint.sblock_sound hs h ha b₁ b₂).1, trivial⟩

/-- The start of a hardened loop body: runs already misspeculating agree on
the invariant `σ`; runs that have just mispredicted the branch back agree on
`Inv`, with the condition false. -/
def LoopStart (A : Taint M) (Inv : M.State → M.State → Prop) (σ : A.T) (c : M.Cond)
    (s₁ s₂ : M.State) : Prop :=
  A.Agree σ s₁ s₂ ∨ (Inv s₁ s₂ ∧ M.eval c s₁ = some false ∧ M.eval c s₂ = some false)

/-- Transient runs of the loop of a hardened loop. -/
theorem loop_sound (hs : Taint.SpecSound A S) (hp : PrologueOk S A τR pt pe Inv) {b : Prog M}
    {c : M.Cond} {σ σp σ' : A.T} {h₂ : Taint.Hint A.T}
    (ih : ∀ {τ τ' h u₁ u₂ D n t₁ t₂ o₁ o₂}, scheck A τR pt pe τ b h = some τ' → A.Agree τ u₁ u₂ →
      SExec S (b.harden pt pe) u₁ true D n t₁ o₁ → SExec S (b.harden pt pe) u₂ true D n t₂ o₂ →
      t₁ = t₂ ∧ Taint.ORel A τ' o₁ o₂)
    (hσp : A.checkBlock σ (pt c) = some σp) (hb : scheck A τR pt pe (A.meet σp τR) b h₂ = some σ')
    (hl : A.le σ σ' = true) (hc : A.condPub σ' c = true) {s₁ s₂ : M.State} {D : List Bool} {n : Nat}
    {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M} (hst : LoopStart A Inv σ c s₁ s₂)
    (e₁ : SExec S (.loop (.seq (.block (pt c)) (b.harden pt pe)) c) s₁ true D n t₁ o₁)
    (e₂ : SExec S (.loop (.seq (.block (pt c)) (b.harden pt pe)) c) s₂ true D n t₂ o₂) :
    t₁ = t₂ ∧ Taint.ORel A σ' o₁ o₂ := by
  have body : ∀ {u₁ u₂ D n t₁ t₂ o₁ o₂}, LoopStart A Inv σ c u₁ u₂ →
      SExec S (.seq (.block (pt c)) (b.harden pt pe)) u₁ true D n t₁ o₁ →
      SExec S (.seq (.block (pt c)) (b.harden pt pe)) u₂ true D n t₂ o₂ →
      t₁ = t₂ ∧ Taint.ORel A σ' o₁ o₂ := by
    intro u₁ u₂ D n t₁ t₂ o₁ o₂ hu x₁ x₂
    refine seqBlock_rel (τ := A.meet σp τR) trivial (fun y₁ y₂ => ?_) (fun ha z₁ z₂ => ih hb ha z₁ z₂) x₁ x₂
    rcases hu with hu | ⟨hi, h₁, h₂⟩
    · obtain ⟨ht, hr⟩ := Taint.sblock_sound hs hσp hu y₁ y₂
      exact ⟨ht, hr.mono fun _ _ => A.meet_left⟩
    · obtain ⟨ht, hr⟩ := hp.pt hi h₁ h₂ y₁ y₂
      exact ⟨ht, hr.mono fun _ _ => A.meet_right⟩
  generalize hL : Code.loop (.seq (.block (pt c)) (b.harden pt pe)) c = L at e₁
  generalize hm : true = m at e₁
  induction e₁ generalizing s₂ t₂ o₂ with
  | loopHalt a₁ =>
    cases hL; subst hm
    cases e₂ with
    | loopHalt a₂ => exact ⟨(body hst a₁ a₂).1, trivial⟩
    | loopEnd a₂ | loopExit a₂ | loopNext a₂ _ => exact (body hst a₁ a₂).2.elim
  | loopEnd a₁ =>
    cases hL; subst hm
    cases e₂ with
    | loopHalt a₂ => exact (body hst a₁ a₂).2.elim
    | loopEnd a₂ =>
      obtain ⟨rfl, -, -, -, hq⟩ := body hst a₁ a₂
      exact ⟨by rw [A.cond_sound hq hc], trivial⟩
    | loopExit a₂ | loopNext a₂ _ => obtain ⟨-, h, -⟩ := (body hst a₁ a₂).2; cases h
  | loopExit a₁ =>
    cases hL; subst hm
    cases e₂ with
    | loopHalt a₂ => exact (body hst a₁ a₂).2.elim
    | loopEnd a₂ | loopNext a₂ _ => obtain ⟨-, h, -⟩ := (body hst a₁ a₂).2; cases h
    | loopExit a₂ =>
      obtain ⟨rfl, rfl, h, rfl, hq⟩ := body hst a₁ a₂
      cases h
      rw [A.cond_sound hq hc]
      exact ⟨rfl, rfl, rfl, rfl, hq⟩
  | loopNext a₁ r₁ _ ih₂ =>
    cases hL; subst hm
    cases e₂ with
    | loopHalt a₂ => exact (body hst a₁ a₂).2.elim
    | loopEnd a₂ | loopExit a₂ => obtain ⟨-, h, -⟩ := (body hst a₁ a₂).2; cases h
    | loopNext a₂ r₂ =>
      obtain ⟨rfl, rfl, h, rfl, hq⟩ := body hst a₁ a₂
      cases h
      have hv := A.cond_sound hq hc
      rw [← hv] at r₂
      cases sexec_true a₁
      obtain ⟨rfl, hr⟩ := ih₂ (.inl (A.le_sound hl hq)) r₂ rfl rfl
      exact ⟨by rw [hv], hr⟩
  | _ => cases hL

/-- Transient runs of what follows the first body of a hardened loop: the
branch into the loop, and the prologue after it. -/
theorem loopRest_sound (hs : Taint.SpecSound A S) (hp : PrologueOk S A τR pt pe Inv) {b : Prog M}
    {c : M.Cond} {σ σp σ' τ₀ τx : A.T} {h₂ : Taint.Hint A.T}
    (ih : ∀ {τ τ' h u₁ u₂ D n t₁ t₂ o₁ o₂}, scheck A τR pt pe τ b h = some τ' → A.Agree τ u₁ u₂ →
      SExec S (b.harden pt pe) u₁ true D n t₁ o₁ → SExec S (b.harden pt pe) u₂ true D n t₂ o₂ →
      t₁ = t₂ ∧ Taint.ORel A τ' o₁ o₂)
    (hc₀ : A.condPub τ₀ c = true) (hσ : A.le σ τ₀ = true)
    (hσp : A.checkBlock σ (pt c) = some σp) (hb : scheck A τR pt pe (A.meet σp τR) b h₂ = some σ')
    (hl : A.le σ σ' = true) (hc : A.condPub σ' c = true)
    (hx : A.checkBlock (A.meet σ' τ₀) (pe c) = some τx) {s₁ s₂ : M.State} (hu : A.Agree τ₀ s₁ s₂)
    {D : List Bool} {n : Nat} {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M}
    (e₁ : SExec S (.seq (.ite c (.loop (.seq (.block (pt c)) (b.harden pt pe)) c) (.block [])) (.block (pe c)))
      s₁ true D n t₁ o₁)
    (e₂ : SExec S (.seq (.ite c (.loop (.seq (.block (pt c)) (b.harden pt pe)) c) (.block [])) (.block (pe c)))
      s₂ true D n t₂ o₂) :
    t₁ = t₂ ∧ Taint.ORel A (A.meet τx τR) o₁ o₂ := by
  refine seq_orel (τ₁ := A.meet σ' τ₀) (fun y₁ y₂ => ?_)
    (fun hw z₁ z₂ => let ⟨ht, hr⟩ := block_orel hs hx hw z₁ z₂
      ⟨ht, Taint.ORel.mono (fun _ _ => A.meet_left) hr⟩) e₁ e₂
  have hv := A.cond_sound hu hc₀
  cases y₁ with
  | iteEnd => cases y₂ with | iteEnd => rw [hv]; exact ⟨rfl, trivial⟩
  | iteT a₁ =>
    cases y₂ with
    | iteT a₂ =>
      rw [← hv] at a₂
      obtain ⟨rfl, hq⟩ := loop_sound hs hp (fun k k' x y => ih k k' x y) hσp hb hl hc
        (.inl (A.le_sound hσ hu)) a₁ a₂
      exact ⟨by rw [hv], Taint.ORel.mono (fun _ _ => A.meet_left) hq⟩
  | iteF a₁ =>
    cases y₂ with
    | iteF a₂ =>
      cases a₁ with
      | blockDone b₁ =>
        cases b₁
        cases a₂ with
        | blockDone b₂ => cases b₂; rw [hv]; exact ⟨rfl, rfl, rfl, rfl, A.meet_right hu⟩
        | blockHalt b₂ => cases b₂
      | blockHalt b₁ => cases b₁

/-- **Soundness of `scheck`**: two transient runs of hardened code from
states agreeing on `τ` leak the same and end alike. -/
theorem scheck_sound (hs : Taint.SpecSound A S) (hp : PrologueOk S A τR pt pe Inv) (c : Prog M) :
    ∀ {τ τ' : A.T} {h : Taint.Hint A.T} {s₁ s₂ : M.State} {D : List Bool} {n : Nat}
      {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M},
      scheck A τR pt pe τ c h = some τ' → A.Agree τ s₁ s₂ →
      SExec S (c.harden pt pe) s₁ true D n t₁ o₁ → SExec S (c.harden pt pe) s₂ true D n t₂ o₂ →
      t₁ = t₂ ∧ Taint.ORel A τ' o₁ o₂ := by
  induction c with
  | block is =>
    intro τ τ' h s₁ s₂ D n t₁ t₂ o₁ o₂ hk ha e₁ e₂
    cases h with
    | block ms cs =>
      have hk : A.checkChunks cs τ is ms = some τ' := hk
      cases e₁ with
      | blockDone b₁ =>
        cases e₂ with
        | blockDone b₂ =>
          obtain ⟨rfl, rfl, hq⟩ := Taint.schunks_sound hs hk ha b₁ b₂; exact ⟨rfl, rfl, rfl, rfl, hq⟩
        | blockHalt b₂ => exact (Taint.schunks_sound hs hk ha b₁ b₂).2.elim
      | blockHalt b₁ =>
        cases e₂ with
        | blockDone b₂ => exact (Taint.schunks_sound hs hk ha b₁ b₂).2.elim
        | blockHalt b₂ => exact ⟨(Taint.schunks_sound hs hk ha b₁ b₂).1, trivial⟩
    | _ => simp [scheck] at hk
  | seq a b iha ihb =>
    intro τ τ' h s₁ s₂ D n t₁ t₂ o₁ o₂ hk ha e₁ e₂
    cases h with
    | seq mid h₁ h₂ =>
      simp only [scheck, Option.bind_eq_some_iff] at hk
      obtain ⟨τ₁, k₁, k₂⟩ := hk
      split at k₂ <;> [rename_i hle; cases k₂]
      exact seq_orel (fun x₁ x₂ => iha k₁ ha x₁ x₂)
        (fun hu x₁ x₂ => ihb k₂ (A.le_sound hle hu) x₁ x₂) e₁ e₂
    | _ => simp [scheck] at hk
  | ite c t e iht ihe =>
    intro τ τ' h s₁ s₂ D n t₁ t₂ o₁ o₂ hk ha e₁ e₂
    cases h with
    | ite h₁ h₂ =>
      simp only [scheck] at hk
      split at hk <;> [rename_i hcp; cases hk]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hk
      obtain ⟨τt, kt, τe, ke, τ₁, k₁, τ₂, k₂, rfl⟩ := hk
      have hv := A.cond_sound ha hcp
      cases e₁ with
      | iteEnd => cases e₂ with | iteEnd => rw [hv]; exact ⟨rfl, trivial⟩
      | iteT a₁ =>
        cases e₂ with
        | iteT a₂ =>
          rw [← hv] at a₂
          obtain ⟨rfl, hq⟩ := seqBlock_rel (τ := A.meet τt τR) (Q := Taint.ORel A τ₁) trivial
            (fun y₁ y₂ => let ⟨ht, hr⟩ := Taint.sblock_sound hs kt ha y₁ y₂
              ⟨ht, hr.mono fun _ _ => A.meet_left⟩)
            (fun hu z₁ z₂ => iht k₁ hu z₁ z₂) (sexec_prefixArm a₁) (sexec_prefixArm a₂)
          exact ⟨by rw [hv], Taint.ORel.mono (fun _ _ => A.meet_left) hq⟩
      | iteF a₁ =>
        cases e₂ with
        | iteF a₂ =>
          rw [← hv] at a₂
          obtain ⟨rfl, hq⟩ := seqBlock_rel (τ := A.meet τe τR) (Q := Taint.ORel A τ₂) trivial
            (fun y₁ y₂ => let ⟨ht, hr⟩ := Taint.sblock_sound hs ke ha y₁ y₂
              ⟨ht, hr.mono fun _ _ => A.meet_left⟩)
            (fun hu z₁ z₂ => ihe k₂ hu z₁ z₂) a₁ a₂
          exact ⟨by rw [hv], Taint.ORel.mono (fun _ _ => A.meet_right) hq⟩
    | _ => simp [scheck] at hk
  | loop b c ih =>
    intro τ τ' h s₁ s₂ D n t₁ t₂ o₁ o₂ hk ha e₁ e₂
    cases h with
    | seq σ h₁ h₂ =>
      simp only [scheck, Option.bind_eq_some_iff] at hk
      obtain ⟨τ₀, k₀, hk⟩ := hk
      split at hk <;> [rename_i hc₀; cases hk]
      simp only [Bool.and_eq_true] at hc₀
      simp only [Option.bind_eq_some_iff] at hk
      obtain ⟨σp, kp, σ', kb, hk⟩ := hk
      split at hk <;> [rename_i hl; cases hk]
      simp only [Bool.and_eq_true] at hl
      simp only [Option.map_eq_some_iff] at hk
      obtain ⟨τx, kx, rfl⟩ := hk
      exact seq_orel (τ₁ := τ₀) (fun x₁ x₂ => ih k₀ ha x₁ x₂)
        (fun hu x₁ x₂ => loopRest_sound hs hp (fun k k' x y => ih k k' x y) hc₀.1 hc₀.2 kp kb hl.1 hl.2
          kx hu x₁ x₂) e₁ e₂
    | _ => simp [scheck] at hk
  | call nm body ih =>
    intro τ τ' h s₁ s₂ D n t₁ t₂ o₁ o₂ hk ha e₁ e₂
    cases h with
    | call hb =>
      simp only [scheck, Option.bind_eq_some_iff] at hk
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := hk
      cases e₁ with
      | callHalt hc₁ a₁ =>
        cases e₂ with
        | callHalt hc₂ b =>
          obtain ⟨ha₁, ha₁'⟩ := A.call_sound ha h₁ hc₁ hc₂
          exact ⟨by rw [ha₁, (ih h₂ ha₁' a₁ b).1], trivial⟩
        | call hc₂ b _ => exact (ih h₂ (A.call_sound ha h₁ hc₁ hc₂).2 a₁ b).2.elim
      | call hc₁ a₁ hr =>
        cases e₂ with
        | callHalt hc₂ b => exact (ih h₂ (A.call_sound ha h₁ hc₁ hc₂).2 a₁ b).2.elim
        | call hc₂ b hr₂ =>
          obtain ⟨ha₁, ha₁'⟩ := A.call_sound ha h₁ hc₁ hc₂
          obtain ⟨rfl, rfl, rfl, rfl, ha₂⟩ := ih h₂ ha₁' a₁ b
          obtain ⟨ha₃, ha₃'⟩ := hs.sret ha₂ h₃ hr hr₂
          exact ⟨by rw [ha₁, ha₃], rfl, rfl, rfl, ha₃'⟩
    | _ => simp [scheck] at hk
  | frame i body j ih =>
    intro τ τ' h s₁ s₂ D n t₁ t₂ o₁ o₂ hk ha e₁ e₂
    cases h with
    | frame hb =>
      simp only [scheck, Option.bind_eq_some_iff] at hk
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := hk
      cases e₁ with
      | frameHalt hp₁ a₁ =>
        cases e₂ with
        | frameHalt hp₂ b =>
          obtain ⟨ha₁, ha₁'⟩ := A.push_sound ha h₁ hp₁ hp₂
          exact ⟨by rw [ha₁, (ih h₂ ha₁' a₁ b).1], trivial⟩
        | frame hp₂ b _ => exact (ih h₂ (A.push_sound ha h₁ hp₁ hp₂).2 a₁ b).2.elim
      | frame hp₁ a₁ hq =>
        cases e₂ with
        | frameHalt hp₂ b => exact (ih h₂ (A.push_sound ha h₁ hp₁ hp₂).2 a₁ b).2.elim
        | frame hp₂ b hq₂ =>
          obtain ⟨ha₁, ha₁'⟩ := A.push_sound ha h₁ hp₁ hp₂
          obtain ⟨rfl, rfl, rfl, rfl, ha₂⟩ := ih h₂ ha₁' a₁ b
          obtain ⟨ha₃, ha₃'⟩ := A.pop_sound ha₂ h₃ hq hq₂
          exact ⟨by rw [ha₁, ha₃], rfl, rfl, rfl, ha₃'⟩
    | _ => simp [scheck] at hk

end Transient

/-! ## Sequential runs that may mispredict -/

section Joint

variable {S : Spectre M} {A : Taint M} {τR : A.T} {pt pe : M.Cond → List M.Instr}
  {Inv : M.State → M.State → Prop} {p : M.Instr → Bool}

/-- What hardening needs of an ISA, its taint analysis and its prologues:
every run makes as many observations; the analysis is sound for transient
runs; the prologues establish `τR` in runs that have just mispredicted, and
change nothing where the condition is as the branch went; and `Inv` (e.g.
the stack pointers agree) holds along two runs on the same path, through
the instructions satisfying `p`. -/
structure SlhOk (S : Spectre M) (A : Taint M) (τR : A.T) (pt pe : M.Cond → List M.Instr)
    (Inv : M.State → M.State → Prop) (p : M.Instr → Bool) : Prop where
  shape : LeakShape M
  sound : Taint.SpecSound A S
  pro : PrologueOk S A τR pt pe Inv
  pt_nop : ∀ c s, M.eval c s = some true → execBlock M (pt c) s = some (s, [])
  pe_nop : ∀ c s, M.eval c s = some false → execBlock M (pe c) s = some (s, [])
  exec : ∀ {i s₁ s₂ s₁' s₂'}, p i = true → Inv s₁ s₂ → M.exec i s₁ = some s₁' →
    M.exec i s₂ = some s₂' → Inv s₁' s₂'
  call : ∀ {s₁ s₂ s₁' s₂'}, Inv s₁ s₂ → M.call s₁ = some s₁' → M.call s₂ = some s₂' → Inv s₁' s₂'
  ret : ∀ {a₁ a₂ b₁ b₂ c₁ c₂}, Inv b₁ b₂ → M.ret a₁ b₁ = some c₁ → M.ret a₂ b₂ = some c₂ → Inv c₁ c₂
  push : ∀ {i s₁ s₂ s₁' s₂'}, Inv s₁ s₂ → M.push i s₁ = some s₁' → M.push i s₂ = some s₂' →
    Inv s₁' s₂'
  pop : ∀ {j a₁ a₂ b₁ b₂ c₁ c₂}, Inv b₁ b₂ → M.pop j a₁ b₁ = some c₁ → M.pop j a₂ b₂ = some c₂ →
    Inv c₁ c₂

/-- How two runs of hardened code that start without misspeculating end:
both stopped; both done without misspeculating, in the final states `s₁'`,
`s₂'` of the sequential runs; or both done misspeculating, in states
agreeing on `τ'`. -/
def HRel (A : Taint M) (Inv : M.State → M.State → Prop) (τ' : A.T) (s₁' s₂' : M.State) :
    SOut M → SOut M → Prop
  | .halt, .halt => True
  | .done a ms D k, .done b ms' E l => ms = ms' ∧ D = E ∧ k = l ∧
      (ms = false → a = s₁' ∧ b = s₂' ∧ Inv a b) ∧ (ms = true → A.Agree τ' a b)
  | _, _ => False

theorem HRel.mono {τ σ : A.T} {s₁' s₂' : M.State} {o₁ o₂ : SOut M}
    (hm : ∀ a b, A.Agree τ a b → A.Agree σ a b) (h : HRel A Inv τ s₁' s₂' o₁ o₂) :
    HRel A Inv σ s₁' s₂' o₁ o₂ := by
  cases o₁ <;> cases o₂ <;> simp only [HRel] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun hm' => hm _ _ (h.2.2.2.2 hm')⟩

theorem HRel.cases_done {τ : A.T} {s₁' s₂' a b : M.State} {ms ms' : Bool} {D E : List Bool}
    {k l : Nat} (h : HRel A Inv τ s₁' s₂' (.done a ms D k) (.done b ms' E l)) :
    D = E ∧ k = l ∧ ((ms = false ∧ ms' = false ∧ a = s₁' ∧ b = s₂' ∧ Inv a b) ∨
      (ms = true ∧ ms' = true ∧ A.Agree τ a b)) := by
  obtain ⟨rfl, hD, hk, hf, ht⟩ := h
  refine ⟨hD, hk, ?_⟩
  cases ms
  · obtain ⟨h₁, h₂, h₃⟩ := hf rfl; exact .inl ⟨rfl, rfl, h₁, h₂, h₃⟩
  · exact .inr ⟨rfl, rfl, ht rfl⟩

/-- `HRel` of two transient runs. -/
theorem HRel.of_orel {c : Prog M} {τ : A.T} {s₁ s₁' s₂' : M.State} {D : List Bool} {n : Nat}
    {t₁ : List SLeak} {o₁ o₂ : SOut M} (e₁ : SExec S c s₁ true D n t₁ o₁)
    (h : Taint.ORel A τ o₁ o₂) : HRel A Inv τ s₁' s₂' o₁ o₂ := by
  cases o₁ <;> cases o₂ <;> simp only [HRel, Taint.ORel] at h ⊢
  obtain ⟨rfl, rfl, rfl, ha⟩ := h
  cases sexec_true e₁
  exact ⟨rfl, rfl, rfl, nofun, fun _ => ha⟩

theorem inv_block (H : SlhOk S A τR pt pe Inv p) {is : List M.Instr} (hall : is.all p = true)
    {s₁ s₂ s₁' s₂' : M.State} {T₁ T₂ : List Leak} (hi : Inv s₁ s₂)
    (x₁ : execBlock M is s₁ = some (s₁', T₁)) (x₂ : execBlock M is s₂ = some (s₂', T₂)) :
    Inv s₁' s₂' := by
  induction is generalizing s₁ s₂ s₁' s₂' T₁ T₂ with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at x₁ x₂
    rw [← x₁.1, ← x₂.1]; exact hi
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hall
    simp only [execBlock] at x₁ x₂
    split at x₁ <;> [cases x₁; rename_i a₁ y₁]
    split at x₂ <;> [cases x₂; rename_i a₂ y₂]
    simp only [Option.map_eq_some_iff, Prod.exists] at x₁ x₂
    obtain ⟨_, _, z₁, h₁⟩ := x₁
    obtain ⟨_, _, z₂, h₂⟩ := x₂
    simp only [Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, -⟩ := h₁
    obtain ⟨rfl, -⟩ := h₂
    exact ih hall.2 (H.exec hall.1 hi y₁ y₂) z₁ z₂

/-- Two runs of a block that changes nothing, then code, without
misspeculating. -/
theorem nopSeq_rel (H : SlhOk S A τR pt pe Inv p) {is : List M.Instr} {x : Prog M} {s₁ s₂ : M.State}
    (h₁ : execBlock M is s₁ = some (s₁, [])) (h₂ : execBlock M is s₂ = some (s₂, []))
    {D : List Bool} {n : Nat} {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M} {R : SOut M → SOut M → Prop}
    (hR : R .halt .halt)
    (hx : ∀ {k t₁ t₂ o₁ o₂}, SExec S x s₁ false D k t₁ o₁ → SExec S x s₂ false D k t₂ o₂ →
      t₁ = t₂ ∧ R o₁ o₂)
    (e₁ : SExec S (.seq (.block is) x) s₁ false D n t₁ o₁)
    (e₂ : SExec S (.seq (.block is) x) s₂ false D n t₂ o₂) : t₁ = t₂ ∧ R o₁ o₂ := by
  cases e₁ with
  | seq a₁ b₁ =>
    cases a₁ with
    | blockDone y₁ =>
      cases e₂ with
      | seq a₂ b₂ =>
        cases a₂ with
        | blockDone y₂ =>
          obtain ⟨rfl, h⟩ := sblock_seq H.shape rfl h₁ h₂ y₁ y₂
          rcases h with ⟨h, -⟩ | ⟨k, h, h'⟩
          · cases h
          · cases h; cases h'
            obtain ⟨rfl, hr⟩ := hx b₁ b₂
            exact ⟨rfl, hr⟩
      | seqHalt a₂ =>
        cases a₂ with
        | blockHalt y₂ =>
          obtain ⟨-, h⟩ := sblock_seq H.shape rfl h₁ h₂ y₁ y₂
          rcases h with ⟨h, -⟩ | ⟨k, -, h⟩ <;> cases h
  | seqHalt a₁ =>
    cases a₁ with
    | blockHalt y₁ =>
      cases e₂ with
      | seq a₂ _ =>
        cases a₂ with
        | blockDone y₂ =>
          obtain ⟨-, h⟩ := sblock_seq H.shape rfl h₁ h₂ y₁ y₂
          rcases h with ⟨-, h⟩ | ⟨k, h, -⟩ <;> cases h
      | seqHalt a₂ =>
        cases a₂ with
        | blockHalt y₂ => exact ⟨(sblock_seq H.shape rfl h₁ h₂ y₁ y₂).1, hR⟩

/-- Two runs of a block that changes nothing, without misspeculating. -/
theorem nopBlock_rel (H : SlhOk S A τR pt pe Inv p) {is : List M.Instr} {s₁ s₂ : M.State}
    (h₁ : execBlock M is s₁ = some (s₁, [])) (h₂ : execBlock M is s₂ = some (s₂, []))
    (hi : Inv s₁ s₂) {τ : A.T} {D : List Bool} {n : Nat} {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M}
    (e₁ : SExec S (.block is) s₁ false D n t₁ o₁) (e₂ : SExec S (.block is) s₂ false D n t₂ o₂) :
    t₁ = t₂ ∧ HRel A Inv τ s₁ s₂ o₁ o₂ := by
  cases e₁ with
  | blockDone y₁ =>
    cases e₂ with
    | blockDone y₂ =>
      obtain ⟨rfl, h⟩ := sblock_seq H.shape rfl h₁ h₂ y₁ y₂
      rcases h with ⟨h, -⟩ | ⟨k, h, h'⟩
      · cases h
      · cases h; cases h'; exact ⟨rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, hi⟩, nofun⟩
    | blockHalt y₂ =>
      obtain ⟨-, h⟩ := sblock_seq H.shape rfl h₁ h₂ y₁ y₂
      rcases h with ⟨h, -⟩ | ⟨k, -, h⟩ <;> cases h
  | blockHalt y₁ =>
    cases e₂ with
    | blockDone y₂ =>
      obtain ⟨-, h⟩ := sblock_seq H.shape rfl h₁ h₂ y₁ y₂
      rcases h with ⟨-, h⟩ | ⟨k, h, -⟩ <;> cases h
    | blockHalt y₂ => exact ⟨(sblock_seq H.shape rfl h₁ h₂ y₁ y₂).1, trivial⟩

/-- Two runs of a prologue block in states where the branch was just
mispredicted (`hb`, from `PrologueOk`), then transient runs of code. -/
theorem freshSeq_rel {is : List M.Instr} {x : Prog M} {s₁ s₂ : M.State} {τ τ' : A.T}
    {D : List Bool} {n : Nat} {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M}
    (hb : ∀ {k t₁ t₂ r₁ r₂}, SBlock S is s₁ true k t₁ r₁ → SBlock S is s₂ true k t₂ r₂ →
      t₁ = t₂ ∧ Taint.BRel A τ r₁ r₂)
    (hx : ∀ {a b k t₁ t₂ o₁ o₂}, A.Agree τ a b → SExec S x a true D k t₁ o₁ →
      SExec S x b true D k t₂ o₂ → t₁ = t₂ ∧ Taint.ORel A τ' o₁ o₂)
    (e₁ : SExec S (.seq (.block is) x) s₁ true D n t₁ o₁)
    (e₂ : SExec S (.seq (.block is) x) s₂ true D n t₂ o₂) :
    t₁ = t₂ ∧ Taint.ORel A τ' o₁ o₂ :=
  seqBlock_rel trivial hb hx e₁ e₂

/-- How two runs of the loop of a hardened loop that start without
misspeculating end: as `HRel`, but a run done misspeculating either agrees on
the loop's `σ'` or has just mispredicted the loop's exit (the condition true),
which the prologue after the loop handles. -/
def LXRel (A : Taint M) (Inv : M.State → M.State → Prop) (σ' : A.T) (c : M.Cond)
    (s₁' s₂' : M.State) : SOut M → SOut M → Prop
  | .halt, .halt => True
  | .done a ms D k, .done b ms' E l => ms = ms' ∧ D = E ∧ k = l ∧
      (ms = false → a = s₁' ∧ b = s₂' ∧ Inv a b) ∧
      (ms = true → A.Agree σ' a b ∨ (Inv a b ∧ M.eval c a = some true ∧ M.eval c b = some true))
  | _, _ => False

theorem LXRel.of_orel {L : Prog M} {σ' : A.T} {c : M.Cond} {s₁ s₁' s₂' : M.State} {D : List Bool}
    {n : Nat} {t₁ : List SLeak} {o₁ o₂ : SOut M} (e₁ : SExec S L s₁ true D n t₁ o₁)
    (h : Taint.ORel A σ' o₁ o₂) : LXRel A Inv σ' c s₁' s₂' o₁ o₂ := by
  cases o₁ <;> cases o₂ <;> simp only [LXRel, Taint.ORel] at h ⊢
  obtain ⟨rfl, rfl, rfl, ha⟩ := h
  cases sexec_true e₁
  exact ⟨rfl, rfl, rfl, nofun, fun _ => .inl ha⟩

/-- The joint relation of `slh_rel`, for code `b`. -/
def JointOk (S : Spectre M) (A : Taint M) (τR : A.T) (pt pe : M.Cond → List M.Instr)
    (Inv : M.State → M.State → Prop) (p : M.Instr → Bool) (b : Prog M) : Prop :=
  ∀ {τ τ' : A.T} {h : Taint.Hint A.T} {s₁ s₂ s₁' s₂' : M.State} {T₁ T₂ : List Leak} {D : List Bool}
    {n : Nat} {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M},
    b.all p = true → scheck A τR pt pe τ b h = some τ' → Exec M b s₁ T₁ s₁' → Exec M b s₂ T₂ s₂' →
    T₁ = T₂ → Inv s₁ s₂ → SExec S (b.harden pt pe) s₁ false D n t₁ o₁ →
    SExec S (b.harden pt pe) s₂ false D n t₂ o₂ → t₁ = t₂ ∧ HRel A Inv τ' s₁' s₂' o₁ o₂

theorem loopTrans_rel (H : SlhOk S A τR pt pe Inv p) {b : Prog M} {c : M.Cond} {σ σp σ' : A.T}
    {h₂ : Taint.Hint A.T}
    (ihT : ∀ {τ τ' h u₁ u₂ D n t₁ t₂ o₁ o₂}, scheck A τR pt pe τ b h = some τ' → A.Agree τ u₁ u₂ →
      SExec S (b.harden pt pe) u₁ true D n t₁ o₁ → SExec S (b.harden pt pe) u₂ true D n t₂ o₂ →
      t₁ = t₂ ∧ Taint.ORel A τ' o₁ o₂)
    (hσp : A.checkBlock σ (pt c) = some σp)
    (hb : scheck A τR pt pe (A.meet σp τR) b h₂ = some σ') (hl : A.le σ σ' = true)
    (hc : A.condPub σ' c = true) {s₁' s₂' u₁ u₂ : M.State} {D : List Bool} {n : Nat}
    {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M} (hst : LoopStart A Inv σ c u₁ u₂)
    (r₁ : SExec S (.loop (.seq (.block (pt c)) (b.harden pt pe)) c) u₁ true D n t₁ o₁)
    (r₂ : SExec S (.loop (.seq (.block (pt c)) (b.harden pt pe)) c) u₂ true D n t₂ o₂) :
    t₁ = t₂ ∧ LXRel A Inv σ' c s₁' s₂' o₁ o₂ :=
  let ⟨ht, hr⟩ := loop_sound H.sound H.pro (fun k k' x y => ihT k k' x y) hσp hb hl hc hst r₁ r₂
  ⟨ht, LXRel.of_orel r₁ hr⟩

/-- Two runs of the loop of a hardened loop, entered without misspeculating
with the condition true. -/
theorem loopSeq_rel (H : SlhOk S A τR pt pe Inv p) {b : Prog M} {c : M.Cond} {σ σp σ' : A.T}
    {h₂ : Taint.Hint A.T} (ihJ : JointOk S A τR pt pe Inv p b)
    (ihT : ∀ {τ τ' h u₁ u₂ D n t₁ t₂ o₁ o₂}, scheck A τR pt pe τ b h = some τ' → A.Agree τ u₁ u₂ →
      SExec S (b.harden pt pe) u₁ true D n t₁ o₁ → SExec S (b.harden pt pe) u₂ true D n t₂ o₂ →
      t₁ = t₂ ∧ Taint.ORel A τ' o₁ o₂)
    (hall : b.all p = true) (hσp : A.checkBlock σ (pt c) = some σp)
    (hb : scheck A τR pt pe (A.meet σp τR) b h₂ = some σ') (hl : A.le σ σ' = true)
    (hc : A.condPub σ' c = true) {x₁ x₂ s₁' s₂' : M.State} {V₁ V₂ : List Leak}
    (xl₁ : Exec M (.loop b c) x₁ V₁ s₁') (xl₂ : Exec M (.loop b c) x₂ V₂ s₂') (hV : V₁ = V₂)
    (hi : Inv x₁ x₂) (hx₁ : M.eval c x₁ = some true) (hx₂ : M.eval c x₂ = some true)
    {D : List Bool} {n : Nat} {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M}
    (e₁ : SExec S (.loop (.seq (.block (pt c)) (b.harden pt pe)) c) x₁ false D n t₁ o₁)
    (e₂ : SExec S (.loop (.seq (.block (pt c)) (b.harden pt pe)) c) x₂ false D n t₂ o₂) :
    t₁ = t₂ ∧ LXRel A Inv σ' c s₁' s₂' o₁ o₂ := by
  have tr := fun {s₁' s₂' u₁ u₂ D n t₁ t₂ o₁ o₂} => @loopTrans_rel _ _ _ _ _ _ _ _ H _ _ _ _ _ _
    (fun k k' x y => ihT k k' x y) hσp hb hl hc s₁' s₂' u₁ u₂ D n t₁ t₂ o₁ o₂
  generalize hL : Code.loop b c = L at xl₁
  induction xl₁ generalizing x₂ V₂ s₂' D n t₁ t₂ o₁ o₂ with
  | @loopExit _ _ _ y₁ U₁ xb₁ hy₁ =>
    cases hL
    cases xl₂ with
    | loopNext xb₂ _ _ =>
      obtain ⟨-, h'⟩ := Exec.prefix_eq H.shape xb₁ xb₂ hV
      simp at h'
    | loopExit xb₂ hy₂ =>
      obtain ⟨hU, -⟩ := Exec.prefix_eq H.shape xb₁ xb₂ hV
      have body := fun {k t₁ t₂ o₁ o₂} => @nopSeq_rel _ _ _ _ _ _ _ _ H _ _ _ _
        (H.pt_nop _ _ hx₁) (H.pt_nop _ _ hx₂) D k t₁ t₂ o₁ o₂ (HRel A Inv σ' y₁ s₂') trivial
        (fun z₁ z₂ => ihJ hall hb xb₁ xb₂ hU hi z₁ z₂)
      cases e₁ with
      | loopHalt a₁ =>
        cases e₂ with
        | loopHalt a₂ => exact ⟨(body a₁ a₂).1, trivial⟩
        | loopEnd a₂ | loopExit a₂ | loopNext a₂ _ => exact (body a₁ a₂).2.elim
      | loopEnd a₁ =>
        cases e₂ with
        | loopHalt a₂ => exact (body a₁ a₂).2.elim
        | loopExit a₂ | loopNext a₂ _ => obtain ⟨h, -⟩ := (body a₁ a₂).2.cases_done; cases h
        | loopEnd a₂ =>
          obtain ⟨rfl, h⟩ := body a₁ a₂
          rcases h.cases_done with ⟨-, -, ⟨rfl, rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, ha⟩⟩
          · rw [hy₁, hy₂]; exact ⟨rfl, trivial⟩
          · rw [A.cond_sound ha hc]; exact ⟨rfl, trivial⟩
      | loopExit a₁ =>
        cases e₂ with
        | loopHalt a₂ => exact (body a₁ a₂).2.elim
        | loopEnd a₂ | loopNext a₂ _ => obtain ⟨h, -⟩ := (body a₁ a₂).2.cases_done; cases h
        | loopExit a₂ =>
          obtain ⟨rfl, h⟩ := body a₁ a₂
          obtain ⟨hD, rfl, hcase⟩ := h.cases_done
          cases hD
          rcases hcase with ⟨rfl, rfl, rfl, rfl, hi'⟩ | ⟨rfl, rfl, ha⟩
          · rw [hy₁, hy₂]
            exact ⟨rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, hi'⟩, nofun⟩
          · rw [A.cond_sound ha hc]
            exact ⟨rfl, rfl, rfl, rfl, nofun, fun _ => .inl ha⟩
      | loopNext a₁ r₁ =>
        cases e₂ with
        | loopHalt a₂ => exact (body a₁ a₂).2.elim
        | loopEnd a₂ | loopExit a₂ => obtain ⟨h, -⟩ := (body a₁ a₂).2.cases_done; cases h
        | loopNext a₂ r₂ =>
          obtain ⟨rfl, h⟩ := body a₁ a₂
          obtain ⟨hD, rfl, hcase⟩ := h.cases_done
          cases hD
          rcases hcase with ⟨rfl, rfl, rfl, rfl, hi'⟩ | ⟨rfl, rfl, ha⟩
          · rw [hy₁] at r₁ ⊢; rw [hy₂] at r₂ ⊢
            obtain ⟨rfl, hr⟩ := tr (.inr ⟨hi', hy₁, hy₂⟩) r₁ r₂
            exact ⟨rfl, hr⟩
          · have hv := A.cond_sound ha hc
            rw [← hv] at r₂
            obtain ⟨rfl, hr⟩ := tr (.inl (A.le_sound hl ha)) r₁ r₂
            exact ⟨by rw [hv], hr⟩
  | @loopNext _ _ _ y₁ _ U₁ W₁ xb₁ hy₁ xr₁ _ ih =>
    cases hL
    cases xl₂ with
    | loopExit xb₂ _ =>
      obtain ⟨-, h'⟩ := Exec.prefix_eq H.shape xb₁ xb₂ hV
      simp at h'
    | @loopNext _ _ _ y₂ _ U₂ W₂ xb₂ hy₂ xr₂ =>
      obtain ⟨hU, hW⟩ := Exec.prefix_eq H.shape xb₁ xb₂ hV
      simp only [List.cons.injEq, true_and] at hW
      have body := fun {k t₁ t₂ o₁ o₂} => @nopSeq_rel _ _ _ _ _ _ _ _ H _ _ _ _
        (H.pt_nop _ _ hx₁) (H.pt_nop _ _ hx₂) D k t₁ t₂ o₁ o₂ (HRel A Inv σ' y₁ y₂) trivial
        (fun z₁ z₂ => ihJ hall hb xb₁ xb₂ hU hi z₁ z₂)
      cases e₁ with
      | loopHalt a₁ =>
        cases e₂ with
        | loopHalt a₂ => exact ⟨(body a₁ a₂).1, trivial⟩
        | loopEnd a₂ | loopExit a₂ | loopNext a₂ _ => exact (body a₁ a₂).2.elim
      | loopEnd a₁ =>
        cases e₂ with
        | loopHalt a₂ => exact (body a₁ a₂).2.elim
        | loopExit a₂ | loopNext a₂ _ => obtain ⟨h, -⟩ := (body a₁ a₂).2.cases_done; cases h
        | loopEnd a₂ =>
          obtain ⟨rfl, h⟩ := body a₁ a₂
          rcases h.cases_done with ⟨-, -, ⟨rfl, rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, ha⟩⟩
          · rw [hy₁, hy₂]; exact ⟨rfl, trivial⟩
          · rw [A.cond_sound ha hc]; exact ⟨rfl, trivial⟩
      | loopExit a₁ =>
        cases e₂ with
        | loopHalt a₂ => exact (body a₁ a₂).2.elim
        | loopEnd a₂ | loopNext a₂ _ => obtain ⟨h, -⟩ := (body a₁ a₂).2.cases_done; cases h
        | loopExit a₂ =>
          obtain ⟨rfl, h⟩ := body a₁ a₂
          obtain ⟨hD, rfl, hcase⟩ := h.cases_done
          cases hD
          rcases hcase with ⟨rfl, rfl, rfl, rfl, hi'⟩ | ⟨rfl, rfl, ha⟩
          · rw [hy₁, hy₂]
            exact ⟨rfl, rfl, rfl, rfl, nofun, fun _ => .inr ⟨hi', hy₁, hy₂⟩⟩
          · rw [A.cond_sound ha hc]
            exact ⟨rfl, rfl, rfl, rfl, nofun, fun _ => .inl ha⟩
      | loopNext a₁ r₁ =>
        cases e₂ with
        | loopHalt a₂ => exact (body a₁ a₂).2.elim
        | loopEnd a₂ | loopExit a₂ => obtain ⟨h, -⟩ := (body a₁ a₂).2.cases_done; cases h
        | loopNext a₂ r₂ =>
          obtain ⟨rfl, h⟩ := body a₁ a₂
          obtain ⟨hD, rfl, hcase⟩ := h.cases_done
          cases hD
          rcases hcase with ⟨rfl, rfl, rfl, rfl, hi'⟩ | ⟨rfl, rfl, ha⟩
          · rw [hy₁] at r₁ ⊢; rw [hy₂] at r₂ ⊢
            obtain ⟨rfl, hr⟩ := ih xr₂ hW hi' hy₁ hy₂ r₁ r₂ rfl
            exact ⟨rfl, hr⟩
          · have hv := A.cond_sound ha hc
            rw [← hv] at r₂
            obtain ⟨rfl, hr⟩ := tr (.inl (A.le_sound hl ha)) r₁ r₂
            exact ⟨by rw [hv], hr⟩
  | _ => cases hL

/-- How two runs of the branch into a hardened loop end, before the
prologue after the loop: both stopped; both done without misspeculating, in
the final states, where the condition is false; or both done misspeculating,
agreeing on `τ`, or having just mispredicted with the condition true. -/
def IRel (A : Taint M) (Inv : M.State → M.State → Prop) (τ : A.T) (c : M.Cond)
    (s₁' s₂' : M.State) : SOut M → SOut M → Prop
  | .halt, .halt => True
  | .done a ms D k, .done b ms' E l => ms = ms' ∧ D = E ∧ k = l ∧
      (ms = false → a = s₁' ∧ b = s₂' ∧ Inv a b ∧ M.eval c a = some false ∧ M.eval c b = some false) ∧
      (ms = true → A.Agree τ a b ∨ (Inv a b ∧ M.eval c a = some true ∧ M.eval c b = some true))
  | _, _ => False

/-- Two runs of the prologue after a loop. -/
theorem pe_rel (H : SlhOk S A τR pt pe Inv p) {c : M.Cond} {τ τx : A.T}
    (hx : A.checkBlock τ (pe c) = some τx) {s₁' s₂' : M.State} {o₁ o₂ : SOut M}
    (hi : IRel A Inv τ c s₁' s₂' o₁ o₂) :
    ∀ {a₁ a₂ ms₁ ms₂ D₁ D₂ k₁ k₂ t₁ t₂ q₁ q₂}, o₁ = .done a₁ ms₁ D₁ k₁ → o₂ = .done a₂ ms₂ D₂ k₂ →
      SExec S (.block (pe c)) a₁ ms₁ D₁ k₁ t₁ q₁ → SExec S (.block (pe c)) a₂ ms₂ D₂ k₂ t₂ q₂ →
      t₁ = t₂ ∧ HRel A Inv (A.meet τx τR) s₁' s₂' q₁ q₂ := by
  intro a₁ a₂ ms₁ ms₂ D₁ D₂ k₁ k₂ t₁ t₂ q₁ q₂ h₁ h₂ e₁ e₂
  subst h₁ h₂
  obtain ⟨rfl, rfl, rfl, hf, ht⟩ := hi
  cases ms₁ with
  | false =>
    obtain ⟨rfl, rfl, hi', hc₁, hc₂⟩ := hf rfl
    exact nopBlock_rel H (H.pe_nop _ _ hc₁) (H.pe_nop _ _ hc₂) hi' e₁ e₂
  | true =>
    rcases ht rfl with ha | ⟨hi', hc₁, hc₂⟩
    · obtain ⟨htr, hr⟩ := block_orel H.sound hx ha e₁ e₂
      exact ⟨htr, HRel.of_orel e₁ (Taint.ORel.mono (fun _ _ => A.meet_left) hr)⟩
    · cases e₁ with
      | blockDone y₁ =>
        cases e₂ with
        | blockDone y₂ =>
          obtain ⟨rfl, ⟨rfl, hr⟩⟩ := H.pro.pe hi' hc₁ hc₂ y₁ y₂
          exact ⟨rfl, rfl, rfl, rfl, nofun, fun _ => A.meet_right hr⟩
        | blockHalt y₂ => exact (H.pro.pe hi' hc₁ hc₂ y₁ y₂).2.elim
      | blockHalt y₁ =>
        cases e₂ with
        | blockDone y₂ => exact (H.pro.pe hi' hc₁ hc₂ y₁ y₂).2.elim
        | blockHalt y₂ => exact ⟨(H.pro.pe hi' hc₁ hc₂ y₁ y₂).1, trivial⟩

/-- Two runs of what follows the first body of a hardened loop, entered
without misspeculating: the loop exits there (`hk`, left) or goes on. -/
theorem loopRest_rel (H : SlhOk S A τR pt pe Inv p) {b : Prog M} {c : M.Cond}
    {σ σp σ' τ₀ τx : A.T} {h₂ : Taint.Hint A.T} (ihJ : JointOk S A τR pt pe Inv p b)
    (ihT : ∀ {τ τ' h u₁ u₂ D n t₁ t₂ o₁ o₂}, scheck A τR pt pe τ b h = some τ' → A.Agree τ u₁ u₂ →
      SExec S (b.harden pt pe) u₁ true D n t₁ o₁ → SExec S (b.harden pt pe) u₂ true D n t₂ o₂ →
      t₁ = t₂ ∧ Taint.ORel A τ' o₁ o₂)
    (hall : b.all p = true) (hσp : A.checkBlock σ (pt c) = some σp)
    (hb : scheck A τR pt pe (A.meet σp τR) b h₂ = some σ') (hl : A.le σ σ' = true)
    (hc : A.condPub σ' c = true) (hx : A.checkBlock (A.meet σ' τ₀) (pe c) = some τx)
    {x₁ x₂ s₁' s₂' : M.State} (hi : Inv x₁ x₂)
    (hk : (M.eval c x₁ = some false ∧ M.eval c x₂ = some false ∧ s₁' = x₁ ∧ s₂' = x₂) ∨
      (M.eval c x₁ = some true ∧ M.eval c x₂ = some true ∧ ∃ W₁ W₂, Exec M (.loop b c) x₁ W₁ s₁' ∧
        Exec M (.loop b c) x₂ W₂ s₂' ∧ W₁ = W₂))
    {D : List Bool} {n : Nat} {t₁ t₂ : List SLeak} {o₁ o₂ : SOut M}
    (e₁ : SExec S (.seq (.ite c (.loop (.seq (.block (pt c)) (b.harden pt pe)) c) (.block [])) (.block (pe c)))
      x₁ false D n t₁ o₁)
    (e₂ : SExec S (.seq (.ite c (.loop (.seq (.block (pt c)) (b.harden pt pe)) c) (.block [])) (.block (pe c)))
      x₂ false D n t₂ o₂) :
    t₁ = t₂ ∧ HRel A Inv (A.meet τx τR) s₁' s₂' o₁ o₂ := by
  have hv : M.eval c x₁ = M.eval c x₂ := by
    rcases hk with ⟨h₁, h₂, -⟩ | ⟨h₁, h₂, -⟩ <;> rw [h₁, h₂]
  -- The branch into the loop.
  have ite : ∀ {D n t₁ t₂ o₁ o₂},
      SExec S (.ite c (.loop (.seq (.block (pt c)) (b.harden pt pe)) c) (.block [])) x₁ false D n t₁ o₁ →
      SExec S (.ite c (.loop (.seq (.block (pt c)) (b.harden pt pe)) c) (.block [])) x₂ false D n t₂ o₂ →
      t₁ = t₂ ∧ IRel A Inv (A.meet σ' τ₀) c s₁' s₂' o₁ o₂ := by
    intro D n t₁ t₂ o₁ o₂ y₁ y₂
    cases y₁ with
    | iteEnd => cases y₂ with | iteEnd => rw [hv]; exact ⟨rfl, trivial⟩
    | iteT a₁ =>
      cases y₂ with
      | iteT a₂ =>
        rw [← hv] at a₂ ⊢
        rcases hk with ⟨h₁, h₂, -, -⟩ | ⟨h₁, h₂, W₁, W₂, w₁, w₂, hW⟩
        · rw [h₁] at a₁ a₂ ⊢
          obtain ⟨rfl, hr⟩ := loopTrans_rel (s₁' := s₁') (s₂' := s₂') H (fun k k' x y => ihT k k' x y)
            hσp hb hl hc (.inr ⟨hi, h₁, h₂⟩) a₁ a₂
          refine ⟨rfl, ?_⟩
          cases o₁ <;> cases o₂ <;> simp only [LXRel, IRel] at hr ⊢
          obtain ⟨rfl, rfl, rfl, -, ht⟩ := hr
          cases sexec_true a₁
          refine ⟨rfl, rfl, rfl, nofun, fun _ => ?_⟩
          rcases ht rfl with ha | ha
          · exact .inl (A.meet_left ha)
          · exact .inr ha
        · rw [h₁] at a₁ a₂ ⊢
          obtain ⟨rfl, hr⟩ := loopSeq_rel H ihJ (fun k k' x y => ihT k k' x y) hall hσp hb hl hc
            w₁ w₂ hW hi h₁ h₂ a₁ a₂
          refine ⟨rfl, ?_⟩
          cases o₁ <;> cases o₂ <;> simp only [LXRel, IRel] at hr ⊢
          obtain ⟨rfl, rfl, rfl, hf, ht⟩ := hr
          refine ⟨rfl, rfl, rfl, fun hm => ?_, fun hm => ?_⟩
          · obtain ⟨rfl, rfl, hi'⟩ := hf hm
            exact ⟨rfl, rfl, hi', Exec.loop_eval w₁, Exec.loop_eval w₂⟩
          · rcases ht hm with ha | ha
            · exact .inl (A.meet_left ha)
            · exact .inr ha
    | iteF a₁ =>
      cases y₂ with
      | iteF a₂ =>
        rw [← hv] at a₂
        cases a₁ with
        | blockDone b₁ =>
          cases b₁
          cases a₂ with
          | blockDone b₂ =>
            cases b₂
            rw [hv]
            rcases hk with ⟨h₁, h₂, rfl, rfl⟩ | ⟨h₁, h₂, -⟩
            · rw [h₂]
              exact ⟨rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, hi, h₁, h₂⟩, by simp [Spectre.mis]⟩
            · rw [h₂]
              exact ⟨rfl, rfl, rfl, rfl, by simp [Spectre.mis], fun _ => .inr ⟨hi, h₁, h₂⟩⟩
          | blockHalt b₂ => cases b₂
        | blockHalt b₁ => cases b₁
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      obtain ⟨rfl, hr⟩ := ite a₁ a₂
      obtain ⟨rfl, hq⟩ := pe_rel H hx hr rfl rfl b₁ b₂
      exact ⟨rfl, hq⟩
    | seqHalt a₂ => exact (ite a₁ a₂).2.elim
  | seqHalt a₁ =>
    cases e₂ with
    | seq a₂ _ => exact (ite a₁ a₂).2.elim
    | seqHalt a₂ => exact ⟨(ite a₁ a₂).1, trivial⟩

/-- **Two runs of hardened code that start without misspeculating**, whose
sequential runs have equal traces, with `Inv` at the start: they leak the
same, and end as `HRel` says. -/
theorem slh_rel (H : SlhOk S A τR pt pe Inv p) (c : Prog M) : JointOk S A τR pt pe Inv p c := by
  induction c with
  | block is =>
    intro τ τ' h s₁ s₂ s₁' s₂' T₁ T₂ D n t₁ t₂ o₁ o₂ hall _ x₁ x₂ hT hi e₁ e₂
    rw [Exec.block_iff] at x₁ x₂
    have hi' := inv_block H hall hi x₁ x₂
    cases e₁ with
    | blockDone b₁ =>
      cases e₂ with
      | blockDone b₂ =>
        obtain ⟨rfl, hr⟩ := sblock_seq H.shape hT x₁ x₂ b₁ b₂
        rcases hr with ⟨h, -⟩ | ⟨k, h₁, h₂⟩
        · cases h
        · cases h₁; cases h₂; exact ⟨rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, hi'⟩, nofun⟩
      | blockHalt b₂ =>
        obtain ⟨-, hr⟩ := sblock_seq H.shape hT x₁ x₂ b₁ b₂
        rcases hr with ⟨h, -⟩ | ⟨k, -, h⟩ <;> cases h
    | blockHalt b₁ =>
      cases e₂ with
      | blockDone b₂ =>
        obtain ⟨-, hr⟩ := sblock_seq H.shape hT x₁ x₂ b₁ b₂
        rcases hr with ⟨-, h⟩ | ⟨k, h, -⟩ <;> cases h
      | blockHalt b₂ => exact ⟨(sblock_seq H.shape hT x₁ x₂ b₁ b₂).1, trivial⟩
  | seq a b iha ihb =>
    intro τ τ' h s₁ s₂ s₁' s₂' T₁ T₂ D n t₁ t₂ o₁ o₂ hall hk x₁ x₂ hT hi e₁ e₂
    simp only [Code.all, Bool.and_eq_true] at hall
    cases h with
    | seq mid h₁ h₂ =>
      simp only [scheck, Option.bind_eq_some_iff] at hk
      obtain ⟨τ₁, k₁, k₂⟩ := hk
      split at k₂ <;> [rename_i hle; cases k₂]
      cases x₁ with
      | seq xa₁ xb₁ =>
        cases x₂ with
        | seq xa₂ xb₂ =>
          obtain ⟨hA, hB⟩ := Exec.prefix_eq H.shape xa₁ xa₂ hT
          cases e₁ with
          | seq a₁ b₁ =>
            cases e₂ with
            | seq a₂ b₂ =>
              obtain ⟨rfl, hr⟩ := iha hall.1 k₁ xa₁ xa₂ hA hi a₁ a₂
              obtain ⟨hD, rfl, hcase⟩ := hr.cases_done
              cases hD
              rcases hcase with ⟨rfl, rfl, rfl, rfl, hi'⟩ | ⟨rfl, rfl, ha⟩
              · obtain ⟨rfl, hq⟩ := ihb hall.2 k₂ xb₁ xb₂ hB hi' b₁ b₂
                exact ⟨rfl, hq⟩
              · obtain ⟨rfl, hq⟩ := scheck_sound H.sound H.pro b k₂ (A.le_sound hle ha) b₁ b₂
                exact ⟨rfl, HRel.of_orel b₁ hq⟩
            | seqHalt a₂ => exact (iha hall.1 k₁ xa₁ xa₂ hA hi a₁ a₂).2.elim
          | seqHalt a₁ =>
            cases e₂ with
            | seq a₂ _ => exact (iha hall.1 k₁ xa₁ xa₂ hA hi a₁ a₂).2.elim
            | seqHalt a₂ => exact ⟨(iha hall.1 k₁ xa₁ xa₂ hA hi a₁ a₂).1, trivial⟩
    | _ => simp [scheck] at hk
  | ite c t e iht ihe =>
    intro τ τ' h s₁ s₂ s₁' s₂' T₁ T₂ D n t₁ t₂ o₁ o₂ hall hk x₁ x₂ hT hi e₁ e₂
    simp only [Code.all, Bool.and_eq_true] at hall
    cases h with
    | ite h₁ h₂ =>
      simp only [scheck] at hk
      split at hk <;> [skip; cases hk]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hk
      obtain ⟨τt, kt, τe, ke, τ₁, k₁, τ₂, k₂, rfl⟩ := hk
      -- Which way the sequential runs go.
      have key : ∃ v, M.eval c s₁ = some v ∧ M.eval c s₂ = some v ∧
          (v = true → ∃ U₁ U₂, Exec M t s₁ U₁ s₁' ∧ Exec M t s₂ U₂ s₂' ∧ U₁ = U₂) ∧
          (v = false → ∃ U₁ U₂, Exec M e s₁ U₁ s₁' ∧ Exec M e s₂ U₂ s₂' ∧ U₁ = U₂) := by
        cases x₁ with
        | iteT g₁ y₁ =>
          cases x₂ with
          | iteT g₂ y₂ =>
            simp only [List.cons.injEq, true_and] at hT
            exact ⟨true, g₁, g₂, fun _ => ⟨_, _, y₁, y₂, hT⟩, nofun⟩
          | iteF _ _ => simp at hT
        | iteF g₁ y₁ =>
          cases x₂ with
          | iteF g₂ y₂ =>
            simp only [List.cons.injEq, true_and] at hT
            exact ⟨false, g₁, g₂, nofun, fun _ => ⟨_, _, y₁, y₂, hT⟩⟩
          | iteT _ _ => simp at hT
      obtain ⟨v, hv₁, hv₂, kt', ke'⟩ := key
      cases e₁ with
      | iteEnd => cases e₂ with | iteEnd => rw [hv₁, hv₂]; exact ⟨rfl, trivial⟩
      | iteT a₁ =>
        cases e₂ with
        | iteT a₂ =>
          rw [hv₁] at a₁ ⊢; rw [hv₂] at a₂ ⊢
          cases v with
          | true =>
            obtain ⟨U₁, U₂, y₁, y₂, hU⟩ := kt' rfl
            obtain ⟨rfl, hq⟩ := nopSeq_rel H (H.pt_nop _ _ hv₁) (H.pt_nop _ _ hv₂) trivial
              (fun z₁ z₂ => iht hall.1 k₁ y₁ y₂ hU hi z₁ z₂) (sexec_prefixArm a₁) (sexec_prefixArm a₂)
            exact ⟨rfl, hq.mono fun _ _ => A.meet_left⟩
          | false =>
            obtain ⟨rfl, hq⟩ := freshSeq_rel (τ := A.meet τt τR)
              (fun y₁ y₂ => let ⟨ht, hr⟩ := H.pro.pt hi hv₁ hv₂ y₁ y₂
                ⟨ht, hr.mono fun _ _ => A.meet_right⟩)
              (fun hu z₁ z₂ => scheck_sound H.sound H.pro t k₁ hu z₁ z₂)
              (sexec_prefixArm a₁) (sexec_prefixArm a₂)
            exact ⟨rfl, HRel.of_orel a₁ (Taint.ORel.mono (fun _ _ => A.meet_left) hq)⟩
      | iteF a₁ =>
        cases e₂ with
        | iteF a₂ =>
          rw [hv₁] at a₁ ⊢; rw [hv₂] at a₂ ⊢
          cases v with
          | false =>
            obtain ⟨U₁, U₂, y₁, y₂, hU⟩ := ke' rfl
            obtain ⟨rfl, hq⟩ := nopSeq_rel H (H.pe_nop _ _ hv₁) (H.pe_nop _ _ hv₂) trivial
              (fun z₁ z₂ => ihe hall.2 k₂ y₁ y₂ hU hi z₁ z₂) a₁ a₂
            exact ⟨rfl, hq.mono fun _ _ => A.meet_right⟩
          | true =>
            obtain ⟨rfl, hq⟩ := freshSeq_rel (τ := A.meet τe τR)
              (fun y₁ y₂ => let ⟨ht, hr⟩ := H.pro.pe hi hv₁ hv₂ y₁ y₂
                ⟨ht, hr.mono fun _ _ => A.meet_right⟩)
              (fun hu z₁ z₂ => scheck_sound H.sound H.pro e k₂ hu z₁ z₂) a₁ a₂
            exact ⟨rfl, HRel.of_orel a₁ (Taint.ORel.mono (fun _ _ => A.meet_right) hq)⟩
    | _ => simp [scheck] at hk
  | loop b c ih =>
    intro τ τ' h s₁ s₂ s₁' s₂' T₁ T₂ D n t₁ t₂ o₁ o₂ hall hk x₁ x₂ hT hi e₁ e₂
    simp only [Code.all] at hall
    cases h with
    | seq σ h₁ h₂ =>
      simp only [scheck, Option.bind_eq_some_iff] at hk
      obtain ⟨τ₀, k₀, hk⟩ := hk
      split at hk <;> [rename_i hc₀; cases hk]
      simp only [Bool.and_eq_true] at hc₀
      simp only [Option.bind_eq_some_iff] at hk
      obtain ⟨σp, kp, σ', kb, hk⟩ := hk
      split at hk <;> [rename_i hl; cases hk]
      simp only [Bool.and_eq_true] at hl
      simp only [Option.map_eq_some_iff] at hk
      obtain ⟨τx, kx, rfl⟩ := hk
      -- The first body, and how the loop goes on.
      have key : ∃ y₁ y₂ U₁ U₂, Exec M b s₁ U₁ y₁ ∧ Exec M b s₂ U₂ y₂ ∧ U₁ = U₂ ∧
          ((M.eval c y₁ = some false ∧ M.eval c y₂ = some false ∧ s₁' = y₁ ∧ s₂' = y₂) ∨
            (M.eval c y₁ = some true ∧ M.eval c y₂ = some true ∧ ∃ W₁ W₂,
              Exec M (.loop b c) y₁ W₁ s₁' ∧ Exec M (.loop b c) y₂ W₂ s₂' ∧ W₁ = W₂)) := by
        cases x₁ with
        | loopExit xb₁ hc₁ =>
          cases x₂ with
          | loopExit xb₂ hc₂ =>
            obtain ⟨hU, -⟩ := Exec.prefix_eq H.shape xb₁ xb₂ hT
            exact ⟨_, _, _, _, xb₁, xb₂, hU, .inl ⟨hc₁, hc₂, rfl, rfl⟩⟩
          | loopNext xb₂ _ _ =>
            obtain ⟨-, h'⟩ := Exec.prefix_eq H.shape xb₁ xb₂ hT
            simp at h'
        | loopNext xb₁ hc₁ xr₁ =>
          cases x₂ with
          | loopExit xb₂ _ =>
            obtain ⟨-, h'⟩ := Exec.prefix_eq H.shape xb₁ xb₂ hT
            simp at h'
          | loopNext xb₂ hc₂ xr₂ =>
            obtain ⟨hU, hW⟩ := Exec.prefix_eq H.shape xb₁ xb₂ hT
            simp only [List.cons.injEq, true_and] at hW
            exact ⟨_, _, _, _, xb₁, xb₂, hU, .inr ⟨hc₁, hc₂, _, _, xr₁, xr₂, hW⟩⟩
      obtain ⟨y₁, y₂, U₁, U₂, xb₁, xb₂, hU, hkind⟩ := key
      have ihT := fun {τ τ' h u₁ u₂ D n t₁ t₂ o₁ o₂} =>
        @scheck_sound M S A τR pt pe Inv H.sound H.pro b τ τ' h u₁ u₂ D n t₁ t₂ o₁ o₂
      cases e₁ with
      | seq a₁ b₁ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨rfl, hr⟩ := ih hall k₀ xb₁ xb₂ hU hi a₁ a₂
          obtain ⟨hD, rfl, hcase⟩ := hr.cases_done
          cases hD
          rcases hcase with ⟨rfl, rfl, rfl, rfl, hi'⟩ | ⟨rfl, rfl, ha⟩
          · obtain ⟨rfl, hq⟩ := loopRest_rel H ih ihT hall kp kb hl.1 hl.2 kx hi' hkind b₁ b₂
            exact ⟨rfl, hq⟩
          · obtain ⟨rfl, hq⟩ := loopRest_sound H.sound H.pro ihT hc₀.1 hc₀.2 kp kb hl.1 hl.2 kx ha b₁ b₂
            exact ⟨rfl, HRel.of_orel b₁ hq⟩
        | seqHalt a₂ => exact (ih hall k₀ xb₁ xb₂ hU hi a₁ a₂).2.elim
      | seqHalt a₁ =>
        cases e₂ with
        | seq a₂ _ => exact (ih hall k₀ xb₁ xb₂ hU hi a₁ a₂).2.elim
        | seqHalt a₂ => exact ⟨(ih hall k₀ xb₁ xb₂ hU hi a₁ a₂).1, trivial⟩
    | _ => simp [scheck] at hk
  | call nm body ih =>
    intro τ τ' h s₁ s₂ s₁' s₂' T₁ T₂ D n t₁ t₂ o₁ o₂ hall hk x₁ x₂ hT hi e₁ e₂
    simp only [Code.all] at hall
    cases h with
    | call hb =>
      simp only [scheck, Option.bind_eq_some_iff] at hk
      obtain ⟨τ₁, k₁, τ₂, k₂, k₃⟩ := hk
      cases x₁ with
      | call hc₁ xb₁ hr₁ =>
        cases x₂ with
        | call hc₂ xb₂ hr₂ =>
          simp only [List.append_assoc] at hT
          obtain ⟨hca, hT₁⟩ := map_addr_append hT (H.shape.callAddrs _ _)
          obtain ⟨hU, hT₂⟩ := Exec.prefix_eq H.shape xb₁ xb₂ hT₁
          have hra := map_addr_inj hT₂
          have hi₁ := H.call hi hc₁ hc₂
          cases e₁ with
          | callHalt hc₁' a₁ =>
            rw [hc₁] at hc₁'; cases hc₁'
            cases e₂ with
            | callHalt hc₂' a₂ =>
              rw [hc₂] at hc₂'; cases hc₂'
              obtain ⟨rfl, -⟩ := ih hall k₂ xb₁ xb₂ hU hi₁ a₁ a₂
              rw [hca]; exact ⟨rfl, trivial⟩
            | call hc₂' a₂ _ =>
              rw [hc₂] at hc₂'; cases hc₂'
              exact (ih hall k₂ xb₁ xb₂ hU hi₁ a₁ a₂).2.elim
          | call hc₁' a₁ hr₁' =>
            rw [hc₁] at hc₁'; cases hc₁'
            cases e₂ with
            | callHalt hc₂' a₂ =>
              rw [hc₂] at hc₂'; cases hc₂'
              exact (ih hall k₂ xb₁ xb₂ hU hi₁ a₁ a₂).2.elim
            | call hc₂' a₂ hr₂' =>
              rw [hc₂] at hc₂'; cases hc₂'
              obtain ⟨rfl, hr⟩ := ih hall k₂ xb₁ xb₂ hU hi₁ a₁ a₂
              obtain ⟨hD, rfl, hcase⟩ := hr.cases_done
              cases hD
              rcases hcase with ⟨rfl, rfl, rfl, rfl, hi'⟩ | ⟨rfl, rfl, ha⟩
              · simp only [Spectre.ret, Bool.false_eq_true, ↓reduceIte] at hr₁' hr₂'
                rw [hr₁] at hr₁'; cases hr₁'
                rw [hr₂] at hr₂'; cases hr₂'
                rw [hca, hra]
                exact ⟨rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, H.ret hi' hr₁ hr₂⟩, nofun⟩
              · obtain ⟨ha₃, ha₃'⟩ := H.sound.sret ha k₃ hr₁' hr₂'
                rw [hca, ha₃]
                exact ⟨rfl, rfl, rfl, rfl, nofun, fun _ => ha₃'⟩
    | _ => simp [scheck] at hk
  | frame i body j ih =>
    intro τ τ' h s₁ s₂ s₁' s₂' T₁ T₂ D n t₁ t₂ o₁ o₂ hall hk x₁ x₂ hT hi e₁ e₂
    simp only [Code.all, Bool.and_eq_true] at hall
    cases h with
    | frame hb =>
      simp only [scheck, Option.bind_eq_some_iff] at hk
      obtain ⟨τ₁, k₁, τ₂, k₂, k₃⟩ := hk
      cases x₁ with
      | frame hp₁ xb₁ hq₁ =>
        cases x₂ with
        | frame hp₂ xb₂ hq₂ =>
          simp only [List.append_assoc] at hT
          obtain ⟨hpa, hT₁⟩ := map_addr_append hT (H.shape.addrs _ _ _)
          obtain ⟨hU, hT₂⟩ := Exec.prefix_eq H.shape xb₁ xb₂ hT₁
          have hqa := map_addr_inj hT₂
          have hi₁ := H.push hi hp₁ hp₂
          cases e₁ with
          | frameHalt hp₁' a₁ =>
            rw [hp₁] at hp₁'; cases hp₁'
            cases e₂ with
            | frameHalt hp₂' a₂ =>
              rw [hp₂] at hp₂'; cases hp₂'
              obtain ⟨rfl, -⟩ := ih hall.1.2 k₂ xb₁ xb₂ hU hi₁ a₁ a₂
              rw [hpa]; exact ⟨rfl, trivial⟩
            | frame hp₂' a₂ _ =>
              rw [hp₂] at hp₂'; cases hp₂'
              exact (ih hall.1.2 k₂ xb₁ xb₂ hU hi₁ a₁ a₂).2.elim
          | frame hp₁' a₁ hq₁' =>
            rw [hp₁] at hp₁'; cases hp₁'
            cases e₂ with
            | frameHalt hp₂' a₂ =>
              rw [hp₂] at hp₂'; cases hp₂'
              exact (ih hall.1.2 k₂ xb₁ xb₂ hU hi₁ a₁ a₂).2.elim
            | frame hp₂' a₂ hq₂' =>
              rw [hp₂] at hp₂'; cases hp₂'
              obtain ⟨rfl, hr⟩ := ih hall.1.2 k₂ xb₁ xb₂ hU hi₁ a₁ a₂
              obtain ⟨hD, rfl, hcase⟩ := hr.cases_done
              cases hD
              rcases hcase with ⟨rfl, rfl, rfl, rfl, hi'⟩ | ⟨rfl, rfl, ha⟩
              · rw [hq₁] at hq₁'; cases hq₁'
                rw [hq₂] at hq₂'; cases hq₂'
                rw [hpa, hqa]
                exact ⟨rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, H.pop hi' hq₁ hq₂⟩, nofun⟩
              · obtain ⟨ha₃, ha₃'⟩ := A.pop_sound ha k₃ hq₁' hq₂'
                rw [hpa, ha₃]
                exact ⟨rfl, rfl, rfl, rfl, nofun, fun _ => ha₃'⟩
    | _ => simp [scheck] at hk

/-- **Hardening makes constant-time code speculatively constant time**,
given the transient analysis (`scheck`, from any taint: it assumes nothing of
the runs before they mispredict). -/
theorem specConstantTime_harden (H : SlhOk S A τR pt pe Inv p) {Pre : M.State → Prop}
    {Pub : M.State → M.State → Prop} {c : Prog M} {τ τ' : A.T} {h : Taint.Hint A.T}
    (hall : c.all p = true) (hk : scheck A τR pt pe τ c h = some τ')
    (hv : ∀ s, Pre s → ∃ t s', Exec M c s t s') (hct : ConstantTime M Pre Pub c)
    (hinv : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → Inv s₁ s₂) :
    SpecConstantTime S Pre Pub (c.harden pt pe) := by
  intro s₁ s₂ D n t₁ t₂ o₁ o₂ h₁ h₂ hp e₁ e₂
  obtain ⟨T₁, s₁', x₁⟩ := hv s₁ h₁
  obtain ⟨T₂, s₂', x₂⟩ := hv s₂ h₂
  exact (slh_rel H c hall hk x₁ x₂ (hct _ _ _ _ _ _ h₁ h₂ hp x₁ x₂) (hinv _ _ h₁ h₂ hp) e₁ e₂).1

/-- **Hardened code with a barrier before it returns is speculatively
safe.** -/
theorem specSafe_harden (H : SlhOk S A τR pt pe Inv p) {f : M.Instr} (hn : Nop M f)
    (hf : S.fence f = true) {Pre : M.State → Prop} {Pub : M.State → M.State → Prop} {c : Prog M}
    {τ τ' : A.T} {h : Taint.Hint A.T} (hall : c.all p = true) (hk : scheck A τR pt pe τ c h = some τ')
    (hv : ∀ s, Pre s → ∃ t s', Exec M c s t s') (hct : ConstantTime M Pre Pub c)
    (hinv : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → Inv s₁ s₂) :
    SpecSafe S Pre Pub (.seq (c.harden pt pe) (.block [f])) := by
  refine ⟨fun s₁ s₂ D n t₁ t₂ o₁ o₂ h₁ h₂ hp e₁ e₂ => ?_, fun s D n t s' ms D' n' _ e => ?_⟩
  · obtain ⟨T₁, s₁', x₁⟩ := hv s₁ h₁
    obtain ⟨T₂, s₂', x₂⟩ := hv s₂ h₂
    have rel := fun {D n t₁ t₂ o₁ o₂} => @slh_rel M S A τR pt pe Inv p H c _ _ _ _ _ _ _ _ _ D n
      t₁ t₂ o₁ o₂ hall hk x₁ x₂ (hct _ _ _ _ _ _ h₁ h₂ hp x₁ x₂) (hinv _ _ h₁ h₂ hp)
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq a₂ b₂ =>
        obtain ⟨rfl, hr⟩ := rel a₁ a₂
        obtain ⟨hD, rfl, hcase⟩ := hr.cases_done
        cases hD
        rcases hcase with ⟨rfl, rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩
        · cases b₁ with
          | blockDone y₁ =>
            cases b₂ with
            | blockDone y₂ =>
              rw [(sblock_fence_false hn y₁).1, (sblock_fence_false hn y₂).1]
            | blockHalt y₂ => rw [(sblock_fence_false hn y₁).1, (sblock_fence_false hn y₂).1]
          | blockHalt y₁ =>
            cases b₂ with
            | blockDone y₂ => rw [(sblock_fence_false hn y₁).1, (sblock_fence_false hn y₂).1]
            | blockHalt y₂ => rw [(sblock_fence_false hn y₁).1, (sblock_fence_false hn y₂).1]
        · cases b₁ with
          | blockDone y₁ => exact absurd (sblock_fence_true hf y₁).2 nofun
          | blockHalt y₁ =>
            cases b₂ with
            | blockDone y₂ => exact absurd (sblock_fence_true hf y₂).2 nofun
            | blockHalt y₂ => rw [(sblock_fence_true hf y₁).1, (sblock_fence_true hf y₂).1]
      | seqHalt a₂ => exact absurd (rel a₁ a₂).2 id
    | seqHalt a₁ =>
      cases e₂ with
      | seq a₂ _ => exact absurd (rel a₁ a₂).2 id
      | seqHalt a₂ => exact (rel a₁ a₂).1
  · cases e with
    | seq _ b =>
      cases b with
      | blockDone y =>
        cases y with
        | cons hf' _ y => cases y; simpa [hf] using hf'

/-- Hardening keeps an artifact verified. -/
theorem Verified.harden {T : Target} {pt pe : T.isa.Cond → List T.isa.Instr}
    (hpt : ∀ c s, T.isa.eval c s = some true → execBlock T.isa (pt c) s = some (s, []))
    (hpe : ∀ c s, T.isa.eval c s = some false → execBlock T.isa (pe c) s = some (s, []))
    {f : T.isa.Instr} (hn : Nop T.isa f) {c : Prog T.isa} {k : Contract T.isa} (h : Verified T c k) :
    Verified T (.seq (c.harden pt pe) (.block [f])) k :=
  have hx : ∀ {s t s'}, Exec T.isa (.seq (c.harden pt pe) (.block [f])) s t s' ↔ Exec T.isa c s t s' :=
    (Exec.seqFence_iff hn).trans (Exec.harden_iff hpt hpe c)
  ⟨fun s hs => let ⟨t, s', e, h₁, h₂⟩ := h.1 s hs; ⟨t, s', hx.mpr e, h₁, h₂⟩,
   fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => h.2.1 _ _ _ _ _ _ h₁ h₂ hp (hx.mp e₁) (hx.mp e₂), h.2.2⟩

end Joint

end VG
