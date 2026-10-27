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

end VG
