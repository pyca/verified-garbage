import VerifiedGarbage.Proof.Framework.TaintSum

/-!
# The analysis of code with its instructions rewritten

An analysis may not read part of an instruction (e.g. the displacement of a
memory operand, from a taint that knows no region bases), as long as its
taint satisfies an invariant `P` that every step keeps (`MapInv`). Then it
checks code with that part rewritten by `f` (`Code.mapBlocks f`) exactly as
the code itself (`check_mapBlocks`, `checkSum_mapBlocks`). Copies of code that
differ only there (field arithmetic on different slots of a working space)
become the same code, whose analysis from the same taint the kernel
evaluates once.
-/

namespace VG

/-- `c` with `f` applied to the instructions of its blocks, also in the
functions it calls and in its frames (but not to a frame's own push and
pop). -/
def Code.mapBlocks {I C : Type} (f : I → I) : Code I C → Code I C
  | .block is => .block (KList.map f is)
  | .seq a b => .seq (a.mapBlocks f) (b.mapBlocks f)
  | .ite c t e => .ite c (t.mapBlocks f) (e.mapBlocks f)
  | .loop b c => .loop (b.mapBlocks f) c
  | .call n b => .call n (b.mapBlocks f)
  | .frame i b j => .frame i (b.mapBlocks f) j

namespace Taint

variable {M : ISA} (A : Taint M)

/-- The analysis does not read what `f` rewrites, from a taint that satisfies
`P`, which every step keeps (and every taint a hint continues from, `le`). -/
structure MapInv (f : M.Instr → M.Instr) (P : A.T → Prop) : Prop where
  step : ∀ {τ} (i : M.Instr), P τ → A.step τ (f i) = A.step τ i
  step_P : ∀ {τ τ'} (i : M.Instr), P τ → A.step τ i = some τ' → P τ'
  le_P : ∀ {m τ}, P τ → A.le m τ = true → P m
  meet_P : ∀ {τ₁ τ₂}, P τ₁ → P (A.meet τ₁ τ₂)
  call_P : ∀ {τ τ'}, P τ → A.call τ = some τ' → P τ'
  ret_P : ∀ {τ τ'}, P τ → A.ret τ = some τ' → P τ'
  push_P : ∀ {τ τ'} (i : M.Instr), P τ → A.push τ i = some τ' → P τ'
  pop_P : ∀ {τ τ'} (i : M.Instr), P τ → A.pop τ i = some τ' → P τ'

variable {A} {f : M.Instr → M.Instr} {P : A.T → Prop}

theorem MapInv.checkBlock (hA : A.MapInv f P) (is : List M.Instr) :
    ∀ τ, P τ → A.checkBlock τ (KList.map f is) = A.checkBlock τ is ∧
      ∀ τ', A.checkBlock τ is = some τ' → P τ' := by
  induction is with
  | nil => exact fun τ hτ => ⟨rfl, fun τ' h => by cases h; exact hτ⟩
  | cons i is ih =>
    intro τ hτ
    show (A.step τ (f i)).bind (A.checkBlock · (KList.map f is)) = (A.step τ i).bind (A.checkBlock · is) ∧
      ∀ τ', (A.step τ i).bind (A.checkBlock · is) = some τ' → P τ'
    rw [hA.step i hτ]
    cases e : A.step τ i with
    | none => exact ⟨rfl, fun _ h => by cases h⟩
    | some τ₁ => exact ih τ₁ (hA.step_P i hτ e)

theorem MapInv.checkChunks (hA : A.MapInv f P) {chunkSize : Nat} (ms : List A.T) :
    ∀ τ (is : List M.Instr), P τ → A.checkChunks chunkSize τ (KList.map f is) ms =
      A.checkChunks chunkSize τ is ms ∧ ∀ τ', A.checkChunks chunkSize τ is ms = some τ' → P τ' := by
  induction ms with
  | nil => exact fun τ is hτ => hA.checkBlock is τ hτ
  | cons m ms ih =>
    intro τ is hτ
    have ht : KList.take chunkSize (KList.map f is) = KList.map f (KList.take chunkSize is) := by
      rw [KList.take_eq, KList.map_eq, KList.map_eq, KList.take_eq, List.map_take]
    have hd : KList.drop chunkSize (KList.map f is) = KList.map f (KList.drop chunkSize is) := by
      rw [KList.drop_eq, KList.map_eq, KList.map_eq, KList.drop_eq, List.map_drop]
    show ((A.checkBlock τ (KList.take chunkSize (KList.map f is))).bind fun τ' =>
        if A.le m τ' then A.checkChunks chunkSize m (KList.drop chunkSize (KList.map f is)) ms else none) =
      ((A.checkBlock τ (KList.take chunkSize is)).bind fun τ' =>
        if A.le m τ' then A.checkChunks chunkSize m (KList.drop chunkSize is) ms else none) ∧
      ∀ τ', ((A.checkBlock τ (KList.take chunkSize is)).bind fun τ' =>
        if A.le m τ' then A.checkChunks chunkSize m (KList.drop chunkSize is) ms else none) = some τ' → P τ'
    rw [ht, hd, (hA.checkBlock _ τ hτ).1]
    have hb := (hA.checkBlock (KList.take chunkSize is) τ hτ).2
    cases e : A.checkBlock τ (KList.take chunkSize is) with
    | none => exact ⟨rfl, fun _ h => by cases h⟩
    | some τ₁ =>
      simp only [Option.bind_some]
      by_cases hl : A.le m τ₁ = true
      · simp only [hl, ite_true]
        exact ih m _ (hA.le_P (hb τ₁ e) hl)
      · simp only [hl]
        exact ⟨rfl, fun _ h => by cases h⟩

/-- The analysis of `c` with `f` applied to its instructions is that of `c`,
from a taint that satisfies `P` (and the taint it ends with satisfies `P`). -/
theorem MapInv.check (hA : A.MapInv f P) (c : Prog M) :
    ∀ τ (h : Hint A.T), P τ → A.check τ (c.mapBlocks f) h = A.check τ c h ∧
      ∀ τ', A.check τ c h = some τ' → P τ' := by
  induction c with
  | block is =>
    intro τ h hτ
    cases h with
    | block ms chunkSize => exact hA.checkChunks ms τ is hτ
    | _ => exact ⟨rfl, fun _ h => by cases h⟩
  | seq a b iha ihb =>
    intro τ h hτ
    cases h with
    | seq mid h₁ h₂ =>
      show ((A.check τ (a.mapBlocks f) h₁).bind fun τ' =>
          if A.le mid τ' then A.check mid (b.mapBlocks f) h₂ else none) =
        ((A.check τ a h₁).bind fun τ' => if A.le mid τ' then A.check mid b h₂ else none) ∧
        ∀ τ', ((A.check τ a h₁).bind fun τ' => if A.le mid τ' then A.check mid b h₂ else none) =
          some τ' → P τ'
      rw [(iha τ h₁ hτ).1]
      have ha := (iha τ h₁ hτ).2
      cases e : A.check τ a h₁ with
      | none => exact ⟨rfl, fun _ h => by cases h⟩
      | some τ₁ =>
        simp only [Option.bind_some]
        by_cases hl : A.le mid τ₁ = true
        · simp only [hl, ite_true]
          exact ihb mid h₂ (hA.le_P (ha τ₁ e) hl)
        · simp only [hl]
          exact ⟨rfl, fun _ h => by cases h⟩
    | _ => exact ⟨rfl, fun _ h => by cases h⟩
  | ite c t e iht ihe =>
    intro τ h hτ
    cases h with
    | ite h₁ h₂ =>
      show (if A.condPub τ c then (A.check τ (t.mapBlocks f) h₁).bind fun τ₁ =>
            (A.check τ (e.mapBlocks f) h₂).map fun τ₂ => A.meet τ₁ τ₂ else none) =
          (if A.condPub τ c then (A.check τ t h₁).bind fun τ₁ =>
            (A.check τ e h₂).map fun τ₂ => A.meet τ₁ τ₂ else none) ∧
        ∀ τ', (if A.condPub τ c then (A.check τ t h₁).bind fun τ₁ =>
            (A.check τ e h₂).map fun τ₂ => A.meet τ₁ τ₂ else none) = some τ' → P τ'
      rw [(iht τ h₁ hτ).1, (ihe τ h₂ hτ).1]
      refine ⟨rfl, fun τ' hs => ?_⟩
      split at hs <;> [skip; cases hs]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs
      obtain ⟨τ₁, h₁', τ₂, -, rfl⟩ := hs
      exact hA.meet_P ((iht τ h₁ hτ).2 τ₁ h₁')
    | _ => exact ⟨rfl, fun _ h => by cases h⟩
  | loop b c ih =>
    intro τ h hτ
    cases h with
    | loop σ hb =>
      show (if A.le σ τ then (A.check σ (b.mapBlocks f) hb).bind fun σ' =>
            if A.le σ σ' && A.condPub σ' c then some σ' else none else none) =
          (if A.le σ τ then (A.check σ b hb).bind fun σ' =>
            if A.le σ σ' && A.condPub σ' c then some σ' else none else none) ∧
        ∀ τ', (if A.le σ τ then (A.check σ b hb).bind fun σ' =>
            if A.le σ σ' && A.condPub σ' c then some σ' else none else none) = some τ' → P τ'
      by_cases hl : A.le σ τ = true
      · simp only [hl, ite_true]
        have hσ := hA.le_P hτ hl
        rw [(ih σ hb hσ).1]
        refine ⟨rfl, fun τ' hs => ?_⟩
        simp only [Option.bind_eq_some_iff] at hs
        obtain ⟨σ', h', hs⟩ := hs
        split at hs <;> [cases hs; cases hs]
        exact (ih σ hb hσ).2 _ h'
      · simp only [hl]
        exact ⟨rfl, fun _ h => by cases h⟩
    | _ => exact ⟨rfl, fun _ h => by cases h⟩
  | call n b ih =>
    intro τ h hτ
    cases h with
    | call hb =>
      show ((A.call τ).bind fun τ₁ => (A.check τ₁ (b.mapBlocks f) hb).bind A.ret) =
          ((A.call τ).bind fun τ₁ => (A.check τ₁ b hb).bind A.ret) ∧
        ∀ τ', ((A.call τ).bind fun τ₁ => (A.check τ₁ b hb).bind A.ret) = some τ' → P τ'
      cases e : A.call τ with
      | none => exact ⟨rfl, fun _ h => by cases h⟩
      | some τ₁ =>
        have h₁ := hA.call_P hτ e
        simp only [Option.bind_some]
        rw [(ih τ₁ hb h₁).1]
        refine ⟨rfl, fun τ' hs => ?_⟩
        simp only [Option.bind_eq_some_iff] at hs
        obtain ⟨τ₂, h₂, h₃⟩ := hs
        exact hA.ret_P ((ih τ₁ hb h₁).2 τ₂ h₂) h₃
    | _ => exact ⟨rfl, fun _ h => by cases h⟩
  | frame i b j ih =>
    intro τ h hτ
    cases h with
    | frame hb =>
      show ((A.push τ i).bind fun τ₁ => (A.check τ₁ (b.mapBlocks f) hb).bind fun τ₂ => A.pop τ₂ j) =
          ((A.push τ i).bind fun τ₁ => (A.check τ₁ b hb).bind fun τ₂ => A.pop τ₂ j) ∧
        ∀ τ', ((A.push τ i).bind fun τ₁ => (A.check τ₁ b hb).bind fun τ₂ => A.pop τ₂ j) =
          some τ' → P τ'
      cases e : A.push τ i with
      | none => exact ⟨rfl, fun _ h => by cases h⟩
      | some τ₁ =>
        have h₁ := hA.push_P i hτ e
        simp only [Option.bind_some]
        rw [(ih τ₁ hb h₁).1]
        refine ⟨rfl, fun τ' hs => ?_⟩
        simp only [Option.bind_eq_some_iff] at hs
        obtain ⟨τ₂, h₂, h₃⟩ := hs
        exact hA.pop_P j ((ih τ₁ hb h₁).2 τ₂ h₂) h₃
    | _ => exact ⟨rfl, fun _ h => by cases h⟩

/-- `check_mapBlocks` without summaries (`checkSum` with none). -/
theorem MapInv.checkSum [Frame A] (hA : A.MapInv f P) (c : Prog M) :
    ∀ τ (h : SHint A.T), P τ → A.checkSum [] τ (c.mapBlocks f) h = A.checkSum [] τ c h ∧
      ∀ τ', A.checkSum [] τ c h = some τ' → P τ' := by
  induction c with
  | block is =>
    intro τ h hτ
    cases h with
    | block ms => exact hA.checkChunks ms τ is hτ
    | _ => exact ⟨rfl, fun _ h => by cases h⟩
  | seq a b iha ihb =>
    intro τ h hτ
    cases h with
    | seq mid h₁ h₂ =>
      show ((A.checkSum [] τ (a.mapBlocks f) h₁).bind fun τ' =>
          if A.le mid τ' then A.checkSum [] mid (b.mapBlocks f) h₂ else none) =
        ((A.checkSum [] τ a h₁).bind fun τ' => if A.le mid τ' then A.checkSum [] mid b h₂ else none) ∧
        ∀ τ', ((A.checkSum [] τ a h₁).bind fun τ' =>
          if A.le mid τ' then A.checkSum [] mid b h₂ else none) = some τ' → P τ'
      rw [(iha τ h₁ hτ).1]
      have ha := (iha τ h₁ hτ).2
      cases e : A.checkSum [] τ a h₁ with
      | none => exact ⟨rfl, fun _ h => by cases h⟩
      | some τ₁ =>
        simp only [Option.bind_some]
        by_cases hl : A.le mid τ₁ = true
        · simp only [hl, ite_true]
          exact ihb mid h₂ (hA.le_P (ha τ₁ e) hl)
        · simp only [hl]
          exact ⟨rfl, fun _ h => by cases h⟩
    | sum k => exact ⟨rfl, fun _ h => by cases h⟩
    | _ => exact ⟨rfl, fun _ h => by cases h⟩
  | ite c t e iht ihe =>
    intro τ h hτ
    cases h with
    | ite h₁ h₂ =>
      show (if A.condPub τ c then (A.checkSum [] τ (t.mapBlocks f) h₁).bind fun τ₁ =>
            (A.checkSum [] τ (e.mapBlocks f) h₂).map fun τ₂ => A.meet τ₁ τ₂ else none) =
          (if A.condPub τ c then (A.checkSum [] τ t h₁).bind fun τ₁ =>
            (A.checkSum [] τ e h₂).map fun τ₂ => A.meet τ₁ τ₂ else none) ∧
        ∀ τ', (if A.condPub τ c then (A.checkSum [] τ t h₁).bind fun τ₁ =>
            (A.checkSum [] τ e h₂).map fun τ₂ => A.meet τ₁ τ₂ else none) = some τ' → P τ'
      rw [(iht τ h₁ hτ).1, (ihe τ h₂ hτ).1]
      refine ⟨rfl, fun τ' hs => ?_⟩
      split at hs <;> [skip; cases hs]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs
      obtain ⟨τ₁, h₁', τ₂, -, rfl⟩ := hs
      exact hA.meet_P ((iht τ h₁ hτ).2 τ₁ h₁')
    | sum k => exact ⟨rfl, fun _ h => by cases h⟩
    | _ => exact ⟨rfl, fun _ h => by cases h⟩
  | loop b c ih =>
    intro τ h hτ
    cases h with
    | loop σ hb =>
      show (if A.le σ τ then (A.checkSum [] σ (b.mapBlocks f) hb).bind fun σ' =>
            if A.le σ σ' && A.condPub σ' c then some σ' else none else none) =
          (if A.le σ τ then (A.checkSum [] σ b hb).bind fun σ' =>
            if A.le σ σ' && A.condPub σ' c then some σ' else none else none) ∧
        ∀ τ', (if A.le σ τ then (A.checkSum [] σ b hb).bind fun σ' =>
            if A.le σ σ' && A.condPub σ' c then some σ' else none else none) = some τ' → P τ'
      by_cases hl : A.le σ τ = true
      · simp only [hl, ite_true]
        have hσ := hA.le_P hτ hl
        rw [(ih σ hb hσ).1]
        refine ⟨rfl, fun τ' hs => ?_⟩
        simp only [Option.bind_eq_some_iff] at hs
        obtain ⟨σ', h', hs⟩ := hs
        split at hs <;> [cases hs; cases hs]
        exact (ih σ hb hσ).2 _ h'
      · simp only [hl]
        exact ⟨rfl, fun _ h => by cases h⟩
    | sum k => exact ⟨rfl, fun _ h => by cases h⟩
    | _ => exact ⟨rfl, fun _ h => by cases h⟩
  | call n b ih =>
    intro τ h hτ
    cases h with
    | call hb =>
      show ((A.call τ).bind fun τ₁ => (A.checkSum [] τ₁ (b.mapBlocks f) hb).bind A.ret) =
          ((A.call τ).bind fun τ₁ => (A.checkSum [] τ₁ b hb).bind A.ret) ∧
        ∀ τ', ((A.call τ).bind fun τ₁ => (A.checkSum [] τ₁ b hb).bind A.ret) = some τ' → P τ'
      cases e : A.call τ with
      | none => exact ⟨rfl, fun _ h => by cases h⟩
      | some τ₁ =>
        have h₁ := hA.call_P hτ e
        simp only [Option.bind_some]
        rw [(ih τ₁ hb h₁).1]
        refine ⟨rfl, fun τ' hs => ?_⟩
        simp only [Option.bind_eq_some_iff] at hs
        obtain ⟨τ₂, h₂, h₃⟩ := hs
        exact hA.ret_P ((ih τ₁ hb h₁).2 τ₂ h₂) h₃
    | sum k => exact ⟨rfl, fun _ h => by cases h⟩
    | _ => exact ⟨rfl, fun _ h => by cases h⟩
  | frame i b j ih =>
    intro τ h hτ
    cases h with
    | frame hb =>
      show ((A.push τ i).bind fun τ₁ => (A.checkSum [] τ₁ (b.mapBlocks f) hb).bind fun τ₂ => A.pop τ₂ j) =
          ((A.push τ i).bind fun τ₁ => (A.checkSum [] τ₁ b hb).bind fun τ₂ => A.pop τ₂ j) ∧
        ∀ τ', ((A.push τ i).bind fun τ₁ => (A.checkSum [] τ₁ b hb).bind fun τ₂ => A.pop τ₂ j) =
          some τ' → P τ'
      cases e : A.push τ i with
      | none => exact ⟨rfl, fun _ h => by cases h⟩
      | some τ₁ =>
        have h₁ := hA.push_P i hτ e
        simp only [Option.bind_some]
        rw [(ih τ₁ hb h₁).1]
        refine ⟨rfl, fun τ' hs => ?_⟩
        simp only [Option.bind_eq_some_iff] at hs
        obtain ⟨τ₂, h₂, h₃⟩ := hs
        exact hA.pop_P j ((ih τ₁ hb h₁).2 τ₂ h₂) h₃
    | sum k => exact ⟨rfl, fun _ h => by cases h⟩
    | _ => exact ⟨rfl, fun _ h => by cases h⟩

/-- Constant time from the analysis of `c'`, which is `c` with `f` applied to
its instructions (e.g. with copies that differ only in what `f` rewrites made
equal). -/
theorem constantTime_mapBlocks (hA : A.MapInv f P) {Pre : M.State → Prop}
    {Pub : M.State → M.State → Prop} {c c' : Prog M} (τ : A.T) (hτ : P τ)
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → A.Agree τ s₁ s₂)
    (he : c.mapBlocks f = c') {hc : Hint A.T} (h : (A.check τ c' hc).isSome = true) :
    ConstantTime M Pre Pub c :=
  VG.Taint.constantTime (A := A) τ hpub (hc := hc) (by rw [← (hA.check c τ hc hτ).1, he]; exact h)

/-- A summary from the analysis (`checkSumLe`) of `c'`, which is `c` with `f`
applied to its instructions (as `sumOk_of_checkSum`, without summaries). -/
theorem sumOk_of_mapBlocks [hm : Frame A] (hA : A.MapInv f P) {c c' : Prog M}
    {pre post F : A.T} (hτ : P pre) (he : c.mapBlocks f = c') {hc : SHint A.T}
    (h : checkSumLe A [] pre c' hc post = true) (hf : fill [] c hc = c)
    (hk : keepsSum A [] F c hc = true) (hF : Frame.Fr (A := A) F F = true) :
    SumOk A (c, pre, post, F) := by
  refine sumOk_of_checkSum (S := []) trivial ?_ hf hk hF
  unfold checkSumLe at h ⊢
  rw [← (hA.checkSum c pre hc hτ).1, he]
  exact h

/-- Without summaries, `fill` leaves any code as it is. -/
theorem fill_nil {T : Type} : ∀ (h : SHint T) (c : Prog M), fill [] c h = c
  | .sum _, _ => rfl
  | .block _, _ => rfl
  | .seq _ h₁ h₂, c => by
    cases c <;> try rfl
    show Code.seq (fill [] _ h₁) (fill [] _ h₂) = _
    rw [fill_nil h₁, fill_nil h₂]
  | .ite h₁ h₂, c => by
    cases c <;> try rfl
    show Code.ite _ (fill [] _ h₁) (fill [] _ h₂) = _
    rw [fill_nil h₁, fill_nil h₂]
  | .loop _ h, c => by
    cases c <;> try rfl
    exact congrArg (Code.loop · _) (fill_nil h _)
  | .call h, c => by
    cases c <;> try rfl
    exact congrArg _ (fill_nil h _)
  | .frame h, c => by
    cases c <;> try rfl
    exact congrArg (Code.frame _ · _) (fill_nil h _)

variable (A) in
/-- `sumOk_of_mapBlocks`, without a frame (`bot`): what `taint_summary_map` proves. -/
theorem sumOk_of_mapBlocks_bot [hm : Frame A] (hA : A.MapInv f P) (c c' : Prog M) (pre post : A.T)
    (hτ : P pre) (he : c.mapBlocks f = c') (hc : SHint A.T) (h : checkSumLe A [] pre c' hc post = true) :
    SumOk A (c, pre, post, Frame.bot) :=
  sumOk_of_mapBlocks hA hτ he h (fill_nil hc c) keepsSum_bot hm.bot_valid

end Taint

open Lean Meta Elab Term Command TaintSum in
/-- `taint_summary_map N : A τ c via hA he` proves the summary
`N : Taint.SumOk A (c, τ, post, bot)` as `taint_summary` does, but from the
analysis of `c'`, which `he : c.mapBlocks f = c'` says is `c` with `f`
applied to its instructions, which the analysis does not read from `τ`
(`hA : A.MapInv f P`, with `P τ` by `decide`): for code whose copies differ
only in what `f` rewrites, which `c'` shares. -/
elab "taint_summary_map " id:ident " : " a:term:max τ:term:max c:term:max " via " hA:term:max he:term:max :
    command => liftTermElabM do
  let A ← instantiateMVars (← elabTerm a none)
  let aTy ← whnf (← inferType A)
  unless aTy.isAppOfArity ``Taint 1 do throwError "taint_summary_map: {A} is not a `Taint`"
  let M := aTy.appArg!
  let T := mkApp2 (mkConst ``Taint.T) M A
  let τ ← elabTermEnsuringType τ T
  let c ← elabTermEnsuringType c (mkApp (mkConst ``Prog) M)
  let hA ← elabTerm hA none
  let he ← elabTerm he none
  synthesizeSyntheticMVarsNoPostponing
  let τ ← instantiateMVars τ
  let c ← instantiateMVars c
  let hA ← instantiateMVars hA
  let he ← instantiateMVars he
  let some (_, _, c') := (← instantiateMVars (← inferType he)).eq?
    | throwError "taint_summary_map: {he} is not an equation `c.mapBlocks f = c'`"
  if τ.hasMVar || c.hasMVar || c'.hasMVar || hA.hasMVar || he.hasMVar then
    throwError "taint_summary_map: the taint, the code and the proofs must be closed"
  let fr ← synthInstance (mkApp2 (mkConst ``Taint.Frame) M A)
  let (S, _) ← summaries M A #[]
  let (post, hint) ← hintChecked "taint_summary_map" M A fr S τ c'
  let hAty ← whnfR (← inferType hA)
  unless hAty.isAppOfArity ``Taint.MapInv 4 do throwError "taint_summary_map: {hA} is not a `Taint.MapInv`"
  let hτ ← mkFreshExprSyntheticOpaqueMVar (Expr.headBeta (mkApp hAty.appArg! τ))
  let h ← mkFreshExprSyntheticOpaqueMVar
    (← mkEq (mkAppN (mkConst ``Taint.checkSumLe) #[M, A, fr, S, τ, c', hint, post]) (mkConst ``Bool.true))
  let gs ← Tactic.run hτ.mvarId! (Tactic.evalTactic (← `(tactic| decide +kernel)))
  let gs' ← Tactic.run h.mvarId! (Tactic.evalTactic (← `(tactic| lit_decide)))
  unless gs.isEmpty && gs'.isEmpty do throwError "taint_summary_map: goals remain"
  let pf ← mkAppOptM ``Taint.sumOk_of_mapBlocks_bot
    #[some M, some A, none, none, some fr, some hA, some c, some c', some τ, some post, some hτ, some he,
      some hint, some h]
  let pf ← instantiateMVars pf
  let ty ← instantiateMVars (← inferType pf)
  addDecl <| .thmDecl
    { name := (← getCurrNamespace) ++ id.getId, levelParams := [], type := ty, value := pf }

end VG
