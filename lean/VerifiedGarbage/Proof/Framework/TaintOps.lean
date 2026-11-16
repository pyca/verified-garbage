module

public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Framework.RelCT
public meta import VerifiedGarbage.Proof.Framework.TaintSum
public meta import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Constant time by taint tracking, with operations proven otherwise

`Taint.check` analyses every function a program calls, and `checkSum`
replaces some of them by summaries, which the analysis itself proves
(`SumOk`). Some code the analysis cannot follow: a function whose timing
depends on state the domain does not track, or with a frame it does not
handle (`vg_mcdt_enter`, `Spec/Mcdt.lean`, whose branch on MXCSR a domain
that knows MXCSR to agree in both runs may allow, but whose frame and
memory round trip it cannot follow). An *operation* (`Op`) is code with
the analysis's transfer function for it, `f`, whose soundness is proven of
the code by any means (`OpSound`): two runs of the code from states that
agree on `τ` leak the same trace and end agreeing on `f τ` (`SemOk`).

`checkOps` is `checkSum` with operations in place of summaries (at a hint
`sum k`, the `k`-th operation), and `checkOps_sound` proves what it
finds of any domain, given operations that are sound and used for their
code (`fillOps`, which the kernel checks by unfolding, as `fill`). For a
domain that is monotone (`Frame`), an operation that is also monotone and
keeps what its `keeps` frames say (`OpMono`) can be used from a taint with
more public: `checkOps_lift`, as `checkSum_frame`. So the analysis of code
from some `pre` with operations in it gives an operation for that code
from any taint above `pre` (`Op.framed`, `opOk_framed`): a summary that
uses operations (`taint_summary_ops`), and a summary of the analysis
itself is one too (`opOk_ofSum`).

`taint_decide_ops [l₁, …]` proves `Taint.Sem A τ c` (there is a taint
two runs of `c` from states agreeing on `τ` end agreeing on, and they leak
the same trace) with the operations `lᵢ : Taint.OpOk A o` (or, for a domain
without `Frame`, `Taint.OpSound A o`), and `taint_decide_ops_check S`
proves `Taint.OpsCheck A S τ c p` for the analysis of a domain without
`Frame` (`X86_64.RTaint`), whose result `p` must accept.
-/

@[expose] public section

namespace VG

namespace Taint

variable {M : ISA}

/-- Code `code`, which the analysis does not follow, and its transfer
function `f`; `keeps F` says that it writes nothing of the frame `F`. -/
structure Op (M : ISA) (T : Type) where
  code : Prog M
  f : T → Option T
  keeps : T → Bool := fun _ => false

variable (A : Taint M)

/-- Two runs of `c` from states that agree on `τ` leak the same trace and end
agreeing on `τ'`. -/
def SemOk (τ : A.T) (c : Prog M) (τ' : A.T) : Prop :=
  ∀ s₁ s₂ t₁ t₂ s₁' s₂', A.Agree τ s₁ s₂ → Exec M c s₁ t₁ s₁' → Exec M c s₂ t₂ s₂' →
    t₁ = t₂ ∧ A.Agree τ' s₁' s₂'

/-- Some taint is what two runs of `c` from states agreeing on `τ` end
agreeing on, and they leak the same trace. -/
def Sem (τ : A.T) (c : Prog M) : Prop := ∃ τ', SemOk A τ c τ'

/-- The operation is sound: from `τ`, its code is as `f τ` says. -/
def OpSound (o : Op M A.T) : Prop := ∀ τ τ', o.f τ = some τ' → SemOk A τ o.code τ'

/-- Every operation of the list is sound. -/
def AllSound : List (Op M A.T) → Prop
  | [] => True
  | o :: S => OpSound A o ∧ AllSound S

/-- `checkSum`, with the operations `S`: at a hint `sum k`, the `k`-th
operation's transfer function, whatever the code there (`fillOps` says it
is the operation's). -/
def checkOps (S : List (Op M A.T)) (τ : A.T) (c : Prog M) (h : SHint A.T) : Option A.T :=
  match h, τ, c with
  | .sum k, τ, _ => match S[k]? with
    | some o => o.f τ
    | none => none
  | .block ms, τ, .block is => checkChunks A chunk τ is ms
  | .seq mid h₁ h₂, τ, .seq c₁ c₂ =>
    (checkOps S τ c₁ h₁).bind fun τ' => if A.le mid τ' then checkOps S mid c₂ h₂ else none
  | .ite h₁ h₂, τ, .ite c t e =>
    if A.condPub τ c then
      (checkOps S τ t h₁).bind fun τ₁ => (checkOps S τ e h₂).map fun τ₂ => A.meet τ₁ τ₂
    else none
  | .loop σ h, τ, .loop body c =>
    if A.le σ τ then
      (checkOps S σ body h).bind fun σ' => if A.le σ σ' && A.condPub σ' c then some σ' else none
    else none
  | .call h, τ, .call _ body => (A.call τ).bind fun τ₁ => (checkOps S τ₁ body h).bind A.ret
  | .frame h, τ, .frame i body j =>
    (A.push τ i).bind fun τ₁ => (checkOps S τ₁ body h).bind fun τ₂ => A.pop τ₂ j
  | _, _, _ => none
termination_by structural h

variable {A} in
/-- `c`, with the code of the operation at each `sum k` of the hint in place
of what is there. `fillOps S c h = c` says that each operation is used for
its code. -/
def fillOps {T : Type} (S : List (Op M T)) (c : Prog M) (h : SHint T) : Prog M :=
  match h, c with
  | .sum k, c => match S[k]? with
    | some o => o.code
    | none => c
  | .seq _ h₁ h₂, .seq a b => .seq (fillOps S a h₁) (fillOps S b h₂)
  | .ite h₁ h₂, .ite cd t e => .ite cd (fillOps S t h₁) (fillOps S e h₂)
  | .loop _ h, .loop b cd => .loop (fillOps S b h) cd
  | .call h, .call n b => .call n (fillOps S b h)
  | .frame h, .frame i b j => .frame i (fillOps S b h) j
  | _, c => c
termination_by structural h

/-- The result of `checkOps`, if any, satisfies `p`; and each operation is
used for its code. -/
def OpsCheck (S : List (Op M A.T)) (τ : A.T) (c : Prog M) (p : A.T → Bool) : Prop :=
  ∃ h, (checkOps A S τ c h).any p = true ∧ fillOps S c h = c

/-! ## Soundness -/

variable {A}

private theorem if_pos'' {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

theorem AllSound.get {S : List (Op M A.T)} (hS : AllSound A S) {k : Nat} {o : Op M A.T}
    (h : S[k]? = some o) : OpSound A o := by
  induction S generalizing k with
  | nil => cases h
  | cons o' S ih =>
    cases k with
    | zero => cases h; exact hS.1
    | succ k => exact ih hS.2 h

theorem SemOk.weaken {τ σ σ' τ' : A.T} {c : Prog M} (h : SemOk A σ c σ') (hl : A.le σ τ = true)
    (hr : A.le τ' σ' = true) : SemOk A τ c τ' := fun _ _ _ _ _ _ ha e₁ e₂ =>
  let ⟨ht, hq⟩ := h _ _ _ _ _ _ (A.le_sound hl ha) e₁ e₂
  ⟨ht, A.le_sound hr hq⟩

/-- A loop whose body keeps its invariant `σ` (at least `σ'`, which keeps
the condition public). -/
theorem semOk_loop {σ σ' : A.T} {body : Prog M} {cd : M.Cond} (hb : SemOk A σ body σ')
    (hl : A.le σ σ' = true) (hc : A.condPub σ' cd = true) : SemOk A σ (.loop body cd) σ' := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ha e₁ e₂
  generalize hL : (Code.loop body cd : Prog M) = L at e₁
  induction e₁ generalizing s₂ t₂ s₂' with
  | loopExit a c₁ =>
    cases hL
    cases e₂ with
    | loopExit b _ => obtain ⟨rfl, hq⟩ := hb _ _ _ _ _ _ ha a b; exact ⟨rfl, hq⟩
    | loopNext b c₂ _ =>
      obtain ⟨_, hq⟩ := hb _ _ _ _ _ _ ha a b
      rw [← A.cond_sound hq hc, c₁] at c₂; cases c₂
  | loopNext a c₁ _ _ ih =>
    cases hL
    cases e₂ with
    | loopExit b c₂ =>
      obtain ⟨_, hq⟩ := hb _ _ _ _ _ _ ha a b
      rw [← A.cond_sound hq hc, c₁] at c₂; cases c₂
    | loopNext b _ r =>
      obtain ⟨rfl, hq⟩ := hb _ _ _ _ _ _ ha a b
      obtain ⟨rfl, hq'⟩ := ih _ _ _ (A.le_sound hl hq) r rfl
      exact ⟨rfl, hq'⟩
  | _ => cases hL

/-- A successful `checkOps`, with sound operations used for their code, is
sound. -/
theorem checkOps_sound {S : List (Op M A.T)} (hS : AllSound A S) :
    ∀ {hc : SHint A.T} {c : Prog M} {τ τ' : A.T}, checkOps A S τ c hc = some τ' →
      fillOps S c hc = c → SemOk A τ c τ' := by
  intro hc
  induction hc with
  | sum k =>
    intro c τ τ' h hf
    replace h : (match S[k]? with | some o => o.f τ | none => none) = some τ' := h
    rw [fillOps] at hf
    cases hk : S[k]? with
    | none => rw [hk] at h; cases h
    | some o =>
      rw [hk] at h hf
      simp only at h hf
      subst hf
      exact hS.get hk τ τ' h
  | block ms =>
    intro c τ τ' h _
    cases c with
    | block is =>
      intro s₁ s₂ t₁ t₂ s₁' s₂' ha e₁ e₂
      cases e₁ with
      | block h₁ => cases e₂ with
        | block h₂ => exact checkChunks_sound (A := A) h ha h₁ h₂
    | _ => cases (h : (none : Option A.T) = some τ')
  | seq mid g₁ g₂ ih₁ ih₂ =>
    intro c τ τ' h hf
    cases c with
    | seq c₁ c₂ =>
      have h : ((checkOps A S τ c₁ g₁).bind fun τ' =>
        if A.le mid τ' then checkOps A S mid c₂ g₂ else none) = some τ' := h
      have hf : Code.seq (fillOps S c₁ g₁) (fillOps S c₂ g₂) = .seq c₁ c₂ := hf
      injection hf with hf₁ hf₂
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, h₂⟩ := h
      split at h₂ <;> [rename_i hl; cases h₂]
      have s₁ := ih₁ h₁ hf₁
      have s₂ := ih₂ h₂ hf₂
      intro x₁ x₂ t₁ t₂ x₁' x₂' ha e₁ e₂
      cases e₁ with
      | seq a₁ b₁ => cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨rfl, hq⟩ := s₁ _ _ _ _ _ _ ha a₁ a₂
          obtain ⟨rfl, hq'⟩ := s₂ _ _ _ _ _ _ (A.le_sound hl hq) b₁ b₂
          exact ⟨rfl, hq'⟩
    | _ => cases (h : (none : Option A.T) = some τ')
  | ite g₁ g₂ ih₁ ih₂ =>
    intro c τ τ' h hf
    cases c with
    | ite cd t e =>
      have h : (if A.condPub τ cd then
          (checkOps A S τ t g₁).bind fun τ₁ => (checkOps A S τ e g₂).map fun τ₂ => A.meet τ₁ τ₂
        else none) = some τ' := h
      have hf : Code.ite cd (fillOps S t g₁) (fillOps S e g₂) = .ite cd t e := hf
      injection hf with _ hf₁ hf₂
      split at h <;> [rename_i hp; cases h]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, rfl⟩ := h
      have st := ih₁ h₁ hf₁
      have se := ih₂ h₂ hf₂
      intro x₁ x₂ t₁ t₂ x₁' x₂' ha e₁ e₂
      have hce := A.cond_sound ha hp
      cases e₁ with
      | iteT c₁ a₁ =>
        cases e₂ with
        | iteT _ a₂ => obtain ⟨rfl, hq⟩ := st _ _ _ _ _ _ ha a₁ a₂; exact ⟨rfl, A.meet_left hq⟩
        | iteF c₂ _ => rw [hce, c₂] at c₁; cases c₁
      | iteF c₁ a₁ =>
        cases e₂ with
        | iteT c₂ _ => rw [hce, c₂] at c₁; cases c₁
        | iteF _ a₂ => obtain ⟨rfl, hq⟩ := se _ _ _ _ _ _ ha a₁ a₂; exact ⟨rfl, A.meet_right hq⟩
    | _ => cases (h : (none : Option A.T) = some τ')
  | loop inv g ih =>
    intro c τ τ' h hf
    cases c with
    | loop body cd =>
      have h : (if A.le inv τ then
          (checkOps A S inv body g).bind fun σ' =>
            if A.le inv σ' && A.condPub σ' cd then some σ' else none
        else none) = some τ' := h
      have hf : Code.loop (fillOps S body g) cd = .loop body cd := hf
      injection hf with hf₁
      split at h <;> [rename_i hl; cases h]
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, h₂⟩ := h
      split at h₂ <;> [rename_i hc; cases h₂]
      cases h₂
      simp only [Bool.and_eq_true] at hc
      have sl := semOk_loop (ih h₁ hf₁) hc.1 hc.2
      intro x₁ x₂ t₁ t₂ x₁' x₂' ha e₁ e₂
      exact sl _ _ _ _ _ _ (A.le_sound hl ha) e₁ e₂
    | _ => cases (h : (none : Option A.T) = some τ')
  | call g ih =>
    intro c τ τ' h hf
    cases c with
    | call n body =>
      have h : ((A.call τ).bind fun τ₁ => (checkOps A S τ₁ body g).bind A.ret) = some τ' := h
      have hf : Code.call n (fillOps S body g) = .call n body := hf
      injection hf with _ hf₁
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      have sb := ih h₂ hf₁
      intro x₁ x₂ t₁ t₂ x₁' x₂' ha e₁ e₂
      cases e₁ with
      | call hc₁ b hr => cases e₂ with
        | call hc₂ b₂ hr₂ =>
          obtain ⟨ha₁, ha₁'⟩ := A.call_sound ha h₁ hc₁ hc₂
          obtain ⟨rfl, ha₂⟩ := sb _ _ _ _ _ _ ha₁' b b₂
          obtain ⟨ha₃, ha₃'⟩ := A.ret_sound ha₂ h₃ hr hr₂
          exact ⟨by rw [ha₁, ha₃], ha₃'⟩
    | _ => cases (h : (none : Option A.T) = some τ')
  | frame g ih =>
    intro c τ τ' h hf
    cases c with
    | frame i body j =>
      have h : ((A.push τ i).bind fun τ₁ => (checkOps A S τ₁ body g).bind fun τ₂ => A.pop τ₂ j) =
        some τ' := h
      have hf : Code.frame i (fillOps S body g) j = .frame i body j := hf
      injection hf with _ hf₁ _
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      have sb := ih h₂ hf₁
      intro x₁ x₂ t₁ t₂ x₁' x₂' ha e₁ e₂
      cases e₁ with
      | frame hp₁ b hq => cases e₂ with
        | frame hp₂ b₂ hq₂ =>
          obtain ⟨ha₁, ha₁'⟩ := A.push_sound ha h₁ hp₁ hp₂
          obtain ⟨rfl, ha₂⟩ := sb _ _ _ _ _ _ ha₁' b b₂
          obtain ⟨ha₃, ha₃'⟩ := A.pop_sound ha₂ h₃ hq hq₂
          exact ⟨by rw [ha₁, ha₃], ha₃'⟩
    | _ => cases (h : (none : Option A.T) = some τ')

/-- `Sem`, from a successful `checkOps` with sound operations used for
their code. -/
theorem sem_of_checkOps {S : List (Op M A.T)} (hS : AllSound A S) {c : Prog M} {τ : A.T}
    {hc : SHint A.T} (h : (checkOps A S τ c hc).isSome = true) (hf : fillOps S c hc = c) : Sem A τ c := by
  obtain ⟨τ', hτ⟩ := Option.isSome_iff_exists.mp h
  exact ⟨τ', checkOps_sound hS hτ hf⟩

/-- What `OpsCheck` finds holds of the final states. -/
theorem OpsCheck.sound {S : List (Op M A.T)} (hS : AllSound A S) {c : Prog M} {τ : A.T}
    {p : A.T → Bool} (h : OpsCheck A S τ c p) : ∃ τ', p τ' = true ∧ SemOk A τ c τ' := by
  obtain ⟨hc, hp, hf⟩ := h
  cases hτ : checkOps A S τ c hc with
  | none => rw [hτ] at hp; cases hp
  | some τ' => rw [hτ] at hp; exact ⟨τ', hp, checkOps_sound hS hτ hf⟩

/-- Code that `Sem` proves constant time, from states agreeing on `τ`, as a
relation between two runs: they end agreeing on some taint. -/
theorem RelCT.ofSem {P : M.State → M.State → Prop} {c : Prog M} {τ : A.T}
    (hp : ∀ s₁ s₂, P s₁ s₂ → A.Agree τ s₁ s₂) (h : Sem A τ c) :
    RelCT M P c fun s₁ s₂ => ∃ τ', A.Agree τ' s₁ s₂ := by
  obtain ⟨τ', hs⟩ := h
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨ht, ha⟩ := hs _ _ _ _ _ _ (hp _ _ hP) e₁ e₂
  exact ⟨ht, τ', ha⟩

/-- `Sem` proves constant time, for any `Pub` under which the initial states
agree on what the initial taint says is public. -/
theorem constantTime_of_sem {Pre : M.State → Prop} {Pub : M.State → M.State → Prop} {c : Prog M}
    (τ : A.T) (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → A.Agree τ s₁ s₂) (h : Sem A τ c) :
    ConstantTime M Pre Pub c := by
  obtain ⟨τ', hs⟩ := h
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  exact (hs _ _ _ _ _ _ (hpub _ _ h₁ h₂ hp) e₁ e₂).1


/-! ## Operations from a taint with more public

For a monotone domain (`Frame`). -/

local notation "J" => Frame.join (A := A)
local notation "R" => Mono.R (A := A)
local notation "Fr" => Frame.Fr (A := A)

variable (A) in
/-- The operation is monotone: from more public (`R`), its transfer function
succeeds with more public after it, and keeps public what of a frame `F` was
if `keeps F`, as an instruction's step does (`Mono.step`, `Frame.step_keeps`). -/
def OpMono [Frame A] (o : Op M A.T) : Prop :=
  (∀ {τ σ τ' : A.T}, R τ σ = true → o.f τ = some τ' → ∃ σ', o.f σ = some σ' ∧ R τ' σ' = true) ∧
  (∀ {F Φ σ σ' : A.T}, o.keeps F = true → Fr Φ F = true → Fr Φ σ = true → o.f σ = some σ' →
    Fr Φ σ' = true)

variable (A) in
/-- The operation is sound and monotone. -/
def OpOk [Frame A] (o : Op M A.T) : Prop := OpSound A o ∧ OpMono A o

variable (A) in
/-- Every operation of the list is sound and monotone. -/
def AllOk' [Frame A] : List (Op M A.T) → Prop
  | [] => True
  | o :: S => OpOk A o ∧ AllOk' S

theorem AllOk'.get [Frame A] {S : List (Op M A.T)} (hS : AllOk' A S) {k : Nat} {o : Op M A.T}
    (h : S[k]? = some o) : OpOk A o := by
  induction S generalizing k with
  | nil => cases h
  | cons o' S ih =>
    cases k with
    | zero => cases h; exact hS.1
    | succ k => exact ih hS.2 h

theorem AllOk'.sound [Frame A] : ∀ {S : List (Op M A.T)}, AllOk' A S → AllSound A S
  | [], _ => trivial
  | _ :: _, h => ⟨h.1.1, AllOk'.sound h.2⟩

variable (A) in
/-- Nothing of `F` is written, but where the hint uses an operation, which
then keeps `F` (`keepsSum`, for operations). -/
def keepsOps [Frame A] (S : List (Op M A.T)) (F : A.T) (c : Prog M) (h : SHint A.T) : Bool :=
  match h, c with
  | .sum k, _ => match S[k]? with
    | some o => o.keeps F
    | none => true
  | .block _, .block is => is.all (Frame.keeps (A := A) F)
  | .seq _ h₁ h₂, .seq a b => keepsOps S F a h₁ && keepsOps S F b h₂
  | .ite h₁ h₂, .ite _ t e => keepsOps S F t h₁ && keepsOps S F e h₂
  | .loop _ h, .loop b _ => keepsOps S F b h
  | .call h, .call _ b => Frame.keepsCall (A := A) F && keepsOps S F b h
  | .frame h, .frame i b j =>
    Frame.keeps (A := A) F i && keepsOps S F b h && Frame.keeps (A := A) F j
  | _, _ => true
termination_by structural h

/-- A successful `checkOps`, with operations that are sound and monotone
used for their code, succeeds from any taint with more public (`R`), and
keeps public what was of `F` if nothing writes it (`keepsOps`): as
`checkSum_frame`. -/
theorem checkOps_lift [hm : Frame A] {S : List (Op M A.T)} (hS : AllOk' A S) {F Φ : A.T}
    (hΦF : Fr Φ F = true) :
    ∀ {hc : SHint A.T} {c : Prog M} {τ σ τ' : A.T}, checkOps A S τ c hc = some τ' →
      fillOps S c hc = c → keepsOps A S F c hc = true → R τ σ = true → Fr Φ σ = true →
      ∃ h σ', checkOps A S σ c h = some σ' ∧ fillOps S c h = c ∧ R τ' σ' = true ∧ Fr Φ σ' = true := by
  intro hc
  induction hc with
  | sum k =>
    intro c τ σ τ' h hf hk hle hΦ
    replace h : (match S[k]? with | some o => o.f τ | none => none) = some τ' := h
    replace hk : (match S[k]? with | some o => o.keeps F | none => true) = true := hk
    cases hks : S[k]? with
    | none => rw [hks] at h; cases h
    | some o =>
      rw [hks] at h hk
      simp only at h hk
      obtain ⟨-, hmo, hke⟩ := hS.get hks
      obtain ⟨σ', h', hle'⟩ := hmo hle h
      refine ⟨.sum k, σ', ?_, hf, hle', hke hk hΦF hΦ h'⟩
      show (match S[k]? with | some o => o.f σ | none => none) = some σ'
      rw [hks]; exact h'
  | block ms =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | block is =>
      obtain ⟨σ', h', hle', hΦ'⟩ := checkChunks_frame (ms := ms) (A := A) h hk hΦF hle hΦ
      exact ⟨.block (ms.map (J · Φ)), σ', h', rfl, hle', hΦ'⟩
    | _ => cases (h : (none : Option A.T) = some τ')
  | seq mid g₁ g₂ ih₁ ih₂ =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | seq c₁ c₂ =>
      have h : ((checkOps A S τ c₁ g₁).bind fun τ' =>
        if A.le mid τ' then checkOps A S mid c₂ g₂ else none) = some τ' := h
      have hf : Code.seq (fillOps S c₁ g₁) (fillOps S c₂ g₂) = .seq c₁ c₂ := hf
      have hk : (keepsOps A S F c₁ g₁ && keepsOps A S F c₂ g₂) = true := hk
      rw [Bool.and_eq_true] at hk
      injection hf with hf_1 hf_2
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, h₂⟩ := h
      split at h₂ <;> [rename_i hl; cases h₂]
      obtain ⟨g₁', σ₁, h₁', f₁, hle₁, hΦ₁⟩ := ih₁ h₁ hf_1 hk.1 hle hΦ
      have jl := hm.join_hint (hm.le_R hl hle₁) hΦ₁
      obtain ⟨g₂', σ₂, h₂', f₂, hle₂, hΦ₂⟩ := ih₂ h₂ hf_2 hk.2 jl.2.1 jl.2.2
      refine ⟨.seq (J mid Φ) g₁' g₂', σ₂, ?_, ?_, hle₂, hΦ₂⟩
      · show ((checkOps A S σ c₁ g₁').bind fun τ' =>
          if A.le (J mid Φ) τ' then checkOps A S (J mid Φ) c₂ g₂' else none) = some σ₂
        rw [h₁', Option.bind_some, if_pos'' jl.1]; exact h₂'
      · show Code.seq (fillOps S c₁ g₁') (fillOps S c₂ g₂') = _
        rw [f₁, f₂]
    | _ => cases (h : (none : Option A.T) = some τ')
  | ite g₁ g₂ ih₁ ih₂ =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | ite cd t e =>
      have h : (if A.condPub τ cd then
          (checkOps A S τ t g₁).bind fun τ₁ => (checkOps A S τ e g₂).map fun τ₂ => A.meet τ₁ τ₂
        else none) = some τ' := h
      have hf : Code.ite cd (fillOps S t g₁) (fillOps S e g₂) = .ite cd t e := hf
      have hk : (keepsOps A S F t g₁ && keepsOps A S F e g₂) = true := hk
      rw [Bool.and_eq_true] at hk
      injection hf with hf_1 hf_2 hf_3
      split at h <;> [rename_i hp; cases h]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, rfl⟩ := h
      obtain ⟨g₁', σ₁, h₁', f₁, hle₁, hΦ₁⟩ := ih₁ h₁ hf_2 hk.1 hle hΦ
      obtain ⟨g₂', σ₂, h₂', f₂, hle₂, hΦ₂⟩ := ih₂ h₂ hf_3 hk.2 hle hΦ
      refine ⟨.ite g₁' g₂', A.meet σ₁ σ₂, ?_, ?_, hm.meet hle₁ hle₂, hm.le_meet hΦ₁ hΦ₂⟩
      · show (if A.condPub σ cd then
            (checkOps A S σ t g₁').bind fun τ₁ => (checkOps A S σ e g₂').map fun τ₂ => A.meet τ₁ τ₂
          else none) = _
        rw [if_pos'' (hm.condPub cd hle hp), h₁', Option.bind_some, h₂', Option.map_some]
      · show Code.ite cd (fillOps S t g₁') (fillOps S e g₂') = _
        rw [f₁, f₂]
    | _ => cases (h : (none : Option A.T) = some τ')
  | loop inv g ih =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | loop body cd =>
      have h : (if A.le inv τ then
          (checkOps A S inv body g).bind fun σ' =>
            if A.le inv σ' && A.condPub σ' cd then some σ' else none
        else none) = some τ' := h
      have hf : Code.loop (fillOps S body g) cd = .loop body cd := hf
      have hk : keepsOps A S F body g = true := hk
      injection hf with hf_1
      split at h <;> [rename_i hl; cases h]
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, h₂⟩ := h
      split at h₂ <;> [rename_i hc; cases h₂]
      cases h₂
      simp only [Bool.and_eq_true] at hc
      have jl := hm.join_hint (hm.le_R hl hle) hΦ
      obtain ⟨g', σ₁, h₁', f₁, hle₁, hΦ₁⟩ := ih h₁ hf_1 hk jl.2.1 jl.2.2
      refine ⟨.loop (J inv Φ) g', σ₁, ?_, ?_, hle₁, hΦ₁⟩
      · show (if A.le (J inv Φ) σ then
            (checkOps A S (J inv Φ) body g').bind fun σ' =>
              if A.le (J inv Φ) σ' && A.condPub σ' cd then some σ' else none
          else none) = some σ₁
        rw [if_pos'' jl.1, h₁', Option.bind_some,
          if_pos'' (by rw [(hm.join_hint (hm.le_R hc.1 hle₁) hΦ₁).1, hm.condPub cd hle₁ hc.2]; rfl)]
      · show Code.loop (fillOps S body g') cd = _
        rw [f₁]
    | _ => cases (h : (none : Option A.T) = some τ')
  | call g ih =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | call n body =>
      have h : ((A.call τ).bind fun τ₁ => (checkOps A S τ₁ body g).bind A.ret) = some τ' := h
      have hf : Code.call n (fillOps S body g) = .call n body := hf
      have hk : (Frame.keepsCall (A := A) F && keepsOps A S F body g) = true := hk
      rw [Bool.and_eq_true] at hk
      injection hf with hf_1 hf_2
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      obtain ⟨σ₁, h₁', hle₁⟩ := hm.call hle h₁
      obtain ⟨g', σ₂, h₂', f₂, hle₂, hΦ₂⟩ := ih h₂ hf_2 hk.2 hle₁ (hm.call_keeps hk.1 hΦF hΦ h₁')
      obtain ⟨σ₃, h₃', hle₃⟩ := hm.ret hle₂ h₃
      refine ⟨.call g', σ₃, ?_, ?_, hle₃, hm.ret_keeps hk.1 hΦF hΦ₂ h₃'⟩
      · show ((A.call σ).bind fun τ₁ => (checkOps A S τ₁ body g').bind A.ret) = some σ₃
        rw [h₁', Option.bind_some, h₂', Option.bind_some, h₃']
      · show Code.call n (fillOps S body g') = _
        rw [f₂]
    | _ => cases (h : (none : Option A.T) = some τ')
  | frame g ih =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | frame i body j =>
      have h : ((A.push τ i).bind fun τ₁ => (checkOps A S τ₁ body g).bind fun τ₂ => A.pop τ₂ j) =
        some τ' := h
      have hf : Code.frame i (fillOps S body g) j = .frame i body j := hf
      have hk : (Frame.keeps (A := A) F i && keepsOps A S F body g && Frame.keeps (A := A) F j) = true :=
        hk
      simp only [Bool.and_eq_true] at hk
      injection hf with hf_1 hf_2 hf_3
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      obtain ⟨σ₁, h₁', hle₁⟩ := hm.push i hle h₁
      obtain ⟨g', σ₂, h₂', f₂, hle₂, hΦ₂⟩ := ih h₂ hf_2 hk.1.2 hle₁
        (hm.push_keeps i hk.1.1 hΦF hΦ h₁')
      obtain ⟨σ₃, h₃', hle₃⟩ := hm.pop j hle₂ h₃
      refine ⟨.frame g', σ₃, ?_, ?_, hle₃, hm.pop_keeps j hk.2 hΦF hΦ₂ h₃'⟩
      · show ((A.push σ i).bind fun τ₁ => (checkOps A S τ₁ body g').bind fun τ₂ => A.pop τ₂ j) =
          some σ₃
        rw [h₁', Option.bind_some, h₂', Option.bind_some, h₃']
      · show Code.frame i (fillOps S body g') j = _
        rw [f₂]
    | _ => cases (h : (none : Option A.T) = some τ')

/-! ## Summaries as operations

For a domain monotone along its own order (`LeFrame`), whose `Frame` has
`R` and `Fr` both `le`. -/

section
variable [hl : LeFrame A]

variable (A) in
/-- The summary `(c, pre, post, F)` as an operation: from at least `pre`
public, `post` and what was public of `F` (as `checkSum` uses it). -/
def Op.framed (c : Prog M) (pre post F : A.T) : Op M A.T where
  code := c
  f τ := if A.le pre τ then some (Frame.join (A := A) post (Frame.frameOf (A := A) τ F)) else none
  keeps F₀ := A.le F₀ F || A.le F₀ (Frame.bot (A := A))

variable (A) in
/-- What `SumOk` says, of the code's runs: from at least `pre` public, two
runs end agreeing on at least `post` and what was public of `F`. -/
def FramedOk (c : Prog M) (pre post F : A.T) : Prop :=
  ∀ σ, A.le pre σ = true → ∃ σ'', SemOk A σ c σ'' ∧ A.le post σ'' = true ∧
    A.le (Frame.frameOf (A := A) σ F) σ'' = true

theorem opOk_framed {c : Prog M} {pre post F : A.T} (h : FramedOk A c pre post F) :
    OpOk A (Op.framed A c pre post F) := by
  refine ⟨fun τ τ' hf => ?_, fun {τ σ τ'} hle hf => ?_, fun {F₀ Φ σ σ'} hk hΦF hΦ hf => ?_⟩
  · simp only [Op.framed] at hf
    split at hf <;> [rename_i hp; cases hf]
    cases hf
    obtain ⟨σ'', hs, hpo, hfr⟩ := h τ hp
    exact hs.weaken (hl.le_right hp) (hl.join_lub hpo hfr).2.2
  · simp only [Op.framed] at hf ⊢
    split at hf <;> [rename_i hp; cases hf]
    cases hf
    have hp' := hl.le_trans hp hle
    rw [if_pos'' hp']
    obtain ⟨σ'', -, hpo, hfr⟩ := h σ hp'
    have jl := hl.join_lub hpo hfr
    refine ⟨_, rfl, (hl.join_lub jl.1 (hl.le_trans (hl.frame_mono F hle) jl.2.1)).2.2⟩
  · simp only [Op.framed] at hf hk
    split at hf <;> [rename_i hp; cases hf]
    cases hf
    obtain ⟨σ'', -, hpo, hfr⟩ := h σ hp
    have jl := hl.join_lub hpo hfr
    rcases Bool.or_eq_true _ _ ▸ hk with hk | hk
    · exact hl.le_trans (hl.le_frame hΦ (hl.le_trans hΦF hk)) jl.2.1
    · exact hl.le_trans (hl.le_trans hΦF hk) (hl.bot_le (hl.le_right jl.1))

/-- A summary of the analysis is an operation. -/
theorem opOk_ofSum {c : Prog M} {pre post F : A.T} (h : SumOk A (c, pre, post, F)) :
    OpOk A (Op.framed A c pre post F) :=
  opOk_framed fun σ hσ =>
    let ⟨_, σ', hc, hpo, hfr⟩ := h σ hσ
    ⟨σ', fun _ _ _ _ _ _ ha e₁ e₂ => check_sound hc ha e₁ e₂, hpo, hfr⟩

/-- An operation proven with other operations: the analysis of `c` from
`pre`, which ends with at least `post` public and writes nothing of `F`. -/
theorem opOk_framed_of_checkOps {S : List (Op M A.T)} (hS : AllOk' A S) {c : Prog M} {pre post F τ' : A.T}
    {hc : SHint A.T} (h : checkOps A S pre c hc = some τ') (hp : A.le post τ' = true)
    (hf : fillOps S c hc = c) (hk : keepsOps A S F c hc = true) (hF : A.le F F = true) :
    OpOk A (Op.framed A c pre post F) :=
  opOk_framed fun σ hσ => by
    obtain ⟨g, σ', h', f', hle', hΦ'⟩ := checkOps_lift (A := A) hS (Φ := Frame.frameOf (A := A) σ F)
      (hl.frame_le_right σ hF) h hf hk hσ (hl.frame_le_left F (hl.le_right hσ))
    exact ⟨σ', checkOps_sound hS.sound h' f', hl.le_trans hp hle', hΦ'⟩

/-- `opOk_framed_of_checkOps`, for the tactics. -/
theorem opOk_framed_of_checkOpsLe {S : List (Op M A.T)} (hS : AllOk' A S) {c : Prog M}
    {pre post F : A.T} {hc : SHint A.T}
    (h : ((checkOps A S pre c hc).map fun τ' => A.le post τ') = some true)
    (hf : fillOps S c hc = c) (hk : keepsOps A S F c hc = true) (hF : A.le F F = true) :
    OpOk A (Op.framed A c pre post F) := by
  obtain ⟨τ', h', hp⟩ := Option.map_eq_some_iff.mp h
  exact opOk_framed_of_checkOps hS h' hp hf hk hF

end


/-! ## Computing hints

Nothing here needs to be sound: `checkOps` and `fillOps` check the hint. -/

variable (A)

/-- The first operation of a call of `n` that applies from `τ`: its index and
the taint after it. -/
def findOp (n : String) (τ : A.T) : List (Op M A.T) → Nat → Option (Nat × A.T)
  | [], _ => none
  | o :: S, k => match o.code with
    | .call n' _ =>
      if n' == n then match o.f τ with
        | some τ' => some (k, τ')
        | none => findOp n τ S (k + 1)
      else findOp n τ S (k + 1)
    | _ => findOp n τ S (k + 1)

/-- The first operation of the code `c` (by `same`) that applies from `τ`. -/
def findOpCode (same : Prog M → Prog M → Bool) (c : Prog M) (τ : A.T) :
    List (Op M A.T) → Nat → Option (Nat × A.T)
  | [], _ => none
  | o :: S, k =>
    if same o.code c then match o.f τ with
      | some τ' => some (k, τ')
      | none => findOpCode same c τ S (k + 1)
    else findOpCode same c τ S (k + 1)

/-- Whether `S` has an operation of a call of `n`. -/
def hasCallOp {T : Type} (S : List (Op M T)) (n : String) : Bool :=
  S.any fun o => match o.code with
    | .call n' _ => n' == n
    | _ => false

/-- `hintSumA`, with operations: at a call of a function an operation is of,
and at code that is an operation's (by `same`), the first operation that
applies. Where the second part of a `seq` starts with such a call, the
analysis may continue after the first part from what an earlier taint knew
(`wk a τ₁`, a taint at most `τ₁`, from an ancestor `a`; for a monotone
domain, `Frame.join a (Frame.frameOf τ₁ τ₁)`), so that the operation
applies. -/
def hintOpsA (S : List (Op M A.T)) (same : Prog M → Prog M → Bool) (wk : A.T → A.T → Option A.T) :
    List A.T → A.T → Prog M → Option (A.T × SHint A.T)
  | _, τ, .block is => sumOr (findOpCode A same (.block is) τ S 0) fun _ =>
    (A.checkBlock τ is).map fun τ' => (τ', .block (chunkHints A chunk τ is is.length))
  | anc, τ, .seq c₁ c₂ => sumOr (findOpCode A same (.seq c₁ c₂) τ S 0) fun _ =>
    (hintOpsA S same wk anc τ c₁).bind fun (τ₁, h₁) =>
      let anc' := τ :: anc
      let plain := (hintOpsA S same wk anc' τ₁ c₂).map fun (τ₂, h₂) => (τ₂, .seq τ₁ h₁ h₂)
      match entryCall c₂ with
      | some n =>
        if hasCallOp S n && !(plain.any fun (_, h) => match h with
            | .seq _ _ h₂ => h₂.leadsWithSum
            | _ => false) then
          (anc'.findSome? fun a => (wk a τ₁).bind fun m =>
              (hintOpsA S same wk anc' m c₂).bind fun (τ₂, h₂) =>
                if h₂.leadsWithSum then some (τ₂, .seq m h₁ h₂) else none) <|> plain
        else plain
      | none => plain
  | anc, τ, .ite cd t e => sumOr (findOpCode A same (.ite cd t e) τ S 0) fun _ =>
    (hintOpsA S same wk anc τ t).bind fun (τ₁, h₁) => (hintOpsA S same wk anc τ e).map fun (τ₂, h₂) =>
      (A.meet τ₁ τ₂, .ite h₁ h₂)
  | anc, τ, .loop body c => sumOr (findOpCode A same (.loop body c) τ S 0) fun _ =>
    hintSumA.go A c (hintOpsA S same wk anc · body) loopFuel τ
  | _, τ, .call n body => match findOp A n τ S 0 with
    | some (k, post) => some (post, .sum k)
    | none => (A.call τ).bind fun τ₁ => (hintOpsA S same wk [] τ₁ body).bind fun (τ₂, h) =>
      (A.ret τ₂).map (·, .call h)
  | _, τ, .frame i body j => sumOr (findOpCode A same (.frame i body j) τ S 0) fun _ =>
    (A.push τ i).bind fun τ₁ => (hintOpsA S same wk [] τ₁ body).bind fun (τ₂, h) =>
      (A.pop τ₂ j).map (·, .frame h)
  | _, _, .icall .. => none

/-- `hintOpsA` from the start of a function, as an expression (the taint at
its end and the hint; `τ` and any hint, if the analysis fails), compiled
once here: the tactics evaluate a call of it. -/
@[nospecialize] def hintOpsExpr [Lean.ToExpr A.T] (S : List (Op M A.T)) (same : Prog M → Prog M → Bool)
    (wk : A.T → A.T → Option A.T) (τ : A.T) (c : Prog M) : Lean.Expr :=
  Lean.toExpr ((hintOpsA A S same wk [] τ c).getD (τ, .block []))

/-- The weakening of `hintOpsA` for a monotone domain. -/
def wkFrame [Frame A] (a τ₁ : A.T) : Option A.T :=
  let m := Frame.join (A := A) a (Frame.frameOf (A := A) τ₁ τ₁)
  if A.le m τ₁ then some m else none

end Taint

namespace TaintOps

open Lean Meta Elab Tactic TaintSum

/-- The operations `ls` (theorems `Taint.OpOk A o`, or all `Taint.OpSound A o`):
the list of their `o`, a proof that they hold (`Taint.AllOk'`, or
`Taint.AllSound`), and whether they are `OpOk`. -/
meta def ops (M A : Expr) (ls : Array Name) : MetaM (Expr × Expr × Bool) := do
  let T := mkApp2 (mkConst ``Taint.T) M A
  let oTy := mkApp2 (mkConst ``Taint.Op) M T
  let mut os := #[]
  let mut okAll := true
  for l in ls do
    let ty ← instantiateMVars (← inferType (mkConst l))
    if ty.isAppOfArity ``Taint.OpOk 4 then os := os.push (ty.getArg! 3)
    else if ty.isAppOfArity ``Taint.OpSound 3 then
      os := os.push (ty.getArg! 2); okAll := false
    else throwError "taint operations: {l} is neither a `Taint.OpOk` nor a `Taint.OpSound`: {ty}"
  let S ← mkListLit oTy os.toList
  let mut prf := mkConst ``True.intro
  for i in [0:ls.size] do
    let j := ls.size - 1 - i
    let mut pj := mkConst ls[j]!
    let mut tj ← inferType pj
    unless okAll do
      let ty ← instantiateMVars tj
      if ty.isAppOfArity ``Taint.OpOk 4 then
        pj ← mkAppM ``And.left #[pj]
        tj ← inferType pj
    prf := mkApp4 (mkConst ``And.intro) tj (← inferType prf) pj prf
  return (S, prf, okAll)

/-- The hint of the analysis of `c` from `τ` with the operations `S` (in
compiled code): the taint at the end, and the hint. -/
meta def hintOf (who : String) (M A S τ c : Expr) : MetaM (Expr × Expr) := do
  let T' ← whnfD (mkApp2 (mkConst ``Taint.T) M A)
  let instT ← synthInstance (mkApp (mkConst ``ToExpr [0]) T')
  let wk ← try
      let fr ← synthInstance (mkApp2 (mkConst ``Taint.Frame) M A)
      pure (mkApp3 (mkConst ``Taint.wkFrame) M A fr)
    catch _ =>
      let T := mkApp2 (mkConst ``Taint.T) M A
      pure (.lam `a T (.lam `b T (← mkAppOptM ``Option.none #[T]) .default) .default)
  let e := mkAppN (mkConst ``Taint.hintOpsExpr) #[M, A, instT, S, ← sameFn M, wk, τ, c]
  let ph ← unsafe evalExpr Expr (mkConst ``Expr) e
  unless ph.isAppOfArity ``Prod.mk 4 do throwError "{who}: unexpected {ph}"
  return (ph.getArg! 2, ph.getArg! 3)

/-- Closes the goals `g` (`checkOps …` by `lit_decide`, `fillOps … = c` by
the kernel's unfolding, `keepsOps …` and `le F F` by `lit_decide`). -/
meta def closeAll (gs : List MVarId) : TacticM Unit := do
  for m in gs do
    setGoals [m]
    let ty ← instantiateMVars (← m.getType)
    if ty.find? (·.isAppOfArity ``Taint.fillOps 5) |>.isSome then fillRfl
    else evalTactic (← `(tactic| lit_decide))

end TaintOps

open Lean Meta Elab Tactic TaintOps in
/-- `taint_decide_ops [l₁, …]` proves `Taint.Sem A τ c` by the analysis of
`c` from `τ` (`Taint.checkOps`), with the operations `lᵢ : Taint.OpOk A o`
(or `Taint.OpSound A o`) in place of the code they are of. -/
elab "taint_decide_ops " "[" ls:ident,* "]" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  unless ty.isAppOfArity ``Taint.Sem 4 do throwError "taint_decide_ops: the goal is not `Taint.Sem A τ c`"
  let args := ty.getAppArgs
  let (M, A, τ, c) := (args[0]!, args[1]!, args[2]!, args[3]!)
  let names ← ls.getElems.mapM fun l => realizeGlobalConstNoOverloadWithInfo l
  let (S, hS, okAll) ← ops M A names
  let (_, hint) ← hintOf "taint_decide_ops" M A S τ c
  let hS ← if okAll then mkAppOptM ``Taint.AllOk'.sound #[M, A, none, S, hS] else pure hS
  let hc ← mkFreshExprSyntheticOpaqueMVar
    (← mkEq (mkAppN (mkConst ``Option.isSome [0]) #[mkApp2 (mkConst ``Taint.T) M A,
      mkAppN (mkConst ``Taint.checkOps) #[M, A, S, τ, c, hint]]) (mkConst ``Bool.true))
  let hf ← mkFreshExprSyntheticOpaqueMVar (← mkEq (mkAppN (mkConst ``Taint.fillOps)
    #[M, mkApp2 (mkConst ``Taint.T) M A, S, c, hint]) c)
  let pf ← mkAppOptM ``Taint.sem_of_checkOps #[M, A, S, hS, c, τ, hint, hc, hf]
  g.assign pf
  closeAll [hc.mvarId!, hf.mvarId!]

open Lean Meta Elab Tactic TaintOps in
/-- `taint_decide_ops_check` proves `Taint.OpsCheck A S τ c p` by the
analysis of `c` from `τ` with the operations `S`, for any domain. -/
elab "taint_decide_ops_check" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  unless ty.isAppOfArity ``Taint.OpsCheck 6 do
    throwError "taint_decide_ops_check: the goal is not `Taint.OpsCheck A S τ c p`"
  let args := ty.getAppArgs
  let (M, A, S, τ, c) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  let (_, hint) ← hintOf "taint_decide_ops_check" M A S τ c
  let hs ← Term.exprToSyntax hint
  evalTactic (← `(tactic| refine ⟨$hs, ?_, ?_⟩))
  closeAll (← getGoals)

open Lean Meta Elab Term Tactic TaintOps in
/-- The theorem `N : Taint.OpOk A (Op.framed A c τ post F)` of `taint_summary_ops`. -/
meta def TaintOps.summaryCmd (id : Ident) (a τ c : Term) (f : Option Term) (ls : Array Ident) :
    TermElabM Unit := do
  let A ← instantiateMVars (← elabTerm a none)
  let aTy ← whnf (← inferType A)
  unless aTy.isAppOfArity ``Taint 1 do throwError "taint_summary_ops: {A} is not a `Taint`"
  let M := aTy.appArg!
  let T := mkApp2 (mkConst ``Taint.T) M A
  let τ ← elabTermEnsuringType τ T
  let c ← elabTermEnsuringType c (mkApp (mkConst ``Prog) M)
  let lf ← synthInstance (mkApp2 (mkConst ``Taint.LeFrame) M A)
  let fr := mkApp3 (mkConst ``Taint.LeFrame.toFrame) M A lf
  let F ← match f with
    | some f => elabTermEnsuringType f T
    | none => pure (mkApp3 (mkConst ``Taint.Frame.bot) M A fr)
  synthesizeSyntheticMVarsNoPostponing
  let τ ← instantiateMVars τ
  let c ← instantiateMVars c
  let F ← instantiateMVars F
  if τ.hasMVar || c.hasMVar || F.hasMVar then
    throwError "taint_summary_ops: the taints and the code must be closed"
  let names ← ls.mapM fun l => realizeGlobalConstNoOverloadWithInfo l
  let (S, hS, okAll) ← ops M A names
  unless okAll do throwError "taint_summary_ops: every operation must be a `Taint.OpOk`"
  let (post, hint) ← hintOf "taint_summary_ops" M A S τ c
  let ty := mkApp4 (mkConst ``Taint.OpOk) M A fr (mkAppN (mkConst ``Taint.Op.framed) #[M, A, lf, c, τ, post, F])
  let mv ← mkFreshExprSyntheticOpaqueMVar ty
  let gs ← Tactic.run mv.mvarId! do
    let g ← getMainGoal
    let e ← mkAppOptM ``Taint.opOk_framed_of_checkOpsLe
      #[some M, some A, some lf, some S, some hS, some c, some τ, some post, some F, some hint]
    let (mvs, _, _) ← forallMetaTelescope (← inferType e)
    let pf := mkAppN e mvs
    unless ← isDefEq (← inferType pf) (← g.getType) do
      throwError "taint_summary_ops: {← inferType pf} does not match {← g.getType}"
    g.assign pf
    closeAll (mvs.toList.map (·.mvarId!))
  unless gs.isEmpty do throwError "taint_summary_ops: goals remain"
  let v ← instantiateMVars mv
  addDecl <| .thmDecl
    { name := (← getCurrNamespace) ++ id.getId, levelParams := [], type := ty, value := v }

/-- `taint_summary_ops N : A τ code keeping F using l₁ …` proves the operation
`N : Taint.OpOk A (Taint.Op.framed A code τ post F)`, with `post` what the
analysis of `code` from `τ` ends with (with the operations `lᵢ` in place of
the code they are of) and `F` what `code` does not write (by default
nothing), as `taint_summary` does. -/
syntax "taint_summary_ops " ident " : " term:max term:max term:max (" keeping " term:max)?
  (" using " ident+)? : command

open Lean Elab Command in
elab_rules : command
  | `(taint_summary_ops $id : $a $τ $c $[keeping $f]? $[using $ls*]?) =>
    liftTermElabM (TaintOps.summaryCmd id a τ c f (ls.getD #[]))

end VG

