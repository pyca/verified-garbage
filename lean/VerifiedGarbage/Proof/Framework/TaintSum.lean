import VerifiedGarbage.Proof.Framework.Taint

/-!
# Summaries of called functions, for the constant-time analysis

`taint_decide` has the kernel evaluate the analysis (`Taint.check`) of the
whole program, including the body of every function it calls, once per call:
a sponge called forty times has its permutation analysed forty times, in every
theorem about a caller. A *summary* `(code, pre, post)` says that the analysis
of `code` from `pre` succeeds and ends with at least `post` public
(`SumOk`); it is proven once, and `checkSum` then uses it, in place of the
analysis of `code`, wherever the program has `code` with at least `pre`
public.

This needs the analysis to be monotone (`Mono`) along an order `R` (with
more public on entry, it succeeds, with as much public at the end), along
which the hints of a check still hold: `le` itself (`LeFrame`), or a finer
order where `le` is not monotone. Summaries apply to calls (by their name)
and to any other code that is the summary's (`CodeEq`, for the hints). The
kernel never compares code:
`checkSum` does not look at the code it summarizes, and `fill` puts the
summarized code back where the hint says, so `fill S c h = c`, which the
kernel checks by definitional unfolding (`Eq.refl`), says that it was the
right code. `taint_decide_sum` and `taint_summary` compute the hints (in
compiled code, which need not be sound) and prove both.
-/

namespace VG

namespace Taint

variable {M : ISA} (A : Taint M)

/-- The analysis is monotone along an order `R`: from a taint with more
public (`R`) on entry, each of its steps succeeds, with more public after
it. The hints of a check (`le`) still hold along `R` (`le_R`), so the check
of the code from the larger taint can use them.

`R` may be `le` itself, or finer: e.g. one that compares only taints that
know the same about memory (and more registers), along which an analysis
that is not monotone along `le` is (x86). `R` need not be reflexive either:
a domain may compare only taints that satisfy an invariant (`R τ τ`), which
the right side of every comparison does. -/
class Mono where
  R : A.T → A.T → Bool
  R_trans : ∀ {a b c}, R a b = true → R b c = true → R a c = true
  R_right : ∀ {a b}, R a b = true → R b b = true
  le_R : ∀ {m τ σ}, A.le m τ = true → R τ σ = true → A.le m σ = true
  step : ∀ {τ σ τ'} (i : M.Instr), R τ σ = true → A.step τ i = some τ' →
    ∃ σ', A.step σ i = some σ' ∧ R τ' σ' = true
  condPub : ∀ {τ σ} (c : M.Cond), R τ σ = true → A.condPub τ c = true → A.condPub σ c = true
  meet : ∀ {τ₁ τ₂ σ₁ σ₂}, R τ₁ σ₁ = true → R τ₂ σ₂ = true → R (A.meet τ₁ τ₂) (A.meet σ₁ σ₂) = true
  call : ∀ {τ σ τ'}, R τ σ = true → A.call τ = some τ' → ∃ σ', A.call σ = some σ' ∧ R τ' σ' = true
  ret : ∀ {τ σ τ'}, R τ σ = true → A.ret τ = some τ' → ∃ σ', A.ret σ = some σ' ∧ R τ' σ' = true
  push : ∀ {τ σ τ'} (i : M.Instr), R τ σ = true → A.push τ i = some τ' →
    ∃ σ', A.push σ i = some σ' ∧ R τ' σ' = true
  pop : ∀ {τ σ τ'} (i : M.Instr), R τ σ = true → A.pop τ i = some τ' →
    ∃ σ', A.pop σ i = some σ' ∧ R τ' σ' = true

/-- The analysis keeps what is public of a set `F` of things it does not
write (`keeps F i`): `frameOf τ F`, what of `F` is public in `τ` (e.g. their
meet), stays public (`Fr`: what the first says is public, the second says
too). Then a summary can say that what was public of its `F` stays public
(`SumOk`), and one summary applies to calls that differ in what is public of
`F`. Where a check has a hint `m`, the check from a taint with more public
continues from `join m Φ`, with what is public of the frame `Φ`; `bot` has
nothing public. The laws hold of the taints that satisfy the domain's
invariant (`R τ τ`). -/
class Frame extends Mono A where
  join : A.T → A.T → A.T
  bot : A.T
  frameOf : A.T → A.T → A.T
  Fr : A.T → A.T → Bool
  Fr_trans : ∀ {a b c}, Fr a b = true → Fr b c = true → Fr a c = true
  Fr_R : ∀ {Φ τ σ}, Fr Φ τ = true → R τ σ = true → Fr Φ σ = true
  join_hint : ∀ {m Φ τ}, A.le m τ = true → Fr Φ τ = true →
    A.le (join m Φ) τ = true ∧ R m (join m Φ) = true ∧ Fr Φ (join m Φ) = true
  join_R : ∀ {a b σ}, R a σ = true → Fr b σ = true → R (join a b) σ = true
  frame_le_left : ∀ {a} F, R a a = true → Fr (frameOf a F) a = true
  frame_le_right : ∀ a {F}, Fr F F = true → Fr (frameOf a F) F = true
  frame_mono : ∀ {τ σ} F, R τ σ = true → Fr (frameOf τ F) (frameOf σ F) = true
  le_frame : ∀ {Φ σ F}, Fr Φ σ = true → Fr Φ F = true → Fr Φ (frameOf σ F) = true
  le_meet : ∀ {Φ a b}, Fr Φ a = true → Fr Φ b = true → Fr Φ (A.meet a b) = true
  bot_le : ∀ {a}, R a a = true → Fr bot a = true
  bot_valid : Fr bot bot = true
  /-- `i` does not write anything of `F`. -/
  keeps : A.T → M.Instr → Bool
  /-- A call and a return do not write anything of `F`. -/
  keepsCall : A.T → Bool
  keeps_bot : ∀ i, keeps bot i = true
  keepsCall_bot : keepsCall bot = true
  step_keeps : ∀ {F Φ σ σ'} (i : M.Instr), keeps F i = true → Fr Φ F = true → Fr Φ σ = true →
    A.step σ i = some σ' → Fr Φ σ' = true
  call_keeps : ∀ {F Φ σ σ'}, keepsCall F = true → Fr Φ F = true → Fr Φ σ = true →
    A.call σ = some σ' → Fr Φ σ' = true
  ret_keeps : ∀ {F Φ σ σ'}, keepsCall F = true → Fr Φ F = true → Fr Φ σ = true →
    A.ret σ = some σ' → Fr Φ σ' = true
  push_keeps : ∀ {F Φ σ σ'} (i : M.Instr), keeps F i = true → Fr Φ F = true → Fr Φ σ = true →
    A.push σ i = some σ' → Fr Φ σ' = true
  pop_keeps : ∀ {F Φ σ σ'} (i : M.Instr), keeps F i = true → Fr Φ F = true → Fr Φ σ = true →
    A.pop σ i = some σ' → Fr Φ σ' = true

/-- A domain whose analysis is monotone along its own order `le`, with
frames: the order is a preorder on the taints that satisfy the domain's
invariant (`le τ τ`), with a join of any two below a third, a least element
and a frame operation (e.g. the meet). -/
class LeFrame where
  le_trans : ∀ {a b c}, A.le a b = true → A.le b c = true → A.le a c = true
  le_right : ∀ {a b}, A.le a b = true → A.le b b = true
  step : ∀ {τ σ τ'} (i : M.Instr), A.le τ σ = true → A.step τ i = some τ' →
    ∃ σ', A.step σ i = some σ' ∧ A.le τ' σ' = true
  condPub : ∀ {τ σ} (c : M.Cond), A.le τ σ = true → A.condPub τ c = true → A.condPub σ c = true
  meet : ∀ {τ₁ τ₂ σ₁ σ₂}, A.le τ₁ σ₁ = true → A.le τ₂ σ₂ = true →
    A.le (A.meet τ₁ τ₂) (A.meet σ₁ σ₂) = true
  call : ∀ {τ σ τ'}, A.le τ σ = true → A.call τ = some τ' →
    ∃ σ', A.call σ = some σ' ∧ A.le τ' σ' = true
  ret : ∀ {τ σ τ'}, A.le τ σ = true → A.ret τ = some τ' →
    ∃ σ', A.ret σ = some σ' ∧ A.le τ' σ' = true
  push : ∀ {τ σ τ'} (i : M.Instr), A.le τ σ = true → A.push τ i = some τ' →
    ∃ σ', A.push σ i = some σ' ∧ A.le τ' σ' = true
  pop : ∀ {τ σ τ'} (i : M.Instr), A.le τ σ = true → A.pop τ i = some τ' →
    ∃ σ', A.pop σ i = some σ' ∧ A.le τ' σ' = true
  join : A.T → A.T → A.T
  bot : A.T
  frameOf : A.T → A.T → A.T
  join_lub : ∀ {a b c}, A.le a c = true → A.le b c = true →
    A.le a (join a b) = true ∧ A.le b (join a b) = true ∧ A.le (join a b) c = true
  frame_le_left : ∀ {a} F, A.le a a = true → A.le (frameOf a F) a = true
  frame_le_right : ∀ a {F}, A.le F F = true → A.le (frameOf a F) F = true
  frame_mono : ∀ {τ σ} F, A.le τ σ = true → A.le (frameOf τ F) (frameOf σ F) = true
  le_frame : ∀ {Φ σ F}, A.le Φ σ = true → A.le Φ F = true → A.le Φ (frameOf σ F) = true
  le_meet : ∀ {a b c}, A.le a b = true → A.le a c = true → A.le a (A.meet b c) = true
  bot_le : ∀ {a}, A.le a a = true → A.le bot a = true
  bot_valid : A.le bot bot = true
  keeps : A.T → M.Instr → Bool
  keepsCall : A.T → Bool
  keeps_bot : ∀ i, keeps bot i = true
  keepsCall_bot : keepsCall bot = true
  step_keeps : ∀ {F Φ σ σ'} (i : M.Instr), keeps F i = true → A.le Φ F = true → A.le Φ σ = true →
    A.step σ i = some σ' → A.le Φ σ' = true
  call_keeps : ∀ {F Φ σ σ'}, keepsCall F = true → A.le Φ F = true → A.le Φ σ = true →
    A.call σ = some σ' → A.le Φ σ' = true
  ret_keeps : ∀ {F Φ σ σ'}, keepsCall F = true → A.le Φ F = true → A.le Φ σ = true →
    A.ret σ = some σ' → A.le Φ σ' = true
  push_keeps : ∀ {F Φ σ σ'} (i : M.Instr), keeps F i = true → A.le Φ F = true → A.le Φ σ = true →
    A.push σ i = some σ' → A.le Φ σ' = true
  pop_keeps : ∀ {F Φ σ σ'} (i : M.Instr), keeps F i = true → A.le Φ F = true → A.le Φ σ = true →
    A.pop σ i = some σ' → A.le Φ σ' = true

/-- A domain monotone along its own order (`LeFrame`) has frames, with `R`
and `Fr` both `le`. -/
instance (priority := low) LeFrame.toFrame [h : LeFrame A] : Frame A where
  R := A.le
  R_trans := h.le_trans
  R_right := h.le_right
  le_R := h.le_trans
  step := h.step
  condPub := h.condPub
  meet := h.meet
  call := h.call
  ret := h.ret
  push := h.push
  pop := h.pop
  join := h.join
  bot := h.bot
  frameOf := h.frameOf
  Fr := A.le
  Fr_trans := h.le_trans
  Fr_R := h.le_trans
  join_hint hm hΦ :=
    let j := h.join_lub hm hΦ
    ⟨j.2.2, j.1, j.2.1⟩
  join_R ha hb := (h.join_lub ha hb).2.2
  frame_le_left := h.frame_le_left
  frame_le_right := h.frame_le_right
  frame_mono := h.frame_mono
  le_frame := h.le_frame
  le_meet := h.le_meet
  bot_le := h.bot_le
  bot_valid := h.bot_valid
  keeps := h.keeps
  keepsCall := h.keepsCall
  keeps_bot := h.keeps_bot
  keepsCall_bot := h.keepsCall_bot
  step_keeps := h.step_keeps
  call_keeps := h.call_keeps
  ret_keeps := h.ret_keeps
  push_keeps := h.push_keeps
  pop_keeps := h.pop_keeps

/-- A hint for `checkSum`: a `Hint`, where `sum k` uses the `k`-th summary. -/
inductive SHint (T : Type) where
  | block (mids : List T)
  | seq (mid : T) (h₁ h₂ : SHint T)
  | ite (h₁ h₂ : SHint T)
  | loop (inv : T) (h : SHint T)
  | call (h : SHint T)
  | frame (h : SHint T)
  | sum (k : Nat)
  deriving Lean.ToExpr

/-- A summary: code, `pre`, `post` and `frame`. -/
abbrev Summary (M : ISA) (T : Type) := Prog M × T × T × T

/-- The summary `(code, pre, post, F)` holds: from at least `pre` public, the
analysis of `code` succeeds, and ends with at least `post` public, and what
was public of `F`. -/
def SumOk [Frame A] (s : Summary M A.T) : Prop :=
  ∀ τ, Mono.R (A := A) s.2.1 τ = true → ∃ h τ', A.check τ s.1 h = some τ' ∧
    Mono.R (A := A) s.2.2.1 τ' = true ∧ Frame.Fr (A := A) (Frame.frameOf τ s.2.2.2) τ' = true

/-- Every summary of the list holds. -/
def AllOk [Frame A] : List (Summary M A.T) → Prop
  | [] => True
  | s :: S => SumOk A s ∧ AllOk S

/-- `check`, with the summaries `S`: at a `sum k` hint, the `k`-th summary
`(code, pre, post, F)`, if at least `pre` is public, gives `post` and what is
public of `F`, whatever the code there (`fill` says it is `code`). -/
def checkSum [Frame A] (S : List (Summary M A.T)) (τ : A.T) (c : Prog M) (h : SHint A.T) : Option A.T :=
  match h, τ, c with
  | .sum k, τ, _ => match S[k]? with
    | some (_, pre, post, F) =>
      if Mono.R (A := A) pre τ then some (Frame.join post (Frame.frameOf τ F)) else none
    | none => none
  | .block ms, τ, .block is => checkChunks A chunk τ is ms
  | .seq mid h₁ h₂, τ, .seq c₁ c₂ =>
    (checkSum S τ c₁ h₁).bind fun τ' => if A.le mid τ' then checkSum S mid c₂ h₂ else none
  | .ite h₁ h₂, τ, .ite c t e =>
    if A.condPub τ c then
      (checkSum S τ t h₁).bind fun τ₁ => (checkSum S τ e h₂).map fun τ₂ => A.meet τ₁ τ₂
    else none
  | .loop σ h, τ, .loop body c =>
    if A.le σ τ then
      (checkSum S σ body h).bind fun σ' => if A.le σ σ' && A.condPub σ' c then some σ' else none
    else none
  | .call h, τ, .call _ body => (A.call τ).bind fun τ₁ => (checkSum S τ₁ body h).bind A.ret
  | .frame h, τ, .frame i body j =>
    (A.push τ i).bind fun τ₁ => (checkSum S τ₁ body h).bind fun τ₂ => A.pop τ₂ j
  | _, _, _ => none
termination_by structural h

/-- Nothing of `F` is written, but where the hint uses a summary, whose frame
then has all of `F` (or `F` has nothing public). -/
def keepsSum [Frame A] (S : List (Summary M A.T)) (F : A.T) (c : Prog M) (h : SHint A.T) : Bool :=
  match h, c with
  | .sum k, _ => match S[k]? with
    | some (_, _, _, F') => Frame.Fr (A := A) F F' || Frame.Fr (A := A) F Frame.bot
    | none => true
  | .block _, .block is => is.all (Frame.keeps (A := A) F)
  | .seq _ h₁ h₂, .seq a b => keepsSum S F a h₁ && keepsSum S F b h₂
  | .ite h₁ h₂, .ite _ t e => keepsSum S F t h₁ && keepsSum S F e h₂
  | .loop _ h, .loop b _ => keepsSum S F b h
  | .call h, .call _ b => Frame.keepsCall (A := A) F && keepsSum S F b h
  | .frame h, .frame i b j =>
    Frame.keeps (A := A) F i && keepsSum S F b h && Frame.keeps (A := A) F j
  | _, _ => true
termination_by structural h

variable {A} in
/-- `c`, with the code of the summary at each `sum k` of the hint in place of
what is there. `fill S c h = c` says that each summary is used for its code. -/
def fill {T : Type} (S : List (Summary M T)) (c : Prog M) (h : SHint T) : Prog M :=
  match h, c with
  | .sum k, c => match S[k]? with
    | some (b, _, _, _) => b
    | none => c
  | .seq _ h₁ h₂, .seq a b => .seq (fill S a h₁) (fill S b h₂)
  | .ite h₁ h₂, .ite cd t e => .ite cd (fill S t h₁) (fill S e h₂)
  | .loop _ h, .loop b cd => .loop (fill S b h) cd
  | .call h, .call n b => .call n (fill S b h)
  | .frame h, .frame i b j => .frame i (fill S b h) j
  | _, c => c
termination_by structural h

/-- `checkSum` ends with at least `post` public. -/
def checkSumLe [Frame A] (S : List (Summary M A.T)) (τ : A.T) (c : Prog M) (h : SHint A.T)
    (post : A.T) : Bool :=
  match checkSum A S τ c h with
  | some τ' => Mono.R (A := A) post τ'
  | none => false

/-! ## Soundness -/

private theorem if_pos' {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

variable {A}

local notation "J" => Frame.join (A := A)
local notation "R" => Mono.R (A := A)
local notation "Fr" => Frame.Fr (A := A)

theorem checkBlock_frame [hm : Frame A] {is : List M.Instr} {F Φ τ σ τ' : A.T}
    (h : A.checkBlock τ is = some τ') (hk : is.all (Frame.keeps (A := A) F) = true)
    (hΦF : Fr Φ F = true) (hle : R τ σ = true) (hΦ : Fr Φ σ = true) :
    ∃ σ', A.checkBlock σ is = some σ' ∧ R τ' σ' = true ∧ Fr Φ σ' = true := by
  induction is generalizing τ σ with
  | nil =>
    simp only [checkBlock, Option.some.injEq] at h
    subst h; exact ⟨σ, rfl, hle, hΦ⟩
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hk
    simp only [checkBlock, Option.bind_eq_some_iff] at h
    obtain ⟨τ₁, hs, hr⟩ := h
    obtain ⟨σ₁, hs', hle'⟩ := hm.step i hle hs
    obtain ⟨σ', h', hle'', hΦ'⟩ := ih hr hk.2 hle' (hm.step_keeps i hk.1 hΦF hΦ hs')
    exact ⟨σ', by simp only [checkBlock, Option.bind_eq_some_iff]; exact ⟨σ₁, hs', h'⟩, hle'', hΦ'⟩

theorem checkChunks_frame [hm : Frame A] {chunkSize : Nat} {ms : List A.T} {is : List M.Instr} {F Φ τ σ τ' : A.T}
    (h : A.checkChunks chunkSize τ is ms = some τ') (hk : is.all (Frame.keeps (A := A) F) = true)
    (hΦF : Fr Φ F = true) (hle : R τ σ = true) (hΦ : Fr Φ σ = true) :
    ∃ σ', A.checkChunks chunkSize σ is (ms.map (J · Φ)) = some σ' ∧ R τ' σ' = true ∧ Fr Φ σ' = true := by
  induction ms generalizing τ σ is with
  | nil => exact checkBlock_frame h hk hΦF hle hΦ
  | cons m ms ih =>
    simp only [checkChunks, KList.take_eq, KList.drop_eq, Option.bind_eq_some_iff] at h
    obtain ⟨τ₁, h₁, h₂⟩ := h
    split at h₂ <;> [rename_i hm₁; cases h₂]
    have hk' : (is.take chunkSize ++ is.drop chunkSize).all (Frame.keeps (A := A) F) = true := by
      rw [List.take_append_drop]; exact hk
    rw [List.all_append, Bool.and_eq_true] at hk'
    obtain ⟨σ₁, h₁', hle₁, hΦ₁⟩ := checkBlock_frame h₁ hk'.1 hΦF hle hΦ
    have jl := hm.join_hint (hm.le_R hm₁ hle₁) hΦ₁
    obtain ⟨σ', h', hle', hΦ'⟩ := ih h₂ hk'.2 jl.2.1 jl.2.2
    refine ⟨σ', ?_, hle', hΦ'⟩
    simp only [List.map_cons, checkChunks, KList.take_eq, KList.drop_eq, Option.bind_eq_some_iff]
    exact ⟨σ₁, h₁', by rw [if_pos' jl.1]; exact h'⟩

theorem AllOk.get [Frame A] {S : List (Summary M A.T)} (hS : AllOk A S) {k : Nat}
    {s : Summary M A.T} (h : S[k]? = some s) : SumOk A s := by
  induction S generalizing k with
  | nil => cases h
  | cons s' S ih =>
    cases k with
    | zero => cases h; exact hS.1
    | succ k => exact ih hS.2 h

/-- A successful `checkSum`, with summaries that hold, used for their code
(`fill`), is a successful `check` from any taint with more public (`R`),
which keeps public what was of `F` if nothing writes it (`keepsSum`). -/
theorem checkSum_frame [hm : Frame A] {S : List (Summary M A.T)} (hS : AllOk A S) {F Φ : A.T}
    (hΦF : Fr Φ F = true) :
    ∀ {hc : SHint A.T} {c : Prog M} {τ σ τ' : A.T}, A.checkSum S τ c hc = some τ' →
      fill S c hc = c → keepsSum A S F c hc = true → R τ σ = true → Fr Φ σ = true →
      ∃ h σ', A.check σ c h = some σ' ∧ R τ' σ' = true ∧ Fr Φ σ' = true := by
  intro hc
  induction hc with
  | sum k =>
    intro c τ σ τ' h hf hk hle hΦ
    replace h : (match S[k]? with
      | some (_, pre, post, F) => if R pre τ then some (J post (Frame.frameOf τ F)) else none
      | none => none) = some τ' := h
    rw [fill] at hf
    rw [keepsSum] at hk
    cases hks : S[k]? with
    | none => rw [hks] at h; cases h
    | some s =>
      obtain ⟨b, pre, post, F'⟩ := s
      rw [hks] at h hf hk
      simp only at h hf hk
      subst hf
      split at h <;> [rename_i hl; cases h]
      cases h
      obtain ⟨g, σ', h', hpost, hfr⟩ := hS.get hks σ (hm.R_trans hl hle)
      refine ⟨g, σ', h', hm.join_R hpost (hm.Fr_trans (hm.frame_mono F' hle) hfr), ?_⟩
      rcases Bool.or_eq_true _ _ ▸ hk with hk | hk
      · exact hm.Fr_trans (hm.le_frame hΦ (hm.Fr_trans hΦF hk)) hfr
      · exact hm.Fr_trans (hm.Fr_trans hΦF hk) (hm.bot_le (hm.R_right hpost))
  | block ms =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | block is =>
      obtain ⟨σ', h', hle', hΦ'⟩ := checkChunks_frame (ms := ms) (A := A) h hk hΦF hle hΦ
      exact ⟨.block (ms.map (J · Φ)) chunk, σ', h', hle', hΦ'⟩
    | _ => cases (h : (none : Option A.T) = some τ')
  | seq mid g₁ g₂ ih₁ ih₂ =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | seq c₁ c₂ =>
      have h : ((A.checkSum S τ c₁ g₁).bind fun τ' =>
        if A.le mid τ' then A.checkSum S mid c₂ g₂ else none) = some τ' := h
      have hf : Code.seq (fill S c₁ g₁) (fill S c₂ g₂) = .seq c₁ c₂ := hf
      have hk : (keepsSum A S F c₁ g₁ && keepsSum A S F c₂ g₂) = true := hk
      rw [Bool.and_eq_true] at hk
      injection hf with hf_1 hf_2
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, h₂⟩ := h
      split at h₂ <;> [rename_i hl; cases h₂]
      obtain ⟨g₁', σ₁, h₁', hle₁, hΦ₁⟩ := ih₁ h₁ hf_1 hk.1 hle hΦ
      have jl := hm.join_hint (hm.le_R hl hle₁) hΦ₁
      obtain ⟨g₂', σ₂, h₂', hle₂, hΦ₂⟩ := ih₂ h₂ hf_2 hk.2 jl.2.1 jl.2.2
      refine ⟨.seq (J mid Φ) g₁' g₂', σ₂, ?_, hle₂, hΦ₂⟩
      show ((A.check σ c₁ g₁').bind fun τ' =>
        if A.le (J mid Φ) τ' then A.check (J mid Φ) c₂ g₂' else none) = some σ₂
      rw [h₁', Option.bind_some, if_pos' jl.1]; exact h₂'
    | _ => cases (h : (none : Option A.T) = some τ')
  | ite g₁ g₂ ih₁ ih₂ =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | ite cd t e =>
      have h : (if A.condPub τ cd then
          (A.checkSum S τ t g₁).bind fun τ₁ => (A.checkSum S τ e g₂).map fun τ₂ => A.meet τ₁ τ₂
        else none) = some τ' := h
      have hf : Code.ite cd (fill S t g₁) (fill S e g₂) = .ite cd t e := hf
      have hk : (keepsSum A S F t g₁ && keepsSum A S F e g₂) = true := hk
      rw [Bool.and_eq_true] at hk
      injection hf with hf_1 hf_2 hf_3
      split at h <;> [rename_i hp; cases h]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, rfl⟩ := h
      obtain ⟨g₁', σ₁, h₁', hle₁, hΦ₁⟩ := ih₁ h₁ hf_2 hk.1 hle hΦ
      obtain ⟨g₂', σ₂, h₂', hle₂, hΦ₂⟩ := ih₂ h₂ hf_3 hk.2 hle hΦ
      refine ⟨.ite g₁' g₂', A.meet σ₁ σ₂, ?_, hm.meet hle₁ hle₂, hm.le_meet hΦ₁ hΦ₂⟩
      show (if A.condPub σ cd then
          (A.check σ t g₁').bind fun τ₁ => (A.check σ e g₂').map fun τ₂ => A.meet τ₁ τ₂
        else none) = _
      rw [if_pos' (hm.condPub cd hle hp), h₁', Option.bind_some, h₂', Option.map_some]
    | _ => cases (h : (none : Option A.T) = some τ')
  | loop inv g ih =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | loop body cd =>
      have h : (if A.le inv τ then
          (A.checkSum S inv body g).bind fun σ' =>
            if A.le inv σ' && A.condPub σ' cd then some σ' else none
        else none) = some τ' := h
      have hf : Code.loop (fill S body g) cd = .loop body cd := hf
      have hk : keepsSum A S F body g = true := hk
      injection hf with hf_1
      split at h <;> [rename_i hl; cases h]
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, h₂⟩ := h
      split at h₂ <;> [rename_i hc; cases h₂]
      cases h₂
      simp only [Bool.and_eq_true] at hc
      have jl := hm.join_hint (hm.le_R hl hle) hΦ
      obtain ⟨g', σ₁, h₁', hle₁, hΦ₁⟩ := ih h₁ hf_1 hk jl.2.1 jl.2.2
      refine ⟨.loop (J inv Φ) g', σ₁, ?_, hle₁, hΦ₁⟩
      show (if A.le (J inv Φ) σ then
          (A.check (J inv Φ) body g').bind fun σ' =>
            if A.le (J inv Φ) σ' && A.condPub σ' cd then some σ' else none
        else none) = some σ₁
      rw [if_pos' jl.1, h₁', Option.bind_some,
        if_pos' (by rw [(hm.join_hint (hm.le_R hc.1 hle₁) hΦ₁).1, hm.condPub cd hle₁ hc.2]; rfl)]
    | _ => cases (h : (none : Option A.T) = some τ')
  | call g ih =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | call n body =>
      have h : ((A.call τ).bind fun τ₁ => (A.checkSum S τ₁ body g).bind A.ret) = some τ' := h
      have hf : Code.call n (fill S body g) = .call n body := hf
      have hk : (Frame.keepsCall (A := A) F && keepsSum A S F body g) = true := hk
      rw [Bool.and_eq_true] at hk
      injection hf with hf_1 hf_2
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      obtain ⟨σ₁, h₁', hle₁⟩ := hm.call hle h₁
      obtain ⟨g', σ₂, h₂', hle₂, hΦ₂⟩ := ih h₂ hf_2 hk.2 hle₁ (hm.call_keeps hk.1 hΦF hΦ h₁')
      obtain ⟨σ₃, h₃', hle₃⟩ := hm.ret hle₂ h₃
      refine ⟨.call g', σ₃, ?_, hle₃, hm.ret_keeps hk.1 hΦF hΦ₂ h₃'⟩
      show ((A.call σ).bind fun τ₁ => (A.check τ₁ body g').bind A.ret) = some σ₃
      rw [h₁', Option.bind_some, h₂', Option.bind_some, h₃']
    | _ => cases (h : (none : Option A.T) = some τ')
  | frame g ih =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | frame i body j =>
      have h : ((A.push τ i).bind fun τ₁ => (A.checkSum S τ₁ body g).bind fun τ₂ => A.pop τ₂ j) =
        some τ' := h
      have hf : Code.frame i (fill S body g) j = .frame i body j := hf
      have hk : (Frame.keeps (A := A) F i && keepsSum A S F body g && Frame.keeps (A := A) F j) = true :=
        hk
      simp only [Bool.and_eq_true] at hk
      injection hf with hf_1 hf_2 hf_3
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      obtain ⟨σ₁, h₁', hle₁⟩ := hm.push i hle h₁
      obtain ⟨g', σ₂, h₂', hle₂, hΦ₂⟩ := ih h₂ hf_2 hk.1.2 hle₁
        (hm.push_keeps i hk.1.1 hΦF hΦ h₁')
      obtain ⟨σ₃, h₃', hle₃⟩ := hm.pop j hle₂ h₃
      refine ⟨.frame g', σ₃, ?_, hle₃, hm.pop_keeps j hk.2 hΦF hΦ₂ h₃'⟩
      show ((A.push σ i).bind fun τ₁ => (A.check τ₁ body g').bind fun τ₂ => A.pop τ₂ j) =
        some σ₃
      rw [h₁', Option.bind_some, h₂', Option.bind_some, h₃']
    | _ => cases (h : (none : Option A.T) = some τ')

/-- Nothing writes `bot`. -/
theorem keepsSum_bot [hm : Frame A] {S : List (Summary M A.T)} :
    ∀ {hc : SHint A.T} {c : Prog M}, keepsSum A S (Frame.bot (A := A)) c hc = true := by
  intro hc
  induction hc with
  | sum k =>
    intro c
    rw [keepsSum]
    cases S[k]? with
    | none => rfl
    | some s => exact (Bool.or_eq_true _ _).mpr (.inr hm.bot_valid)
  | block ms =>
    intro c
    cases c with
    | block is => exact List.all_eq_true.mpr fun i _ => hm.keeps_bot i
    | _ => rfl
  | seq _ g₁ g₂ ih₁ ih₂ =>
    intro c
    cases c with
    | seq a b => exact (Bool.and_eq_true _ _).mpr ⟨ih₁, ih₂⟩
    | _ => rfl
  | ite g₁ g₂ ih₁ ih₂ =>
    intro c
    cases c with
    | ite _ a b => exact (Bool.and_eq_true _ _).mpr ⟨ih₁, ih₂⟩
    | _ => rfl
  | loop _ g ih =>
    intro c
    cases c with
    | loop b _ => exact ih
    | _ => rfl
  | call g ih =>
    intro c
    cases c with
    | call _ b => exact (Bool.and_eq_true _ _).mpr ⟨hm.keepsCall_bot, ih⟩
    | _ => rfl
  | frame g ih =>
    intro c
    cases c with
    | frame i b j =>
      simp only [keepsSum, hm.keeps_bot, ih, Bool.and_self]
    | _ => rfl

/-- A summary proven with other summaries. -/
theorem sumOk_of_checkSum [hm : Frame A] {S : List (Summary M A.T)} (hS : AllOk A S)
    {c : Prog M} {pre post F : A.T} {hc : SHint A.T} (h : checkSumLe A S pre c hc post = true)
    (hf : fill S c hc = c) (hk : keepsSum A S F c hc = true) (hF : Fr F F = true) :
    SumOk A (c, pre, post, F) := by
  unfold checkSumLe at h
  split at h <;> [rename_i τ' hτ; cases h]
  intro τ hτ'
  obtain ⟨g, σ', h', hle', hΦ'⟩ := checkSum_frame hS (hm.frame_le_right τ hF) hτ hf hk hτ'
    (hm.frame_le_left F (hm.R_right hτ'))
  exact ⟨g, σ', h', hm.R_trans h hle', hΦ'⟩

/-- A successful `checkSum` with summaries that hold, used for their code, is
a successful `check`. -/
theorem exists_check_of_checkSum [hm : Frame A] {S : List (Summary M A.T)} (hS : AllOk A S)
    {c : Prog M} {τ : A.T} {hc : SHint A.T} (h : (checkSum A S τ c hc).isSome = true)
    (hf : fill S c hc = c) (hv : R τ τ = true) : ∃ h, (A.check τ c h).isSome = true := by
  obtain ⟨τ', hτ⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨g, σ', h', -⟩ := checkSum_frame hS hm.bot_valid hτ hf keepsSum_bot hv (hm.bot_le hv)
  exact ⟨g, by rw [h']; rfl⟩

/-- The analysis of the code of a summary, from at least its `pre`. -/
theorem exists_check_of_sumOk [Frame A] {c : Prog M} {pre post F τ : A.T} (h : SumOk A (c, pre, post, F))
    (hτ : R pre τ = true) : ∃ h, (A.check τ c h).isSome = true := by
  obtain ⟨g, τ', hg, -⟩ := h τ hτ
  exact ⟨g, by rw [hg]; rfl⟩

/-- The analysis of a function, from a summary of a call of it, from a taint
that the call does not change. -/
theorem exists_check_of_sumOk_call [Frame A] {n : String} {c : Prog M} {pre post F τ : A.T}
    (h : SumOk A (.call n c, pre, post, F)) (hτ : R pre τ = true) (hc : A.call τ = some τ) :
    ∃ h, (A.check τ c h).isSome = true := by
  obtain ⟨g, τ', hg, -⟩ := h τ hτ
  cases g with
  | call g =>
    have hg : ((A.call τ).bind fun τ₁ => (A.check τ₁ c g).bind A.ret) = some τ' := hg
    rw [hc, Option.bind_some, Option.bind_eq_some_iff] at hg
    obtain ⟨τ₂, h₂, -⟩ := hg
    exact ⟨g, by rw [h₂]; rfl⟩
  | _ => cases (hg : (none : Option A.T) = some τ')

/-! ## Computing hints

Nothing here needs to be sound: `checkSum` and `fill` check the hint. -/

variable (A)

/-- Structural equality of code (for `hintSum`, which need not be sound). -/
def codeBeq {I C : Type} [BEq I] [BEq C] : Code I C → Code I C → Bool
  | .block a, .block b => a == b
  | .seq a b, .seq c d => codeBeq a c && codeBeq b d
  | .ite x a b, .ite y c d => x == y && codeBeq a c && codeBeq b d
  | .loop a x, .loop b y => x == y && codeBeq a b
  | .call n a, .call m b => n == m && codeBeq a b
  | .frame i a j, .frame k b l => i == k && j == l && codeBeq a b
  | _, _ => false

/-- Equality of the code of `M`, for the hints of summaries of code that is
not a call (`hintSum`): an instance, compiled once with the ISA's equality of
instructions (e.g. `⟨codeBeq⟩`), rather than at every evaluation. Without
one, summaries apply only to calls. -/
class CodeEq (M : ISA) where
  same : Prog M → Prog M → Bool

/-- The first summary of a call of `n` that applies from `τ`: its index and
`post`. -/
def findSum [Frame A] (n : String) (τ : A.T) : List (Summary M A.T) → Nat → Option (Nat × A.T)
  | [], _ => none
  | (c, pre, post, F) :: S, k => match c with
    | .call n' _ =>
      if n' == n && Mono.R (A := A) pre τ then some (k, Frame.join post (Frame.frameOf τ F))
      else findSum n τ S (k + 1)
    | _ => findSum n τ S (k + 1)

/-- The first summary of the code `c` (by `same`) that applies from `τ`: its
index and `post`. -/
def findSumCode [Frame A] (same : Prog M → Prog M → Bool) (c : Prog M) (τ : A.T) :
    List (Summary M A.T) → Nat → Option (Nat × A.T)
  | [], _ => none
  | (c', pre, post, F) :: S, k =>
    if same c' c && Mono.R (A := A) pre τ then some (k, Frame.join post (Frame.frameOf τ F))
    else findSumCode same c τ S (k + 1)

/-- The hint of a summary, if `o` found one, or `k ()`. -/
def sumOr {T : Type} (o : Option (Nat × T)) (k : Unit → Option (T × SHint T)) :
    Option (T × SHint T) :=
  match o with
  | some (k, post) => some (post, .sum k)
  | none => k ()

/-- `hint`, using the first summary that applies at each call (by its name),
and at any other code that is a summary's (by `same`). -/
def hintSum [Frame A] (S : List (Summary M A.T)) (same : Prog M → Prog M → Bool) :
    A.T → Prog M → Option (A.T × SHint A.T)
  | τ, .block is => sumOr (findSumCode A same (.block is) τ S 0) fun _ =>
    (A.checkBlock τ is).map fun τ' => (τ', .block (chunkHints A chunk τ is is.length))
  | τ, .seq c₁ c₂ => sumOr (findSumCode A same (.seq c₁ c₂) τ S 0) fun _ =>
    (hintSum S same τ c₁).bind fun (τ₁, h₁) =>
      (hintSum S same τ₁ c₂).map fun (τ₂, h₂) => (τ₂, .seq τ₁ h₁ h₂)
  | τ, .ite cd t e => sumOr (findSumCode A same (.ite cd t e) τ S 0) fun _ =>
    (hintSum S same τ t).bind fun (τ₁, h₁) => (hintSum S same τ e).map fun (τ₂, h₂) =>
      (A.meet τ₁ τ₂, .ite h₁ h₂)
  | τ, .loop body c => sumOr (findSumCode A same (.loop body c) τ S 0) fun _ =>
    go c (hintSum S same · body) loopFuel τ
  | τ, .call n body => match findSum A n τ S 0 with
    | some (k, post) => some (post, .sum k)
    | none => (A.call τ).bind fun τ₁ => (hintSum S same τ₁ body).bind fun (τ₂, h) =>
      (A.ret τ₂).map (·, .call h)
  | τ, .frame i body j => sumOr (findSumCode A same (.frame i body j) τ S 0) fun _ =>
    (A.push τ i).bind fun τ₁ => (hintSum S same τ₁ body).bind fun (τ₂, h) =>
      (A.pop τ₂ j).map (·, .frame h)
where
  go (c : M.Cond) (body : A.T → Option (A.T × SHint A.T)) :
      Nat → A.T → Option (A.T × SHint A.T)
    | 0, _ => none
    | n + 1, σ => (body σ).bind fun (σ', h) =>
      if A.le σ σ' && A.condPub σ' c then some (σ', .loop σ h) else go c body n (A.meet σ σ')

/-- The taint at the end of `hintSum` and its hint (`τ` and any hint, if the
analysis fails). -/
def postHintSumOf [Frame A] (S : List (Summary M A.T)) (same : Prog M → Prog M → Bool) (τ : A.T)
    (c : Prog M) : A.T × SHint A.T :=
  (hintSum A S same τ c).getD (τ, .block [])

/-- The calls in `c` that its hint `h` analyses in full although a summary
in `S` is of the same function, by its name or by its code (`body`): their
names. Each is a summary that was meant to apply there and did not (its
`pre` does not hold there, or it is stated about another name), which only
costs time, so nothing else would notice. -/
@[nospecialize] def missedCalls {T : Type} (S : List (Summary M T))
    (body : Prog M → Prog M → Bool) : Prog M → SHint T → List String
  | .seq c₁ c₂, .seq _ h₁ h₂ => missedCalls S body c₁ h₁ ++ missedCalls S body c₂ h₂
  | .ite _ t e, .ite h₁ h₂ => missedCalls S body t h₁ ++ missedCalls S body e h₂
  | .loop b _, .loop _ h => missedCalls S body b h
  | .frame _ b _, .frame h => missedCalls S body b h
  | .call n b, .call h =>
    let same := S.any fun s => match s.1 with
      | .call n' b' => n' == n || body b' b
      | _ => false
    (if same then [n] else []) ++ missedCalls S body b h
  | _, _ => []

/-- `postHintSumOf`, with the calls the hint analyses in full although a
summary is of the same function (`missedCalls`). `TaintSum.hintChecked`
evaluates it once per check, in a definition it compiles: `nospecialize`
keeps the compiler from specializing the whole analysis to the instances and
functions of each check, which cost more than it saves. -/
@[nospecialize] def hintReport [Frame A] (S : List (Summary M A.T))
    (same body : Prog M → Prog M → Bool) (τ : A.T) (c : Prog M) :
    (A.T × SHint A.T) × List String :=
  let ph := postHintSumOf A S same τ c
  (ph, missedCalls S body c ph.2)

end Taint

namespace TaintSum

open Lean Meta Elab Tactic

/-- The summaries `ls` (theorems `Taint.SumOk A s`): the list of their `s`, and a
proof that they hold (`Taint.AllOk A`). -/
def summaries (M A : Expr) (ls : Array Name) : MetaM (Expr × Expr) := do
  let T := mkApp2 (mkConst ``Taint.T) M A
  let sTy := mkApp2 (mkConst ``Taint.Summary) M T
  let mut ss := #[]
  for l in ls do
    let ty ← instantiateMVars (← inferType (mkConst l))
    unless ty.isAppOfArity ``Taint.SumOk 4 do
      throwError "taint summaries: {l} is not a `Taint.SumOk`: {ty}"
    ss := ss.push (ty.getArg! 3)
  let S ← mkListLit sTy ss.toList
  let mut prf := mkConst ``True.intro
  for i in [0:ls.size] do
    let j := ls.size - 1 - i
    prf := mkApp4 (mkConst ``And.intro) (← inferType (mkConst ls[j]!))
      (← inferType prf) (mkConst ls[j]!) prf
  return (S, prf)

/-- The equality of the code of `M` (`Taint.CodeEq`), for the hints, if it
has one; otherwise none. -/
def sameFn (M : Expr) : MetaM Expr := do
  try
    let inst ← synthInstance (mkApp (mkConst ``Taint.CodeEq) M)
    return mkApp2 (mkConst ``Taint.CodeEq.same) M inst
  catch _ =>
    let P := mkApp (mkConst ``Prog) M
    return .lam `a P (.lam `b P (mkConst ``Bool.false) .default) .default

/-- Structural equality of the code of `M` (`Taint.codeBeq`), with its
instructions' and conditions' `BEq`, if it has them; otherwise none. -/
def bodyFn (M : Expr) : MetaM Expr := do
  let P := mkApp (mkConst ``Prog) M
  try
    let I ← whnfD (mkApp (mkConst ``ISA.Instr) M)
    let C ← whnfD (mkApp (mkConst ``ISA.Cond) M)
    let bi ← synthInstance (mkApp (mkConst ``BEq [0]) I)
    let bc ← synthInstance (mkApp (mkConst ``BEq [0]) C)
    return mkApp4 (mkConst ``Taint.codeBeq) I C bi bc
  catch _ =>
    return .lam `a P (.lam `b P (mkConst ``Bool.false) .default) .default

/-- The analysis of `c` from `τ` with the summaries `names` (whose list is
`S`), in compiled code: what it ends with and its hint (`postHintSumOf`).
It fails if the hint analyses in full a call of a function that one of the
summaries is of (by its name or its code: `Taint.missedCalls`), which would
otherwise only cost time, silently. (A summary that is never used is not an
error: callers share one list of summaries among several checks.) -/
def hintChecked (who : String) (M A fr S τ c : Expr) : MetaM (Expr × Expr) := do
  let T' ← whnfD (mkApp2 (mkConst ``Taint.T) M A)
  let phTy ← mkAppM ``Prod #[T', mkApp (mkConst ``Taint.SHint) T']
  let repTy := mkApp (mkConst ``List [0]) (mkConst ``String)
  let r := mkAppN (mkConst ``Taint.hintReport) #[M, A, fr, S, ← sameFn M, ← bodyFn M, τ, c]
  let e ← withLetDecl `r (← mkAppM ``Prod #[phTy, repTy]) r fun r => do
    let ph ← mkAppM ``ToExpr.toExpr #[← mkAppM ``Prod.fst #[r]]
    mkLetFVars #[r] (← mkAppM ``Prod.mk #[ph, ← mkAppM ``Prod.snd #[r]])
  let ty ← mkAppM ``Prod #[mkConst ``Expr, repTy]
  let (ph, missed) ← unsafe evalExpr (Expr × List String) ty e
  unless missed.isEmpty do
    throwError "{who}: the calls {missed.eraseDups} are analysed in full, although a summary \
      of the same function (by its name or its code) is given: its `pre` does not hold \
      there, or it is stated about another name or code"
  unless ph.isAppOfArity ``Prod.mk 4 do throwError "{who}: unexpected {ph}"
  return (ph.getArg! 2, ph.getArg! 3)

/-- Proves the main goal `fill S c h = c` by the kernel's unfolding. The code
is not rewritten to its literals: `fill` only unfolds `c` down to where the
summaries are, whose code is then the same term in both. -/
def fillRfl : TacticM Unit := do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (α, _, rhs) := ty.eq? | throwError "taint summaries: not an equation: {ty}"
  let u ← getLevel α
  let n ← mkAuxLemma [] ty (mkApp2 (mkConst ``Eq.refl [u]) α rhs)
  g.assign (mkConst n)
  replaceMainGoal []

/-- Proves `p` (with summaries `S`, which `hS` proves): `p` applied to the
hint (`hintChecked`), then to proofs of `check` (by `lit_decide`) and of
`fill` (`fillRfl`). -/
def proveWith (M A S hS c : Expr) (p : Name) (extra : Array Expr) (hint : Expr) :
    TacticM Unit := do
  let g ← getMainGoal
  let mono ← synthInstance (mkApp2 (mkConst ``Taint.Frame) M A)
  let e ← mkAppOptM p (#[some M, some A, some mono, some S, some hS, some c] ++
    extra.map some ++ #[some hint])
  let (mvs, _, _) ← forallMetaTelescope (← inferType e)
  let pf := mkAppN e mvs
  let ty ← inferType pf
  unless ← isDefEq ty (← g.getType) do
    throwError "taint summaries: {ty} does not match the goal {← g.getType}"
  g.assign pf
  let m₁ :: m₂ :: ms := mvs.toList | throwError "taint summaries: unexpected {p}"
  setGoals [m₁.mvarId!]
  evalTactic (← `(tactic| lit_decide))
  setGoals [m₂.mvarId!]
  fillRfl
  -- `keepsSum` (nothing to check for `bot`), and that the frame or the
  -- taint on entry satisfies the domain's invariant (`le τ τ`).
  for m in ms do
    setGoals [m.mvarId!]
    let ty ← instantiateMVars (← m.mvarId!.getType)
    match ty.find? (·.isAppOfArity ``Taint.keepsSum 7) with
    | some k =>
      if (k.getArg! 4).isAppOf ``Taint.Frame.bot then
        evalTactic (← `(tactic| exact Taint.keepsSum_bot))
      else
        evalTactic (← `(tactic| lit_decide))
    | none => evalTactic (← `(tactic| decide +kernel))

end TaintSum

open Lean Meta Elab Tactic TaintSum in
/-- `taint_decide_sum [l₁, …]` proves `∃ h, (Taint.check A τ c h).isSome = true`
like `taint_decide`, but with the summaries `lᵢ : Taint.SumOk A (code, pre, post, F)`
(`taint_summary`) in place of the analysis of each call that one of them
applies to (the first call of the same name, or the first code equal to
the summary's, from at least `pre` public). It fails if a call of a
function that one of the summaries is of (by its name or its code) is
analysed in full nonetheless (`Taint.missedCalls`): the summary's `pre` does
not hold there, or it is stated about another name (e.g. the function was
renamed), which would otherwise only cost time, unnoticed. -/
elab "taint_decide_sum " "[" ls:ident,* "]" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (_, body) := ty.app2? ``Exists
    | throwError "taint_decide_sum: the goal is not `∃ h, (Taint.check A τ c h).isSome = true`"
  let .lam _ _ b _ := body
    | throwError "taint_decide_sum: the goal is not `∃ h, (Taint.check A τ c h).isSome = true`"
  let some chk := b.find? (·.isAppOfArity ``Taint.check 5)
    | throwError "taint_decide_sum: the goal is not `∃ h, (Taint.check A τ c h).isSome = true`"
  let args := chk.getAppArgs
  let (M, A, τ, c) := (args[0]!, args[1]!, args[2]!, args[3]!)
  let names ← ls.getElems.mapM fun l => realizeGlobalConstNoOverloadWithInfo l
  let (S, hS) ← summaries M A names
  let fr ← synthInstance (mkApp2 (mkConst ``Taint.Frame) M A)
  let (_, hint) ← hintChecked "taint_decide_sum" M A fr S τ c
  proveWith M A S hS c ``Taint.exists_check_of_checkSum #[τ] hint

open Lean Meta Elab Term Tactic TaintSum in
/-- The theorem `N : Taint.SumOk A (c, τ, post)` of `taint_summary`. -/
def TaintSum.summaryCmd (id : Ident) (a τ c : Term) (f : Option Term) (ls : Array Ident) :
    TermElabM Unit := do
  let A ← instantiateMVars (← elabTerm a none)
  let aTy ← whnf (← inferType A)
  unless aTy.isAppOfArity ``Taint 1 do throwError "taint_summary: {A} is not a `Taint`"
  let M := aTy.appArg!
  let T := mkApp2 (mkConst ``Taint.T) M A
  let τ ← elabTermEnsuringType τ T
  let c ← elabTermEnsuringType c (mkApp (mkConst ``Prog) M)
  let fr ← synthInstance (mkApp2 (mkConst ``Taint.Frame) M A)
  let F ← match f with
    | some f => elabTermEnsuringType f T
    | none => pure (mkApp3 (mkConst ``Taint.Frame.bot) M A fr)
  synthesizeSyntheticMVarsNoPostponing
  let τ ← instantiateMVars τ
  let c ← instantiateMVars c
  let F ← instantiateMVars F
  if τ.hasMVar || c.hasMVar || F.hasMVar then
    throwError "taint_summary: the taints and the code must be closed"
  let names ← ls.mapM fun l => realizeGlobalConstNoOverloadWithInfo l
  let (S, hS) ← summaries M A names
  -- The analysis, in compiled code, once: its result and its hint.
  let (post, hint) ← hintChecked "taint_summary" M A fr S τ c
  let s ← mkAppM ``Prod.mk #[c, ← mkAppM ``Prod.mk #[τ, ← mkAppM ``Prod.mk #[post, F]]]
  let ty := mkApp4 (mkConst ``Taint.SumOk) M A fr s
  let mv ← mkFreshExprSyntheticOpaqueMVar ty
  let gs ← Tactic.run mv.mvarId! (proveWith M A S hS c ``Taint.sumOk_of_checkSum #[τ, post, F] hint)
  unless gs.isEmpty do throwError "taint_summary: goals remain"
  let v ← instantiateMVars mv
  addDecl <| .thmDecl
    { name := (← getCurrNamespace) ++ id.getId, levelParams := [], type := ty, value := v }

/-- `taint_summary N : A τ code keeping F using l₁ …` proves the summary
`N : Taint.SumOk A (code, τ, post, F)`, with `post` what the analysis of
`code` from `τ` ends with, and `F` what `code` does not write (`Frame.keeps`,
by default nothing), by evaluation (`lit_decide`), with the summaries `lᵢ` in
place of the calls they apply to (as `taint_decide_sum`). -/
syntax "taint_summary " ident " : " term:max term:max term:max (" keeping " term:max)?
  (" using " ident+)? : command

open Lean Elab Command in
elab_rules : command
  | `(taint_summary $id : $a $τ $c $[keeping $f]? $[using $ls*]?) =>
    liftTermElabM (TaintSum.summaryCmd id a τ c f (ls.getD #[]))

end VG
