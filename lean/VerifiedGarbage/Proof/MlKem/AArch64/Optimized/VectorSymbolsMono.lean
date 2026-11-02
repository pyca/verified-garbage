module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbols
public import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbols
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintMono

/-!
# The analysis with public table addresses is monotone, and at least the vector analysis

`VectorSymbols.analysis names` is `VectorTaint.taint` but at an `adrSym` of a
listed symbol, which it makes public. It is monotone, with the meet as frames
(`Taint.LeFrame`), so its checks can use summaries of called functions
(`taint_decide_generic`). From any taint, its check of any code succeeds
wherever the vector analysis's does, with at least as much public
(`check_dom`), so every summary of the vector analysis is one of it
(`allOk_of_vector`): e.g. the summaries of a Keccak backend's permutation.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Optimized.VectorSymbols

open VG VG.AArch64 VG.AArch64.VectorTaint
open VG.Taint (LeFrame)

theorem step_mono (names : List String) {τ σ τ' : T} (i : Instr) (h : taint.le τ σ = true)
    (hs : step names τ i = some τ') : ∃ σ', step names σ i = some σ' ∧ taint.le τ' σ' = true := by
  cases hi : i.sym with
  | none =>
    simp only [step, hi] at hs ⊢
    exact VectorTaint.step_mono i h hs
  | some p =>
    obtain ⟨d, n⟩ := p
    simp only [step, hi] at hs ⊢
    by_cases hn : n ∈ names
    · simp only [hn, ↓reduceIte, Option.some.injEq] at hs ⊢
      subst hs
      exact ⟨_, rfl, le_iff.mpr ⟨Taint.set_mono (le_iff.mp h).1 d id, (le_iff.mp h).2⟩⟩
    · simp only [hn, ↓reduceIte] at hs ⊢
      exact VectorTaint.step_mono i h hs

theorem step_keeps (names : List String) {F Φ σ σ' : T} (i : Instr) (hk : keeps F i = true)
    (hΦF : taint.le Φ F = true) (hΦ : taint.le Φ σ = true) (hs : step names σ i = some σ') :
    taint.le Φ σ' = true := by
  cases hi : i.sym with
  | none =>
    simp only [step, hi] at hs
    exact VectorTaint.step_keeps i hk hΦF hΦ hs
  | some p =>
    obtain ⟨d, n⟩ := p
    simp only [step, hi] at hs
    by_cases hn : n ∈ names
    · simp only [hn, ↓reduceIte, Option.some.injEq] at hs
      subst hs
      obtain rfl := Instr.sym_eq hi
      have hg := keeps_gpr hk
      simp only [Taint.keepsI, Taint.gprDst, Bool.not_eq_true'] at hg
      exact le_iff.mpr ⟨Taint.set_keeps (le_iff.mp hΦF).1 (le_iff.mp hΦ).1 hg true, (le_iff.mp hΦ).2⟩
    · simp only [hn, ↓reduceIte] at hs
      exact VectorTaint.step_keeps i hk hΦF hΦ hs

/-- From the same taint, a step of the analysis keeps public at least what
the vector analysis's does. -/
theorem step_dom (names : List String) {τ τ' : T} (i : Instr) (hs : VectorTaint.step τ i = some τ') :
    ∃ σ', step names τ i = some σ' ∧ taint.le τ' σ' = true := by
  cases hi : i.sym with
  | none => exact ⟨τ', by simp only [step, hi]; exact hs, le_refl _⟩
  | some p =>
    obtain ⟨d, n⟩ := p
    obtain rfl := Instr.sym_eq hi
    by_cases hn : n ∈ names
    · have hs' : some (Taint.set τ.1 d false, τ.2) = some τ' := hs
      cases hs'
      refine ⟨(Taint.set τ.1 d true, τ.2), by simp only [step, Instr.sym, hn, ↓reduceIte], ?_⟩
      exact le_iff.mpr ⟨Taint.set_mono (RegSet.subset_refl _) d (fun h => absurd h Bool.false_ne_true),
        RegSet.subset_refl _⟩
    · exact ⟨τ', by simp only [step, Instr.sym, hn, ↓reduceIte]; exact hs, le_refl _⟩

/-- The analysis is monotone, with the meet as frames: as `VectorTaint.taint`. -/
instance (names : List String) : LeFrame (analysis names) where
  le_trans := LeFrame.le_trans (A := VectorTaint.taint)
  le_right := LeFrame.le_right (A := VectorTaint.taint)
  step i h hs := step_mono names i h hs
  condPub := LeFrame.condPub (A := VectorTaint.taint)
  meet := LeFrame.meet (A := VectorTaint.taint)
  call := LeFrame.call (A := VectorTaint.taint)
  ret := LeFrame.ret (A := VectorTaint.taint)
  push := LeFrame.push (A := VectorTaint.taint)
  pop := LeFrame.pop (A := VectorTaint.taint)
  join := LeFrame.join (A := VectorTaint.taint)
  bot := LeFrame.bot (A := VectorTaint.taint)
  frameOf := LeFrame.frameOf (A := VectorTaint.taint)
  join_lub := LeFrame.join_lub (A := VectorTaint.taint)
  frame_le_left := LeFrame.frame_le_left (A := VectorTaint.taint)
  frame_le_right := LeFrame.frame_le_right (A := VectorTaint.taint)
  frame_mono := LeFrame.frame_mono (A := VectorTaint.taint)
  le_frame := LeFrame.le_frame (A := VectorTaint.taint)
  le_meet := LeFrame.le_meet (A := VectorTaint.taint)
  bot_le := LeFrame.bot_le (A := VectorTaint.taint)
  bot_valid := LeFrame.bot_valid (A := VectorTaint.taint)
  keeps := keeps
  keepsCall := keepsCall
  keeps_bot := LeFrame.keeps_bot (A := VectorTaint.taint)
  keepsCall_bot := LeFrame.keepsCall_bot (A := VectorTaint.taint)
  step_keeps i hk hΦF hΦ hs := step_keeps names i hk hΦF hΦ hs
  call_keeps := LeFrame.call_keeps (A := VectorTaint.taint)
  ret_keeps := LeFrame.ret_keeps (A := VectorTaint.taint)
  push_keeps := LeFrame.push_keeps (A := VectorTaint.taint)
  pop_keeps := LeFrame.pop_keeps (A := VectorTaint.taint)

theorem checkBlock_dom (names : List String) {is : List Instr} {τ σ τ' : T}
    (h : VectorTaint.taint.checkBlock τ is = some τ') (hle : taint.le τ σ = true) :
    ∃ σ', (analysis names).checkBlock σ is = some σ' ∧ taint.le τ' σ' = true := by
  induction is generalizing τ σ with
  | nil =>
    change some τ = some τ' at h
    cases h; exact ⟨σ, rfl, hle⟩
  | cons i is ih =>
    change (VectorTaint.taint.step τ i).bind (VectorTaint.taint.checkBlock · is) = some τ' at h
    obtain ⟨τ₁, hs, hr⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨σ₀, hs₀, hle₀⟩ := VectorTaint.step_mono i hle hs
    obtain ⟨σ₁, hs₁, hle₁⟩ := step_dom names i hs₀
    obtain ⟨σ', h', hle'⟩ := ih hr (LeFrame.le_trans (A := VectorTaint.taint) hle₀ hle₁)
    refine ⟨σ', ?_, hle'⟩
    change ((analysis names).step σ i).bind ((analysis names).checkBlock · is) = some σ'
    exact Option.bind_eq_some_iff.mpr ⟨σ₁, hs₁, h'⟩

theorem checkChunks_dom (names : List String) {chunkSize : Nat} {ms : List T} {is : List Instr}
    {τ σ τ' : T} (h : VectorTaint.taint.checkChunks chunkSize τ is ms = some τ')
    (hle : taint.le τ σ = true) :
    ∃ σ', (analysis names).checkChunks chunkSize σ is ms = some σ' ∧ taint.le τ' σ' = true := by
  induction ms generalizing τ σ is with
  | nil => exact checkBlock_dom names h hle
  | cons m ms ih =>
    change (VectorTaint.taint.checkBlock τ (KList.take chunkSize is)).bind (fun τ' =>
      if VectorTaint.taint.le m τ' then VectorTaint.taint.checkChunks chunkSize m (KList.drop chunkSize is) ms
      else none) = some τ' at h
    obtain ⟨τ₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    split at h₂ <;> [rename_i hm; cases h₂]
    obtain ⟨σ₁, h₁', hle₁⟩ := checkBlock_dom names h₁ hle
    have hm' : taint.le m σ₁ = true := LeFrame.le_trans (A := VectorTaint.taint) hm hle₁
    obtain ⟨σ', h', hle'⟩ := ih h₂ (le_refl m)
    refine ⟨σ', ?_, hle'⟩
    change ((analysis names).checkBlock σ (KList.take chunkSize is)).bind (fun τ' =>
      if (analysis names).le m τ' then (analysis names).checkChunks chunkSize m (KList.drop chunkSize is) ms
      else none) = some σ'
    refine Option.bind_eq_some_iff.mpr ⟨σ₁, h₁', ?_⟩
    simp only [show (analysis names).le m σ₁ = true from hm', ↓reduceIte]; exact h'

/-- Wherever the vector analysis of code succeeds, this one does, from a taint
with more public, with more public at the end. -/
theorem check_dom (names : List String) {c : Prog isa} {h : VG.Taint.Hint T} {τ σ τ' : T}
    (hc : VectorTaint.taint.check τ c h = some τ') (hle : taint.le τ σ = true) :
    ∃ σ', (analysis names).check σ c h = some σ' ∧ taint.le τ' σ' = true := by
  have tr := fun {a b c : T} => LeFrame.le_trans (A := VectorTaint.taint) (a := a) (b := b) (c := c)
  induction c generalizing τ σ τ' h with
  | icall => cases h <;> simp only [VG.Taint.check, reduceCtorEq] at hc
  | block is =>
    cases h <;> try (simp only [VG.Taint.check, reduceCtorEq] at hc; done)
    exact checkChunks_dom names hc hle
  | seq a b iha ihb =>
    cases h <;> try (simp only [VG.Taint.check, reduceCtorEq] at hc; done)
    rename_i mid h₁ h₂
    change (VectorTaint.taint.check τ a h₁).bind (fun τ' =>
      if VectorTaint.taint.le mid τ' then VectorTaint.taint.check mid b h₂ else none) = some τ' at hc
    obtain ⟨τ₁, h₁', h₂'⟩ := Option.bind_eq_some_iff.mp hc
    split at h₂' <;> [rename_i hm; cases h₂']
    obtain ⟨σ₁, ha, hle₁⟩ := iha h₁' hle
    obtain ⟨σ', hb, hle'⟩ := ihb h₂' (le_refl mid)
    refine ⟨σ', ?_, hle'⟩
    change ((analysis names).check σ a h₁).bind (fun τ' =>
      if (analysis names).le mid τ' then (analysis names).check mid b h₂ else none) = some σ'
    refine Option.bind_eq_some_iff.mpr ⟨σ₁, ha, ?_⟩
    simp only [show (analysis names).le mid σ₁ = true from tr hm hle₁, ↓reduceIte]; exact hb
  | ite cd t e iht ihe =>
    cases h <;> try (simp only [VG.Taint.check, reduceCtorEq] at hc; done)
    rename_i h₁ h₂
    change (if VectorTaint.taint.condPub τ cd then
      (VectorTaint.taint.check τ t h₁).bind fun τ₁ =>
        (VectorTaint.taint.check τ e h₂).map fun τ₂ => VectorTaint.taint.meet τ₁ τ₂
      else none) = some τ' at hc
    split at hc <;> [rename_i hp; cases hc]
    obtain ⟨τ₁, ht, hm⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨τ₂, he, rfl⟩ := Option.map_eq_some_iff.mp hm
    obtain ⟨σ₁, ht', hle₁⟩ := iht ht hle
    obtain ⟨σ₂, he', hle₂⟩ := ihe he hle
    refine ⟨taint.meet σ₁ σ₂, ?_, LeFrame.meet (A := VectorTaint.taint) hle₁ hle₂⟩
    have hp' : (analysis names).condPub σ cd = true := LeFrame.condPub (A := VectorTaint.taint) cd hle hp
    change (if (analysis names).condPub σ cd then
      ((analysis names).check σ t h₁).bind fun τ₁ =>
        ((analysis names).check σ e h₂).map fun τ₂ => (analysis names).meet τ₁ τ₂
      else none) = some (taint.meet σ₁ σ₂)
    rw [ite_eq_left hp', ht', Option.bind_some, he', Option.map_some]
    rfl
  | loop body cd ih =>
    cases h <;> try (simp only [VG.Taint.check, reduceCtorEq] at hc; done)
    rename_i inv hb
    change (if VectorTaint.taint.le inv τ then
      (VectorTaint.taint.check inv body hb).bind fun σ' =>
        if VectorTaint.taint.le inv σ' && VectorTaint.taint.condPub σ' cd then some σ' else none
      else none) = some τ' at hc
    split at hc <;> [rename_i hi; cases hc]
    obtain ⟨σ₀, hb', hk⟩ := Option.bind_eq_some_iff.mp hc
    split at hk <;> [rename_i hok; cases hk]
    cases hk
    simp only [Bool.and_eq_true] at hok
    obtain ⟨σ₁, hb'', hle₁⟩ := ih hb' (le_refl inv)
    refine ⟨σ₁, ?_, hle₁⟩
    have hi' : (analysis names).le inv σ = true := tr hi hle
    have hok' : ((analysis names).le inv σ₁ && (analysis names).condPub σ₁ cd) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨tr hok.1 hle₁, LeFrame.condPub (A := VectorTaint.taint) cd hle₁ hok.2⟩
    change (if (analysis names).le inv σ then
      ((analysis names).check inv body hb).bind fun σ' =>
        if (analysis names).le inv σ' && (analysis names).condPub σ' cd then some σ' else none
      else none) = some σ₁
    rw [ite_eq_left hi', hb'', Option.bind_some, ite_eq_left hok']
  | call n body ih =>
    cases h <;> try (simp only [VG.Taint.check, reduceCtorEq] at hc; done)
    rename_i hb
    change (VectorTaint.taint.call τ).bind (fun τ₁ =>
      (VectorTaint.taint.check τ₁ body hb).bind VectorTaint.taint.ret) = some τ' at hc
    obtain ⟨τ₁, hcall, hr⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨τ₂, hb', hret⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨σ₁, hcall', hle₁⟩ := LeFrame.call (A := VectorTaint.taint) hle hcall
    obtain ⟨σ₂, hb'', hle₂⟩ := ih hb' hle₁
    obtain ⟨σ', hret', hle'⟩ := LeFrame.ret (A := VectorTaint.taint) hle₂ hret
    refine ⟨σ', ?_, hle'⟩
    change ((analysis names).call σ).bind (fun τ₁ =>
      ((analysis names).check τ₁ body hb).bind (analysis names).ret) = some σ'
    exact Option.bind_eq_some_iff.mpr ⟨σ₁, hcall', Option.bind_eq_some_iff.mpr ⟨σ₂, hb'', hret'⟩⟩
  | frame i body j ih =>
    cases h <;> try (simp only [VG.Taint.check, reduceCtorEq] at hc; done)
    rename_i hb
    change (VectorTaint.taint.push τ i).bind (fun τ₁ =>
      (VectorTaint.taint.check τ₁ body hb).bind fun τ₂ => VectorTaint.taint.pop τ₂ j) = some τ' at hc
    obtain ⟨τ₁, hpush, hr⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨τ₂, hb', hpop⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨σ₁, hpush', hle₁⟩ := LeFrame.push (A := VectorTaint.taint) i hle hpush
    obtain ⟨σ₂, hb'', hle₂⟩ := ih hb' hle₁
    obtain ⟨σ', hpop', hle'⟩ := LeFrame.pop (A := VectorTaint.taint) j hle₂ hpop
    refine ⟨σ', ?_, hle'⟩
    change ((analysis names).push σ i).bind (fun τ₁ =>
      ((analysis names).check τ₁ body hb).bind fun τ₂ => (analysis names).pop τ₂ j) = some σ'
    exact Option.bind_eq_some_iff.mpr ⟨σ₁, hpush', Option.bind_eq_some_iff.mpr ⟨σ₂, hb'', hpop'⟩⟩

/-- A summary of the vector analysis is one of this analysis. -/
theorem sumOk_of_vector (names : List String) {s : VG.Taint.Summary isa T}
    (h : VG.Taint.SumOk VectorTaint.taint s) : VG.Taint.SumOk (analysis names) s := fun τ hτ => by
  obtain ⟨g, τ', hg, hpost, hfr⟩ := h τ hτ
  obtain ⟨σ', hg', hle⟩ := check_dom names hg (le_refl τ)
  exact ⟨g, σ', hg', LeFrame.le_trans (A := VectorTaint.taint) hpost hle,
    LeFrame.le_trans (A := VectorTaint.taint) hfr hle⟩

/-- Summaries of the vector analysis are ones of this analysis. -/
theorem allOk_of_vector (names : List String) {S : List (VG.Taint.Summary isa T)}
    (h : VG.Taint.AllOk VectorTaint.taint S) : VG.Taint.AllOk (analysis names) S := by
  induction S with
  | nil => trivial
  | cons s S ih => exact ⟨sumOk_of_vector names h.1, ih h.2⟩

end VG.Proof.MlKem.AArch64.Optimized.VectorSymbols
