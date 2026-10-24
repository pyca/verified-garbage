module

public import VerifiedGarbage.Proof.Framework.Scratch

/-!
# SM4-GCM on PPC64LE: two working spaces

Untrusted: everything here is checked by Lean. The functions keep AES-GCM's
working space and SM4's each in a frame of their own (a frame is less than
a page, too small for both): around the code, proved with both as its last
two arguments, a frame allocates SM4's, and around that frame another
allocates AES-GCM's. Each frame needs the contract of the code inside it to
read the memory on entry only within the function's buffers; the inner
frame's contract has AES-GCM's working space as one more argument, which
it ignores (`Curry.withScratch`), and stays local (`local_withScratch`,
`leakLocal_withScratch`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG

/-- A function of the arguments and the memory on entry that reads the
memory only within the buffers does so too taking one more array argument,
last, which it ignores. -/
theorem local_withScratch {α : Type} {pb : Nat} {sig : Sig} (nm : String) (e : Elem) (n : Nat)
    {f : Curry (sig.words pb) (Mem → α)} {R : α → α → Prop}
    (h : ∀ vs m₁ m₂, vs.length = (sig.words pb).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      R (Curry.apply (sig.words pb) f vs m₁) (Curry.apply (sig.words pb) f vs m₂)) :
    ∀ vs m₁ m₂, vs.length = ((sig.withScratch nm e n).words pb).length →
      (∀ b ∈ Sig.bufs (sig.withScratch nm e n).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      R (Curry.apply _ (Curry.withScratch pb nm e n sig.params f) vs m₁)
        (Curry.apply _ (Curry.withScratch pb nm e n sig.params f) vs m₂) := by
  intro vs m₁ m₂ hl hb
  rw [Sig.words_withScratch, List.length_append, List.length_singleton] at hl
  obtain ⟨vs', x, rfl⟩ : ∃ vs' x, vs = vs' ++ [x] := by
    rcases List.eq_nil_or_concat vs with h0 | ⟨L, b, rfl⟩
    · subst h0; simp at hl
    · exact ⟨L, b, List.concat_eq_append ..⟩
  have hl' : vs'.length = (sig.words pb).length := by
    rw [List.length_append, List.length_singleton] at hl; omega
  show R (Curry.apply _ (Curry.withScratch pb nm e n sig.params f) (vs' ++ [x]) m₁)
    (Curry.apply _ (Curry.withScratch pb nm e n sig.params f) (vs' ++ [x]) m₂)
  rw [Curry.apply_withScratch pb nm e n sig.params f vs' x hl']
  refine h vs' m₁ m₂ hl' fun b hb' => hb b ?_
  show b ∈ Sig.bufs (sig.params ++ [((nm, .array true e n) : String × Param)]) (vs' ++ [x])
  rw [Sig.bufs_append_array pb nm e n x sig.params vs' hl']
  exact List.mem_append_left _ hb'

/-- `local_withScratch`, for a precondition. -/
theorem pre_withScratch {pb : Nat} {sig : Sig} (nm : String) (e : Elem) (n : Nat)
    {pre : Curry (sig.words pb) (Mem → Prop)}
    (h : ∀ vs m₁ m₂, vs.length = (sig.words pb).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words pb) pre vs m₁ → Curry.apply (sig.words pb) pre vs m₂) :
    ∀ vs m₁ m₂, vs.length = ((sig.withScratch nm e n).words pb).length →
      (∀ b ∈ Sig.bufs (sig.withScratch nm e n).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply _ (Curry.withScratch pb nm e n sig.params pre) vs m₁ →
        Curry.apply _ (Curry.withScratch pb nm e n sig.params pre) vs m₂ :=
  local_withScratch nm e n (R := fun P Q => P → Q) h

/-- `local_withScratch`, for a postcondition. -/
theorem post_withScratch {pb : Nat} {sig : Sig} (nm : String) (e : Elem) (n : Nat) {post : sig.Post pb}
    (h : ∀ vs m₁ m₂ m' r, vs.length = (sig.words pb).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words pb) post vs m₁ m' r → Curry.apply (sig.words pb) post vs m₂ m' r) :
    ∀ vs m₁ m₂ m' r, vs.length = ((sig.withScratch nm e n).words pb).length →
      (∀ b ∈ Sig.bufs (sig.withScratch nm e n).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply _ (Curry.withScratch pb nm e n sig.params post) vs m₁ m' r →
        Curry.apply _ (Curry.withScratch pb nm e n sig.params post) vs m₂ m' r :=
  fun vs m₁ m₂ m' r hl hb => local_withScratch nm e n
    (R := fun (P Q : Mem → BitVec (sig.retBits pb) → Prop) => ∀ m' r, P m' r → Q m' r)
    (fun vs m₁ m₂ hl hb m' r => h vs m₁ m₂ m' r hl hb) vs m₁ m₂ hl hb m' r

/-- A leak local within the buffers stays local taking one more array argument. -/
theorem leakLocal_withScratch {pb : Nat} {sig : Sig} (nm : String) (e : Elem) (n : Nat)
    {leak : Option (Curry (sig.words pb) (Mem → List Nat))} (h : Sig.LeakLocal pb sig leak) :
    Sig.LeakLocal pb (sig.withScratch nm e n) (leak.map (Curry.withScratch pb nm e n sig.params)) := by
  cases leak with
  | none => trivial
  | some f => exact local_withScratch nm e n (R := Eq) h

end VG.Proof.Sm4Gcm.PPC64LE
