module

public import VerifiedGarbage.Impl.Scrub.CodeOnce

/-!
# Following the code of each function once

A check that follows structured code (`Code.all`; on x86-64, `UpperLock.up`,
`Mx.mx`, `mxClass`) goes through the code of a function once per call of it,
through every function that calls it: on code whose calls nest, most of what
it does it has done before, and the emitter, which evaluates these checks
for every function it scrubs, spent most of its time there.

`Code.memoCall` (`Impl/Scrub/CodeOnce.lean`, with the other definitions)
runs such a check on the code of a call unless that code is the code of the
last call of the same function, with the same key, whose answer it then
gives. A check written with it gives what the check itself gives
(`Code.memoCall_ok`): `Code.allOnce` is `Code.all` (`Code.allOnce_eq`).
-/

@[expose] public section

namespace VG

variable {I C : Type} [DecidableEq I] [DecidableEq C]

theorem Code.eq_of_same {a b : Code I C} (h : Code.same a b = true) : a = b :=
  @of_decide_eq_true _ (withPtrEqDecEq a b fun _ => Code.dec a b) h

section Memo

variable {β κ : Type} [DecidableEq κ]

/-- `Code.memoCall` gives `spec`'s value, and calls with `spec`'s values, if
`run` does and the calls it is given have them. -/
theorem Code.memoCall_ok {spec : Code I C → κ → β} {n : String} {b : Code I C} {key : κ}
    {k : List (String × Code I C × κ × β)} {run : Unit → β × List (String × Code I C × κ × β)}
    (hk : ∀ e ∈ k, e.2.2.2 = spec e.2.1 e.2.2.1)
    (hr : (run ()).1 = spec b key ∧ ∀ e ∈ (run ()).2, e.2.2.2 = spec e.2.1 e.2.2.1) :
    (Code.memoCall n b key k run).1 = spec b key ∧
      ∀ e ∈ (Code.memoCall n b key k run).2, e.2.2.2 = spec e.2.1 e.2.2.1 := by
  have hn : ∀ e ∈ (n, b, key, (run ()).1) :: (run ()).2, e.2.2.2 = spec e.2.1 e.2.2.1 := fun e he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact hr.1
    · exact hr.2 e he
  unfold Code.memoCall
  split
  · rename_i e he
    have hp := List.find?_some he
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    split
    · rename_i hs
      exact ⟨by rw [hk e (List.mem_of_find?_eq_some he), hp.2, ← Code.eq_of_same hs], hk⟩
    · exact ⟨hr.1, hn⟩
  · exact ⟨hr.1, hn⟩

end Memo

theorem Code.allFrom_ok (p : I → Bool) : ∀ (c : Code I C) (k : List (String × Code I C × Unit × Bool)),
    (∀ e ∈ k, e.2.2.2 = e.2.1.all p) →
      (allFrom p c k).1 = c.all p ∧ ∀ e ∈ (allFrom p c k).2, e.2.2.2 = e.2.1.all p
  | .block is, k, hk => ⟨rfl, hk⟩
  | .seq a b, k, hk => by
    obtain ⟨ha, ka⟩ := allFrom_ok p a k hk
    simp only [allFrom, Code.all]
    split
    · rename_i h
      obtain ⟨hb, kb⟩ := allFrom_ok p b _ ka
      exact ⟨by rw [hb, ← ha, h, Bool.true_and], kb⟩
    · rename_i h
      exact ⟨by rw [← ha, Bool.not_eq_true _ |>.mp h, Bool.false_and], ka⟩
  | .ite _ t e, k, hk => by
    obtain ⟨ha, ka⟩ := allFrom_ok p t k hk
    simp only [allFrom, Code.all]
    split
    · rename_i h
      obtain ⟨hb, kb⟩ := allFrom_ok p e _ ka
      exact ⟨by rw [hb, ← ha, h, Bool.true_and], kb⟩
    · rename_i h
      exact ⟨by rw [← ha, Bool.not_eq_true _ |>.mp h, Bool.false_and], ka⟩
  | .loop b _, k, hk => allFrom_ok p b k hk
  | .call n b, k, hk =>
    Code.memoCall_ok (n := n) (run := fun _ => allFrom p b k) (spec := fun c _ => c.all p) hk (allFrom_ok p b k hk)
  | .frame i b j, k, hk => by
    obtain ⟨hb, kb⟩ := allFrom_ok p b k hk
    simp only [allFrom, Code.all]
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      exact ⟨by rw [hb, h.1, h.2, Bool.true_and, Bool.and_true], kb⟩
    · rename_i h
      refine ⟨?_, hk⟩
      cases hi : p i <;> cases hj : p j <;> simp_all
  | .icall i n b nx, k, hk => by
    obtain ⟨hb, kb⟩ := Code.memoCall_ok (n := n) (run := fun _ => allFrom p b k) (spec := fun c _ => c.all p) hk
      (allFrom_ok p b k hk)
    simp only [allFrom, Code.all]
    split
    · rename_i hi
      split
      · rename_i h
        obtain ⟨hn, kn⟩ := allFrom_ok p nx _ kb
        exact ⟨by rw [hn, ← hb, hi, h, Bool.true_and, Bool.true_and], kn⟩
      · rename_i h
        exact ⟨by rw [← hb, Bool.not_eq_true _ |>.mp h, Bool.and_false, Bool.false_and], kb⟩
    · rename_i hi
      exact ⟨by rw [Bool.not_eq_true _ |>.mp hi, Bool.false_and, Bool.false_and], hk⟩

theorem Code.allOnce_eq (p : I → Bool) (c : Code I C) : c.allOnce p = c.all p :=
  (Code.allFrom_ok p c [] fun _ h => by cases h).1

end VG
