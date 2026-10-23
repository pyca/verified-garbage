module

public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline

/-!
# Frames of local variables (PPC64LE)

Untrusted: everything here is checked by Lean. A frame `.frame (.alloc n)
body (.free n)` runs its body from `allocated n s` (the back chain stored at
the new stack pointer, the frame's local variable space writable) and frees
it to `freed n s₂` (`WP.alloc`); its push leaks the new stack pointer, so
two runs from states with the same stack pointer leak the same trace if
their bodies do (`RelCT.alloc`). As on AArch64
(`Proof/Framework/AArch64/Call.lean`, `RelCT.lean`).
-/

@[expose] public section

namespace VG.PPC64LE

/-- The state after `addi r1, r1, n`, freeing the frame the body of a
frame ends in, `s₂`. -/
def freed (bytes : Nat) (s : State) : State :=
  { s with sp := s.sp + BitVec.ofNat 64 bytes, wr := s.wr.tail }

theorem push_alloc {bytes : Nat} {s : State} (hn : 32 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0)
    (hsp : bytes ≤ s.sp.toNat) : isa.push (.alloc bytes) s = some (allocated bytes s) := by
  show push (.alloc bytes) s = some (allocated bytes s)
  unfold push
  exact ite_eq_left_of_eq_true _ _ (eq_true ⟨hn.1, hn.2.1, hn.2.2, hsp⟩) |>.trans rfl

/-- A frame of `bytes` bytes: its body runs from `allocated bytes s`, and the
frame is freed to `freed bytes s₂`. -/
theorem WP.alloc {bytes : Nat} {body : Prog isa} {s : State} {Q : State → Prop}
    (hn : 32 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0) (hsp : bytes ≤ s.sp.toNat)
    (hb : WP isa body (allocated bytes s) fun s₂ => Q (freed bytes s₂)) :
    WP isa (.frame (.alloc bytes) body (.free bytes)) s Q := by
  obtain ⟨t, s₂, he, hq⟩ := hb
  obtain ⟨-, hw, hp⟩ := Exec.rdwr he
  have hf : isa.pop (.free bytes) (allocated bytes s) s₂ = some (freed bytes s₂) := by
    show pop (.free bytes) (allocated bytes s) s₂ = some (freed bytes s₂)
    unfold pop
    exact ite_eq_left_of_eq_true _ _ (eq_true ⟨hn.1, hn.2.1, hn.2.2, hp, hw, rfl⟩) |>.trans rfl
  exact ⟨_, _, Exec.frame (push_alloc hn hsp) he hf, hq⟩

/-- Allocating and freeing a frame leaks the stack pointer, which the two
runs agree on. -/
theorem RelCT.alloc {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hsp : ∀ s t, P s t → s.sp = t.sp)
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocated bytes s ∧ b = allocated bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocated bytes a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      refine ⟨?_, trivial⟩
      simp only [addrs, hsp s t hp]

end VG.PPC64LE
