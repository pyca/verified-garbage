module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub

/-!
# Postconditions local under the precondition (64-bit RISC-V)

`postOut_of_local_pre`: `RISCV64.Scrub.postOut_of_local` for a
postcondition that reads the memory on return only within the buffers when
the precondition holds (as a key's length bounds the key context it
states), as `Proof.Aes.X86_64.Scrub.postOut_of_local_pre` on x86-64.
-/

@[expose] public section

namespace VG.RISCV64.Scrub

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers when the precondition holds. -/
theorem postOut_of_local_pre {sig : Sig}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      Curry.apply (sig.words abi.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract abi pre post wa stack leak) (sig.retBits abi.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -, -, -, hpre⟩ := hs
    rw [ScrubAbi.plain.ret, ScrubAbi.plain.mem, ScrubAbi.plain.mem] at hp ⊢
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [ScrubAbi.plain.argsLen _ _ hargs s, List.length_map])
      (by rw [← ScrubAbi.plain.mem s]; exact hpre.1) (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply ScrubAbi.plain.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← ScrubAbi.plain.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

end VG.RISCV64.Scrub
