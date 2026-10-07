import VerifiedGarbage.Proof.Framework.X86_64.CallInline

/-!
# Calls as inlined code: contracts that keep buffers off the return address

A contract built by `Sig.contract` with `stack` at least 8 keeps every
buffer and argument area away from the 8 bytes below `rsp`, where a call
stores its return address (`Sig.clear_of_pre`), as `Verified.of_inline`
requires.
-/

namespace VG.X86_64

theorem Sig.clear_of_pre {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
    {wa : Bool} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s : State}
    (h : (sig.contract abi pre post wa 8 leak).pre s) : Clear (hole (s.gpr .rsp)) s := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · obtain ⟨_, hrd, hwr, _, hres, _⟩ := h
    intro r hr
    have hh : (hole (s.gpr .rsp)) ∈ abi.reserved 8 s := by
      simp [abi, stackBelow, hole]
    rcases List.mem_append.mp hr with hr | hr
    · rw [show s.rd = abi.rd s from rfl, hrd] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact (hres _ hh a (List.mem_filter.mp ha).1).symm
    · rw [show s.wr = abi.wr s from rfl, hwr] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact (hres _ hh a (List.mem_filter.mp ha).1).symm

theorem Sig.rsp_of_pub {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
    {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s₁ s₂ : State}
    (h : (sig.contract abi pre post wa stack leak).pub s₁ s₂) : s₁.gpr .rsp = s₂.gpr .rsp := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · cases leak with
    | none => exact h.1
    | some f => exact h.1.1

end VG.X86_64
