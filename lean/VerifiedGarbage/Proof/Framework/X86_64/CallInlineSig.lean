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

/-! ## Contracts for callees that call -/

/-- `k`, with no buffer on the 8 bytes below `rsp`: what a caller of code
with calls (and so of its inlined form) must also give it. -/
def _root_.VG.Contract.clear (k : Contract isa) : Contract isa :=
  { k with pre := fun s => k.pre s ∧ Clear (hole (s.gpr .rsp)) s }

/-- Correctness of `c` from that of `c.inline`, for a postcondition that
does not read the 8 bytes below `rsp`. -/
theorem ok_of_inline {c : Prog isa} (hc : c.InlineOk = true) {k : Contract isa}
    (hcor : ∀ s, k.pre s → ∃ t s', Exec isa c.inline s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hpost : ∀ s b hv u, k.pre s → Clear (hole (s.gpr .rsp)) s → k.post s b →
      k.post s (b.patch (hole (s.gpr .rsp)) hv u)) :
    ∀ s, k.clear.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s' := by
  intro s ⟨hs, hcl⟩
  obtain ⟨t, b, he, ha, hp⟩ := hcor s hs
  obtain ⟨hv, u, ta, ha', _, _⟩ := Exec.of_inline hc he hcl
  exact ⟨ta, _, ha', abiPreserved_patch hv u ha, hpost s b hv u hs hcl hp⟩

/-- Constant time of `c` from that of `c.inline`, for a relation that fixes `rsp`. -/
theorem ct_of_inline {c : Prog isa} (hc : c.InlineOk = true) {k : Contract isa}
    (hrun : ∀ s, k.pre s → ∃ t s', Exec isa c.inline s t s')
    (hrsp : ∀ s₁ s₂, k.pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp)
    (hct : ConstantTime isa k.pre k.pub c.inline) : ConstantTime isa k.clear.pre k.pub c :=
  ConstantTime.of_inline hc (fun s h => hrun s h.1) (fun _ h => h.2) (fun _ _ _ _ h => hrsp _ _ h)
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => hct s₁ s₂ t₁ t₂ s₁' s₂' h₁.1 h₂.1 hp e₁ e₂

end VG.X86_64
