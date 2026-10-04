import VerifiedGarbage.Proof.Framework.X86_64.Spectre
import VerifiedGarbage.Proof.Framework.SpectreSeq
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Verified

/-! # Speculative constant time of the x86-64 X25519 artifacts

Each `_sct` theorem is proved by the same taint check as the artifact's
`ConstantTime` (repeated here as `_ct`, to compare the kernel's time),
through `Taint.specConstantTime`. -/

namespace VG.Proof.SpectreDemo

open VG VG.X86_64 VG.X86_64.Spectre

/-- The existing (sequential) check, for comparison. -/
theorem x25519_ct : ConstantTime isa Proof.X25519.x25519X86_64.pre Proof.X25519.x25519X86_64.pub Impl.X25519.X86_64.x25519 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
  · intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem x25519_sct : SpecConstantTime spectre Proof.X25519.x25519X86_64.pre Proof.X25519.x25519X86_64.pub Impl.X25519.X86_64.x25519 := by
  refine Taint.specConstantTime specSound (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
  · intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- The existing (sequential) check, for comparison. -/
theorem x25519Adx_ct : ConstantTime isa Proof.X25519.x25519X86_64.pre Proof.X25519.x25519X86_64.pub Impl.X25519.X86_64.x25519Adx := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
  · intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem x25519Adx_sct : SpecConstantTime spectre Proof.X25519.x25519X86_64.pre Proof.X25519.x25519X86_64.pub Impl.X25519.X86_64.x25519Adx := by
  refine Taint.specConstantTime specSound (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
  · intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- The existing (sequential) check, for comparison. -/
theorem x25519Ifma_ct : ConstantTime isa Proof.X25519.x25519X86_64.pre Proof.X25519.x25519X86_64.pub Impl.X25519.X86_64.x25519Ifma := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
  · intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem x25519Ifma_sct : SpecConstantTime spectre Proof.X25519.x25519X86_64.pre Proof.X25519.x25519X86_64.pub Impl.X25519.X86_64.x25519Ifma := by
  refine Taint.specConstantTime specSound (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
  · intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- The artifact's sequential constant time, recovered from its speculative
constant time (`SpecConstantTime.constantTime`). -/
theorem x25519_ct_of_sct : ConstantTime isa Proof.X25519.x25519X86_64.pre
    Proof.X25519.x25519X86_64.pub Impl.X25519.X86_64.x25519 :=
  SpecConstantTime.constantTime spectre x25519_sct

end VG.Proof.SpectreDemo
