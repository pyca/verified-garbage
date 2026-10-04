import VerifiedGarbage.Proof.Framework.X86_64.Spectre
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Compress

/-! # Speculative constant time of the x86-64 SHA-256 artifacts

Each `_sct` theorem is proved by the same taint check as the artifact's
`ConstantTime` (repeated here as `_ct`, to compare the kernel's time),
through `Taint.specConstantTime`. -/

namespace VG.Proof.SpectreDemo

open VG VG.X86_64 VG.X86_64.Spectre

/-- The existing (sequential) check, for comparison. -/
theorem sha256Compress_ct : ConstantTime isa Proof.Sha256.compressX86_64.pre Proof.Sha256.compressX86_64.pub Impl.Sha256.X86_64.compress := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
  · intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem sha256Compress_sct : SpecConstantTime spectre Proof.Sha256.compressX86_64.pre Proof.Sha256.compressX86_64.pub Impl.Sha256.X86_64.compress := by
  refine Taint.specConstantTime specSound (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
  · intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- The existing (sequential) check, for comparison. -/
theorem sha256CompressShaNi_ct : ConstantTime isa Proof.Sha256.compressX86_64.pre Proof.Sha256.compressX86_64.pub Impl.Sha256.X86_64.ShaNi.compress := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
  · intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem sha256CompressShaNi_sct : SpecConstantTime spectre Proof.Sha256.compressX86_64.pre Proof.Sha256.compressX86_64.pub Impl.Sha256.X86_64.ShaNi.compress := by
  refine Taint.specConstantTime specSound (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
  · intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- The existing (sequential) check, for comparison. -/
theorem sha256CompressAvx2_ct : ConstantTime isa Proof.Sha256.compressX86_64.pre Proof.Sha256.compressX86_64.pub Impl.Sha256.X86_64.Avx2.compress := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
  · intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem sha256CompressAvx2_sct : SpecConstantTime spectre Proof.Sha256.compressX86_64.pre Proof.Sha256.compressX86_64.pub Impl.Sha256.X86_64.Avx2.compress := by
  refine Taint.specConstantTime specSound (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
  · intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.SpectreDemo
