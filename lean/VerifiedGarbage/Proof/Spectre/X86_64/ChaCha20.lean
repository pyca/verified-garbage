import VerifiedGarbage.Proof.Framework.X86_64.Spectre
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor

/-! # Speculative constant time of the x86-64 ChaCha20 artifacts

Each `_sct` theorem is proved by the same taint check as the artifact's
`ConstantTime` (repeated here as `_ct`, to compare the kernel's time),
through `Taint.specConstantTime`. -/

namespace VG.Proof.SpectreDemo

open VG VG.X86_64 VG.X86_64.Spectre

/-- The existing (sequential) check, for comparison. -/
theorem chachaBlock_ct : ConstantTime isa Proof.ChaCha20.blockX86_64.pre Proof.ChaCha20.blockX86_64.pub Impl.ChaCha20.X86_64.block := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi]) ?_ (by taint_decide)
  · intro s₁ s₂ _ _ ⟨h1, h2⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption

theorem chachaBlock_sct : SpecConstantTime spectre Proof.ChaCha20.blockX86_64.pre Proof.ChaCha20.blockX86_64.pub Impl.ChaCha20.X86_64.block := by
  refine Taint.specConstantTime specSound (Taint.ofRegs [.rdi, .rsi]) ?_ (by taint_decide)
  · intro s₁ s₂ _ _ ⟨h1, h2⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption

theorem chachaXor_ct : ConstantTime isa Proof.ChaCha20.xorX86_64.pre Proof.ChaCha20.xorX86_64.pub Impl.ChaCha20.X86_64.Xor.xor :=
  VG.Taint.constantTime (A := taint) Proof.ChaCha20.X86_64.Xor.τ₀ (fun _ _ h₁ h₂ hp => Proof.ChaCha20.X86_64.Xor.agree₀ h₁ h₂ hp) (by taint_decide)

theorem chachaXor_sct : SpecConstantTime spectre Proof.ChaCha20.xorX86_64.pre Proof.ChaCha20.xorX86_64.pub Impl.ChaCha20.X86_64.Xor.xor :=
  Taint.specConstantTime specSound Proof.ChaCha20.X86_64.Xor.τ₀ (fun _ _ h₁ h₂ hp => Proof.ChaCha20.X86_64.Xor.agree₀ h₁ h₂ hp) (by taint_decide)

theorem chachaXorAvx2_ct : ConstantTime isa Proof.ChaCha20.X86_64.Avx2.xorAvx2X86_64.pre Proof.ChaCha20.X86_64.Avx2.xorAvx2X86_64.pub Impl.ChaCha20.X86_64.Avx2.xor :=
  VG.Taint.constantTime (A := taint) Proof.ChaCha20.X86_64.Avx2.τ₀ (fun _ _ h₁ h₂ hp => Proof.ChaCha20.X86_64.Avx2.agree₀ h₁ h₂ hp) (by taint_decide)

theorem chachaXorAvx2_sct : SpecConstantTime spectre Proof.ChaCha20.X86_64.Avx2.xorAvx2X86_64.pre Proof.ChaCha20.X86_64.Avx2.xorAvx2X86_64.pub Impl.ChaCha20.X86_64.Avx2.xor :=
  Taint.specConstantTime specSound Proof.ChaCha20.X86_64.Avx2.τ₀ (fun _ _ h₁ h₂ hp => Proof.ChaCha20.X86_64.Avx2.agree₀ h₁ h₂ hp) (by taint_decide)

theorem chachaXorAvx512_ct : ConstantTime isa Proof.ChaCha20.X86_64.Avx2.xorAvx2X86_64.pre Proof.ChaCha20.X86_64.Avx2.xorAvx2X86_64.pub Impl.ChaCha20.X86_64.Avx512.xor :=
  VG.Taint.constantTime (A := taint) Proof.ChaCha20.X86_64.Avx2.τ₀ (fun _ _ h₁ h₂ hp => Proof.ChaCha20.X86_64.Avx2.agree₀ h₁ h₂ hp) (by taint_decide)

theorem chachaXorAvx512_sct : SpecConstantTime spectre Proof.ChaCha20.X86_64.Avx2.xorAvx2X86_64.pre Proof.ChaCha20.X86_64.Avx2.xorAvx2X86_64.pub Impl.ChaCha20.X86_64.Avx512.xor :=
  Taint.specConstantTime specSound Proof.ChaCha20.X86_64.Avx2.τ₀ (fun _ _ h₁ h₂ hp => Proof.ChaCha20.X86_64.Avx2.agree₀ h₁ h₂ hp) (by taint_decide)

end VG.Proof.SpectreDemo
