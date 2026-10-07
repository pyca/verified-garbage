import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Lit
import VerifiedGarbage.Proof.Ecdh.X86_64.Contract
import VerifiedGarbage.Proof.Framework.X86_64.TaintSym

/-! Secret scalars affect neither branches nor addresses in the five-bit loop. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Ecdh.X86_64.Window5

theorem baseline_ct : ConstantTime isa ecdhX86_64.pre ecdhX86_64.pub exchangeP256 := by
  obtain ⟨_, hc⟩ : ∃ h, (taintS.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) exchangeP256 h).isSome = true := by
    taint_decide_sum []
  refine VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ hc
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem adx_ct : ConstantTime isa ecdhX86_64.pre ecdhX86_64.pub exchangeP256Adx := by
  obtain ⟨_, hc⟩ : ∃ h, (taintS.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) exchangeP256Adx h).isSome = true := by
    taint_decide_sum []
  refine VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ hc
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

end VG.Proof.Ecdh.X86_64.Secret
