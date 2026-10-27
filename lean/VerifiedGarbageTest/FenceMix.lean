import VerifiedGarbage.Proof.Framework.X86_64.FenceMix
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Compress
import VerifiedGarbage.TCB.Axioms

/-!
# Fences only before returning, for code the taint analysis checks

ChaCha20's `xor` and SHA-256's `compress` loop over their input, and their
constant time is proven by the taint analysis: with only an `lfence` before
they return, they are speculatively safe (`specSafe_taint`), by the same
check (`taint_decide`) on the code with the barrier appended.
-/

namespace VG.Test.FenceMix

open VG VG.X86_64

theorem chachaXor_safe :
    SpecSafe Spectre.spectre Proof.ChaCha20.xorX86_64.pre Proof.ChaCha20.xorX86_64.pub
      (.seq Impl.ChaCha20.X86_64.Xor.xor (.block [.lfence])) :=
  specSafe_taint Spectre.specSound rfl Proof.ChaCha20.X86_64.Xor.τ₀
    (fun _ _ h₁ h₂ hp => Proof.ChaCha20.X86_64.Xor.agree₀ h₁ h₂ hp) (by taint_decide)

theorem sha256Compress_safe :
    SpecSafe Spectre.spectre Proof.Sha256.compressX86_64.pre Proof.Sha256.compressX86_64.pub
      (.seq Impl.Sha256.X86_64.compress (.block [.lfence])) := by
  refine specSafe_taint Spectre.specSound rfl (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

#assert_standard_axioms chachaXor_safe
#assert_standard_axioms sha256Compress_safe
#assert_standard_axioms verified_fenceFn_safe
#assert_standard_axioms verified_taint_safe

end VG.Test.FenceMix
