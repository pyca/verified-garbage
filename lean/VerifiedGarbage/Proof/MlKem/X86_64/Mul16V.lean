module

public import VerifiedGarbage.Proof.MlKem.X86_64.EncMulY
meta import VerifiedGarbage.Proof.MlKem.X86_64.EncMulY
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
meta import VerifiedGarbage.Proof.MlKem.X86_64.Lit
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/-!
# ML-KEM on x86-64: `encrypt_mul` reading `Â` as `u16`s, for each rank

`encryptMul16Y k` meets `encMulK16 k` (`EncMulY.wp_all16`) for `k = 3, 4`,
as code the K-PKE functions run inline.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem encMul16Y3_wo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
    (EncMulY.innerY16 3) = true := writesOnly_of (by lit_decide)

theorem encMul16Y4_wo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
    (EncMulY.innerY16 4) = true := writesOnly_of (by lit_decide)

theorem encMul16Y3_ctl : ctlOk (encryptMul16Y 3) = true := by lit_decide
theorem encMul16Y4_ctl : ctlOk (encryptMul16Y 4) = true := by lit_decide

theorem encMul16Y_correct {k : Nat} (hk : k = 3 ∨ k = 4)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
      (EncMulY.innerY16 k) = true)
    (hctl : ctlOk (encryptMul16Y k) = true) (s : State) (hs : (encMulK16 k).pre s) :
    ∃ t s', Exec isa (encryptMul16Y k) s t s' ∧ abiPreserved s s' ∧ (encMulK16 k).post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := EncMulY.wp_all16 hs (by omega) hk hwo
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hg, hpost⟩

theorem encMul16Y3_correct : ∀ s, (encMulK16 3).pre s →
    ∃ t s', Exec isa (encryptMul16Y 3) s t s' ∧ abiPreserved s s' ∧ (encMulK16 3).post s s' :=
  encMul16Y_correct (.inl rfl) encMul16Y3_wo encMul16Y3_ctl

theorem encMul16Y4_correct : ∀ s, (encMulK16 4).pre s →
    ∃ t s', Exec isa (encryptMul16Y 4) s t s' ∧ abiPreserved s s' ∧ (encMulK16 4).post s s' :=
  encMul16Y_correct (.inr rfl) encMul16Y4_wo encMul16Y4_ctl

end VG.Proof.MlKem.X86_64
