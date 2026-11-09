module

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit

public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeKg
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
import VerifiedGarbage.Proof.MlKem.X86_64.Mul16V
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeKg
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
meta import VerifiedGarbage.Proof.MlKem.X86_64.Mul16V
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: `vg_mlkem768_kpke_keygen`, verified

The proof of `KpkeKg.lean` with AVX2, its constant time (`kpkeKg_mid`: the
pointers after the products are those of the entry, as for `kpke_encrypt`),
and its contract implying the shared one of `Proof/MlKem/Kpke16Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Kpke16
open VG.Spec.MlKem

theorem kpkeKg_agree (L : Kem) (s₁ s₂ : State) (_ : (kpkeKgK L).pre s₁) (_ : (kpkeKgK L).pre s₂)
    (hp : (kpkeKgK L).pub s₁ s₂) :
    X86_64.Taint.Agree (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2]

/-- The pointers that `kpkeKgPost` uses agree after `kpkeKgPre`. -/
theorem kpkeKg_mid {L : Kem} {s₁ s₂ σ₁ σ₂ : State} (hp : (kpkeKgK L).pub σ₁ σ₂)
    (e₁ : KpkeKg.EO L σ₁ 0 0 s₁) (e₂ : KpkeKg.EO L σ₂ 0 0 s₂) :
    ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r15, .rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [e₁.kt.rbx, e₂.kt.rbx, hp.2.2.2.2.1]
  · rw [e₁.kt.rbp, e₂.kt.rbp, hp.2.1]
  · rw [e₁.kt.r12, e₂.kt.r12, hp.2.2.1]
  · rw [e₁.kt.r13, e₂.kt.r13, hp.2.2.2.1]
  · rw [e₁.kt.r15, e₂.kt.r15, hp.1]
  · rw [e₁.kt.rsp, e₂.kt.rsp, hp.2.2.2.2.2]

theorem kpkeKg768Y_ct :
    ConstantTime isa (kpkeKgK kem768).pre (kpkeKgK kem768).pub (kpkeKg kem768 .avx2 keygenMul16Y) := by
  unfold kpkeKg
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq
    (R := fun (s₁ s₂ : State) => ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r15, .rsp], s₁.gpr r = s₂.gpr r) ?_ ?_)
  · refine ((RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp])
      (fun x y h => kpkeKg_agree kem768 x y h.1 h.2.1 h.2.2) [] (by taint_decide)).wpDep
      (F := fun σ s => KpkeKg.EO kem768 σ 0 0 s) fun s₁ s₂ h =>
        ⟨KpkeKg.pre_wp keWf768 kgMul16Y3_correct (by lit_decide) h.1,
          KpkeKg.pre_wp keWf768 kgMul16Y3_correct (by lit_decide) h.2.1⟩).mono
      (fun _ _ h => h) fun s₁ s₂ ⟨_, σ₁, σ₂, ⟨_, _, hp⟩, e₁, e₂⟩ => kpkeKg_mid hp e₁ e₂
  · exact RelCT.mono (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r15, .rsp])
      (fun x y h => X86_64.Taint.agree_ofRegs h) [] (by taint_decide)) (fun _ _ h => h) fun _ _ _ => trivial

theorem kpkeKg768Y_correct : ∀ s, (kpkeKgK kem768).pre s →
    ∃ t s', Exec isa (kpkeKg kem768 .avx2 keygenMul16Y) s t s' ∧ abiPreserved s s' ∧ (kpkeKgK kem768).post s s' :=
  KpkeKg.kpkeKg_correct PrimsOk.avx2 keWf768 kgMul16Y3_correct (by lit_decide) (by lit_decide) (by lit_decide)

end VG.Proof.MlKem.X86_64
