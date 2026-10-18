module

public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDec
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDec
public import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
public import VerifiedGarbage.Proof.MlKem.X86_64.MulYV
meta import VerifiedGarbage.Proof.MlKem.X86_64.MulYV
import VerifiedGarbage.Proof.MlKem.X86_64.RowEY
meta import VerifiedGarbage.Proof.MlKem.X86_64.RowEY
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
meta import VerifiedGarbage.Proof.MlKem.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/-!
# ML-KEM on x86-64: `vg_mlkem768_kpke_decrypt`, verified

The proof of `KpkeDec.lean` for each backend, its constant time, and its
contract implying the shared one of `Spec/MlKem/Kpke16.lean`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Kpke16
open VG.Spec.MlKem

/-- The products of `decryptMul .sse`, inline. -/
theorem dmOkSse : KpkeDec.DmOk (dmInner .sse) where
  ok k hk s₀ hs := DecMul.body_ok hs (by omega) BodiesOk.sse (by omega) decMulSse_wo
  nc k hk := by rcases hk with rfl | rfl <;> lit_decide
  r15 k hk := by rcases hk with rfl | rfl <;> lit_decide

/-- The products of `decryptMulY`, inline. -/
theorem dmOkY : KpkeDec.DmOk dmInnerY where
  ok k hk s₀ hs := by
    rcases hk with rfl | rfl
    · exact DecMulY.body_ok hs (by decide) (by decide) decMulY3_wo (rowEY_wo (.inl rfl) (.inl rfl))
    · exact DecMulY.body_ok hs (by decide) (by decide) decMulY4_wo (rowEY_wo (.inr rfl) (.inl rfl))
  nc k hk := by rcases hk with rfl | rfl <;> lit_decide
  r15 k hk := by rcases hk with rfl | rfl <;> lit_decide

theorem kpkeDec_agree (L : Kem) (s₁ s₂ : State) (_ : (kpkeDecK L).pre s₁) (_ : (kpkeDecK L).pre s₂)
    (hp : (kpkeDecK L).pub s₁ s₂) :
    X86_64.Taint.Agree (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2]

theorem kdWf768 : KpkeDec.KdWf kem768 := ⟨.inl rfl, by decide, by decide, by decide⟩

theorem kdCalls768 : KemCalls kem768 compressWidths compressWidths := ⟨Codecs.ceI, Codecs.ddI, by decide, by decide⟩

theorem kpkeDec768Sse_ct :
    ConstantTime isa (kpkeDecK kem768).pre (kpkeDecK kem768).pub (kpkeDec kem768 .sse (dmInner .sse)) :=
  VG.Taint.constantTime (A := taint) _ (kpkeDec_agree kem768) (by taint_decide)

theorem kpkeDec768Y_ct :
    ConstantTime isa (kpkeDecK kem768).pre (kpkeDecK kem768).pub (kpkeDec kem768 .avx2 dmInnerY) :=
  VG.Taint.constantTime (A := taint) _ (kpkeDec_agree kem768) (by taint_decide)

theorem kpkeDec768Sse_correct : ∀ s, (kpkeDecK kem768).pre s →
    ∃ t s', Exec isa (kpkeDec kem768 .sse (dmInner .sse)) s t s' ∧ abiPreserved s s' ∧ (kpkeDecK kem768).post s s' :=
  KpkeDec.kpkeDec_correct ArithOk.sse kdCalls768 kdWf768 dmOkSse (by lit_decide) (by lit_decide) (by lit_decide)
    (by lit_decide) (by lit_decide)

theorem kpkeDec768Y_correct : ∀ s, (kpkeDecK kem768).pre s →
    ∃ t s', Exec isa (kpkeDec kem768 .avx2 dmInnerY) s t s' ∧ abiPreserved s s' ∧ (kpkeDecK kem768).post s s' :=
  KpkeDec.kpkeDec_correct ArithOk.avx2 kdCalls768 kdWf768 dmOkY (by lit_decide) (by lit_decide) (by lit_decide)
    (by lit_decide) (by lit_decide)

end VG.Proof.MlKem.X86_64
