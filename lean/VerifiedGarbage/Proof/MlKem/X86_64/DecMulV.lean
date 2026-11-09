module

public import VerifiedGarbage.Proof.MlKem.X86_64.DecMul
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecMul
meta import VerifiedGarbage.Proof.MlKem.X86_64.Lit
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: `vg_mlkem768_decrypt_mul` and `vg_mlkem1024_decrypt_mul`, verified

The proof of `DecMul.lean` for each backend and rank, its constant time,
and its contract implying the shared one of `Proof/MlKem/KpkeMulContract.lean`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem decMul_correct {B : Bodies} {R : AccRep} {T : TabRep} (hB : BodiesOk B R T) {k : Nat} (hk : k ≤ 4) (hk0 : 0 < k)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14] (DecMul.inner B) = true)
    (hctl : ctlOk (decryptMul B k) = true) (s : State) (hs : (decMulK k).pre s) :
    ∃ t s', Exec isa (decryptMul B k) s t s' ∧ abiPreserved s s' ∧ (decMulK k).post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := DecMul.wp_all hs hk hB hk0 hwo
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hg, hpost⟩

theorem decMul_agree {k : Nat} (s₁ s₂ : State) (_ : (decMulK k).pre s₁) (_ : (decMulK k).pre s₂)
    (hp : (decMulK k).pub s₁ s₂) : X86_64.Taint.Agree (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2]

theorem decMulSse3_ct : ConstantTime isa (decMulK 3).pre (decMulK 3).pub (decryptMul .sse 3) :=
  VG.Taint.constantTime (A := taint) _ decMul_agree (by taint_decide)

theorem decMulSse4_ct : ConstantTime isa (decMulK 4).pre (decMulK 4).pub (decryptMul .sse 4) :=
  VG.Taint.constantTime (A := taint) _ decMul_agree (by taint_decide)

/-! The facts about the code, each checked once (on the literals of `Lit.lean`): the registers
the inlined code writes, which depends only on the backend, and the loads of MXCSR. -/

theorem decMulSse_wo :
    writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14] (DecMul.inner .sse) = true :=
  writesOnly_of (by lit_decide)

theorem decMulSse3_ctl : ctlOk (decryptMul .sse 3) = true := by lit_decide
theorem decMulSse4_ctl : ctlOk (decryptMul .sse 4) = true := by lit_decide
theorem decMulSse3_correct : ∀ s, (decMulK 3).pre s →
    ∃ t s', Exec isa (decryptMul .sse 3) s t s' ∧ abiPreserved s s' ∧ (decMulK 3).post s s' :=
  decMul_correct BodiesOk.sse (by decide) (by decide) decMulSse_wo decMulSse3_ctl

theorem decMulSse4_correct : ∀ s, (decMulK 4).pre s →
    ∃ t s', Exec isa (decryptMul .sse 4) s t s' ∧ abiPreserved s s' ∧ (decMulK 4).post s s' :=
  decMul_correct BodiesOk.sse (by decide) (by decide) decMulSse_wo decMulSse4_ctl

end VG.Proof.MlKem.X86_64
