module

public import VerifiedGarbage.Proof.MlKem.X86_64.EncMul
import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.EncMul
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: `vg_mlkem768_encrypt_mul` and `vg_mlkem1024_encrypt_mul`, verified

The proof of `EncMul.lean` for each backend and rank, its constant time,
and its contract implying the shared one of `Proof/MlKem/KpkeMulContract.lean`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem encMul_correct {B : Bodies} {R : AccRep} {T : TabRep} (hB : BodiesOk B R T) {k : Nat} (hk : k ≤ 4) (hk0 : 0 < k)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
      (EncMul.innerE B k) = true)
    (hctl : ctlOk (encryptMul B k) = true) (s : State) (hs : (encMulK k).pre s) :
    ∃ t s', Exec isa (encryptMul B k) s t s' ∧ abiPreserved s s' ∧ (encMulK k).post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := EncMul.wp_all hs hk hB hk0 hwo
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hg, hpost⟩

theorem encMul_agree {k : Nat} (s₁ s₂ : State) (_ : (encMulK k).pre s₁) (_ : (encMulK k).pre s₂)
    (hp : (encMulK k).pub s₁ s₂) :
    X86_64.Taint.Agree (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2]

/-! The facts about the code, each checked once (on the literals of `Lit.lean`). -/

theorem encMulSse3_wo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
    (EncMul.innerE .sse 3) = true :=
  writesOnly_of (by lit_decide)

theorem encMulSse3_ctl : ctlOk (encryptMul .sse 3) = true := by lit_decide

theorem encMulSse4_wo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
    (EncMul.innerE .sse 4) = true :=
  writesOnly_of (by lit_decide)

theorem encMulSse4_ctl : ctlOk (encryptMul .sse 4) = true := by lit_decide

theorem encMulSse3_ct : ConstantTime isa (encMulK 3).pre (encMulK 3).pub (encryptMul .sse 3) :=
  VG.Taint.constantTime (A := taint) _ encMul_agree (by taint_decide)

theorem encMulSse3_correct : ∀ s, (encMulK 3).pre s →
    ∃ t s', Exec isa (encryptMul .sse 3) s t s' ∧ abiPreserved s s' ∧ (encMulK 3).post s s' :=
  encMul_correct BodiesOk.sse (by decide) (by decide) encMulSse3_wo encMulSse3_ctl

theorem encMulSse4_ct : ConstantTime isa (encMulK 4).pre (encMulK 4).pub (encryptMul .sse 4) :=
  VG.Taint.constantTime (A := taint) _ encMul_agree (by taint_decide)

theorem encMulSse4_correct : ∀ s, (encMulK 4).pre s →
    ∃ t s', Exec isa (encryptMul .sse 4) s t s' ∧ abiPreserved s s' ∧ (encMulK 4).post s s' :=
  encMul_correct BodiesOk.sse (by decide) (by decide) encMulSse4_wo encMulSse4_ctl

end VG.Proof.MlKem.X86_64
