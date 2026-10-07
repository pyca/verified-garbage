import VerifiedGarbage.Proof.X25519.X86_64.Base.Verified
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseAdx

/-!
# Fixed-base X25519 with BMI2 and ADX: `Verified`

`x25519BaseAdx` is `x25519Base adx` with Ed25519's comb selecting its entries with AVX2
(`Proof.Ed25519.X86_64.combOkY`).
-/

namespace VG.Proof.X25519.X86_64.Base

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64.Base VG.Proof.Ed25519.X86_64

/-- The engine with the comb selecting with AVX2. -/
abbrev engineAdxY : Prog isa :=
  engineOf Impl.X25519.X86_64.adx (combMultiply Impl.X25519.X86_64.adx combSelectY)

theorem engineAdxY_ok [DivstepInv] : UEngineOk engineAdxY := engineOf_ok combOkY

theorem engineAdxY_public (base k T : Addr) :
    RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y) engineAdxY
      (fun _ _ => True) := by
  apply taintSymFld (Taint.ofRegs [.rdi, .rsi]) _ (by exact ⟨_, by taint_decide⟩)
  intro x y h
  refine ⟨Taint.agree_ofRegs fun r hr => ?_, fun n hn => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.rdi.trans h.2.1.rdi.symm
    · exact h.1.2.1.trans h.2.2.1.symm
  · simp only [List.mem_singleton] at hn; subst hn
    exact h.1.2.2.2.2.1.sym.trans h.2.2.2.2.2.1.sym.symm

theorem x25519BaseAdx_ok [DivstepInv] (s : State) (hs : baseLocal.pre s) :
    ∃ tr t, Exec isa x25519BaseAdx s tr t ∧ abiPreserved s t ∧ baseLocal.post s t := by
  obtain ⟨tr, t, he, h⟩ := x25519BaseWith_correct _ engineAdxY_ok hs
  exact ⟨tr, t, he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem x25519BaseAdx_verified [DivstepInv] : Verified X86_64.target x25519BaseAdx
    (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts)) :=
  Verified.of_correct x25519BaseAdx_ok (x25519BaseWith_ct _ engineAdxY_ok engineAdxY_public) base_implies

end VG.Proof.X25519.X86_64.Base
