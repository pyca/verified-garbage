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
      (fun _ _ => True) :=
  engineOf_ct combOkY base k T


theorem x25519BaseAdx_ok [DivstepInv] (s : State) (hs : baseLocal.pre s) :
    ∃ tr t, Exec isa x25519BaseAdx s tr t ∧ abiPreserved s t ∧ baseLocal.post s t := by
  obtain ⟨tr, t, he, h⟩ := x25519BaseWith_correct _ engineAdxY_ok hs
  exact ⟨tr, t, he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem x25519BaseAdx_verified [DivstepInv] : Verified X86_64.target x25519BaseAdx
    (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts)) :=
  Verified.of_correct x25519BaseAdx_ok (x25519BaseWith_ct _ engineAdxY_ok engineAdxY_public) base_implies

end VG.Proof.X25519.X86_64.Base
