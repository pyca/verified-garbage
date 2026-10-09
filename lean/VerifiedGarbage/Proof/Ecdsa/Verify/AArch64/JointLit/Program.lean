import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Arithmetic

/-! The forwarded field programs of P-256 verification are the optimizer's
output (`Forward.Arithmetic.optimized`), whose literals the Forward framework
(`Proof/Weierstrass/AArch64/Forward/`) checks: the literals of `JointLit/`
are those, by rewriting, rather than the kernel running the optimizer
again. -/

namespace VG.Proof.Ecdsa.Verify.AArch64.JointLit
open VG VG.Impl.P256

/-- A selected field program is the optimizer's output on it. -/
theorem program_eq (k : VerifyArithmetic.Kind) :
    VerifyArithmetic.program VerifyDouble.M (VerifyArithmetic.operations k) =
      .block (Proof.Weierstrass.AArch64.Forward.Arithmetic.optimized k) := by
  rw [VerifyArithmetic.program,
    ite_eq_left ⟨rfl, List.mem_map.mpr ⟨k, by cases k <;> decide, rfl⟩⟩]
  rfl

end VG.Proof.Ecdsa.Verify.AArch64.JointLit
