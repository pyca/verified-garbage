import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyLit
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/-!
# Facts about the code of each registered verification

That every load of MXCSR restores it (`ctlOk`, the hypothesis of
`verify_verified`) and that no instruction writes the stack pointer, for each
field multiplication and doubling `vg_ed25519_verify_equation` is registered
with: evaluated once here, from the literals, for both the equation's own
artifacts and the generic verification over SHA-512 that calls it.
-/

namespace VG.Proof.Ed25519.X86_64.VerifyCode

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

theorem baseline_mx : ctlOk (verifyEquation Impl.X25519.X86_64.baseline
    (double4 Impl.X25519.X86_64.baseline)) = true := by lit_decide

theorem baseline_spSafe : (verifyEquation Impl.X25519.X86_64.baseline
    (double4 Impl.X25519.X86_64.baseline)).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)

theorem adx_mx : ctlOk (verifyEquation Impl.X25519.X86_64.adx
    (double4 Impl.X25519.X86_64.adx)) = true := by lit_decide

theorem adx_spSafe : (verifyEquation Impl.X25519.X86_64.adx
    (double4 Impl.X25519.X86_64.adx)).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)

theorem ifma_mx : ctlOk (verifyEquation Impl.X25519.X86_64.adx Ifma.double4) = true := by
  lit_decide

theorem ifma_spSafe : (verifyEquation Impl.X25519.X86_64.adx Ifma.double4).all
    (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)

end VG.Proof.Ed25519.X86_64.VerifyCode
