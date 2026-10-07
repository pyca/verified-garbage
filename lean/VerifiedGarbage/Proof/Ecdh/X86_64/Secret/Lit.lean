import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ecdh.P256.X86_64.Window5

/-! Materialize the secret-window programs once for kernel-evaluated checks. -/
namespace VG
materialize_code Impl.Ecdh.X86_64.Window5.exchangeP256
materialize_code Impl.Ecdh.X86_64.Window5.exchangeP256Adx
end VG
