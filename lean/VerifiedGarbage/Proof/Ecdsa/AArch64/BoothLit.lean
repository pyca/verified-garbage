import VerifiedGarbage.Impl.P256.Booth
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lit
import VerifiedGarbage.Proof.EcKey.AArch64.Lit

/-! The comb that signing and public keys share is checked once, and their
literals read it. -/

namespace VG.Impl.P256.Booth
materialize_code comb
materialize_code sign
materialize_code publicKey
end VG.Impl.P256.Booth
