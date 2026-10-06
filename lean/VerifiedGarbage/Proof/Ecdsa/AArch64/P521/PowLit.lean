import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ecdsa.P521.AArch64

/-!
# ECDSA over P-521 on AArch64: the power modulo `n` as a literal

`x^(n - 2) mod n` by sliding windows (`Cfg.nPow`), whose chain over P-521's
`n` has a hundred steps of nine-word multiplications: the kernel takes most of
the memory and time of the literals of signing and verification in building
it. As a literal (`materialize_code`, `Proof/Framework/Lit.lean`) of its own,
it is built once, here, and the literals of both
(`Lit.lean`, `Verify/AArch64/P521/Lit.lean`) read it.
-/

namespace VG.Proof.Ecdsa.AArch64.P521

materialize_code nPow := Impl.Ecdsa.AArch64.p521.nPow

end VG.Proof.Ecdsa.AArch64.P521
