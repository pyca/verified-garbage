module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.AArch64.Comb
import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP384r1Literals
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.AArch64.Comb
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP384r1Literals
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # The fixed-base signing code as a kernel-checked literal -/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.AArch64.BrainpoolP384r1.signComb

end VG
