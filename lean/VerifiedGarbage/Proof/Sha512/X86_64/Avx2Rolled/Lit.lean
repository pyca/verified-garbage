module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Sha512.X86_64.Avx2Rolled
meta import VerifiedGarbage.Impl.Sha512.X86_64.Avx2Rolled

/-!
# SHA-512 with AVX2 on x86-64, rolled: the code as a literal

The compression function as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`).
-/

@[expose] public section

namespace VG

materialize_code Impl.Sha512.X86_64.Avx2Rolled.compress

end VG
