module

public import VerifiedGarbage.Impl.Rsa.X86_64.PubIfma
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.Rsa.X86_64.PubIfma
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# The IFMA code's conversion to 64-bit words, as literals

`CrtIfma.to64 l` finds the limbs that overlap each word by a filter of all
the limbs (`W + 1` filters of `L` limbs, each with two comparisons by their
`Decidable` instances): about 0.1 ms a limb for the kernel, in every check
that evaluates code with the conversion in it. Its literal for each layout
(`materialize_value`, `Proof/Framework/Lit.lean`) is checked once here, and
the checks read it.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

materialize_value to64_2048 := Impl.Rsa.X86_64.CrtIfma.to64 Impl.Rsa.X86_64.PubIfma.pay2048
materialize_value to64_3072 := Impl.Rsa.X86_64.CrtIfma.to64 Impl.Rsa.X86_64.PubIfma.pay3072
materialize_value to64_4096 := Impl.Rsa.X86_64.CrtIfma.to64 Impl.Rsa.X86_64.PubIfma.pay4096

end VG.Proof.Bignum.X86_64.Ifma
