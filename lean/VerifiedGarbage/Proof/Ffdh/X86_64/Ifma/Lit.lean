module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Ifma
public import VerifiedGarbage.Impl.Rsa.X86_64.PubIfma
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.Ffdh.X86_64.Ifma
meta import VerifiedGarbage.Impl.Rsa.X86_64.PubIfma
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# FFDH's exponentiation with AVX512_IFMA on x86-64: the vector code as a literal

Each layout's vector code (`Impl.Ffdh.X86_64.Ifma.vec`) is unrolled, and the
kernel takes over a second to build it: its constant-time check
(`Proof/Ffdh/X86_64/Ifma/CT.lean`, `lT`) and the checks of the code around it
(`Proof/Variants/FfdhExp/X86_64/Ifma.lean`, `loks`) read its literal instead
(`materialize_code`, `Proof/Framework/Lit.lean`), which is checked once here.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Ifma

open VG.Impl.Rsa.X86_64

materialize_code vec2048 := Impl.Ffdh.X86_64.Ifma.vec PubIfma.pay2048
materialize_code vec3072 := Impl.Ffdh.X86_64.Ifma.vec PubIfma.pay3072
materialize_code vec4096 := Impl.Ffdh.X86_64.Ifma.vec PubIfma.pay4096

end VG.Proof.Ffdh.X86_64.Ifma
