module

public import VerifiedGarbage.Impl.MlKem.X86_64.Ntt
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.MlKem.X86_64.Ntt
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# ML-KEM on x86-64: the zetas `ζ · 2¹⁶ mod q` as a table

The kernel evaluates `zmTab` (a power of `ζ` by a bit reversal, which it
evaluates slowly) for every entry of the NTT's table of zetas
(`NttR/Lit.lean`); it reads the 128 values from this table instead.
-/

@[expose] public section

namespace VG

materialize_table Impl.MlKem.X86_64.zmTab 128

end VG
