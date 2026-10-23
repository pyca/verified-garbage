module

public import VerifiedGarbage.Impl.Blake2.PPC64LE
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Blake2.PPC64LE
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-!
# BLAKE2 on PPC64LE: the code as literals

The code of the compression functions of BLAKE2b and BLAKE2s as literals
(`materialize_code`, `Proof/Framework/Lit.lean`).
-/

@[expose] public section

namespace VG.Proof.Blake2.PPC64LE

materialize_code compressB := Impl.Blake2.PPC64LE.compress Spec.Blake2.b
materialize_code compressS := Impl.Blake2.PPC64LE.compress Spec.Blake2.s

end VG.Proof.Blake2.PPC64LE
