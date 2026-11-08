module

public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Permutation
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.Permutation
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

@[expose] public section

namespace VG.Impl.TripleDes.PPC64LE

materialize_code initialPermutation
materialize_code finalPermutation
materialize_code keyPermutation1
materialize_code keyPermutation2

end VG.Impl.TripleDes.PPC64LE
