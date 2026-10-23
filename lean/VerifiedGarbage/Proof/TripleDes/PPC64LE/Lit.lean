module

import VerifiedGarbage.Proof.TripleDes.PPC64LE.SboxTable
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Sbox
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Permutation
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.SboxTable
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.Sbox
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.Permutation
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

@[expose] public section

namespace VG.Impl.TripleDes.PPC64LE

materialize_code sbox0
materialize_code sbox1
materialize_code sbox2
materialize_code sbox3
materialize_code sbox4
materialize_code sbox5
materialize_code sbox6
materialize_code sbox7

materialize_code initialPermutation
materialize_code finalPermutation
materialize_code keyPermutation1
materialize_code keyPermutation2

end VG.Impl.TripleDes.PPC64LE
