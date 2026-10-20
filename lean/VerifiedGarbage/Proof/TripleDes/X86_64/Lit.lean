module

import VerifiedGarbage.Proof.TripleDes.X86_64.SboxTable
public import VerifiedGarbage.Impl.TripleDes.X86_64.Sbox
public import VerifiedGarbage.Impl.TripleDes.X86_64.Permutation
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.X86_64.SboxTable
meta import VerifiedGarbage.Impl.TripleDes.X86_64.Sbox
meta import VerifiedGarbage.Impl.TripleDes.X86_64.Permutation
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

@[expose] public section

namespace VG.Impl.TripleDes.X86_64

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

end VG.Impl.TripleDes.X86_64
