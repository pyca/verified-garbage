module

import VerifiedGarbage.Proof.TripleDes.X86.RoundLit
public import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.X86.Ecb
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.X86.RoundLit
meta import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
meta import VerifiedGarbage.Impl.TripleDes.X86.Ecb
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

@[expose] public section

namespace VG

/-! The parts the block functions share, evaluated once: the round, and the
initial and final permutations. -/

materialize_value Impl.TripleDes.X86.roundBody
materialize_value Impl.TripleDes.X86.blockLoad
materialize_value Impl.TripleDes.X86.finalSave

/-! The functions. -/

materialize_code Impl.TripleDes.X86.encryptBlock
materialize_code Impl.TripleDes.X86.decryptBlock
materialize_code Impl.TripleDes.X86.Key.expandKey
materialize_code Impl.TripleDes.X86.Ecb.encrypt
materialize_code Impl.TripleDes.X86.Ecb.decrypt

end VG
