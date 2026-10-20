module

import VerifiedGarbage.Proof.TripleDes.Arm.Lit
public import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.Arm.Ecb
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.Arm.Lit
meta import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
meta import VerifiedGarbage.Impl.TripleDes.Arm.Ecb
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

@[expose] public section

namespace VG

/-! The parts the block functions share, evaluated once: the round, and the
initial and final permutations. -/

materialize_value Impl.TripleDes.Arm.roundBody
materialize_value Impl.TripleDes.Arm.blockLoad

/-! The functions. -/

materialize_code Impl.TripleDes.Arm.encryptBlock
materialize_code Impl.TripleDes.Arm.decryptBlock
materialize_code Impl.TripleDes.Arm.Key.expandKey
materialize_code Impl.TripleDes.Arm.Ecb.encrypt
materialize_code Impl.TripleDes.Arm.Ecb.decrypt

end VG
