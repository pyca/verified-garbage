module

import VerifiedGarbage.Proof.TripleDes.Arm.Lit
import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.SboxLit
public import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.Arm.Wide
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.Arm.Lit
meta import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.SboxLit
meta import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
meta import VerifiedGarbage.Impl.TripleDes.Arm.Wide
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Triple DES's functions on ARMv7, as literals. -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.Arm.Key.expandKey
materialize_code Impl.TripleDes.Arm.Bitslice.encrypt
materialize_code Impl.TripleDes.Arm.Bitslice.decrypt
materialize_code Impl.TripleDes.Arm.Wide.cbcDecrypt
materialize_code Impl.TripleDes.Arm.Wide.cfbDecrypt

end VG
