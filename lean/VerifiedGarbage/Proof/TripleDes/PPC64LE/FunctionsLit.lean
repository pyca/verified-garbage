module

import VerifiedGarbage.Proof.TripleDes.PPC64LE.SboxTable
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Block
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Ecb
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.SboxTable
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.ExpandKey
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.Block
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.Ecb
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

@[expose] public section

namespace VG

/-! The parts the block functions share, evaluated once: the round, and the
initial and final permutations. -/

materialize_value Impl.TripleDes.PPC64LE.roundBody
materialize_value Impl.TripleDes.PPC64LE.blockLoad
materialize_value Impl.TripleDes.PPC64LE.blockStore

/-! The functions. -/

materialize_code Impl.TripleDes.PPC64LE.encryptBlock
materialize_code Impl.TripleDes.PPC64LE.decryptBlock
materialize_code Impl.TripleDes.PPC64LE.Key.expandKey
materialize_code Impl.TripleDes.PPC64LE.Ecb.encrypt
materialize_code Impl.TripleDes.PPC64LE.Ecb.decrypt

end VG
