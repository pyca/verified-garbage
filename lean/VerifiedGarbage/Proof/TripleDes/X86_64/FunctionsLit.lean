module

import VerifiedGarbage.Proof.TripleDes.X86_64.SboxTable
meta import VerifiedGarbage.Proof.TripleDes.X86_64.SboxTable
public import VerifiedGarbage.Impl.TripleDes.X86_64.Block
meta import VerifiedGarbage.Impl.TripleDes.X86_64.Block
public import VerifiedGarbage.Impl.TripleDes.X86_64.ExpandKey
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.TripleDes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

@[expose] public section

namespace VG

/-! The parts the block functions share, evaluated once: the round, and the
initial and final permutations. -/

materialize_value Impl.TripleDes.X86_64.roundBody
materialize_value Impl.TripleDes.X86_64.blockLoad
materialize_value Impl.TripleDes.X86_64.blockStore

/-! The functions. -/

materialize_code Impl.TripleDes.X86_64.encryptBlock
materialize_code Impl.TripleDes.X86_64.decryptBlock
materialize_code Impl.TripleDes.X86_64.Key.expandKey

end VG
