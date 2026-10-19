module

public import VerifiedGarbage.Impl.Rc2.X86.Block
meta import VerifiedGarbage.Impl.Rc2.X86.Block
import VerifiedGarbage.Proof.Rc2.X86.KeyLit
meta import VerifiedGarbage.Proof.Rc2.X86.KeyLit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

@[expose] public section

namespace VG.Impl.Rc2.X86

materialize_value keyLookup

materialize_flat_code encryptBlock
materialize_flat_code decryptBlock

end VG.Impl.Rc2.X86
