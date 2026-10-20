module

public import VerifiedGarbage.Impl.Rc2.X86.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Rc2.X86.KeyLit
meta import VerifiedGarbage.Impl.Rc2.X86.Block
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Rc2.X86.KeyLit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

@[expose] public section

namespace VG.Impl.Rc2.X86

materialize_value keyLookup

materialize_flat_code encryptBlock
materialize_flat_code decryptBlock

end VG.Impl.Rc2.X86
