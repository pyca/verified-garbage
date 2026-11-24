module

public import VerifiedGarbage.Impl.Rc2.X86.Ssse3
public import VerifiedGarbage.Proof.Rc2.TableLit
public import VerifiedGarbage.Proof.Rc2.X86.Stream.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Rc2.X86.Ssse3
meta import VerifiedGarbage.Proof.Rc2.TableLit
meta import VerifiedGarbage.Proof.Rc2.X86.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # RC2's key expansion by `pshufb` on x86 (32-bit): the code as literals -/

@[expose] public section

namespace VG.Impl.Rc2.X86.Ssse3

materialize_value piLookup
materialize_code expandKey
materialize_code init

end VG.Impl.Rc2.X86.Ssse3
