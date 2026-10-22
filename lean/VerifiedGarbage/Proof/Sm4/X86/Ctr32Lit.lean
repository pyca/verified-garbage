module

public import VerifiedGarbage.Impl.Sm4.X86.Ctr32
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sm4.X86.Ctr32
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # SM4's counter mode with `inc₃₂` on x86: a code literal for the taint and stack checks -/

@[expose] public section

namespace VG.Proof.Sm4.X86

materialize_flat_code ctr32Code := Impl.Sm4.X86.ctr32

end VG.Proof.Sm4.X86
