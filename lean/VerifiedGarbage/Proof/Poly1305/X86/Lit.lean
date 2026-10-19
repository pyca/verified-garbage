module

public import VerifiedGarbage.Impl.Poly1305.X86
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Poly1305.X86
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-!
# Poly1305 on X86: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Poly1305.X86.init
materialize_code Impl.Poly1305.X86.blocks
materialize_code Impl.Poly1305.X86.update
materialize_code Impl.Poly1305.X86.finalize

end VG
