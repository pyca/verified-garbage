module

public import VerifiedGarbage.Impl.Sha1.X86.Stream
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Sha1.X86.Stream
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

/-!
# SHA-1 on x86 (32-bit): the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Sha1.X86.compress
materialize_code Impl.Sha1.X86.Stream.update
materialize_code Impl.Sha1.X86.Stream.finalize

end VG
