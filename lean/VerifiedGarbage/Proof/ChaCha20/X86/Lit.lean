module

public import VerifiedGarbage.Impl.ChaCha20.X86.Xor
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.ChaCha20.X86.Xor
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
# ChaCha20 on X86: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.ChaCha20.X86.block
materialize_code Impl.ChaCha20.X86.Xor.xor
materialize_code Impl.ChaCha20.X86.Xor.xorSsse3

end VG
