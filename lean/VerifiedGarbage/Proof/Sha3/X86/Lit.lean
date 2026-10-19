module

public import VerifiedGarbage.Impl.Sha3.X86
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Sha3.X86
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
# Keccak-f[1600] on x86 (32-bit): the code as a literal

The permutation's code is built by functions (its rounds, planes and
round-constant stores): its literal (`materialize_code`) spares the kernel
building the instructions in every check that evaluates the code (constant
time, `NoSp`, the stack's use, `spSafe`), and the streaming functions call it.
-/

@[expose] public section

namespace VG.Impl.Sha3.X86

materialize_code permute

end VG.Impl.Sha3.X86
