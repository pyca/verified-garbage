module

public import VerifiedGarbage.Impl.Camellia.X86.Modes
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Camellia.X86.Modes
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
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-!
# Camellia-CBC on x86 (32-bit): the code as literals

The code of CBC encryption and decryption as literals
(`materialize_flat_code`), which the checks of the whole functions
(`taint_decide`, `lit_decide`) read rather than build the code again.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

materialize_flat_code cbcEncryptChainedCode := Impl.Camellia.X86.cbcEncryptChained
materialize_flat_code cbcDecryptChainedCode := Impl.Camellia.X86.cbcDecryptChained

end VG.Proof.Camellia.X86
