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

/-!
# Camellia-OFB and Camellia-CFB128 on x86 (32-bit): the code as literals

The code of OFB and CFB128 as literals (`materialize_flat_code`), which the
checks of the whole functions (`taint_decide`, `lit_decide`) read rather
than build the code again.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

materialize_flat_code ofbCode := Impl.Camellia.X86.ofb
materialize_flat_code cfbEncryptCode := Impl.Camellia.X86.cfbEncrypt
materialize_flat_code cfbDecryptCode := Impl.Camellia.X86.cfbDecrypt

end VG.Proof.Camellia.X86
