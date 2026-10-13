module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Seed.X86.Modes
meta import VerifiedGarbage.Impl.Seed.X86.Modes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# SEED-OFB and SEED-CFB128 on x86 (32-bit): the code as literals

The code of OFB and CFB128 as literals (`materialize_flat_code`), which the
checks of the whole functions (`taint_decide`, `lit_decide`) read rather
than build the code again.
-/

@[expose] public section

namespace VG.Proof.Seed.X86

materialize_flat_code ofbCode := Impl.Seed.X86.ofb
materialize_flat_code cfbEncryptCode := Impl.Seed.X86.cfbEncrypt
materialize_flat_code cfbDecryptCode := Impl.Seed.X86.cfbDecrypt

end VG.Proof.Seed.X86
