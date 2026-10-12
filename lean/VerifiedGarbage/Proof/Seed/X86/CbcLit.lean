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
# SEED-CBC on x86 (32-bit): the code as literals

The code of CBC encryption and decryption as literals
(`materialize_flat_code`), which the checks of the whole functions
(`taint_decide`, `lit_decide`) read rather than build the code again.
-/

@[expose] public section

namespace VG.Proof.Seed.X86

materialize_flat_code cbcEncryptCode := Impl.Seed.X86.cbcEncrypt
materialize_flat_code cbcDecryptCode := Impl.Seed.X86.cbcDecrypt

end VG.Proof.Seed.X86
