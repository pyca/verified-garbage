module

import VerifiedGarbage.Proof.Blowfish.AArch64.Lit
meta import VerifiedGarbage.Proof.Blowfish.AArch64.Lit
public import VerifiedGarbage.Impl.Blowfish.AArch64.Modes
meta import VerifiedGarbage.Impl.Blowfish.AArch64.Modes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-! # Blowfish-CBC, -OFB and -CFB64's AArch64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

/-! The batches, whose registers `crypt`'s proof checks. -/

materialize_code Impl.Blowfish.AArch64.batchEnc
materialize_code Impl.Blowfish.AArch64.batchDec

/-! The functions. -/

materialize_code Impl.Blowfish.AArch64.cbcEncrypt
materialize_code Impl.Blowfish.AArch64.cbcDecrypt
materialize_code Impl.Blowfish.AArch64.ofb
materialize_code Impl.Blowfish.AArch64.cfbEncrypt
materialize_code Impl.Blowfish.AArch64.cfbDecrypt

end VG
