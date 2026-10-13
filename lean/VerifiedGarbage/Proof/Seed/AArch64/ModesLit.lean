module

public import VerifiedGarbage.Proof.Seed.AArch64.Lit
meta import VerifiedGarbage.Proof.Seed.AArch64.Lit
public import VerifiedGarbage.Impl.Seed.AArch64.Modes
meta import VerifiedGarbage.Impl.Seed.AArch64.Modes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # SEED-CBC, -OFB and -CFB128's AArch64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.Seed.AArch64.cbcEncrypt
materialize_code Impl.Seed.AArch64.cbcDecrypt
materialize_code Impl.Seed.AArch64.ofb
materialize_code Impl.Seed.AArch64.cfbEncrypt
materialize_code Impl.Seed.AArch64.cfbDecrypt

end VG
