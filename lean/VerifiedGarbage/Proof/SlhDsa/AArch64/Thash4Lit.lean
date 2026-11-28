module

-- separate module: the literals of every `thash4`, which its checks and its callers' evaluate

public import VerifiedGarbage.Impl.SlhDsa.AArch64.Thash4
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.SlhDsa.AArch64.Thash4
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # SLH-DSA on AArch64: the code of each `thash4`, as literals -/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Thash4Lit

open VG.AArch64

materialize_code scalar16 := Impl.SlhDsa.AArch64.Thash4.thash4 16 false
materialize_code scalar24 := Impl.SlhDsa.AArch64.Thash4.thash4 24 false
materialize_code scalar32 := Impl.SlhDsa.AArch64.Thash4.thash4 32 false
materialize_code sha3_16 := Impl.SlhDsa.AArch64.Thash4.thash4 16 true
materialize_code sha3_24 := Impl.SlhDsa.AArch64.Thash4.thash4 24 true
materialize_code sha3_32 := Impl.SlhDsa.AArch64.Thash4.thash4 32 true

end VG.Proof.SlhDsa.AArch64.Thash4Lit
