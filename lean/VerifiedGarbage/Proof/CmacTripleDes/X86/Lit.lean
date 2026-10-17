module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.CmacTripleDes.X86
meta import VerifiedGarbage.Impl.CmacTripleDes.X86
import VerifiedGarbage.Proof.CmacTripleDes.X86.KeysLit
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.KeysLit
import VerifiedGarbage.Proof.CmacTripleDes.X86.RoundLit
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.RoundLit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-! # TDEA-CMAC's x86 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.CmacTripleDes.X86.init
materialize_code Impl.CmacTripleDes.X86.update
materialize_code Impl.CmacTripleDes.X86.finalize

end VG
