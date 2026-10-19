module

public import VerifiedGarbage.Impl.CmacTripleDes.X86
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.CmacTripleDes.X86
import VerifiedGarbage.Proof.CmacTripleDes.X86.KeysLit
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.KeysLit
import VerifiedGarbage.Proof.CmacTripleDes.X86.RoundLit
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.RoundLit
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

/-! # TDEA-CMAC's x86 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.CmacTripleDes.X86.init
materialize_code Impl.CmacTripleDes.X86.update
materialize_code Impl.CmacTripleDes.X86.finalize

end VG
