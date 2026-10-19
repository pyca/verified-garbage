module

import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Util.CompileInductive
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.Words
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Scalar
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Data
public import VerifiedGarbage.TCB.AArch64.Target

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64


end VG.Proof.Weierstrass.AArch64.Forward
