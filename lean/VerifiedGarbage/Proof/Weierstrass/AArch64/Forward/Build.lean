module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Data
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Certificate
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Util.CompileInductive
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Impl.Mont.AArch64
import VerifiedGarbage.Spec.Weierstrass.Mont

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64


end VG.Proof.Weierstrass.AArch64.Forward
