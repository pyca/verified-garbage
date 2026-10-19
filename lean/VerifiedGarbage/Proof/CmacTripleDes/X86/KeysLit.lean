module

public import VerifiedGarbage.Impl.CmacTripleDes.X86.Round
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.CmacTripleDes.X86.Round
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
meta import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
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

/-! # The key schedule's code as a literal, for kernel-evaluated checks

Evaluated once, here: the checks of `Keys.lean` and the literal of `init`
(`Lit.lean`), which runs it, read it. -/

@[expose] public section

namespace VG

materialize_value Impl.CmacTripleDes.X86.roundKeys

theorem Proof.CmacTripleDes.X86.roundKeys_eq :
    Impl.CmacTripleDes.X86.roundKeys = Impl.CmacTripleDes.X86.roundKeys.lit :=
  Impl.CmacTripleDes.X86.roundKeys.lit_eq

end VG
