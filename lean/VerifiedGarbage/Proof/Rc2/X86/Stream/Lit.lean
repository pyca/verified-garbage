module

public import VerifiedGarbage.Impl.Rc2.X86.Stream
meta import VerifiedGarbage.Impl.Rc2.X86.Stream
public import VerifiedGarbage.Proof.Rc2.X86.Cbc.Lit
meta import VerifiedGarbage.Proof.Rc2.X86.Cbc.Lit
public import VerifiedGarbage.Proof.Rc2.X86.KeyLit
meta import VerifiedGarbage.Proof.Rc2.X86.KeyLit
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

/-! # Streaming RC2-CBC on x86 (32-bit): the code as literals -/

@[expose] public section

namespace VG.Impl.Rc2.X86.Stream
materialize_code init
materialize_code encryptUpdate
materialize_code decryptUpdate
end VG.Impl.Rc2.X86.Stream
