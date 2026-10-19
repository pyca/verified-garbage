module

public import VerifiedGarbage.Impl.Rc2.X86.Cbc
meta import VerifiedGarbage.Impl.Rc2.X86.Cbc
public import VerifiedGarbage.Proof.Rc2.X86.Lit
meta import VerifiedGarbage.Proof.Rc2.X86.Lit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import Mathlib.Util.CompileInductive
meta import Mathlib.Util.CompileInductive
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Rc2.X86.ExpandKey
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Impl.Rc2.X86.ExpandKey
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

@[expose] public section

namespace VG.Impl.Rc2.X86.Cbc
materialize_code encrypt
materialize_code decrypt
end VG.Impl.Rc2.X86.Cbc
