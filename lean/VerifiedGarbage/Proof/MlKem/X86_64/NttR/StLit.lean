module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Sym
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Sym
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Words

/-!
# ML-KEM on x86-64: the NTT on registers, the machine's states as literals

`ToExpr` for the terms and states of `Sym.run`, so that `materialize_value`
writes the state after a part of the run as a literal (`RunA.lean`), and
the kernel checks each part of the run in a declaration of its own.
-/

public meta section

namespace VG.Proof.MlKem.X86_64.NttR

deriving instance Lean.ToExpr for E
deriving instance Lean.ToExpr for St

end VG.Proof.MlKem.X86_64.NttR
