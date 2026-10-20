module

public import VerifiedGarbage.Proof.X448.X86_64.Lit
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
public import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X448.X86_64.Lit
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
meta import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# Ed448 verification's equation on x86-64: the code as literals

The kernel checks each literal once; the taint and instruction checks reuse
them. The pieces come first, so that the whole function's literal calls theirs.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64

materialize_code verifyRootLit := (rootCall Impl.X448.X86_64.baseline : Prog isa)
materialize_code verifyDecodeALit :=
  (decode Impl.X448.X86_64.baseline 6 7 (rootCall Impl.X448.X86_64.baseline) : Prog isa)
materialize_code verifyDecodeLit :=
  (vdecode Impl.X448.X86_64.baseline (rootCall Impl.X448.X86_64.baseline) : Prog isa)
materialize_code verifyLoopLit := (vloop Point64.calls : Prog isa)
materialize_code verifyFinishLit := (vfinish Impl.X448.X86_64.baseline Point64.calls : Prog isa)

end VG.Proof.Ed448.X86_64

namespace VG

materialize_code Impl.Ed448.X86_64.verifyEquation

end VG

namespace VG.Proof.Ed448.X86_64

theorem verifyEquation_inlineOk : Impl.Ed448.X86_64.verifyEquation.InlineOk = true := by lit_decide

end VG.Proof.Ed448.X86_64
