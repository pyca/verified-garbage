module

public import VerifiedGarbage.Proof.MlDsa.X86.Message.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.MlDsa.DecideAt
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds
public import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign
public import VerifiedGarbage.Proof.MlDsa.X86.Message.Verify
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Verified
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Ball
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Final
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Local
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Row
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Top
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Verified
public import VerifiedGarbage.Proof.MlKem.X86.CheckEkBody
public import VerifiedGarbage.Proof.MlKem.X86.EncV
public import VerifiedGarbage.Proof.MlKem.X86.NttSetup
public import VerifiedGarbage.Proof.MlKem.X86.Table
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds
import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign
import VerifiedGarbage.Proof.MlDsa.X86.Message.Verify
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Ball
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Final
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Local
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Row
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Top
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Verified
import VerifiedGarbage.Proof.MlKem.X86.CheckEkBody
import VerifiedGarbage.Proof.MlKem.X86.EncV
import VerifiedGarbage.Proof.MlKem.X86.NttSetup
import VerifiedGarbage.Proof.MlKem.X86.Table

/-!
# ML-DSA (FIPS 204) on x86 (32-bit): verifying messages

A registration file (see `TCB/Emit.lean`): the artifacts it lists are emitted.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller to
the contract; check them against the contract's `pre`/`post`. Each artifact is
made from its function's `Api` (in `Spec/MlDsa/Contract.lean`, reviewed with
the contract). The emitter adds the `# Safety` items that depend on the target
(`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks against
the contract.

The function saves its caller's registers in a frame of 16 bytes below the
return address; below that, its calls push at most 4 arguments and the return
address, and the verification function on `μ` uses 96 bytes
(`stack := 16 + 16 + 4 + 96 = 132`).
-/

@[expose] public section

namespace VG.Artifacts.MlDsaVerifyMessage.X86

open VG

def artifacts : List Artifact := [
  Spec.MlDsa.verifyMessage44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Message.verifyMessage Spec.MlDsa.verify44Api.name
      Impl.MlDsa.X86.Verify.verify44 Spec.MlDsa.mlDsa44
    stack := 132
    verified := Proof.MlDsa.X86.Message.verifyMessage44_verified },
  Spec.MlDsa.verifyMessage65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Message.verifyMessage Spec.MlDsa.verify65Api.name
      Impl.MlDsa.X86.Verify.verify65 Spec.MlDsa.mlDsa65
    stack := 132
    verified := Proof.MlDsa.X86.Message.verifyMessage65_verified },
  Spec.MlDsa.verifyMessage87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Message.verifyMessage Spec.MlDsa.verify87Api.name
      Impl.MlDsa.X86.Verify.verify87 Spec.MlDsa.mlDsa87
    stack := 132
    verified := Proof.MlDsa.X86.Message.verifyMessage87_verified }]

end VG.Artifacts.MlDsaVerifyMessage.X86
