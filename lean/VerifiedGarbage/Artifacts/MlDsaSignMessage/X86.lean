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
# ML-DSA (FIPS 204) on x86 (32-bit): signing messages

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

The function saves its caller's registers in a frame of 16 bytes below the
return address; below that, its calls push at most 5 arguments and the return
address, and the signing function on `μ` uses 96 bytes
(`stack := 16 + 20 + 4 + 96 = 136`).
-/

@[expose] public section

namespace VG.Artifacts.MlDsaSignMessage.X86

open VG

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's callee-saved registers in a frame of 16 bytes, and keeps the \
    address of the last 1 KiB of `scratch` in `esi`. It computes the message representative with \
    the SHAKE256 sponge (`vg_keccak_absorb`, `vg_keccak_pad`, `vg_keccak_squeeze`) in that 1 KiB, \
    and calls the signing function on it, which uses the rest of `scratch`."]

def artifacts : List Artifact := [
  Spec.MlDsa.signMessage44Api.artifact X86.target {
    notes := notes
    code := Impl.MlDsa.X86.Message.signMessage Spec.MlDsa.sign44Api.name
      (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    stack := 136
    verified := Proof.MlDsa.X86.Message.signMessage44_verified },
  Spec.MlDsa.signMessage65Api.artifact X86.target {
    notes := notes
    code := Impl.MlDsa.X86.Message.signMessage Spec.MlDsa.sign65Api.name
      (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    stack := 136
    verified := Proof.MlDsa.X86.Message.signMessage65_verified },
  Spec.MlDsa.signMessage87Api.artifact X86.target {
    notes := notes
    code := Impl.MlDsa.X86.Message.signMessage Spec.MlDsa.sign87Api.name
      (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    stack := 136
    verified := Proof.MlDsa.X86.Message.signMessage87_verified }]

end VG.Artifacts.MlDsaSignMessage.X86
