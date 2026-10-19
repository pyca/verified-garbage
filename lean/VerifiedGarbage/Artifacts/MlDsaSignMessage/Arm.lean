module

import VerifiedGarbage.Proof.MlDsa.Arm.Message.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.Arm.Message
public import VerifiedGarbage.Impl.MlDsa.Arm.Sign.Sign
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Lay
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.Verified
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.HashCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCorrect
public import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Ball
public import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.BlockTr
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseCCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseDCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseKCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseOCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.SignCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Control
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Row
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Top
public import VerifiedGarbage.Proof.MlDsa.Pack.Arith
public import VerifiedGarbage.Proof.MlDsa.Pack.Stream
public import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlDsa.Arm.Message.HashCT
import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCT
import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCT
import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCorrect
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.BlockTr
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseCCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseKCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseOCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.SignCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Control
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Row
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Top
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds

/-!
# ML-DSA (FIPS 204) on 32-bit ARM: signing messages

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

@[expose] public section

namespace VG.Artifacts.MlDsaSignMessage.Arm

open VG

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's `r7` and `lr` and its arguments in the last 1 KiB of `scratch` \
    (keeping the caller's `r7` in the first word of `scratch` while it computes that address), and \
    pushes nothing of its own but the fifth argument of the signing function on `μ`, with `lr`; the functions it calls use the 36 bytes of stack below the \
    stack pointer. It computes the message representative with the SHAKE256 sponge \
    (`vg_keccak_absorb`, `vg_keccak_pad`, `vg_keccak_squeeze`) in that 1 KiB, and calls the \
    signing function on it, which uses the rest of `scratch`."]

def artifacts : List Artifact := [
  Spec.MlDsa.signMessage44Api.artifact Arm.target {
    notes := notes
    code := Impl.MlDsa.Arm.Message.signMessage Spec.MlDsa.sign44Api.name
      (Impl.MlDsa.Arm.Sign.sign Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    stack := 36
    verified := Proof.MlDsa.Arm.Message.signMessage_verified Proof.MlDsa.Arm.Message.sign44Fn
      (List.mem_cons_self ..) },
  Spec.MlDsa.signMessage65Api.artifact Arm.target {
    notes := notes
    code := Impl.MlDsa.Arm.Message.signMessage Spec.MlDsa.sign65Api.name
      (Impl.MlDsa.Arm.Sign.sign Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    stack := 36
    verified := Proof.MlDsa.Arm.Message.signMessage_verified Proof.MlDsa.Arm.Message.sign65Fn
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) },
  Spec.MlDsa.signMessage87Api.artifact Arm.target {
    notes := notes
    code := Impl.MlDsa.Arm.Message.signMessage Spec.MlDsa.sign87Api.name
      (Impl.MlDsa.Arm.Sign.sign Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    stack := 36
    verified := Proof.MlDsa.Arm.Message.signMessage_verified Proof.MlDsa.Arm.Message.sign87Fn
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) }]

end VG.Artifacts.MlDsaSignMessage.Arm
