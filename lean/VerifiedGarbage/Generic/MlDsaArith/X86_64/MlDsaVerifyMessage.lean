module

import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyFn
import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.X86_64.Message
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Prims
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyVerified
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyFn
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyVerified
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.MlDsa.Pack.Arith
public import VerifiedGarbage.Proof.MlDsa.Pack.Stream
public import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
public import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
public import VerifiedGarbage.Proof.MlDsa.Verify.Mem
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.HashCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCorrect
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignVerified
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyCorrect
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintUnpack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseCCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseDCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseKCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.SignCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTCompute
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTSample
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTStages
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Control
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Correct
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Verified
public import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.HashCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCorrect
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignVerified
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyCorrect
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintUnpack
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseCCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseKCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.SignCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTCompute
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTSample
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTStages
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Control
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Correct
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Verified
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress

/-!
# ML-DSA (FIPS 204) on x86-64: verifying messages

A generic file (see `TCB/Emit.lean`): the artifacts it lists, which call
`vg_mldsa*_verify` with an implementation `v` of the polynomial arithmetic
(`Variants/MlDsaArith/X86_64/`), are emitted once for each implementation,
named with its suffix (e.g. `vg_mldsa44_verify_message_avx2`), and need its CPU
features. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

@[expose] public section

namespace VG.Generic.MlDsaArith.X86_64.MlDsaVerifyMessage

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.Verify (primsWith prims_okWith verify_spSafe)
open VG.Proof.MlDsa.X86_64.Message (verifyFn verifyMessage_verified verifyMessage_spSafe)

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function keeps its arguments in a frame of 72 bytes on the stack, and its calls use the 40 \
    bytes of stack below the frame. It computes `tr = H(pk, 64)` and then the message representative with the SHAKE256 sponge \
    (`vg_keccak_absorb`, `vg_keccak_pad`, `vg_keccak_squeeze`) in the last 1 KiB of `scratch`, and \
    calls the verification function on it, which uses the rest of `scratch`."]

def artifacts (v : ArithImpl) : List Artifact := [
  Spec.MlDsa.verifyMessage44Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    notes := notes
    code := Impl.MlDsa.X86_64.Message.verifyMessage (Spec.MlDsa.verify44Api.name ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    stack := 112
    verified := verifyMessage_verified (verifyFn v (List.mem_cons_self ..)) (List.mem_cons_self ..)
    spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_self ..)) },
  Spec.MlDsa.verifyMessage65Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    notes := notes
    code := Impl.MlDsa.X86_64.Message.verifyMessage (Spec.MlDsa.verify65Api.name ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    stack := 112
    verified := verifyMessage_verified (verifyFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))) },
  Spec.MlDsa.verifyMessage87Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    notes := notes
    code := Impl.MlDsa.X86_64.Message.verifyMessage (Spec.MlDsa.verify87Api.name ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    stack := 112
    verified := verifyMessage_verified (verifyFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) }]

end VG.Generic.MlDsaArith.X86_64.MlDsaVerifyMessage
