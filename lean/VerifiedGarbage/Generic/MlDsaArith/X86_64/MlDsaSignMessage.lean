module

import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignFn
import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.X86_64.Message
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Sign
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignVerified
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified

/-!
# ML-DSA (FIPS 204) on x86-64: signing messages

A generic file (see `TCB/Emit.lean`): the artifacts it lists, which call
`vg_mldsa*_sign` with an implementation `v` of the polynomial arithmetic
(`Variants/MlDsaArith/X86_64/`), are emitted once for each implementation,
named with its suffix (e.g. `vg_mldsa44_sign_message_avx2`), and need its CPU
features. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

@[expose] public section

namespace VG.Generic.MlDsaArith.X86_64.MlDsaSignMessage

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.Sign (primsWith)
open VG.Proof.MlDsa.X86_64.Message (signFn signMessage_verified signMessage_spSafe)

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function keeps its arguments in a frame of 72 bytes on the stack, and its calls use the 40 \
    bytes of stack below the frame. It computes the message representative with the SHAKE256 sponge \
    (`vg_keccak_absorb`, `vg_keccak_pad`, `vg_keccak_squeeze`) in the last 1 KiB of `scratch`, and \
    calls the signing function on it, which uses the rest of `scratch`."]

def artifacts (v : ArithImpl) : List Artifact := [
  Spec.MlDsa.signMessage44Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    notes := notes
    code := Impl.MlDsa.X86_64.Message.signMessage (Spec.MlDsa.sign44Api.name ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    stack := 112
    verified := signMessage_verified (signFn v (List.mem_cons_self ..)) (List.mem_cons_self ..)
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) },
  Spec.MlDsa.signMessage65Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    notes := notes
    code := Impl.MlDsa.X86_64.Message.signMessage (Spec.MlDsa.sign65Api.name ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    stack := 112
    verified := signMessage_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) },
  Spec.MlDsa.signMessage87Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    notes := notes
    code := Impl.MlDsa.X86_64.Message.signMessage (Spec.MlDsa.sign87Api.name ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    stack := 112
    verified := signMessage_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) }]

end VG.Generic.MlDsaArith.X86_64.MlDsaSignMessage
