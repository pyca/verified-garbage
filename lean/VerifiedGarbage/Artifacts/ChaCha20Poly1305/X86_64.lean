module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Instance
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Shared
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.OpenTo
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.ScrubFn
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Fn
import VerifiedGarbage.Proof.Variants.ChaCha20Xor.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on x86-64 -/

namespace VG.Artifacts.ChaCha20Poly1305.X86_64

open VG.Proof.ChaCha20Poly1305.X86_64

public def artifacts : List (Artifact X86_64.target) :=
  VG.Proof.Variants.ChaCha20Xor.X86_64.variants.flatMap fun (v : Proof.ChaCha20.X86_64.XorImpl) => [
    Spec.ChaCha20Poly1305.sealApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.ChaCha20Poly1305.X86_64.Fn.seal (ScrubFn.cpLevel v) v.callee v.poly
      verified := Proof.ChaCha20Poly1305.X86_64.ScrubFn.seal_scrubbed v
      spSafe := Proof.ChaCha20Poly1305.X86_64.ScrubFn.seal_spSafeFn v },
    Spec.ChaCha20Poly1305.openZeroApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.ChaCha20Poly1305.X86_64.Fn.open (ScrubFn.cpLevel v) v.callee v.poly
      verified := Proof.ChaCha20Poly1305.X86_64.ScrubFn.open_scrubbed v
      spSafe := Proof.ChaCha20Poly1305.X86_64.ScrubFn.open_spSafeFn v },
    Spec.ChaCha20Poly1305.openToApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.ChaCha20Poly1305.X86_64.Fn.openTo (ScrubFn.cpLevel v) v.callee v.poly
      verified := Proof.ChaCha20Poly1305.X86_64.ScrubFn.openTo_scrubbed v
      spSafe := Proof.ChaCha20Poly1305.X86_64.ScrubFn.openTo_spSafeFn v },
    Spec.ChaCha20Poly1305.sealGatherApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.ChaCha20Poly1305.X86_64.Fn.sealGather (ScrubFn.cpLevel v) (ScrubFn.sealName v)
        (ScrubFn.splitName v) v.callee v.poly
      verified := Proof.ChaCha20Poly1305.X86_64.ScrubFn.gather_scrubbed v
      spSafe := Proof.ChaCha20Poly1305.X86_64.ScrubFn.gather_spSafeFn v }]

spec_apis artifacts

end VG.Artifacts.ChaCha20Poly1305.X86_64
