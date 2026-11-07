module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Instance
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Shared

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on x86-64 -/

@[expose] public section

namespace VG.Generic.ChaCha20Xor.X86_64.ChaCha20Poly1305

open VG.Proof.ChaCha20Poly1305.X86_64

/-- The CPU features an instance requires: those of both implementations. -/
def features (v : Proof.ChaCha20.X86_64.XorImpl) : List String :=
  (v.features ++ v.poly.features).eraseDups

/-- The CPU features `open` requires: with the IFMA implementation of
`vg_poly1305_blocks`, those of `vg_chacha20_xor_avx512vl` too, which its
window calls. -/
def openFeatures (v : Proof.ChaCha20.X86_64.XorImpl) : List String :=
  match v.poly with
  | .ifma => (features v ++ Proof.ChaCha20.X86_64.XorImpl.avx512vl.features).eraseDups
  | _ => features v

def artifacts (v : Proof.ChaCha20.X86_64.XorImpl) : List Artifact := [
  Spec.ChaCha20Poly1305.sealApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.ChaCha20Poly1305.X86_64.Shared.sealCode v.callee v.poly
    stack := 1768
    verified := Shared.seal_verified v
    spSafe := Shared.seal_sp v
    features := features v },
  Spec.ChaCha20Poly1305.openZeroApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.ChaCha20Poly1305.X86_64.Shared.openCode v.callee v.poly
    stack := 1768
    verified := Shared.open_verified v
    spSafe := Shared.open_sp v
    features := openFeatures v },
  Spec.ChaCha20Poly1305.sealGatherApi.artifact X86_64.target {
    suffix := v.suffix
    code := Gather.gatherCode v
    stack := 1880
    verified := Gather.gather_verified v
    spSafe := Gather.gather_spSafe v
    features := features v }]

end VG.Generic.ChaCha20Xor.X86_64.ChaCha20Poly1305
