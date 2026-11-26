module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
import VerifiedGarbage.Proof.X448.X86_64.Lit
import VerifiedGarbage.Proof.X448.X86_64.Instances
import VerifiedGarbage.Proof.X448.X86_64.Exchange
import VerifiedGarbage.Proof.X448.X86_64.Scrub
import VerifiedGarbage.Proof.Variants.Curve448Field.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # X448 (RFC 7748) on x86-64 -/

namespace VG.Artifacts.X448.X86_64

public def artifacts : List (Artifact X86_64.target) :=
  VG.Proof.Variants.Curve448Field.X86_64.variants.flatMap fun (v : Impl.Ed448.X86_64.FieldVariant) => [
    Spec.X448.exchangeApi.artifact X86_64.target
      { suffix := v.suffix
        code := Impl.X448.X86_64.Fn.x448 v
        verified := Proof.X448.X86_64.exchange_scrubbed v
        spSafe := Proof.X448.X86_64.exchange_spSafe v },
    Spec.X448.x448BaseApi.artifact X86_64.target
      { suffix := v.suffix
        code := Impl.X448.X86_64.Fn.x448Base v
        verified := Proof.X448.X86_64.base_scrubbed v
        spSafe := Proof.X448.X86_64.base_spSafe v }]

spec_apis artifacts

end VG.Artifacts.X448.X86_64
