module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hkdf.Table
import VerifiedGarbage.Proof.Hkdf.RISCV64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.MdHash.RISCV64
import VerifiedGarbage.Impl.Hkdf.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HKDF (RFC 5869) on RISC-V -/

namespace VG.Artifacts.Hkdf.RISCV64

open VG.Proof.HmacTable.RISCV64 (tables)
open VG.Proof.Variants.MdHash.RISCV64 (variants fns)

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Hkdf.extractApi.artifact RISCV64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Hkdf.RISCV64.Fn.extract fns
    verified := Proof.Hkdf.RISCV64.Scrub.extract_scrubbedV },
  Spec.Hkdf.keyApi.artifact RISCV64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Hkdf.RISCV64.Fn.key fns
    verified := Proof.Hkdf.RISCV64.Scrub.key_scrubbedV },
  Spec.Hkdf.expandApi.artifact RISCV64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Hkdf.RISCV64.Fn.expand fns
    verified := Proof.Hkdf.RISCV64.Scrub.expand_scrubbedV }]

spec_apis artifacts

end VG.Artifacts.Hkdf.RISCV64
