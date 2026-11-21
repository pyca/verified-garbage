module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Hkdf.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Variants.MdHash.RISCV64
public import VerifiedGarbage.Impl.Hkdf.RISCV64.Fn
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # HKDF (RFC 5869) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Hkdf.RISCV64

open VG.Proof.HmacTable.RISCV64 (tables)
open VG.Proof.Variants.MdHash.RISCV64 (variants fns)

def artifacts : List Artifact := [
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

end VG.Artifacts.Hkdf.RISCV64
