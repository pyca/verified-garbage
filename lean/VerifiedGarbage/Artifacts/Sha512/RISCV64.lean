module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha512.RISCV64.Shared
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha384
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_224
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_256
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sha512.RISCV64

def artifacts : List Artifact := [
  Spec.Sha512.init384Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_384
    verified := Proof.Sha512.RISCV64.Shared.init384 },
  Spec.Sha512.init512Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_512
    verified := Proof.Sha512.RISCV64.Shared.init512 },
  Spec.Sha512.init512_224Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_512_224
    verified := Proof.Sha512.RISCV64.Shared.init512_224 },
  Spec.Sha512.init512_256Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_512_256
    verified := Proof.Sha512.RISCV64.Shared.init512_256 },
  Spec.Sha512.updateApi.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.update
    stack := 208
    verified := Proof.Sha512.RISCV64.Shared.update },
  Spec.Sha512.finalizeApi.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.finalize
    stack := 208
    verified := Proof.Sha512.RISCV64.Shared.finalize },
  Spec.Sha512.finalize384Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.finalize384
    stack := 208
    verified := Proof.Sha512.RISCV64.Shared.finalize384 },
  Spec.Sha512.finalize512_256Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.finalize512_256
    stack := 208
    verified := Proof.Sha512.RISCV64.Shared.finalize512_256 },
  Spec.Sha512.finalize512_224Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.finalize512_224
    stack := 208
    verified := Proof.Sha512.RISCV64.Shared.finalize512_224 },
  Spec.Sha512.digest384Api.artifact RISCV64.target {
    code := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha384.hash
    stack := Impl.MdStream.RISCV64.Digest.dbytes Proof.Hmac.Stream.RISCV64.Sha384.hash + Proof.Hmac.Stream.RISCV64.Sha384.hash.F
    verified := Proof.Hmac.Stream.RISCV64.Sha384.digest },
  Spec.Sha512.digest512Api.artifact RISCV64.target {
    code := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha512.hash
    stack := Impl.MdStream.RISCV64.Digest.dbytes Proof.Hmac.Stream.RISCV64.Sha512.hash + Proof.Hmac.Stream.RISCV64.Sha512.hash.F
    verified := Proof.Hmac.Stream.RISCV64.Sha512.digest },
  Spec.Sha512.digest512_224Api.artifact RISCV64.target {
    code := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha512_224.hash
    stack := Impl.MdStream.RISCV64.Digest.dbytes Proof.Hmac.Stream.RISCV64.Sha512_224.hash + Proof.Hmac.Stream.RISCV64.Sha512_224.hash.F
    verified := Proof.Hmac.Stream.RISCV64.Sha512_224.digest },
  Spec.Sha512.digest512_256Api.artifact RISCV64.target {
    code := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha512_256.hash
    stack := Impl.MdStream.RISCV64.Digest.dbytes Proof.Hmac.Stream.RISCV64.Sha512_256.hash + Proof.Hmac.Stream.RISCV64.Sha512_256.hash.F
    verified := Proof.Hmac.Stream.RISCV64.Sha512_256.digest }]

end VG.Artifacts.Sha512.RISCV64
