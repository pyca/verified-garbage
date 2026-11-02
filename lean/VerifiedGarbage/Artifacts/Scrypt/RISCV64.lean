module

public import VerifiedGarbage.Proof.Scrypt.RISCV64.BlockMix
public import VerifiedGarbage.Proof.Scrypt.RISCV64.RoMix
public import VerifiedGarbage.Proof.Scrypt.RISCV64.Whole.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # scrypt (RFC 7914): Salsa20/8, scryptBlockMix, scryptROMix and scrypt on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Scrypt.RISCV64

def artifacts : List Artifact := [
  Spec.Scrypt.scryptApi.artifact RISCV64.target {
    code := Impl.Scrypt.RISCV64.Whole.scrypt Proof.Scrypt.RISCV64.Whole.pbkName
      Proof.Scrypt.RISCV64.Whole.pbkCode
    stack := 1248
    verified := Proof.Scrypt.RISCV64.Whole.scrypt_verified }]

end VG.Artifacts.Scrypt.RISCV64
