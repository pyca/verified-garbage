module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Fn
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Backend
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.Rsa.RISCV64.IbInverse
public import VerifiedGarbage.Proof.Divstep.TcSBounds

/-! # RSA key generation (FIPS 186-5 A.1.3) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.RISCV64

def direct : List Artifact := [
  Spec.RsaKeyGen.keyInitApi.artifact RISCV64.target {
    code := Impl.RsaKeyGen.RISCV64.KeyInit.Fn.init
    verified := .scrubbed Proof.RsaKeyGen.RISCV64.Fn.init_scrubbed }]

def artifacts : List Artifact :=
  direct ++ Proof.RsaKeyGen.RISCV64.Fn.keySearchRegs.map (Spec.RsaKeyGen.keySearchApi.artifact RISCV64.target)

end VG.Artifacts.RsaKeyGen.RISCV64
