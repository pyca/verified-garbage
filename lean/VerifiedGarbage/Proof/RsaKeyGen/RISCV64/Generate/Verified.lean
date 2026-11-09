module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Generate.CT
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Generate.Implies

/-! # The verified key search, for every arithmetic backend (RISC-V) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Generate

open VG VG.RISCV64
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)
open VG.Proof.Rsa.RISCV64 (InvLaw)

/-- The controller, given the inverse's law (`InvLaw`, whose instance the
registration file imports). -/
theorem gen_verified [InvLaw] (v : RoundImpl) :
    Verified target (genCode v) (Spec.RsaKeyGen.keySearchContract (abi.withConsts tables) stackUse) :=
  Verified.of_correct (gen_correct v) (gen_constantTime v) gen_implies

end VG.Proof.RsaKeyGen.RISCV64.Generate
