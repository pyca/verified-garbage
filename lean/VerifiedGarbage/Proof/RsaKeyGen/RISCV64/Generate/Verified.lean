module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Generate.CT
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Generate.Implies
public import VerifiedGarbage.Proof.Variants.MillerRabin.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved

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

/-- What `Scrub.scrubOf` needs of the key search with each Miller-Rabin
round: evaluated here. -/
theorem keySearchSide (v : RoundImpl) (hv : v ∈ Proof.Variants.MillerRabin.RISCV64.variants) :
    Scrub.scrubSide (genCode v) stackUse (Spec.RsaKeyGen.keySearchSig.retBits 64) [] = true := by
  have h : (Proof.Variants.MillerRabin.RISCV64.variants.all fun v =>
      Scrub.scrubSide (genCode v) stackUse (Spec.RsaKeyGen.keySearchSig.retBits 64) []) = true := by
    lit_decide
  exact List.all_eq_true.mp h v hv

end VG.Proof.RsaKeyGen.RISCV64.Generate
