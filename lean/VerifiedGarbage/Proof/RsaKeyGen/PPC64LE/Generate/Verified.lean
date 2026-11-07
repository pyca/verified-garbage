module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Generate.Correct
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Generate.CT
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Generate.Implies

/-! # The verified key search, for every arithmetic backend (PPC64LE) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Generate

open VG VG.PPC64LE
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Rsa.PPC64LE (InvLaw)

/-- The controller, given the inverse's law (`InvLaw`, whose instance the
registration file imports). -/
theorem gen_verified [InvLaw] (v : RoundImpl) :
    Verified target (genCode v) (Spec.RsaKeyGen.keySearchContract (abi.withConsts tables) stackUse) :=
  Verified.of_correct (gen_correct v) (gen_constantTime v) gen_implies

end VG.Proof.RsaKeyGen.PPC64LE.Generate
