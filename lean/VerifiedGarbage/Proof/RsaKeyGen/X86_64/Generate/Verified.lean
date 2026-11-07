module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Correct
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.CT
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Implies

/-! # The verified key search, for every arithmetic backend -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

/-- The controller, given the key's proof (`Key.keyProof`, which the
registration file imports). -/
theorem gen_verified [Key.KeyProof] (v : RoundImpl) :
    Verified target (genCode v) (Spec.RsaKeyGen.keySearchContract abi stackUse) :=
  Verified.of_correct (gen_correct v) (gen_constantTime v) gen_implies

end VG.Proof.RsaKeyGen.X86_64.Generate
