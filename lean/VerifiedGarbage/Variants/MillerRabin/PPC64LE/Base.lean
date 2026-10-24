module

public import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE.Base

/-! # The baseline shared Miller–Rabin round on PPC64LE -/

@[expose] public section
namespace VG.Variants.MillerRabin.PPC64LE.Base

def variant : Proof.MillerRabin.PPC64LE.RoundImpl := Proof.Variants.MillerRabin.PPC64LE.Base.variant

end VG.Variants.MillerRabin.PPC64LE.Base
