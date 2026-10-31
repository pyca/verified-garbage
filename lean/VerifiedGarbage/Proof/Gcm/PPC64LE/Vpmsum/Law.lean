module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Ghash

/-! # The proved POWER8 GHASH contract -/

@[expose] public section
namespace VG.Proof.Gcm.PPC64LE
instance : GhashLaw := ⟨Vpmsum.ghash_correct, Vpmsum.ghash_ct⟩
end VG.Proof.Gcm.PPC64LE
