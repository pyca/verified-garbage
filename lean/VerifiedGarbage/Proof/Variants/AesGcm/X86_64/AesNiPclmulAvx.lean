module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Ct

/-!
# The functions AES-GCM calls on x86-64: AesNiPclmulAvx: the variant's code and proofs

The variant `VG.Variants.AesGcm.X86_64.AesNiPclmulAvx.variant`
(`Variants/AesGcm/X86_64/AesNiPclmulAvx.lean`), with the proofs its interface
asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.AesGcm.X86_64.AesNiPclmulAvx

open VG VG.X86_64

/-- The eight-state interleaved loops of `Impl.Gcm.X86_64.StitchAvx8` (their proof is `StitchName.ok`). -/
def stitch : Proof.AesGcm.X86_64.StitchPart where
  name := .aesniAvx
  suffix := "_avx"
  features := ["avx"]
  encP := Proof.Gcm.X86_64.StitchAvx8.enc_piece
  decP := Proof.Gcm.X86_64.StitchAvx8.dec_piece
  pieceR := some ⟨Proof.Gcm.X86_64.StitchAvx8.encR_piece, Proof.Gcm.X86_64.StitchAvx8.decR_piece⟩
  toPart := some
    { name := .aesniAvx
      piece := Proof.Gcm.X86_64.StitchAvx8.encTo_piece
      pieceR := some ⟨Proof.Gcm.X86_64.StitchAvx8.encToR_piece⟩ }

def variant : Proof.AesGcm.X86_64.GcmVariant := ⟨.aesni, .aesni, .pclmul, some stitch⟩

end VG.Proof.Variants.AesGcm.X86_64.AesNiPclmulAvx
