module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Lit
meta import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Lit
import VerifiedGarbage.Spec.TripleDes
meta import VerifiedGarbage.Spec.TripleDes

/-!
# The functions AES-GCM calls on x86-64: VaesVpclmul: the variant's code and proofs

The variant `VG.Variants.AesGcm.X86_64.VaesVpclmul.variant`
(`Variants/AesGcm/X86_64/VaesVpclmul.lean`), with the proofs its interface
asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul

open VG VG.X86_64

/-- The interleaved loops of `Impl.Gcm.X86_64.Stitch` (their proof is `StitchName.ok`). -/
def stitch : Proof.AesGcm.X86_64.StitchPart := by
  refine {
    name := .vaes
    suffix := ""
    features := []
    encP := ((⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.Stitch.enc))
    decP := ((⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.Stitch.dec))
    pieceR := (some
      ⟨(⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchR.enc true false),
       (⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchR.decR true true)⟩)
    toPart := some
      { name := .vaes
        piece := (⟨?_, ?_, ?_, ?_, ?_,
          ⟨?_, ?_⟩⟩)
        pieceR := (some ⟨⟨?_, ?_, ?_, ?_, ?_,
          ⟨?_, ?_⟩⟩⟩) } }
  taint_decide_all

def variant : Proof.AesGcm.X86_64.GcmVariant := ⟨.vaes, .aesni, .vpclmul, some stitch⟩

end VG.Proof.Variants.AesGcm.X86_64.VaesVpclmul
