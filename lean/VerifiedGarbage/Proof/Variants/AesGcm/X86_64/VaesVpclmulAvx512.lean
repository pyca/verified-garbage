module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Lit
meta import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Lit
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Spec.TripleDes
meta import VerifiedGarbage.Impl.Gcm.X86_64
meta import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
meta import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Spec.TripleDes

/-!
# The functions AES-GCM calls on x86-64: VaesVpclmulAvx512: the variant's code and proofs

The variant `VG.Variants.AesGcm.X86_64.VaesVpclmulAvx512.variant`
(`Variants/AesGcm/X86_64/VaesVpclmulAvx512.lean`), with the proofs its
interface asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.AesGcm.X86_64.VaesVpclmulAvx512

open VG VG.X86_64

/-- The interleaved loops of `Impl.Gcm.X86_64.StitchZ` (their proof is `StitchName.ok`). -/
def stitch : Proof.AesGcm.X86_64.StitchPart := by
  refine {
    name := .vaesAvx512
    suffix := "_avx512"
    features := ["avx512f", "avx512bw"]
    encP := ((⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchZ.enc))
    decP := ((⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchZ.dec))
    pieceP := (some
      ⟨(⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchZP.enc),
       (⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchZP.dec)⟩)
    pieceR := (some
      ⟨(⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchZH.encR true true),
       (⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩ : Proof.AesGcm.X86_64.Piece Impl.Gcm.X86_64.StitchZH.decR true true)⟩)
    toPart := some
      { name := .vaesAvx512
        piece := (⟨?_, ?_, ?_, ?_, ?_,
          ⟨?_, ?_⟩⟩)
        pieceP := (some ⟨⟨?_, ?_, ?_, ?_, ?_,
          ⟨?_, ?_⟩⟩⟩)
        pieceR := (some ⟨⟨?_, ?_, ?_, ?_, ?_,
          ⟨?_, ?_⟩⟩⟩) } }
  taint_decide_all

def variant : Proof.AesGcm.X86_64.GcmVariant := ⟨.vaes, .aesni, .vpclmul, some stitch⟩

end VG.Proof.Variants.AesGcm.X86_64.VaesVpclmulAvx512
