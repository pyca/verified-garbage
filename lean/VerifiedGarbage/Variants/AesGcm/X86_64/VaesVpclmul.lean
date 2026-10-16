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
# The functions AES-GCM calls on x86-64: VaesVpclmul

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): VAES for the cipher (`vg_aes_ctr32_vaes`, with `vg_aes_expand_key_scratch_aesni`) and VPCLMULQDQ for the hash (`vg_ghash_vpclmul`), with counter mode and GHASH interleaved in `vg_aes_gcm_encrypt_blocks_vaes_vpclmul` and `_decrypt_blocks_vaes_vpclmul` (`Impl.Gcm.X86_64.Stitch`, on 256-bit registers, which need no CPU features beyond the callees'), and out of place in `vg_aes_gcm_encrypt_blocks_to_vaes_vpclmul` (`Impl.Gcm.X86_64.StitchTo`).
-/

@[expose] public section

namespace VG.Variants.AesGcm.X86_64.VaesVpclmul

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

end VG.Variants.AesGcm.X86_64.VaesVpclmul
