import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee

/-!
# The functions AES-GCM calls on x86-64: VaesVpclmul

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): VAES for the cipher (`vg_aes_ctr32_vaes`, with `vg_aes_expand_key_aesni`) and VPCLMULQDQ for the hash (`vg_ghash_vpclmul`), with counter mode and GHASH interleaved in `vg_aes_gcm_encrypt_blocks_vaes_vpclmul` and `_decrypt_blocks_vaes_vpclmul` (`Impl.Gcm.X86_64.Stitch`, on 256-bit registers, which need no CPU features beyond the callees').
-/

namespace VG.Variants.AesGcm.X86_64.VaesVpclmul

open VG VG.X86_64

/-- The interleaved loops of `Impl.Gcm.X86_64.Stitch`, from their proof. -/
def stitch : Proof.AesGcm.X86_64.StitchImpl where
  suffix := ""
  features := []
  enc := Impl.Gcm.X86_64.Stitch.enc
  dec := Impl.Gcm.X86_64.Stitch.dec
  ok := Proof.Gcm.X86_64.Stitch.stitch_ok
  encP := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide +kernel,
    ⟨_, by taint_decide⟩⟩
  decP := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide +kernel,
    ⟨_, by taint_decide⟩⟩

def variant : Proof.AesGcm.X86_64.GcmVariant := ⟨.vaes, .aesni, .vpclmul, some stitch⟩

end VG.Variants.AesGcm.X86_64.VaesVpclmul
