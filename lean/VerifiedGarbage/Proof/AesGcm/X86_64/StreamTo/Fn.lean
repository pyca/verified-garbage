import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Rest

/-!
# AES-GCM streaming encryption out of place, x86-64: correctness

Untrusted: everything here is checked by Lean. The entry, the whole blocks
(if any), and the bytes left (`encrypt_wp`).
-/

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.Impl.AesGcm.X86_64.StreamTo
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

theorem encrypt_wp {M : CtxMode} (T : BlkToFn M) (E : EncFn M) {s : State}
    (hpre : Proof.AesGcm.streamToPreM M s) : WP isa (encrypt T.fn E.fn) s (Done s) := by
  have hp := SP'.ofM hpre
  refine WP.seq (WP.mono (entry_ok hp) fun s₁ ⟨h11, hg, hk, hf, hrd, hwr⟩ => ?_)
  have M₁ := mid_entry hp (hg _ (by decide) (by decide) (by decide))
    (fun r hr => hg r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr)) hk hf hrd hwr
  exact WP.seq (WP.mono (blocks_ok hp T M₁ h11 (hg _ (by decide) (by decide) (by decide))
      (hg _ (by decide) (by decide) (by decide)))
    fun _ ⟨_, M⟩ => rest_ok hp E M)

end VG.Proof.AesGcm.X86_64.StreamTo
