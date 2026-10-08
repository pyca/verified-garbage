import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8

/-!
# Stack safety and constant-time checks for the eight-block pipeline

The counter value in `r8` is secret; its arithmetic never controls an
address or branch. The original counter pointer stays public in `rsi`.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.AesGcm.X86_64 (Piece)
open VG.Impl.Gcm.X86_64.StitchAvx8 (enc dec)

theorem enc_piece : Piece enc :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide,
    by decide +kernel, ⟨_, by taint_decide⟩⟩

theorem dec_piece : Piece dec :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide,
    by decide +kernel, ⟨_, by taint_decide⟩⟩

end VG.Proof.Gcm.X86_64.StitchAvx8
