import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8

/-!
# Stack safety and constant-time checks for the eight-block pipeline

The counter value in `r8` is secret; its arithmetic never controls an
address or branch. The original counter pointer stays public in `rsi`.
Encryption is checked as `Blocks.stitchPart` runs it with `full`: the number
of blocks after the pipeline's, in `r9`, is public.

With a prepared key context (`encR`, `dec`), the working tables are
aligned (`Blocks.stitchPart`'s `aligned`).

Each loop is checked six times, so it is built once, as a literal.
-/

namespace VG

materialize_code Impl.Gcm.X86_64.StitchAvx8.enc
materialize_code Impl.Gcm.X86_64.StitchAvx8.dec
materialize_code Impl.Gcm.X86_64.StitchAvx8.encR

end VG

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.AesGcm.X86_64 (Piece)
open VG.Impl.Gcm.X86_64.StitchAvx8 (enc dec encR)

theorem enc_piece : Piece enc false true :=
  ⟨by lit_decide, by lit_decide, by lit_decide, by lit_decide,
    by lit_decide, ⟨_, by taint_decide⟩⟩

theorem dec_piece : Piece dec :=
  ⟨by lit_decide, by lit_decide, by lit_decide, by lit_decide,
    by lit_decide, ⟨_, by taint_decide⟩⟩

theorem encR_piece : Piece encR true true :=
  ⟨by lit_decide, by lit_decide, by lit_decide, by lit_decide,
    by lit_decide, ⟨_, by taint_decide⟩⟩

theorem decR_piece : Piece dec true :=
  ⟨by lit_decide, by lit_decide, by lit_decide, by lit_decide,
    by lit_decide, ⟨_, by taint_decide⟩⟩

end VG.Proof.Gcm.X86_64.StitchAvx8
