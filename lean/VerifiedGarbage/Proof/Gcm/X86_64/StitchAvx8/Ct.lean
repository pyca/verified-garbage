module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8
meta import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Spec.TripleDes
meta import VerifiedGarbage.Spec.TripleDes

/-!
# Stack safety and constant-time checks for the eight-block pipeline

The counter value in `r8` is secret; its arithmetic never controls an
address or branch. The original counter pointer stays public in `rsi`.
Encryption, and decryption with a prepared key context, are checked as
`Blocks.stitchPart` runs them with `full`: the number of blocks after the
pipeline's, in `r9`, is public.

With a prepared key context (`encR`, `dec`), the working tables are
aligned (`Blocks.stitchPart`'s `aligned`).

Out of place (`encTo`, `encToR`, as `BlocksTo.stitchPart` runs them), `rbx`,
which the caller's taint leaves secret, is only stored and loaded back; the
`src - dst` it holds in the loop, from the public `r8` and `r10`, is public.

Each loop is checked six times, so it is built once, as a literal.
-/

@[expose] public section

namespace VG

materialize_code Impl.Gcm.X86_64.StitchAvx8.enc
materialize_code Impl.Gcm.X86_64.StitchAvx8.dec
materialize_code Impl.Gcm.X86_64.StitchAvx8.encR
materialize_code Impl.Gcm.X86_64.StitchAvx8.decR
materialize_code Impl.Gcm.X86_64.StitchAvx8.encTo
materialize_code Impl.Gcm.X86_64.StitchAvx8.encToR

end VG

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.AesGcm.X86_64 (Piece PieceTo)
open VG.Impl.Gcm.X86_64.StitchAvx8 (enc dec encR decR encTo encToR)

theorem enc_piece : Piece enc false true :=
  ⟨by lit_decide, by lit_decide, by lit_decide, by lit_decide,
    by lit_decide, ⟨_, by taint_decide⟩⟩

theorem dec_piece : Piece dec :=
  ⟨by lit_decide, by lit_decide, by lit_decide, by lit_decide,
    by lit_decide, ⟨_, by taint_decide⟩⟩

theorem encR_piece : Piece encR true true :=
  ⟨by lit_decide, by lit_decide, by lit_decide, by lit_decide,
    by lit_decide, ⟨_, by taint_decide⟩⟩

theorem decR_piece : Piece decR true true :=
  ⟨by lit_decide, by lit_decide, by lit_decide, by lit_decide,
    by lit_decide, ⟨_, by taint_decide⟩⟩

theorem encTo_piece : PieceTo encTo false true :=
  ⟨by lit_decide, by lit_decide, by lit_decide, by lit_decide,
    by lit_decide, ⟨_, by taint_decide⟩⟩

theorem encToR_piece : PieceTo encToR true true :=
  ⟨by lit_decide, by lit_decide, by lit_decide, by lit_decide,
    by lit_decide, ⟨_, by taint_decide⟩⟩

end VG.Proof.Gcm.X86_64.StitchAvx8
