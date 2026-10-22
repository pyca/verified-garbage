module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
meta import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# Stack safety and constant-time checks for the eight-block pipeline

The counter value in `r8` is secret; its arithmetic never controls an
address or branch. The original counter pointer stays public in `rsi`.
Encryption, and decryption with a prepared key context, are checked as
`Blocks.stitchPart` runs them with `full`: the number of blocks after the
pipeline's, in `r9`, is public.

With a prepared key context (`encR`, `decR`, `encRS`, `decRS`), the working tables are
aligned (`Blocks.stitchPart`'s `aligned`).

Out of place (`encTo`, `encToR`, as `BlocksTo.stitchPart` runs them), `rbx`,
which the caller's taint leaves secret, is only stored and loaded back; the
`src - dst` it holds in the loop, from the public `r8` and `r10`, is public.

Each loop is checked several times, so it is built once, as a literal.
-/

@[expose] public section

namespace VG

materialize_code Impl.Gcm.X86_64.StitchAvx8.enc
materialize_code Impl.Gcm.X86_64.StitchAvx8.dec
materialize_code Impl.Gcm.X86_64.StitchAvx8.encR
materialize_code Impl.Gcm.X86_64.StitchAvx8.decR
materialize_code Impl.Gcm.X86_64.StitchAvx8.encRS
materialize_code Impl.Gcm.X86_64.StitchAvx8.decRS
materialize_code Impl.Gcm.X86_64.StitchAvx8.encTo
materialize_code Impl.Gcm.X86_64.StitchAvx8.encToR

end VG

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.AesGcm.X86_64 (Piece PieceTo)
open VG.Impl.Gcm.X86_64.StitchAvx8 (enc dec encR decR encRS decRS encTo encToR)

/-- The eight loops' checks, in one kernel evaluation (`taint_decide_all`). -/
theorem pieces : Piece enc false true ∧ Piece dec ∧ Piece encR true true ∧ Piece decR true true ∧
    Piece encRS true true ∧ Piece decRS true true ∧ PieceTo encTo false true ∧ PieceTo encToR true true := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩, ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩, ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩, ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩, ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩, ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩, ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩, ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩⟩
  taint_decide_all

theorem enc_piece : Piece enc false true := pieces.1
theorem dec_piece : Piece dec := pieces.2.1
theorem encR_piece : Piece encR true true := pieces.2.2.1
theorem decR_piece : Piece decR true true := pieces.2.2.2.1
theorem encRS_piece : Piece encRS true true := pieces.2.2.2.2.1
theorem decRS_piece : Piece decRS true true := pieces.2.2.2.2.2.1
theorem encTo_piece : PieceTo encTo false true := pieces.2.2.2.2.2.2.1
theorem encToR_piece : PieceTo encToR true true := pieces.2.2.2.2.2.2.2

end VG.Proof.Gcm.X86_64.StitchAvx8
