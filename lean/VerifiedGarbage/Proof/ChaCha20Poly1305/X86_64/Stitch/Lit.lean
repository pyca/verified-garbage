module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Stitch
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Stitch
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ChaCha20 and Poly1305 together (x86-64): the code as literals

The stitched code (`Impl/ChaCha20Poly1305/X86_64/Stitch.lean`) for each of
its configurations, from the rounds up to `bulk`'s, as literals
(`materialize_code`, `Proof/Framework/Lit.lean`): the checks of every
instruction (`spSafe`) and the constant-time analyses of its pieces then read
them rather than having the kernel build the rounds again in each.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch.Lits

open VG.Impl.ChaCha20Poly1305.X86_64.Stitch

materialize_code roundsF := Impl.ChaCha20.X86_64.Avx2.roundsFor false
materialize_code roundsT := Impl.ChaCha20.X86_64.Avx2.roundsFor true
materialize_code sroundsFF := sroundsFor false false
materialize_code sroundsFT := sroundsFor false true
materialize_code sroundsTF := sroundsFor true false
materialize_code sroundsTT := sroundsFor true true
materialize_code troundsFF := trounds false false 10
materialize_code troundsFT := trounds false true 10
materialize_code troundsTF := trounds true false 10
materialize_code troundsTT := trounds true true 10
materialize_code troundsO4 := troundsG false (oblocks 4) (ofirst 4) 10
materialize_code troundsO8 := troundsG true (oblocks 8) (ofirst 8) 10
materialize_code troundsO12 := troundsG true (oblocks 12) (ofirst 12) 10

materialize_code firstChunkF := firstChunk false
materialize_code firstChunkT := firstChunk true
materialize_code chunkFF := chunk false false
materialize_code chunkFT := chunk false true
materialize_code chunkTF := chunk true false
materialize_code chunkTT := chunk true true
materialize_code chunkOF := chunkO false
materialize_code chunkOT := chunkO true
materialize_code tailABFF := tailAB false false
materialize_code tailABFT := tailAB false true
materialize_code tailABTF := tailAB true false
materialize_code tailABTT := tailAB true true
materialize_code tailO4 := tailO false 4
materialize_code tailO8 := tailO true 8
materialize_code tailO12 := tailO true 12
materialize_code tailKABFF := tailKAB false false
materialize_code tailKABFT := tailKAB false true
materialize_code tailKABTF := tailKAB true false
materialize_code tailKABTT := tailKAB true true

materialize_code bulkF := bulk false
materialize_code bulkT := bulk true
materialize_code tailPF := tailP false
materialize_code tailPT := tailP true
materialize_code bulkPF := bulkP false
materialize_code bulkPT := bulkP true
materialize_code bulkOF := bulkO false
materialize_code bulkOT := bulkO true
materialize_code bigSF := bigS false
materialize_code bigST := bigS true

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch.Lits
