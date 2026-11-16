module

import VerifiedGarbage.Proof.TripleDes.AArch64.SboxTable
public import VerifiedGarbage.Impl.TripleDes.AArch64.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.AArch64.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.AArch64.SboxTable
meta import VerifiedGarbage.Impl.TripleDes.AArch64.ExpandKey
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Block
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

@[expose] public section

namespace VG

/-! The parts the block functions share, evaluated once: the round, and the
initial and final permutations. -/

materialize_value Impl.TripleDes.AArch64.roundBody
materialize_value Impl.TripleDes.AArch64.blockLoad
materialize_value Impl.TripleDes.AArch64.blockStore

/-! The functions. -/

materialize_code Impl.TripleDes.AArch64.encryptBlock
materialize_code Impl.TripleDes.AArch64.decryptBlock
end VG

namespace VG.Proof.TripleDes.AArch64

open VG.Impl.TripleDes.AArch64

/-! The static of the key expansion (`Key.tabWords`): each of its bytes is a
key bit's place (`Key.sel`), two lookups in the specification's permutations
and a sum of its rotations, which the kernel would evaluate for every byte,
and each byte for both words of its vector. The permutations and then
`Key.sel` are tables here, evaluated once (`sel.lit_eq`), which the literal
of the static reads. -/

/-- PC-1 and PC-2, as functions. -/
private def pc1N (i : Nat) : Nat := Spec.TripleDes.pc1.getD i 1
private def pc2N (i : Nat) : Nat := Spec.TripleDes.pc2.getD i 1

materialize_table pc1N 56
materialize_table pc2N 48

/-- `Key.sel`, with the permutations by name. -/
private def selN (r i : Nat) : Nat :=
  let q := pc2N i
  let u := if q ≤ 28 then (q - 1 + Key.shiftOf r) % 28 + 1 else (q - 29 + Key.shiftOf r) % 28 + 29
  pc1N (u - 1)

materialize_table selN 16 48

/-- The literal of `Key.sel` in this module (it is private, so that the
checks of other modules do not look for `Key.sel` in their code). -/
private noncomputable abbrev sel.lit : Nat → Nat → Nat := selN.lit

private theorem sel.lit_eq : Key.sel = sel.lit := Eq.trans (b := selN) rfl selN.lit_eq

end VG.Proof.TripleDes.AArch64

namespace VG

materialize_value Impl.TripleDes.AArch64.Key.tabWords
materialize_code Impl.TripleDes.AArch64.Key.expandKey

end VG
