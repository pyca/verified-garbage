module
public import VerifiedGarbage.Impl.X448.AArch64
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Proof.X448.Field

import VerifiedGarbage.Proof.X448.AArch64.Init
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.X448.Limbs
import Batteries.Logic

/-!
# X448 on AArch64: field multiplication

The row loop, coefficient folds and carry passes together compute
multiplication modulo the field prime, with bounded output limbs. Either input
may also be the output.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe := toFe (fe m base o)

def clob : List Reg := [.x4, .x6, .x5, .x9, .x10, .x11, .x7, .x8, .x13, .x14, .x15, .x16]

structure Op (base : Addr) (o : Nat) (s t : State) : Prop where
  keeps : Keeps clob s t
  mem : FieldMem base o s.mem t.mem

abbrev Slot (o : Nat) : Prop := o + 128 ≤ ACC

end VG.Proof.X448.AArch64
