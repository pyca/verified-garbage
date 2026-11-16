module

public import VerifiedGarbage.Impl.Rc2.RISCV64.Block
public import VerifiedGarbage.Impl.Rc2.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Rc2.PiLit
import VerifiedGarbage.Proof.Rc2.Table
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Rc2.RISCV64.Block
meta import VerifiedGarbage.Impl.Rc2.RISCV64.ExpandKey
meta import VerifiedGarbage.Proof.Rc2.PiLit
meta import VerifiedGarbage.Proof.Rc2.Table
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! Literal code keeps the audits that evaluate it (constant time, `spSafe`)
from rebuilding it. -/

@[expose] public section

namespace VG

materialize_code Impl.Rc2.RISCV64.encryptBlock
materialize_code Impl.Rc2.RISCV64.decryptBlock
/-- `piQuad`, PITABLE's bytes read from the packed table of
`Proof/Rc2/PiLit.lean` (`Proof.Rc2.piQuadNat`, with the table's literal):
`expandKey`'s literal, whose code stores the 32 quadwords from immediates,
reads the 256 bytes through it (`unfoldToLits` rewrites `piQuad` to this, as
to a table of `materialize_table`) rather than look each up in the
specification's vector. -/
noncomputable abbrev Impl.Rc2.piQuad.lit (q : Nat) : BitVec 64 :=
  (List.range 8).foldr (fun j acc => acc |||
    (BitVec.ofNat 8 (if 8 * q + j < 256 then Rc2.piRowNat.lit ((8 * q + j) / 16) ((8 * q + j) % 16) else 0)).setWidth 64
      <<< (8 * j)) 0

theorem Impl.Rc2.piQuad.lit_eq : Impl.Rc2.piQuad = Impl.Rc2.piQuad.lit := by
  rw [Proof.Rc2.piQuad_eq]
  funext q
  rw [Proof.Rc2.piQuadNat, Impl.Rc2.piQuad.lit, ← Rc2.piRowNat.lit_eq]
  rfl

materialize_code Impl.Rc2.RISCV64.expandKey

end VG
