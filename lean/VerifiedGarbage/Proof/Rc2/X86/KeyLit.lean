module

public import VerifiedGarbage.Impl.Rc2.X86.ExpandKey
public import VerifiedGarbage.Proof.Rc2.PiLit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Rc2.X86.ExpandKey
meta import VerifiedGarbage.Proof.Rc2.PiLit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

@[expose] public section

namespace VG.Impl.Rc2.X86

open VG.X86

/-- `piWord`, reading PITABLE from its packed table (`Rc2.piTable_getD`). -/
def piWordLit (j : Nat) : BitVec 32 :=
  (BitVec.ofNat 8 (VG.Rc2.piNat (4 * j))).setWidth 32 |||
    (BitVec.ofNat 8 (VG.Rc2.piNat (4 * j + 1))).setWidth 32 <<< 8 |||
    (BitVec.ofNat 8 (VG.Rc2.piNat (4 * j + 2))).setWidth 32 <<< 16 |||
    (BitVec.ofNat 8 (VG.Rc2.piNat (4 * j + 3))).setWidth 32 <<< 24

/-- `piLookup`, reading PITABLE from its packed table. -/
def piLookupLit : List Instr := piLookupWith piWordLit

materialize_value piLookupLit

/-- The literal of `piLookup`, evaluated through the packed PITABLE. -/
noncomputable abbrev piLookup.lit : List Instr := piLookupLit.lit

theorem piLookup.lit_eq : piLookup = piLookup.lit := by
  have : piWord = piWordLit := by
    funext j; simp only [piWord, piWordLit, VG.Rc2.piTable_getD]
  refine Eq.trans ?_ piLookupLit.lit_eq
  rw [piLookup, piLookupLit, this]

materialize_flat_code expandKey

end VG.Impl.Rc2.X86
