module

public import VerifiedGarbage.Impl.Cast5.AArch64.Tbl
public import VerifiedGarbage.Impl.Cast5.AArch64.TblModes
public import VerifiedGarbage.Impl.Cast5.AArch64.TblKey
public import VerifiedGarbage.Proof.Cast5.SboxRows
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Cast5.AArch64.Tbl
meta import VerifiedGarbage.Impl.Cast5.AArch64.TblModes
meta import VerifiedGarbage.Impl.Cast5.AArch64.TblKey
meta import VerifiedGarbage.Proof.Cast5.SboxRows
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! Literal code for the kernel-evaluated checks (constant time, `spSafe`, the ABI) of the code
that reads the S-boxes by `tbl`. -/

@[expose] public section

namespace VG

/-! `sboxes` are the S-boxes' lists, whose literal (`Proof/Cast5/SboxRows.lean`) the table below
and the code that carries it read. -/

noncomputable abbrev Impl.Cast5.AArch64.Tbl.sboxes.lit : List (List Spec.Cast5.Word) :=
  Proof.Cast5.sboxRows.lit

open Proof.Cast5 in
theorem Impl.Cast5.AArch64.Tbl.sboxes.lit_eq :
    Impl.Cast5.AArch64.Tbl.sboxes = Impl.Cast5.AArch64.Tbl.sboxes.lit := by
  rw [Impl.Cast5.AArch64.Tbl.sboxes, s1L.2, s2L.2, s3L.2, s4L.2, s5L.2, s6L.2, s7L.2, s8L.2]
  exact sboxRows.lit_eq

/-! The table every load carries, evaluated once. -/

materialize_value Impl.Cast5.AArch64.Tbl.planeWords

/-! Quote table loads with the existing checked table literal. Reifying its
1,024 words separately at every load dominates quoting the round code. -/

open Lean in
@[instance_reducible] private meta def tblInstrToExpr : ToExpr AArch64.Instr :=
  let ordinary : ToExpr AArch64.Instr := inferInstance
  { ordinary with toExpr := fun i => match i with
    | .ldrqTbl t n off name words =>
      if name == Impl.Cast5.AArch64.Tbl.planesSym && words == Impl.Cast5.AArch64.Tbl.planeWords then
        mkApp5 (mkConst ``AArch64.Instr.ldrqTbl) (toExpr t) (toExpr n) (toExpr off) (toExpr name)
          (mkConst ``Impl.Cast5.AArch64.Tbl.planeWords.lit)
      else ordinary.toExpr i
    | _ => ordinary.toExpr i }

attribute [local instance] tblInstrToExpr

/-! The functions. -/

materialize_code Impl.Cast5.AArch64.Tbl.ecbEncrypt
materialize_code Impl.Cast5.AArch64.Tbl.ecbDecrypt

/-! The batches, whose registers `crypt`'s proof checks, and the modes over them. -/

materialize_code Impl.Cast5.AArch64.Tbl.batchEnc
materialize_code Impl.Cast5.AArch64.Tbl.batchDec
materialize_code Impl.Cast5.AArch64.Tbl.cbcDecryptChained
materialize_code Impl.Cast5.AArch64.Tbl.cfbDecrypt

/-! Key expansion, and the lookups it calls, evaluated once. -/

materialize_value Impl.Cast5.AArch64.Tbl.sboxes5678
materialize_code Impl.Cast5.AArch64.Tbl.expandKey

end VG
