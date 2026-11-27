module

public import VerifiedGarbage.Impl.Weierstrass.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Impl.Weierstrass.AArch64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! Literals of the shared inline products of the four Brainpool ladders. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.LadderFieldLit
open VG.Impl.Weierstrass.AArch64
open VG.Impl.Mont VG.Impl.Weierstrass
theorem layout_eq {M : Mod} {p : Nat} (h : ladderFieldLayout M p = true) : M = ladderFieldMod p := by
  cases M
  rename_i n mo tmp minv red tight adx sparse inl fnN fnMod
  cases red <;> cases fnMod <;> simp_all [ladderFieldLayout, ladderFieldMod, Bool.and_eq_true]

theorem same_eq {op : FOp} {p i : Nat} (h : sameLadderField op p i = true) : op = ladderFieldOp p i := by
  cases op <;> simp_all [sameLadderField, ladderFieldOp, Bool.and_eq_true]

materialize_code field0_0 := ladderFieldBody 0 0
materialize_code field0_1 := ladderFieldBody 0 1
materialize_code field0_2 := ladderFieldBody 0 2
materialize_code field0_3 := ladderFieldBody 0 3
materialize_code field0_4 := ladderFieldBody 0 4
materialize_code field0_5 := ladderFieldBody 0 5
materialize_code field0_6 := ladderFieldBody 0 6
materialize_code field1_0 := ladderFieldBody 1 0
materialize_code field1_1 := ladderFieldBody 1 1
materialize_code field1_2 := ladderFieldBody 1 2
materialize_code field1_3 := ladderFieldBody 1 3
materialize_code field1_4 := ladderFieldBody 1 4
materialize_code field1_5 := ladderFieldBody 1 5
materialize_code field1_6 := ladderFieldBody 1 6
materialize_code field2_0 := ladderFieldBody 2 0
materialize_code field2_1 := ladderFieldBody 2 1
materialize_code field2_2 := ladderFieldBody 2 2
materialize_code field2_3 := ladderFieldBody 2 3
materialize_code field2_4 := ladderFieldBody 2 4
materialize_code field2_5 := ladderFieldBody 2 5
materialize_code field2_6 := ladderFieldBody 2 6
materialize_code field3_0 := ladderFieldBody 3 0
materialize_code field3_1 := ladderFieldBody 3 1
materialize_code field3_2 := ladderFieldBody 3 2
materialize_code field3_3 := ladderFieldBody 3 3
materialize_code field3_4 := ladderFieldBody 3 4
materialize_code field3_5 := ladderFieldBody 3 5
materialize_code field3_6 := ladderFieldBody 3 6
end VG.Proof.Weierstrass.AArch64.LadderFieldLit
