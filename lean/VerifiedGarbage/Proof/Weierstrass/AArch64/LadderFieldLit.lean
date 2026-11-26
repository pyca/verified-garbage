module

public import VerifiedGarbage.Impl.Weierstrass.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Impl.Weierstrass.AArch64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! Literals of the seven shared inline products of the Brainpool P-512 ladder. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.LadderFieldLit
open VG.Impl.Weierstrass.AArch64
open VG.Impl.Mont VG.Impl.Weierstrass
theorem layout_eq {M : Mod} (h : ladderFieldLayout M = true) : M = ladderFieldMod := by
  cases M
  rename_i n mo tmp minv red tight adx sparse inl fnN fnMod
  cases red <;> cases fnMod <;> simp_all [ladderFieldLayout, ladderFieldMod, Bool.and_eq_true]

theorem same_eq {op : FOp} {i : Nat} (h : sameLadderField op i = true) : op = ladderFieldOp i := by
  cases op <;> simp_all [sameLadderField, ladderFieldOp, Bool.and_eq_true]

materialize_code field0 := ladderFieldBody 0
materialize_code field1 := ladderFieldBody 1
materialize_code field2 := ladderFieldBody 2
materialize_code field3 := ladderFieldBody 3
materialize_code field4 := ladderFieldBody 4
materialize_code field5 := ladderFieldBody 5
materialize_code field6 := ladderFieldBody 6
end VG.Proof.Weierstrass.AArch64.LadderFieldLit
