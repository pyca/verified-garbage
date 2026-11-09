module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsChainMath

/-! The scalar lowering's two subtractions compute a word complement. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field

theorem cms_complement (x : BitVec 64) : (0 : BitVec 64)-x-1#64= ~~~x := by
  change (0#64-x)-1#64= ~~~x
  rw [BitVec.zero_sub,BitVec.neg_eq_not_add]
  exact BitVec.add_sub_cancel _ _

end VG.Proof.Mont.AArch64.P521Field
