import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailClear

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (WP.cons)

/-- The helper accepts a nonce word and absorbs precisely its low two bytes. -/
def nonceWord (k : BitVec 64) : BitVec 64 := ((k <<< 48) >>> 48)+0x1f0000

theorem nonce_ok (s : State) :
    WP isa (.block [.lsl .x .x7 .x5 48,.lsr .x .x7 .x7 48,
      .movz .x .x8 31 1,.add .x .x7 .x7 .x8]) s fun t =>
      RegKeep [.x7,.x8] s t ∧ t.mem=s.mem ∧ t.v=s.v ∧
      t.gpr .x7=nonceWord (s.gpr .x5) := by
  refine WP.cons rfl (WP.cons rfl (WP.cons rfl (WP.cons rfl (WP.block_nil_iff.mpr ?_))))
  refine ⟨⟨fun r hr => ?_,rfl,rfl,rfl⟩,rfl,rfl,?_⟩
  · have h7 : r≠.x7 := fun h => hr (by simp only [h,List.mem_cons,true_or])
    have h8 : r≠.x8 := fun h => hr (by simp [h])
    simp only [RegUpd.gpr_write,h7,h8,ite_false]
  · simp only [RegUpd.gpr_write_self,RegUpd.gpr_write,State.read,Size.bits,
      BitVec.setWidth_eq,reduceCtorEq,ite_false]
    rfl

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
