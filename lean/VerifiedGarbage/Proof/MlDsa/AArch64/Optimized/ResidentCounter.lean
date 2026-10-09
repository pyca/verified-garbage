import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentStep
import VerifiedGarbage.Proof.MlKem.AArch64.Wp

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (Pairs)

/-- The three public loop updates leave all resident lanes and memory intact. -/
theorem advance_ok {s : State} {ra rb : Reg} {rate : Nat}
    (hrate : rate < 4096) (hab : ra ≠ rb)
    (ha28 : ra ≠ .x28) (hb28 : rb ≠ .x28) :
    WP isa (.block ([.addImm .x ra ra rate,.addImm .x rb rb rate,
      .subImm .x .x28 .x28 1] : List Instr)) s fun t =>
      t.gpr ra = s.gpr ra + BitVec.ofNat 64 rate ∧
      t.gpr rb = s.gpr rb + BitVec.ofNat 64 rate ∧
      t.gpr .x28 = s.gpr .x28 - 1 ∧
      (∀ r, r ≠ ra → r ≠ rb → r ≠ .x28 → t.gpr r = s.gpr r) ∧
      t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  let s1 := s.write .x ra (s.gpr ra + BitVec.ofNat 64 rate)
  let s2 := s1.write .x rb (s1.gpr rb + BitVec.ofNat 64 rate)
  let s3 := s2.write .x .x28 (s2.gpr .x28 - 1)
  refine WP.block_cons_iff.mpr ⟨s1,by simp [isa,exec,hrate,State.read,s1],?_⟩
  refine WP.block_cons_iff.mpr ⟨s2,by simp [isa,exec,hrate,State.read,s2],?_⟩
  refine WP.block_cons_iff.mpr ⟨s3,rfl,?_⟩
  apply WP.block_nil_iff.mpr
  dsimp only [s3,s2,s1]
  simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq]
  simp only [ha28,hb28,hab,Ne.symm hab,Ne.symm ha28,Ne.symm hb28,ite_false,ite_true,true_and]
  constructor
  · intro r hra hrb hr28
    simp only [hra,hrb,hr28,ite_false]
  · exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Resident
