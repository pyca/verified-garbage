import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackLoad

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64

/-- Advance one public sixteen-field group. The counter controls a fixed
sixteen-iteration loop and does not depend on sampled data. -/
theorem advance_ok (s : State) {d : Nat} (hd : d=18 ∨ d=20) :
    WP isa (.block [.addImm .x .x0 .x0 (2*d),.addImm .x .x4 .x4 64,
      .subImm .x .x11 .x11 1]) s fun t =>
      t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (2*d) ∧
      t.gpr .x4=s.gpr .x4+64 ∧ t.gpr .x11=s.gpr .x11-1 ∧
      (∀ r, r≠.x0 → r≠.x4 → r≠.x11 → t.gpr r=s.gpr r) ∧
      t.v=s.v ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp := by
  let a := s.write .x .x0 (s.gpr .x0+BitVec.ofNat 64 (2*d))
  let b := a.write .x .x4 (a.gpr .x4+64)
  let t := b.write .x .x11 (b.gpr .x11-1)
  refine WP.block_cons_iff.mpr ⟨a,by simp [isa,exec,show 2*d<4096 by omega,State.read,a],?_⟩
  refine WP.block_cons_iff.mpr ⟨b,rfl,?_⟩
  refine WP.block_cons_iff.mpr ⟨t,rfl,?_⟩
  apply WP.block_nil_iff.mpr
  dsimp only [t,b,a]
  simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq]
  simp only [show Reg.x0≠.x11 by decide,show Reg.x0≠.x4 by decide,
    show Reg.x4≠.x11 by decide,show Reg.x4≠.x0 by decide,
    show Reg.x11≠.x4 by decide,show Reg.x11≠.x0 by decide,ite_false,ite_true,true_and]
  constructor
  · intro r h0 h4 h11
    simp only [h0,h4,h11,ite_false]
  · exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
