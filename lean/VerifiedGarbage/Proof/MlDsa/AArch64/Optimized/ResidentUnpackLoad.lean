import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackOne

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_ldrq)

/-- Three overlapping vector loads consume exactly the packed sixteen-field
block. Their addresses are fixed by the public width. -/
theorem loads_ok (s : State) {d : Nat} (hd : d=18 ∨ d=20)
    (h0 : InRegions (s.rd++s.wr) (s.gpr .x0) 16)
    (h1 : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 16) 16)
    (h2 : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (2*d-16)) 16) :
    WP isa (.block [.ldrq .v0 .x0 0,.ldrq .v1 .x0 16,
      .addImm .x .x9 .x0 (2*d-16),.ldrq .v2 .x9 0]) s fun t =>
      t.v .v0=s.mem.read (s.gpr .x0) 16 ∧
      t.v .v1=s.mem.read (s.gpr .x0+BitVec.ofNat 64 16) 16 ∧
      t.v .v2=s.mem.read (s.gpr .x0+BitVec.ofNat 64 (2*d-16)) 16 ∧
      (∀ r, r≠.x9 → t.gpr r=s.gpr r) ∧
      (∀ v, v≠.v0 → v≠.v1 → v≠.v2 → t.v v=s.v v) ∧
      t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp := by
  refine wp_ldrq (by decide) (by simp) h0 fun a ha => ?_
  refine wp_ldrq (by decide) rfl (by simpa only [ha.gpr,ha.rd,ha.wr] using h1) fun b hb => ?_
  let c := b.write .x .x9 (b.gpr .x0+BitVec.ofNat 64 (2*d-16))
  have hc : exec (.addImm .x .x9 .x0 (2*d-16)) b=some c := by
    simp only [exec,show 2*d-16<4096 by omega,ite_true,State.read,c,Size.bits,BitVec.setWidth_eq]
  refine WP.block_cons_iff.mpr ⟨c,hc,?_⟩
  have cg : c.gpr .x9=s.gpr .x0+BitVec.ofNat 64 (2*d-16) := by
    simp only [c,RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,ite_true,hb.gpr,ha.gpr]
  refine wp_ldrq (a := s.gpr .x0+BitVec.ofNat 64 (2*d-16)) (by decide) (by simpa only [BitVec.add_zero] using cg)
    (by simpa only [show c.rd=b.rd from rfl,show c.wr=b.wr from rfl,hb.rd,hb.wr,ha.rd,ha.wr] using h2)
    fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.other .v0 (by decide),show c.v=b.v from rfl,hb.other .v0 (by decide),ha.v]
  · rw [ht.other .v1 (by decide),show c.v=b.v from rfl,hb.v,ha.mem,ha.gpr]
  · rw [ht.v,show c.mem=b.mem from rfl,hb.mem,ha.mem]
  · intro r hr
    rw [ht.gpr]
    simp only [c,RegUpd.gpr_write,hr,ite_false,hb.gpr,ha.gpr]
  · intro v hv0 hv1 hv2
    rw [ht.other v hv2,show c.v=b.v from rfl,hb.other v hv1,ha.other v hv0]
  · rw [ht.mem,show c.mem=b.mem from rfl,hb.mem,ha.mem]
  · rw [ht.rd,show c.rd=b.rd from rfl,hb.rd,ha.rd]
  · rw [ht.wr,show c.wr=b.wr from rfl,hb.wr,ha.wr]
  · rw [ht.sp,show c.sp=b.sp from rfl,hb.sp,ha.sp]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
