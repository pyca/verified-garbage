import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideFold

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

/-- Initial mask consists of the public all-one acceptance bit in each lane. -/
def wideInitial (s : State) : State := s.setV .v20 (ofVDwords (s.gpr .x12) (s.gpr .x12))

/-- Exact sixteen-candidate probe, using four independent decoders and one
horizontal acceptance reduction. No input-dependent memory access occurs. -/
theorem wideTry_ok {s : State} (hi : s.v .v3=gatherIndex)
    (hr : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16) :
    WP isa (.block wideTry) s fun t =>
      ProbeFrame [.x6,.x7] wideVectors s t ∧
      (∀j<4,t.v wideRegs[j]! = quarterValues s j) ∧
      t.gpr .x6=(vdword (quarterMask (wideInitial s) 4) 0 &&&
        vdword (quarterMask (wideInitial s) 4) 1) ^^^ s.gpr .x12 := by
  rw [show wideTry=.vop (.dup .d2 .v20 .x12)::
      ((List.range 4).flatMap quarterCode++reduceRegisterCode .v20) from rfl]
  refine wp_vop (d := .v20) rfl fun a ha => ?_
  rw [WP.block_append_iff]
  refine WP.mono (quarters_ok 4 (by decide) (s := a)
    (by rw [ha.other .v3 (by decide)]; exact hi)
    (fun j hj => by rw [ha.rd,ha.wr,ha.gpr]; exact hr j hj)) fun b hb => ?_
  refine WP.mono (reduceRegister_ok b .v20) fun t ⟨ht,hvec,hflag⟩ => ?_
  have hf : ProbeFrame [.x6,.x7] wideVectors s t :=
    (((ProbeFrame.ofVector ha.chg (by decide)).trans hb.frame).trans
      (ProbeFrame.ofScalar ht hvec)).mono (by simp) (by simp [wideVectors])
  refine ⟨hf,?_,?_⟩
  · intro j hj
    rw [hvec,hb.values j hj,quarterValues,ha.mem,ha.gpr,ha.other .v4 (by decide)]
    rfl
  · rw [hflag,hb.mask,hb.frame.only.get .x12,ha.gpr]
    have hmask : quarterMask a 4=quarterMask (wideInitial s) 4 := by
      simp only [quarterMask,quarterValues,ha.v,ha.mem,ha.gpr,
        ha.other .v4 (by decide),ha.other .v5 (by decide)]
      rfl
    rw [hmask]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
