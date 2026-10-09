import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

def maskGroup : List Instr :=
 [.ldrq .v1 .x3 0,.vop (.logic .and .v1 .v1 .v0),.strq .v1 .x3 0]
def maskMem (m : Mem) (p : Addr) (v : BitVec 128) : Mem :=
 m.write p 16 (m.read p 16 &&& v)

theorem maskGroup_ok {s : State}
    (hr : InRegions (s.rd++s.wr) (s.gpr .x3) 16)
    (hw : InRegions s.wr (s.gpr .x3) 16) :
    WP isa (.block maskGroup) s fun t=>
      StepKeep [.v1] s t ∧ t.mem=maskMem s.mem (s.gpr .x3) (s.v .v0) := by
  unfold maskGroup
  refine wp_ldrq (by decide) (by simp) hr fun a ha=>?_
  refine wp_vop (d := .v1) rfl fun b hb=>?_
  have hk : VChg [.v1] s b := (ha.chg.trans hb.chg).mono (by decide)
  refine wp_strq (a := s.gpr .x3) (by decide) (by rw [hk.gpr]; simp) (by rw [hk.wr]; exact hw) fun t ht=>wp_nil ?_
  refine ⟨((StepKeep.ofChg hk (by decide)).trans (StepKeep.ofMem ht)).mono (by decide),?_⟩
  rw [ht.mem,hk.mem,hb.v,ha.v,ha.get .v0]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
