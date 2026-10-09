import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MatrixMask

namespace VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.MatrixMask
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

def maskMem (m : Mem) (p : Addr) (v : BitVec 128) : Mem :=
 m.write p 16 (m.read p 16 &&& v)

theorem group_ok {s : State} {i : Nat} (hi : i<4)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hw : InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (group i)) s fun t=>
      StepKeep [.v1] s t ∧ t.mem=maskMem s.mem (s.gpr .x1+BitVec.ofNat 64 (16*i)) (s.v .v0) := by
  unfold group
  refine wp_ldrq (by omega) rfl hr fun a ha=>?_
  refine wp_vop (d := .v1) rfl fun b hb=>?_
  have hk : VChg [.v1] s b := (ha.chg.trans hb.chg).mono (by decide)
  refine wp_strq (a := s.gpr .x1+BitVec.ofNat 64 (16*i)) (by omega) (by rw [hk.gpr]) (by rw [hk.wr]; exact hw) fun t ht=>wp_nil ?_
  refine ⟨((StepKeep.ofChg hk (by decide)).trans (StepKeep.ofMem ht)).mono (by decide),?_⟩
  rw [ht.mem,hk.mem,hb.v,ha.v,ha.get .v0]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
