import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowNorm2

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_strq wp_vop VChg vword_mapWords3)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

def storeTwo (a b : VReg) (n : Reg) (off : Nat) : List Instr :=
 [.strq a n off,.strq b n (off+128)]

theorem storeTwo_ok {a b : VReg} {n : Reg} {off : Nat}
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off+128<65536)
    (hr : InRegions s.wr (s.gpr n+BitVec.ofNat 64 off) 16)
    (hr' : InRegions s.wr (s.gpr n+BitVec.ofNat 64 (off+128)) 16)
    (k : ∀v,StepKeep [] s v → v.v=s.v →
      v.mem=(s.mem.write (s.gpr n+BitVec.ofNat 64 off) 16 (s.v a)).write
        (s.gpr n+BitVec.ofNat 64 (off+128)) 16 (s.v b) → WP isa (.block rest) v Q) :
    WP isa (.block (storeTwo a b n off++rest)) s Q := by
  refine wp_strq (by omega) rfl hr fun u hu =>
    wp_strq (by omega) rfl (by rw [hu.wr,hu.gpr]; exact hr') fun v hv =>
      k v (((StepKeep.ofMem hu).trans (StepKeep.ofMem hv)).mono (by simp)) (hv.v.trans hu.v) ?_
  rw [hv.mem,hu.mem,hu.gpr,hu.v]

def mlsTwo (r : VReg) : List Instr :=
 [.vop (.mls .v24 .v26 .v15),.vop (.mls r .v28 .v15)]

theorem mlsTwo_ok {r : VReg} (hr : r≠.v24)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀v,VChg [.v24,r] s v →
      (∀e<4,vword (v.v .v24) e=vword (s.v .v24) e-vword (s.v .v26) e*vword (s.v .v15) e) →
      (∀e<4,vword (v.v r) e=vword (s.v r) e-vword (s.v .v28) e*vword (s.v .v15) e) →
      WP isa (.block rest) v Q) :
    WP isa (.block (mlsTwo r++rest)) s Q := by
  refine wp_vop (d := .v24) rfl fun u hu => wp_vop (d := r) rfl fun v hv =>
    k v ((hu.chg.trans hv.chg).mono (by simp)) ?_ ?_
  · intro e he
    rw [hv.get .v24 (Ne.symm hr),hu.v,vword_mapWords3 _ _ _ _ he]
  · intro e he
    rw [hv.v,vword_mapWords3 _ _ _ _ he,hu.get r hr,
      hu.get .v28 (by decide),hu.get .v15 (by decide)]
end VG.Proof.MlDsa.AArch64.Optimized.Paired
