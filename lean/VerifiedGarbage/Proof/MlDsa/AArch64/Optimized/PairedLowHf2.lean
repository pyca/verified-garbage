import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowLoad2

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round VG.Impl.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (raw)

def lowHfTwo (g : Nat) (a b : VReg) : List Instr :=
 ((lowHf g .v26 a).zip (lowHf g .v28 b)).flatMap fun (x,y) => [x,y]

theorem lowHfTwo_ok {g : Nat} (hg : IsG g) {a b : VReg} (hb : b≠.v26)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (h11 : ∀e<4,vword (s.v .v11) e=BitVec.ofNat 32 127)
    (h12 : ∀e<4,vword (s.v .v12) e=BitVec.ofNat 32 (hbMul g))
    (h13 : ∀e<4,vword (s.v .v13) e=BitVec.ofNat 32 (hbAdd g))
    (k : ∀v,VChg [.v26,.v28] s v →
      (∀e<4,vword (v.v .v26) e=raw g (vword (s.v a) e)) →
      (∀e<4,vword (v.v .v28) e=raw g (vword (s.v b) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (lowHfTwo g a b++rest)) s Q := by
  have hsh : VShiftOp.ushr.ok VArr.s4.esize (dShift g) = true := by
    rcases hg with rfl | rfl <;> rfl
  refine wp_vop (d := .v26) rfl fun s1 h1 => ?_
  refine wp_vop (d := .v28) rfl fun s2 h2 => ?_
  refine wp_vop (d := .v26) rfl fun s3 h3 => ?_
  refine wp_vop (d := .v28) rfl fun s4 h4 => ?_
  refine wp_vop (d := .v26) rfl fun s5 h5 => ?_
  refine wp_vop (d := .v28) rfl fun s6 h6 => ?_
  refine wp_vop (d := .v26) rfl fun s7 h7 => ?_
  refine wp_vop (d := .v28) rfl fun s8 h8 => ?_
  refine wp_vop (d := .v26) (by simp only [VOp.eval,hsh,ite_true]; rfl) fun s9 h9 => ?_
  refine wp_vop (d := .v28) (by simp only [VOp.eval,hsh,ite_true]; rfl) fun s10 h10 => ?_
  refine k s10 ((((((((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg).trans h6.chg).trans h7.chg).trans h8.chg).trans h9.chg).trans h10.chg).mono (by simp)) ?_ ?_
  · intro e he
    have w1 : vword (s1.v .v26) e = vword (s.v a) e + BitVec.ofNat 32 127 := by
      rw [h1.v, VG.AArch64.vword_map2 _ _ _ he, h11 e he]
    have w3 : vword (s3.v .v26) e = (vword (s.v a) e + BitVec.ofNat 32 127) >>> 7 := by
      rw [h3.v, VG.AArch64.vword_map2 _ _ _ he, h2.get .v26 (by decide), w1]
      rfl
    have w5 : vword (s5.v .v26) e = ((vword (s.v a) e + BitVec.ofNat 32 127) >>> 7) * BitVec.ofNat 32 (hbMul g) := by
      rw [h5.v, VG.AArch64.vword_map2 _ _ _ he, h4.get .v26 (by decide), w3, h4.get .v12 (by decide), h3.get .v12 (by decide), h2.get .v12 (by decide), h1.get .v12 (by decide), h12 e he]
    have w7 : vword (s7.v .v26) e = ((vword (s.v a) e + BitVec.ofNat 32 127) >>> 7) * BitVec.ofNat 32 (hbMul g) + BitVec.ofNat 32 (hbAdd g) := by
      rw [h7.v, VG.AArch64.vword_map2 _ _ _ he, h6.get .v26 (by decide), w5, h6.get .v13 (by decide), h5.get .v13 (by decide), h4.get .v13 (by decide), h3.get .v13 (by decide), h2.get .v13 (by decide), h1.get .v13 (by decide), h13 e he]
    rw [h10.get .v26 (by decide), h9.v, VG.AArch64.vword_map2 _ _ _ he, h8.get .v26 (by decide), w7]
    rfl
  · intro e he
    have w2 : vword (s2.v .v28) e = vword (s.v b) e + BitVec.ofNat 32 127 := by
      rw [h2.v, VG.AArch64.vword_map2 _ _ _ he, h1.get b hb, h1.get .v11 (by decide), h11 e he]
    have w4 : vword (s4.v .v28) e = (vword (s.v b) e + BitVec.ofNat 32 127) >>> 7 := by
      rw [h4.v, VG.AArch64.vword_map2 _ _ _ he, h3.get .v28 (by decide), w2]
      rfl
    have w6 : vword (s6.v .v28) e = ((vword (s.v b) e + BitVec.ofNat 32 127) >>> 7) * BitVec.ofNat 32 (hbMul g) := by
      rw [h6.v, VG.AArch64.vword_map2 _ _ _ he, h5.get .v28 (by decide), w4, h5.get .v12 (by decide), h4.get .v12 (by decide), h3.get .v12 (by decide), h2.get .v12 (by decide), h1.get .v12 (by decide), h12 e he]
    have w8 : vword (s8.v .v28) e = ((vword (s.v b) e + BitVec.ofNat 32 127) >>> 7) * BitVec.ofNat 32 (hbMul g) + BitVec.ofNat 32 (hbAdd g) := by
      rw [h8.v, VG.AArch64.vword_map2 _ _ _ he, h7.get .v28 (by decide), w6, h7.get .v13 (by decide), h6.get .v13 (by decide), h5.get .v13 (by decide), h4.get .v13 (by decide), h3.get .v13 (by decide), h2.get .v13 (by decide), h1.get .v13 (by decide), h13 e he]
    rw [h10.v, VG.AArch64.vword_map2 _ _ _ he, h9.get .v28 (by decide), w8]
    rfl
end VG.Proof.MlDsa.AArch64.Optimized.Paired
