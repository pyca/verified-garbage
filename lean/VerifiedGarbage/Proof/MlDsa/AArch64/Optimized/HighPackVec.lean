import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackMath
import VerifiedGarbage.Proof.MlKem.AArch64.Vec

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.HighPack
open VG.Impl.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Round
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

/-- Four simultaneous decomposition quotients, without scalarizing lanes. -/
theorem hf_ok {g : Nat} (hg : IsG g) {d a : VReg}
    (hd18 : d ≠ .v18) (hd19 : d ≠ .v19)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (h17 : ∀ e < 4, vword (s.v .v17) e = BitVec.ofNat 32 127)
    (h18 : ∀ e < 4, vword (s.v .v18) e = BitVec.ofNat 32 (hbMul g))
    (h19 : ∀ e < 4, vword (s.v .v19) e = BitVec.ofNat 32 (hbAdd g))
    (k : ∀ t, VChg [d] s t →
      (∀ e < 4, vword (t.v d) e = raw g (vword (s.v a) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (hf g d a ++ rest)) s Q := by
  have hsh : VShiftOp.ushr.ok VArr.s4.esize (dShift g) = true := by
    rcases hg with rfl | rfl <;> rfl
  refine wp_vop (d := d) rfl fun s1 h1 => wp_vop (d := d) rfl fun s2 h2 =>
    wp_vop (d := d) rfl fun s3 h3 => wp_vop (d := d) rfl fun s4 h4 =>
    wp_vop (d := d) (by simp only [VOp.eval, hsh, ite_true]; rfl) fun t h5 => ?_
  have keep := (((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg
  refine k t (keep.mono (by intro r hr; simpa only [List.mem_append, List.mem_singleton, or_self] using hr)) ?_
  intro e he
  have w1 : vword (s1.v d) e = vword (s.v a) e + BitVec.ofNat 32 127 := by
    rw [h1.v, VG.AArch64.vword_map2 _ _ _ he, h17 e he]
  have w2 : vword (s2.v d) e = (vword (s.v a) e + BitVec.ofNat 32 127) >>> 7 := by
    rw [h2.v, VG.AArch64.vword_map2 _ _ _ he, w1]
    rfl
  have w3 : vword (s3.v d) e = ((vword (s.v a) e + BitVec.ofNat 32 127) >>> 7) * BitVec.ofNat 32 (hbMul g) := by
    rw [h3.v, VG.AArch64.vword_map2 _ _ _ he, w2, h2.get .v18 (Ne.symm hd18),
      h1.get .v18 (Ne.symm hd18), h18 e he]
  have w4 : vword (s4.v d) e = ((vword (s.v a) e + BitVec.ofNat 32 127) >>> 7) * BitVec.ofNat 32 (hbMul g) +
      BitVec.ofNat 32 (hbAdd g) := by
    rw [h4.v, VG.AArch64.vword_map2 _ _ _ he, w3, h3.get .v19 (Ne.symm hd19),
      h2.get .v19 (Ne.symm hd19), h1.get .v19 (Ne.symm hd19), h19 e he]
  rw [h5.v, VG.AArch64.vword_map2 _ _ _ he, w4]
  rfl

/-- The sign-mask correction implements all four high-bit outputs exactly. -/
theorem hb_ok {g : Nat} (hg : IsG g) {d a : VReg}
    (hd7 : d ≠ .v7) (hd18 : d ≠ .v18) (hd19 : d ≠ .v19) (hd20 : d ≠ .v20)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (h17 : ∀ e < 4, vword (s.v .v17) e = BitVec.ofNat 32 127)
    (h18 : ∀ e < 4, vword (s.v .v18) e = BitVec.ofNat 32 (hbMul g))
    (h19 : ∀ e < 4, vword (s.v .v19) e = BitVec.ofNat 32 (hbAdd g))
    (h20 : ∀ e < 4, vword (s.v .v20) e = BitVec.ofNat 32 (dMod g))
    (k : ∀ t, VChg [d,.v7] s t →
      (∀ e < 4, vword (t.v d) e = highWord g (vword (s.v a) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (hb g d a ++ rest)) s Q := by
  unfold Impl.MlDsa.AArch64.Optimized.HighPack.hb
  rw [List.append_assoc]
  refine hf_ok hg hd18 hd19 h17 h18 h19 fun u hu hw => ?_
  refine wp_vop (d := .v7) rfl fun s1 h1 => wp_vop (d := .v7) rfl fun s2 h2 =>
    wp_vop (d := d) rfl fun t h3 => ?_
  refine k t ((hu.trans ((h1.chg.trans h2.chg).trans h3.chg)).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    grind only
  · intro e he
    rw [h3.v]
    have vand (x y : BitVec 128) : vword (x &&& y) e = vword x e &&& vword y e := by
      simp only [vword, BitVec.extractLsb'_and]
    change vword (s2.v d &&& s2.v .v7) e = _
    rw [vand]
    rw [h2.get d hd7, h1.get d hd7, hw e he, h2.v, VG.AArch64.vword_map2 _ _ _ he]
    change raw g (vword (s.v a) e) &&& (vword (s1.v .v7) e).sshiftRight 31 = _
    rw [h1.v, VG.AArch64.vword_map2 _ _ _ he, hw e he,
      hu.v .v20 (by simp only [List.mem_singleton]; exact Ne.symm hd20), h20 e he]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
