import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Resident
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Squeeze

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq)

/-- Squeezing leaves the resident state intact; only two temporary vectors
and the scalar temporaries for an odd final word can change. -/
structure SqueezeKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r
  vec : ∀ r, r ≠ .v26 → r ≠ .v27 → t.v r = s.v r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem SqueezeKeep.refl (s : State) : SqueezeKeep s s :=
  ⟨fun _ _ _ => rfl,fun _ _ _ => rfl,rfl,rfl,rfl⟩

theorem SqueezeKeep.trans {s t u : State} (h : SqueezeKeep s t)
    (k : SqueezeKeep t u) : SqueezeKeep s u :=
  ⟨fun r h6 h7 => (k.gpr r h6 h7).trans (h.gpr r h6 h7),
   fun r h26 h27 => (k.vec r h26 h27).trans (h.vec r h26 h27),
   k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩

theorem stateReg_ne : ∀ i < 25, vreg i ≠ .v26 ∧ vreg i ≠ .v27 := by decide +kernel

theorem SqueezeKeep.pairs {s t : State} {A B : Spec.Sha3.State}
    (h : SqueezeKeep s t) (hp : VG.Proof.Sha3.AArch64.Neon.Pairs s A B) :
    VG.Proof.Sha3.AArch64.Neon.Pairs t A B := by
  intro i hi
  rw [h.vec _ (stateReg_ne i hi).1 (stateReg_ne i hi).2]
  exact hp i hi

private theorem narrow64 (w : BitVec 64) : (w.setWidth 128).setWidth 64 = w := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_eq]

private theorem pair_congr {a b c d : BitVec 64} (h : a = c) (k : b = d) :
    ofVDwords a b = ofVDwords c d := by
  subst h k
  rfl

theorem trn1_dwords (x y : BitVec 128) :
    VPermOp.eval .trn1 .d2 x y = ofVDwords (vdword x 0) (vdword y 0) := by
  simp only [VPermOp.eval,VArr.lanes,VArr.ofLanes,List.length_cons,List.length_nil,
    Nat.reduceAdd,Nat.reduceDiv]
  exact pair_congr (narrow64 _) (narrow64 _)

theorem trn2_dwords (x y : BitVec 128) :
    VPermOp.eval .trn2 .d2 x y = ofVDwords (vdword x 1) (vdword y 1) := by
  simp only [VPermOp.eval,VArr.lanes,VArr.ofLanes,List.length_cons,List.length_nil,
    Nat.reduceAdd,Nat.reduceDiv]
  exact pair_congr (narrow64 _) (narrow64 _)

/-- Four instructions emit four rate words without disturbing either state. -/
theorem squeezePair_ok {s : State} {a b : Addr} {ra rb : Reg} {i : Nat}
    (hi : 2*i+1 < 25) (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (hwa : InRegions s.wr (a+BitVec.ofNat 64 (16*i)) 16)
    (hwb : InRegions s.wr (b+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.Resident.squeezePair ra rb i)) s fun t =>
      SqueezeKeep s t ∧ t.mem =
        (s.mem.write (a+BitVec.ofNat 64 (16*i)) 16
          (ofVDwords (vdword (s.v (vreg (2*i))) 0) (vdword (s.v (vreg (2*i+1))) 0))).write
        (b+BitVec.ofNat 64 (16*i)) 16
          (ofVDwords (vdword (s.v (vreg (2*i))) 1) (vdword (s.v (vreg (2*i+1))) 1)) := by
  unfold Impl.MlDsa.AArch64.Optimized.Resident.squeezePair
  refine wp_vop (d := .v26) rfl fun s1 h1 => ?_
  refine wp_vop (d := .v27) rfl fun s2 h2 => ?_
  refine wp_strq (t := .v26) (a := a+BitVec.ofNat 64 (16*i)) ⟨by omega,by omega⟩
    (by rw [h2.gpr,h1.gpr,ha]) (by rw [h2.wr,h1.wr]; exact hwa) fun s3 h3 => ?_
  refine wp_strq (t := .v27) (a := b+BitVec.ofNat 64 (16*i)) ⟨by omega,by omega⟩
    (by rw [h3.gpr,h2.gpr,h1.gpr,hb]) (by rw [h3.wr,h2.wr,h1.wr]; exact hwb)
    fun t h4 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · refine ⟨fun r _ _ => ?_,fun r h26 h27 => ?_,?_,?_,?_⟩
    · rw [h4.gpr,h3.gpr,h2.gpr,h1.gpr]
    · rw [h4.v,h3.v,h2.other r h27,h1.other r h26]
    · exact h4.rd.trans (h3.rd.trans (h2.rd.trans h1.rd))
    · exact h4.wr.trans (h3.wr.trans (h2.wr.trans h1.wr))
    · exact h4.sp.trans (h3.sp.trans (h2.sp.trans h1.sp))
  · rw [h4.mem,h3.mem,h3.v,h2.v,h2.other .v26 (by decide),h1.v,
      h2.mem,h1.mem,trn1_dwords,trn2_dwords,
      h1.other _ (stateReg_ne _ (by omega)).1,
      h1.other _ (stateReg_ne _ hi).1]
/-- The odd final word reuses the established scalar pair-squeeze theorem. -/
theorem squeezeLast_ok {s : State} {a b : Addr} {ra rb : Reg} {i : Nat}
    (hi : i < 21) (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hwa : InRegions s.wr (VG.Proof.Sha3.AArch64.Neon.outAddr a i) 8)
    (hwb : InRegions s.wr (VG.Proof.Sha3.AArch64.Neon.outAddr b i) 8) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.Resident.squeezeLast ra rb i)) s fun t =>
      SqueezeKeep s t ∧ t.mem =
        (s.mem.writeW (VG.Proof.Sha3.AArch64.Neon.outAddr a i) (vdword (s.v (vreg i)) 0)).writeW
        (VG.Proof.Sha3.AArch64.Neon.outAddr b i) (vdword (s.v (vreg i)) 1) := by
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.squeeze_step hi ha hb ha6 ha7 hb6 hb7 hwa hwb) ?_
  intro t h
  exact ⟨⟨h.1.gpr,fun _ _ _ => congrFun h.1.vec _,h.1.rd,h.1.wr,h.1.sp⟩,h.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.Resident
