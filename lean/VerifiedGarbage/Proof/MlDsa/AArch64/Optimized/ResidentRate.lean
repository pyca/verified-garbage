import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Resident
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRounds
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeccakMix
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Squeeze

/-! ## From `Resident.lean` -/

section

/-! The resident core uses the established two-lane Keccak proof. -/
namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (Pairs)
open VG.Proof.Sha3.AArch64.Sha3.Vector (CoreKeep)

/-- An inline paired permutation, with no custom ABI or external symbol. -/
structure Core where
  code : Prog isa
  correct : ∀ {s : State} {A B : Spec.Sha3.State}, Pairs s A B →
    WP isa code s fun t => CoreKeep s t ∧ Pairs t (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B)

def originalCore : Core :=
  ⟨Impl.MlDsa.AArch64.Optimized.Resident.permute, VG.Proof.Sha3.AArch64.Neon.Hw.rounds2_ok⟩

def n2Core : Core :=
  ⟨.block Impl.MlDsa.AArch64.Optimized.KeccakMix.rounds, KeccakMix.rounds2_ok⟩

/-- Neither stream constrains the other: every input bit in both lanes is
covered, and the inline permutation leaves memory untouched. -/
theorem permute_ok {s : State} {A B : Spec.Sha3.State} (h : Pairs s A B) :
    WP isa Impl.MlDsa.AArch64.Optimized.Resident.permute s fun t =>
      CoreKeep s t ∧ Pairs t (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) :=
  VG.Proof.Sha3.AArch64.Neon.Hw.rounds2_ok h
end VG.Proof.MlDsa.AArch64.Optimized.Resident

end

/-! ## From `ResidentSqueeze.lean` -/

section

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

end

/-! ## From `ResidentRate.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.Sha3.AArch64.Neon (Pairs)

/-- Complete 128-bit groups of one serialized SHAKE rate. -/
def RatePairs (m : Mem) (a : Addr) (n : Nat) (A : Spec.Sha3.State) : Prop :=
  ∀ i < n, m.read (a+BitVec.ofNat 64 (16*i)) 16 = ofVDwords A[2*i]! A[2*i+1]!

theorem squeezePairs_ok {s : State} {a b : Addr} {ra rb : Reg} {n : Nat}
    {A B : Spec.Sha3.State} (hn : n ≤ 12) (hp : Pairs s A B)
    (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hd : (Region.mk a (16*n)).Disjoint ⟨b,16*n⟩)
    (hwa : ∀ i < n, InRegions s.wr (a+BitVec.ofNat 64 (16*i)) 16)
    (hwb : ∀ i < n, InRegions s.wr (b+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block ((List.range n).flatMap
      (Impl.MlDsa.AArch64.Optimized.Resident.squeezePair ra rb))) s fun t =>
      SqueezeKeep s t ∧ Pairs t A B ∧ RatePairs t.mem a n A ∧ RatePairs t.mem b n B ∧
        Frame [⟨a,16*n⟩,⟨b,16*n⟩] s.mem t.mem := by
  have ac (i : Nat) (hi : i < n) : (Region.mk a (16*n)).Contains (a+BitVec.ofNat 64 (16*i)) 16 :=
    Offset.contains_base a (by omega) (by omega)
  have bc (i : Nat) (hi : i < n) : (Region.mk b (16*n)).Contains (b+BitVec.ofNat 64 (16*i)) 16 :=
    Offset.contains_base b (by omega) (by omega)
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k t => SqueezeKeep s t ∧ RatePairs t.mem a k A ∧ RatePairs t.mem b k B ∧
      Frame [⟨a,16*n⟩,⟨b,16*n⟩] s.mem t.mem)
    (fun k t hk ht => ?_) n (Nat.le_refl _) s
    ⟨SqueezeKeep.refl _,fun _ h => by omega,fun _ h => by omega,Frame.refl _ _⟩)
    (fun t h => ⟨h.1,h.1.pairs hp,h.2.1,h.2.2.1,h.2.2.2⟩)
  have hpt := ht.1.pairs hp
  refine WP.mono (squeezePair_ok (by omega)
    ((ht.1.gpr ra ha6 ha7).trans ha) ((ht.1.gpr rb hb6 hb7).trans hb)
    (by rw [ht.1.wr]; exact hwa k hk) (by rw [ht.1.wr]; exact hwb k hk)) ?_
  intro u hu
  have hm : u.mem = (t.mem.write (a+BitVec.ofNat 64 (16*k)) 16 (ofVDwords A[2*k]! A[2*k+1]!)).write
      (b+BitVec.ofNat 64 (16*k)) 16 (ofVDwords B[2*k]! B[2*k+1]!) := by
    rw [hu.2,hpt _ (by omega),hpt _ (by omega),vdword_ofVDwords_0,vdword_ofVDwords_0,
      vdword_ofVDwords_1,vdword_ofVDwords_1]
  refine ⟨ht.1.trans hu.1,?_,?_,?_⟩
  · intro i hi
    rw [hm,Mem.read_write_sep (hd.sep (ac i (by omega)) (bc k hk)) (by decide)]
    by_cases he : i = k
    · subst i
      exact VG.Proof.Sha3.AArch64.Neon.read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep a (d := 16*i) (n := 16) (e := 16*k) (k := 16)
        (by omega) (by omega) (by omega)) (by decide)]
      exact ht.2.1 i (by omega)
  · intro i hi
    rw [hm]
    by_cases he : i = k
    · subst i
      exact VG.Proof.Sha3.AArch64.Neon.read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep b (d := 16*i) (n := 16) (e := 16*k) (k := 16)
        (by omega) (by omega) (by omega)) (by decide),
        Mem.read_write_sep (hd.symm.sep (bc i (by omega)) (ac k hk)) (by decide)]
      exact ht.2.2.1 i (by omega)
  · rw [hm]
    exact (ht.2.2.2.write (by simp) _ (ac k hk)).write (by simp) _ (bc k hk)
end VG.Proof.MlDsa.AArch64.Optimized.Resident

end
