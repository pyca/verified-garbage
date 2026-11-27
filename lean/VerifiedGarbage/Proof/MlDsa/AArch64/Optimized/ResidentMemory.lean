module

import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Resident
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

/-! ### `MlDsa.AArch64.Optimized.ResidentBlock`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.ResidentRate`, which this module and modules that import it used -/

section

/-! ## From `Resident.lean` -/

@[expose] public section

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
    VG.Proof.Sha3.AArch64.Sha3.Vector.RcTable s (s.gpr .x15) →
    WP isa code s fun t => CoreKeep s t ∧ Pairs t (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B)

/-- Neither stream constrains the other: every input bit in both lanes is
covered, and the inline permutation leaves memory untouched. -/
theorem permute_ok {s : State} {A B : Spec.Sha3.State} (h : Pairs s A B)
    (ht : VG.Proof.Sha3.AArch64.Sha3.Vector.RcTable s (s.gpr .x15)) :
    WP isa Impl.MlDsa.AArch64.Optimized.Resident.permute s fun t =>
      CoreKeep s t ∧ Pairs t (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) :=
  VG.Proof.Sha3.AArch64.Sha3.Vector.rounds_ok h ht

def originalCore : Core := ⟨Impl.MlDsa.AArch64.Optimized.Resident.permute, permute_ok⟩

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
  refine wp_strq (t := .v26) (a := a+BitVec.ofNat 64 (16*i)) ⟨by omega_using [],by omega_using [hi]⟩
    (by rw [h2.gpr,h1.gpr,ha]) (by rw [h2.wr,h1.wr]; exact hwa) fun s3 h3 => ?_
  refine wp_strq (t := .v27) (a := b+BitVec.ofNat 64 (16*i)) ⟨by omega_using [],by omega_using [hi]⟩
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
      h1.other _ (stateReg_ne _ (by omega_using [hi])).1,
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
    Offset.contains_base a (by omega_using [hi]) (by omega_using [hn, hi])
  have bc (i : Nat) (hi : i < n) : (Region.mk b (16*n)).Contains (b+BitVec.ofNat 64 (16*i)) 16 :=
    Offset.contains_base b (by omega_using [hi]) (by omega_using [hn, hi])
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k t => SqueezeKeep s t ∧ RatePairs t.mem a k A ∧ RatePairs t.mem b k B ∧
      Frame [⟨a,16*n⟩,⟨b,16*n⟩] s.mem t.mem)
    (fun k t hk ht => ?_) n (Nat.le_refl _) s
    ⟨SqueezeKeep.refl _,fun _ h => by omega,fun _ h => by omega,Frame.refl _ _⟩)
    (fun t h => ⟨h.1,h.1.pairs hp,h.2.1,h.2.2.1,h.2.2.2⟩)
  have hpt := ht.1.pairs hp
  refine WP.mono (squeezePair_ok (by omega_using [hn, hk])
    ((ht.1.gpr ra ha6 ha7).trans ha) ((ht.1.gpr rb hb6 hb7).trans hb)
    (by rw [ht.1.wr]; exact hwa k hk) (by rw [ht.1.wr]; exact hwb k hk)) ?_
  intro u hu
  have hm : u.mem = (t.mem.write (a+BitVec.ofNat 64 (16*k)) 16 (ofVDwords A[2*k]! A[2*k+1]!)).write
      (b+BitVec.ofNat 64 (16*k)) 16 (ofVDwords B[2*k]! B[2*k+1]!) := by
    rw [hu.2,hpt _ (by omega_using [hn, hk]),hpt _ (by omega_using [hn, hk]),vdword_ofVDwords_0,vdword_ofVDwords_0,
      vdword_ofVDwords_1,vdword_ofVDwords_1]
  refine ⟨ht.1.trans hu.1,?_,?_,?_⟩
  · intro i hi
    rw [hm,Mem.read_write_sep (hd.sep (ac i (by omega_using [hk, hi])) (bc k hk)) (by decide)]
    by_cases he : i = k
    · subst i
      exact VG.Proof.Sha3.AArch64.Neon.read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep a (d := 16*i) (n := 16) (e := 16*k) (k := 16)
        (by omega_using [he]) (by omega_using [hn, hk, hi]) (by omega_using [hn, hk])) (by decide)]
      exact ht.2.1 i (by omega_using [hi, he])
  · intro i hi
    rw [hm]
    by_cases he : i = k
    · subst i
      exact VG.Proof.Sha3.AArch64.Neon.read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep b (d := 16*i) (n := 16) (e := 16*k) (k := 16)
        (by omega_using [he]) (by omega_using [hn, hk, hi]) (by omega_using [hn, hk])) (by decide),
        Mem.read_write_sep (hd.symm.sep (bc i (by omega_using [hk, hi])) (ac k hk)) (by decide)]
      exact ht.2.2.1 i (by omega_using [hi, he])
  · rw [hm]
    exact (ht.2.2.2.write (by simp) _ (ac k hk)).write (by simp) _ (bc k hk)
end VG.Proof.MlDsa.AArch64.Optimized.Resident

end

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.Sha3.AArch64.Neon (Pairs)

/-- An odd-word rate: complete vector groups and its final scalar word. -/
def RateBlock (m : Mem) (a : Addr) (n : Nat) (A : Spec.Sha3.State) : Prop :=
  RatePairs m a n A ∧ m.readW (a+BitVec.ofNat 64 (16*n)) 64 = A[2*n]!

/-- Vector serialization of either SHAKE rate, including the odd final word. -/
theorem squeeze_ok {s : State} {a b : Addr} {ra rb : Reg} {n : Nat}
    {A B : Spec.Sha3.State} (hn : n ≤ 10) (hp : Pairs s A B)
    (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hd : (Region.mk a (16*n+8)).Disjoint ⟨b,16*n+8⟩)
    (hwa : ∀ i < n, InRegions s.wr (a+BitVec.ofNat 64 (16*i)) 16)
    (hwb : ∀ i < n, InRegions s.wr (b+BitVec.ofNat 64 (16*i)) 16)
    (hwal : InRegions s.wr (a+BitVec.ofNat 64 (16*n)) 8)
    (hwbl : InRegions s.wr (b+BitVec.ofNat 64 (16*n)) 8) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.Resident.squeeze (2*n+1) ra rb)) s fun t =>
      SqueezeKeep s t ∧ Pairs t A B ∧ RateBlock t.mem a n A ∧ RateBlock t.mem b n B ∧
        Frame [⟨a,16*n+8⟩,⟨b,16*n+8⟩] s.mem t.mem := by
  have ac (i : Nat) (hi : i < n) : (Region.mk a (16*n+8)).Contains (a+BitVec.ofNat 64 (16*i)) 16 :=
    Offset.contains_base a (by omega_using [hi]) (by omega_using [hn, hi])
  have bc (i : Nat) (hi : i < n) : (Region.mk b (16*n+8)).Contains (b+BitVec.ofNat 64 (16*i)) 16 :=
    Offset.contains_base b (by omega_using [hi]) (by omega_using [hn, hi])
  have al : (Region.mk a (16*n+8)).Contains (a+BitVec.ofNat 64 (16*n)) 8 :=
    Offset.contains_base a (by omega_using []) (by omega_using [hn])
  have bl : (Region.mk b (16*n+8)).Contains (b+BitVec.ofNat 64 (16*n)) 8 :=
    Offset.contains_base b (by omega_using []) (by omega_using [hn])
  have haSub : (Region.mk a (16*n)).Sub ⟨a,16*n+8⟩ := by
    simpa using Offset.sub_base a (d := 0) (n := 16*n) (k := 16*n+8) (by omega_using [])
  have hbSub : (Region.mk b (16*n)).Sub ⟨b,16*n+8⟩ := by
    simpa using Offset.sub_base b (d := 0) (n := 16*n) (k := 16*n+8) (by omega_using [])
  unfold Impl.MlDsa.AArch64.Optimized.Resident.squeeze
  rw [show (2*n+1)/2=n by omega_using [],show (2*n+1)%2=1 by omega_using [],ite_eq_left rfl,
    show 2*n+1-1=2*n by omega_using [],WP.block_append_iff]
  refine WP.mono (squeezePairs_ok (by omega_using [hn]) hp ha hb ha6 ha7 hb6 hb7
    ((hd.sub_left haSub).sub_right hbSub) hwa hwb) ?_
  intro t ht
  refine WP.mono (squeezeLast_ok (i := 2*n) (by omega_using [hn])
    ((ht.1.gpr ra ha6 ha7).trans ha) ((ht.1.gpr rb hb6 hb7).trans hb)
    ha6 ha7 hb6 hb7
    (by rw [ht.1.wr]; simpa [VG.Proof.Sha3.AArch64.Neon.outAddr,show 8*(2*n)=16*n by omega_using []] using hwal)
    (by rw [ht.1.wr]; simpa [VG.Proof.Sha3.AArch64.Neon.outAddr,show 8*(2*n)=16*n by omega_using []] using hwbl)) ?_
  intro u hu
  have hm : u.mem = (t.mem.writeW (a+BitVec.ofNat 64 (16*n)) A[2*n]!).writeW
      (b+BitVec.ofNat 64 (16*n)) B[2*n]! := by
    rw [hu.2,ht.2.1 _ (by omega_using [hn]),vdword_ofVDwords_0,vdword_ofVDwords_1]
    simp only [VG.Proof.Sha3.AArch64.Neon.outAddr,show 8*(2*n)=16*n by omega_using []]
  refine ⟨ht.1.trans hu.1,hu.1.pairs ht.2.1,⟨?_,?_⟩,⟨?_,?_⟩,?_⟩
  · intro i hi
    rw [hm,Mem.writeW,Mem.writeW,
      Mem.read_write_sep (hd.sep (ac i hi) bl) (by decide),
      Mem.read_write_sep (Offset.sep a (d := 16*i) (n := 16) (e := 16*n) (k := 8)
        (by omega_using [hi]) (by omega_using [hn, hi]) (by omega_using [hn])) (by decide)]
    exact ht.2.2.1 i hi
  · rw [hm,Mem.readW_writeW_sep (hd.sep al bl) (by decide),Mem.readW_writeW_self64]
  · intro i hi
    rw [hm,Mem.writeW,Mem.writeW,
      Mem.read_write_sep (Offset.sep b (d := 16*i) (n := 16) (e := 16*n) (k := 8)
        (by omega_using [hi]) (by omega_using [hn, hi]) (by omega_using [hn])) (by decide),
      Mem.read_write_sep (hd.symm.sep (bc i hi) al) (by decide)]
    exact ht.2.2.2.1 i hi
  · rw [hm,Mem.readW_writeW_self64]
  · rw [hm]
    have hf : Frame [⟨a,16*n+8⟩,⟨b,16*n+8⟩] s.mem t.mem :=
      ht.2.2.2.2.sub (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_,by simp,haSub⟩
        · exact ⟨_,by simp,hbSub⟩)
    exact (hf.writeW (by simp) _ al).writeW (by simp) _ bl
end VG.Proof.MlDsa.AArch64.Optimized.Resident

end

end

/-! ## From `ResidentStep.lean` -/

@[expose] public section

/-! ## From `ResidentCounter.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (Pairs)

/-- The three public loop updates leave all resident lanes and memory intact. -/
theorem advance_ok {s : State} {ra rb : Reg} {rate : Nat}
    (hrate : rate < 4096) (hab : ra ≠ rb)
    (ha28 : ra ≠ .x28) (hb28 : rb ≠ .x28) :
    WP isa (.block ([.addImm .x ra ra rate,.addImm .x rb rb rate,
      .subImm .x .x28 .x28 1] : List Instr)) s fun t =>
      t.gpr ra = s.gpr ra + BitVec.ofNat 64 rate ∧
      t.gpr rb = s.gpr rb + BitVec.ofNat 64 rate ∧
      t.gpr .x28 = s.gpr .x28 - 1 ∧
      (∀ r, r ≠ ra → r ≠ rb → r ≠ .x28 → t.gpr r = s.gpr r) ∧
      t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  let s1 := s.write .x ra (s.gpr ra + BitVec.ofNat 64 rate)
  let s2 := s1.write .x rb (s1.gpr rb + BitVec.ofNat 64 rate)
  let s3 := s2.write .x .x28 (s2.gpr .x28 - 1)
  refine WP.block_cons_iff.mpr ⟨s1,by simp [isa,reduceExec,hrate,State.read,s1],?_⟩
  refine WP.block_cons_iff.mpr ⟨s2,by simp [isa,reduceExec,hrate,State.read,s2],?_⟩
  refine WP.block_cons_iff.mpr ⟨s3,rfl,?_⟩
  apply WP.block_nil_iff.mpr
  dsimp only [s3,s2,s1]
  simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq]
  simp only [ha28,hb28,hab,Ne.symm hab,Ne.symm ha28,Ne.symm hb28,ite_false,ite_true,true_and]
  constructor
  · intro r hra hrb hr28
    simp only [hra,hrb,hr28,ite_false]
  · exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Resident

end

/-! ## From `ResidentMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64

/-- Later output blocks cannot change an already serialized rate block. -/
theorem RateBlock.keep {m m' : Mem} {a : Addr} {n : Nat} {A : Spec.Sha3.State}
    {rs : List Region} (h : RateBlock m a n A) (hn : n ≤ 10)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (Region.mk a (16*n+8)).Disjoint r) :
    RateBlock m' a n A := by
  constructor
  · intro i hi
    rw [hf.read (Offset.contains_base a (by omega_using [hi]) (by omega_using [hn, hi])) hd (by decide)]
    exact h.1 i hi
  · rw [hf.readW (Offset.contains_base a (by omega_using []) (by omega_using [hn])) hd (by decide)]
    exact h.2

def permuted (A : Spec.Sha3.State) : Nat → Spec.Sha3.State
  | 0 => A
  | j+1 => Spec.Sha3.keccakF (permuted A j)

/-- Output of the first `j` paired permutations. -/
def StreamOutput (m : Mem) (a : Addr) (n j : Nat) (A : Spec.Sha3.State) : Prop :=
  ∀ i < j, RateBlock m (a+BitVec.ofNat 64 ((16*n+8)*i)) n
    (permuted A (i+1))

/-- Adjacent bounded output blocks have disjoint addresses even if the base
address itself wraps. -/
theorem block_disjoint {a : Addr} {n i j : Nat} (hn : n ≤ 10)
    (hij : i < j) (hj : j < 65536) :
    (Region.mk (a+BitVec.ofNat 64 ((16*n+8)*i)) (16*n+8)).Disjoint
      ⟨a+BitVec.ofNat 64 ((16*n+8)*j),16*n+8⟩ := by
  have hij' := Nat.mul_le_mul_left (16*n+8) hij
  have hiBound := Nat.mul_le_mul (show 16*n+8 ≤ 168 by omega_using [hn]) (show i+1 ≤ 65536 by omega_using [hij, hj])
  have hjBound := Nat.mul_le_mul (show 16*n+8 ≤ 168 by omega_using [hn]) (show j+1 ≤ 65536 by omega_using [hj])
  simp only [Nat.mul_add,Nat.mul_one] at hij' hiBound hjBound
  exact Offset.disjoint a (Or.inl (by omega)) (by omega_using [hiBound]) (by omega_using [hjBound])

/-- Appending a block preserves every earlier block in both streams. -/
theorem StreamOutput.append {m m' : Mem} {a b : Addr} {n j blocks : Nat}
    {A B : Spec.Sha3.State} (hn : n ≤ 10) (hj : j < blocks) (hblocks : blocks ≤ 65536)
    (hd : (Region.mk a ((16*n+8)*blocks)).Disjoint ⟨b,(16*n+8)*blocks⟩)
    (ha : StreamOutput m a n j A) (hb : StreamOutput m b n j B)
    (hnewa : RateBlock m' (a+BitVec.ofNat 64 ((16*n+8)*j)) n (permuted A (j+1)))
    (hnewb : RateBlock m' (b+BitVec.ofNat 64 ((16*n+8)*j)) n (permuted B (j+1)))
    (hf : Frame [⟨a+BitVec.ofNat 64 ((16*n+8)*j),16*n+8⟩,
      ⟨b+BitVec.ofNat 64 ((16*n+8)*j),16*n+8⟩] m m') :
    StreamOutput m' a n (j+1) A ∧ StreamOutput m' b n (j+1) B := by
  have sub (p : Addr) (i : Nat) (hi : i < blocks) :
      (Region.mk (p+BitVec.ofNat 64 ((16*n+8)*i)) (16*n+8)).Sub
        ⟨p,(16*n+8)*blocks⟩ := by
    apply Offset.sub_base
    have h := Nat.mul_le_mul_left (16*n+8) hi
    simpa only [Nat.mul_succ] using h
  constructor
  · intro i hi
    by_cases he : i = j
    · simpa only [he] using hnewa
    · refine (ha i (by omega_using [hi, he])).keep hn hf ?_
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact block_disjoint hn (by omega_using [hi, he]) (by omega_using [hj, hblocks])
      · exact (hd.sub_left (sub a i (by omega_using [hj, hi]))).sub_right (sub b j hj)
  · intro i hi
    by_cases he : i = j
    · simpa only [he] using hnewb
    · refine (hb i (by omega_using [hi, he])).keep hn hf ?_
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact (hd.symm.sub_left (sub b i (by omega_using [hj, hi]))).sub_right (sub a j hj)
      · exact block_disjoint hn (by omega_using [hi, he]) (by omega_using [hj, hblocks])

end VG.Proof.MlDsa.AArch64.Optimized.Resident

end
