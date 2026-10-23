module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Cross
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Core
import VerifiedGarbage.Proof.Ed448.AArch64.Window.TableInit
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.MulSlots
import VerifiedGarbage.Proof.Framework.Block

/-! Retain the existing cofactor comparison after joint scalar multiplication. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64 (RX RY CAN)
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Impl.X448.AArch64.Base (constSlot)
open VG.Proof.X448.AArch64 (Scr Keeps Outside2 limbs word)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt zero_env constSlot_ok bnd_of_words F_of_words)
open VG.Proof.Ed448.AArch64.Window (Cross dbl2 copy3_ok copyS_ok pt_of_limbs bnd_copy
  crossClob crossClob_clob crossClob_ckeep dblEnv_345 dblPt_eq FV_of_limbs)
open VG.Proof.Ed448.AArch64.Point56 (mulOpK)
open VG.Spec.Ed448 (Point)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E
local notation "FV" => VG.Proof.X448.AArch64.Weak.F

theorem cross_ok {s:State} {base:Addr} (hs:Scr s base) (hb:BEnv s.mem base)
    (hz5:Bnd Mb s.mem base (slot 5)) (h20:EV s.mem base 20=1)
    (hrx:∀ i<8,limbs s.mem base RX i<Ib) (hry:∀ i<8,limbs s.mem base RY i<Ib) :
    WP isa cross s fun t =>
      Scr t base ∧ Keeps crossClob s t ∧ Outside2 base 64 2816 ACC 1152 s.mem t.mem ∧
      Cross (pt (EV s.mem base) 3 4 5) ⟨FV s.mem base RX,FV s.mem base RY,1⟩ (EV t.mem base) ∧
      (∀ i:Index,12 ≤ i.val → i.val<16 → Bnd Mb t.mem base (slot i.val)):=by
  unfold cross
  -- `Q`, doubled twice.
  rw [WP.seq_iff]
  refine WP.mono (Point56.doubleCall_ok hs hb hz5) fun t3 ⟨k3, b3, s3, _, _, m3, e3, _⟩ => ?_
  have hs3 := k3.scr hs
  have one3 : EV t3.mem base 20 = 1 := by rw [Same.env s3 (i := 20) (by decide)]; exact h20
  rw [WP.seq_iff]
  refine WP.mono (Point56.doubleCall_ok hs3 b3 m3) fun t4 ⟨k4, b4, s4, _, _, _, e4, _⟩ => ?_
  have hs4 := k4.scr hs3
  have one4 : EV t4.mem base 20 = 1 := by rw [Same.env s4 (i := 20) (by decide)]; exact one3
  have q4 : pt (EV t4.mem base) 3 4 5 = dbl2 (pt (EV s.mem base) 3 4 5) := by
    rw [e4, dblEnv_345, one3, dblPt_eq, e3, dblEnv_345, h20, dblPt_eq]; rfl
  -- `Q` to slots 0–2, and `R` into slots 3–5.
  rw [WP.seq_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy3_ok hs4 0 3 (by decide) (by decide) (by decide)) fun t5 ⟨v5, o5, f5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  -- `RX` and `RY`, kept by every step so far.
  have mR : ∀ o, o = RX ∨ o = RY → ∀ i < 8, limbs t5.mem base o i = limbs s.mem base o i := fun o ho i hi => by
    have hn : o + 8 * i + 8 ≤ 8192 := by rcases ho with rfl | rfl <;> simp only [RX, RY, CAN] <;> omega
    refine congrArg BitVec.toNat ?_
    rw [f5.word (Or.inr (by rcases ho with rfl | rfl <;> simp only [slot, RX, RY, CAN] <;> omega)) hn,
      k4.mem.word (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY, CAN] <;> omega))
        (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY, CAN, ACC] <;> omega)) hn,
      k3.mem.word (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY, CAN] <;> omega))
        (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY, CAN, ACC] <;> omega)) hn]

  refine WP.mono (copyS_ok hs5 (o := slot 3) (a := RX) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t6 ⟨v6, o6, k6⟩ => ?_
  have hs6 := hs5.of_keeps k6 (by decide)
  refine WP.mono (copyS_ok hs6 (o := slot 4) (a := RY) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t7 ⟨v7, o7, k7⟩ => ?_
  have hs7 := hs6.of_keeps k7 (by decide)
  refine WP.mono (constSlot_ok hs7 (o := slot 5) (by decide) (by decide) 1) fun t8 ⟨v8, o8, k8⟩ => ?_
  have hs8 := hs7.of_keeps k8 (by decide)
  have keep8 : ∀ i : Index, i ≠ 3 → i ≠ 4 → i ≠ 5 → ∀ j < 8,
      limbs t8.mem base (slot i.val) j = limbs t5.mem base (slot i.val) j := fun i h3 h4 h5 j hj => by
    have := i.isLt
    have n3 : i.val ≠ 3 := fun e => h3 (Fin.ext e)
    have n4 : i.val ≠ 4 := fun e => h4 (Fin.ext e)
    have n5 : i.val ≠ 5 := fun e => h5 (Fin.ext e)
    rw [o8.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega),
      o7.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega),
      o6.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega)]
  have l3 : ∀ j < 8, limbs t8.mem base (slot 3) j = limbs s.mem base RX j := fun j hj => by
    rw [o8.limbs (by decide) (by decide) (by omega), o7.limbs (by decide) (by decide) (by omega), v6 j hj,
      mR _ (.inl rfl) j hj]
  have l4 : ∀ j < 8, limbs t8.mem base (slot 4) j = limbs s.mem base RY j := fun j hj => by
    rw [o8.limbs (by decide) (by decide) (by omega), v7 j hj,
      o6.limbs (by simp only [RY, CAN]; decide) (by simp only [RY, CAN]; decide) (by omega), mR _ (.inr rfl) j hj]
  have l0 : ∀ c < 3, ∀ j < 8, limbs t8.mem base (slot (0 + c)) j = limbs t4.mem base (slot (3 + c)) j :=
    fun c hc j hj => by
      rw [show limbs t8.mem base (slot (0 + c)) j = limbs t8.mem base (slot (⟨0 + c, by omega⟩ : Index).val) j
        from rfl, keep8 _ (by intro h; simp [Fin.ext_iff] at h; omega) (by intro h; simp [Fin.ext_iff] at h; omega)
        (by intro h; simp [Fin.ext_iff] at h; omega) j hj]
      exact v5 c hc j hj
  have b8 : BEnv t8.mem base := by
    intro i
    by_cases h3 : i = 3
    · subst h3; exact fun j hj => by show limbs t8.mem base (slot 3) j < Ib; rw [l3 j hj]; exact hrx j hj
    by_cases h4 : i = 4
    · subst h4; exact fun j hj => by show limbs t8.mem base (slot 4) j < Ib; rw [l4 j hj]; exact hry j hj
    by_cases h5 : i = 5
    · subst h5; exact bnd_of_words v8
    · refine fun j hj => ?_
      rw [keep8 i h3 h4 h5 j hj]
      by_cases h : i.val < 0 ∨ 0 + 3 ≤ i.val
      · rw [o5 i h j hj]; exact b4 i j hj
      · have : i.val = 0 + i.val := by omega
        show limbs t5.mem base (slot i.val) j < Ib
        rw [this, v5 _ (by omega) j hj]; exact b4 ⟨3 + i.val, by omega⟩ j hj
  have e8 : ∀ i : Index, i ≠ 3 → i ≠ 4 → i ≠ 5 → EV t8.mem base i = EV t5.mem base i := fun i h3 h4 h5 =>
    congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (keep8 i h3 h4 h5))
  have r8 : pt (EV t8.mem base) 3 4 5 = ⟨FV s.mem base RX, FV s.mem base RY, 1⟩ := by
    show (⟨FV t8.mem base (slot 3), FV t8.mem base (slot 4), FV t8.mem base (slot 5)⟩ : Point) = _
    rw [FV_of_limbs l3, FV_of_limbs l4, F_of_words v8]
  have q8 : pt (EV t8.mem base) 0 1 2 = dbl2 (pt (EV s.mem base) 3 4 5) := by
    rw [pt_of_limbs (x := 0) (y := 1) (z := 2) (x' := 3) (y' := 4) (z' := 5) l0 rfl rfl rfl rfl rfl rfl, q4]
  have one8 : EV t8.mem base 20 = 1 := by
    rw [e8 20 (by decide) (by decide) (by decide)]
    rw [show EV t5.mem base 20 = EV t4.mem base 20 from
      congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (o5 20 (by decide)))]
    exact one4
  have z8 : Bnd Mb t8.mem base (slot (5 : Index).val) := fun j hj => by
    show (word t8.mem base (slot 5 + 8 * j)).toNat < Mb
    rw [v8 j hj]; exact Nat.lt_of_lt_of_le (VG.Proof.X448.AArch64.Base.limb_lt _ _) (by decide)
  -- `R`, doubled twice.
  rw [WP.seq_iff]
  refine WP.mono (Point56.doubleCall_ok hs8 b8 z8) fun t9 ⟨k9, b9, s9, _, _, m9, e9, _⟩ => ?_
  have hs9 := k9.scr hs8
  have one9 : EV t9.mem base 20 = 1 := by rw [Same.env s9 (i := 20) (by decide)]; exact one8
  rw [WP.seq_iff]
  refine WP.mono (Point56.doubleCall_ok hs9 b9 m9) fun t10 ⟨k10, b10, s10, _, _, _, e10, _⟩ => ?_
  have hs10 := k10.scr hs9
  have r10 : pt (EV t10.mem base) 3 4 5 = dbl2 ⟨FV s.mem base RX, FV s.mem base RY, 1⟩ := by
    rw [e10, dblEnv_345, one9, dblPt_eq, e9, dblEnv_345, one8, dblPt_eq, r8]; rfl
  have q10 : pt (EV t10.mem base) 0 1 2 = dbl2 (pt (EV s.mem base) 3 4 5) := by
    rw [← q8]; simp only [pt]
    rw [Same.env s10 (i := 0) (by decide), Same.env s10 (i := 1) (by decide), Same.env s10 (i := 2) (by decide),
      Same.env s9 (i := 0) (by decide), Same.env s9 (i := 1) (by decide), Same.env s9 (i := 2) (by decide)]
  -- The products.
  refine mulOpK hs10 b10 12 0 5 (Or.inr (by decide)) fun t11 k11 b11 m12 s11 e11 => ?_
  have hs11 := k11.scr hs10
  refine mulOpK hs11 b11 13 3 2 (Or.inr (by decide)) fun t12 k12 b12 m13 s12 e12 => ?_
  have hs12 := k12.scr hs11
  refine mulOpK hs12 b12 14 1 5 (Or.inr (by decide)) fun t13 k13 b13 m14 s13 e13 => ?_
  have hs13 := k13.scr hs12
  refine mulOpK hs13 b13 15 4 2 (Or.inr (by decide)) fun t k14 b14 m15 s14 e14 => WP.block_nil ?_
  have qx : EV t10.mem base 0 = (dbl2 (pt (EV s.mem base) 3 4 5)).X :=
    congrArg Point.X q10
  have qy : EV t10.mem base 1 = (dbl2 (pt (EV s.mem base) 3 4 5)).Y :=
    congrArg Point.Y q10
  have qz : EV t10.mem base 2 = (dbl2 (pt (EV s.mem base) 3 4 5)).Z :=
    congrArg Point.Z q10
  have rx : EV t10.mem base 3 = (dbl2 ⟨FV s.mem base RX, FV s.mem base RY, 1⟩).X := congrArg Point.X r10
  have ry : EV t10.mem base 4 = (dbl2 ⟨FV s.mem base RX, FV s.mem base RY, 1⟩).Y := congrArg Point.Y r10
  have rz : EV t10.mem base 5 = (dbl2 ⟨FV s.mem base RX, FV s.mem base RY, 1⟩).Z := congrArg Point.Z r10
  have kf : FKeep base t10 t := k11.trans (k12.trans (k13.trans k14))
  refine ⟨kf.scr hs10, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have ka:Keeps crossClob s t5:=((crossClob_ckeep k3).trans (crossClob_ckeep k4)).trans
      (crossClob_clob k5)
    have kb:Keeps crossClob t5 t8:=((crossClob_clob k6).trans (crossClob_clob k7)).trans
      (k8.mono (by intro r hr;simp only [List.mem_singleton] at hr;subst r;decide))
    exact ((ka.trans kb).trans ((crossClob_ckeep k9).trans (crossClob_ckeep k10))).trans
      (kf.regs.mono (by intro r hr;exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hr))))
  · have o58:Outside2 base 64 2816 ACC 1152 t4.mem t8.mem:=fun x a _ => by
      rw [o8 x (by simp only [slot] at a ⊢;omega),o7 x (by simp only [slot] at a ⊢;omega),
        o6 x (by simp only [slot] at a ⊢;omega),f5 x (by simp only [slot] at a ⊢;omega)]
    exact ((((k3.mem.trans k4.mem).trans o58).trans k9.mem).trans k10.mem).trans kf.mem
  · rw [Same.env s14 (i := 12) (by decide), Same.env s13 (i := 12) (by decide), Same.env s12 (i := 12) (by decide),
      e11, Function.update_self, qx, rz]
  · rw [Same.env s14 (i := 13) (by decide), Same.env s13 (i := 13) (by decide), e12, Function.update_self,
      Same.env s11 (i := 3) (by decide), Same.env s11 (i := 2) (by decide), rx, qz]
  · rw [Same.env s14 (i := 14) (by decide), e13, Function.update_self, Same.env s12 (i := 1) (by decide),
      Same.env s11 (i := 1) (by decide), Same.env s12 (i := 5) (by decide), Same.env s11 (i := 5) (by decide), qy, rz]
  · rw [e14, Function.update_self, Same.env s13 (i := 4) (by decide), Same.env s12 (i := 4) (by decide),
      Same.env s11 (i := 4) (by decide), Same.env s13 (i := 2) (by decide), Same.env s12 (i := 2) (by decide),
      Same.env s11 (i := 2) (by decide), ry, qz]
  · intro i h1 h2
    have hi : i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by
      rcases i with ⟨i, hlt⟩; simp only [Fin.ext_iff] at h1 h2 ⊢; omega
    rcases hi with rfl | rfl | rfl | rfl
    · exact s14.bnd (by decide) (s13.bnd (by decide) (s12.bnd (by decide) m12))
    · exact s14.bnd (by decide) (s13.bnd (by decide) m13)
    · exact s14.bnd (by decide) m14
    · exact m15

end VG.Proof.Ed448.AArch64.Sparse
