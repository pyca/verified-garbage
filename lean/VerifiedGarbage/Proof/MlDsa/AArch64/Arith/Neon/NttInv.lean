import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.MlKem.AArch64.AddSub
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.NttInv
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedLayer`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Word`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q)

/-- The widening product of two vector words. -/
def product (x z : BitVec 32) : BitVec 64 := x.setWidth 64 * z.setWidth 64

def multiplier (p : BitVec 64) : BitVec 32 := p.extractLsb' 0 32 * BitVec.ofNat 32 montQInv

def redc (p : BitVec 64) : BitVec 32 :=
  (p + (VG.Proof.MlDsa.AArch64.Arith.Neon.multiplier p).setWidth 64 * BitVec.ofNat 64 VG.Spec.MlDsa.q).extractLsb' 32 32

theorem product_nat (x z : BitVec 32) : (VG.Proof.MlDsa.AArch64.Arith.Neon.product x z).toNat = x.toNat * z.toNat := by
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.product, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have hx := x.isLt
  have hz := z.isLt
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2^64),
    Nat.mod_eq_of_lt (by omega : z.toNat < 2^64)]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hx hz) (by decide))

theorem multiplier_nat (p : BitVec 64) : (VG.Proof.MlDsa.AArch64.Arith.Neon.multiplier p).toNat = montM p.toNat := by
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.multiplier, BitVec.toNat_mul, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : montQInv < 2^32)]
  rfl

theorem redc_nat (p : BitVec 64) (hp : p.toNat < VG.Spec.MlDsa.q * 2^32) :
    (VG.Proof.MlDsa.AArch64.Arith.Neon.redc p).toNat = VG.Proof.MlDsa.Arith.mont p.toNat := by
  have hM := montM_lt p.toNat
  have hR := mont_lt hp
  have hsum := mont_mul p.toNat
  have hq : VG.Spec.MlDsa.q = 8380417 := rfl
  have hm : ((VG.Proof.MlDsa.AArch64.Arith.Neon.multiplier p).setWidth 64 * BitVec.ofNat 64 VG.Spec.MlDsa.q).toNat = montM p.toNat * VG.Spec.MlDsa.q := by
    rw [BitVec.toNat_mul, BitVec.toNat_setWidth, VG.Proof.MlDsa.AArch64.Arith.Neon.multiplier_nat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : montM p.toNat < 2^64), Nat.mod_eq_of_lt (by decide : q < 2^64)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_right hM (by decide)) (by decide))
  have ha : (p + (VG.Proof.MlDsa.AArch64.Arith.Neon.multiplier p).setWidth 64 * BitVec.ofNat 64 VG.Spec.MlDsa.q).toNat = VG.Proof.MlDsa.Arith.mont p.toNat * 2^32 := by
    rw [BitVec.toNat_add, hm, ← hsum]
    exact Nat.mod_eq_of_lt (by rw [hq] at hR; omega)
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.redc, BitVec.extractLsb'_toNat, ha, Nat.shiftRight_eq_div_pow,
    Nat.mul_div_cancel _ (by decide)]
  exact Nat.mod_eq_of_lt (by rw [hq] at hR; omega)

theorem mont_word_nat (x z : BitVec 32) (hz : z.toNat < VG.Spec.MlDsa.q) :
    (VG.Proof.MlDsa.AArch64.Arith.Neon.redc (VG.Proof.MlDsa.AArch64.Arith.Neon.product x z)).toNat = VG.Proof.MlDsa.Arith.mont (x.toNat * z.toNat) := by
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.redc_nat _ (by rw [VG.Proof.MlDsa.AArch64.Arith.Neon.product_nat]; simpa only [Nat.mul_comm] using Nat.mul_lt_mul'' x.isLt hz), VG.Proof.MlDsa.AArch64.Arith.Neon.product_nat]
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VUpd Lanes wp_vop lanes_sub lanes_umin)
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q)

set_option linter.unusedSimpArgs false

/-- Unzip the low or high halves of four widening products. -/
theorem unzip_wide (hi : Bool) (a b c d : BitVec 64) :
    VPermOp.eval (if hi then .uzp2 else .uzp1) .s4 (ofVDwords a b) (ofVDwords c d) =
      ofVWords (a.extractLsb' (if hi then 32 else 0) 32)
        (b.extractLsb' (if hi then 32 else 0) 32)
        (c.extractLsb' (if hi then 32 else 0) 32)
        (d.extractLsb' (if hi then 32 else 0) 32) := by
  apply vec_ext
  intro e he
  rw [vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
    cases hi <;> ext i hi <;>
    simp +arith [VPermOp.eval, VArr.ofLanes, VArr.lanes, vword, ofVDwords,
      ofVWords, BitVec.getElem_extractLsb', BitVec.getLsbD_append, hi]
  all_goals (repeat rw [BitVec.getLsbD_append])
  all_goals simp +arith [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi]
  all_goals rw [BitVec.getLsbD_append]
  all_goals simp +arith [hi]
  all_goals (intro h; omega)

/-- Pointwise operations on a concrete four-word vector. -/
theorem map2_words (f : (w : Nat) → BitVec w → BitVec w → BitVec w)
    (a b c d e f' g h : BitVec 32) :
    VArr.s4.map2 f (ofVWords a b c d) (ofVWords e f' g h) =
      ofVWords (f 32 a e) (f 32 b f') (f 32 c g) (f 32 d h) := by
  apply vec_ext
  intro i hi
  rw [vword_map2 _ _ _ hi, vword_ofVWords _ _ _ _ hi,
    vword_ofVWords _ _ _ _ hi, vword_ofVWords _ _ _ _ hi]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem csub_ok {d t : VReg} (hdt : d ≠ t := by decide)
    (hq : Lanes (s.v .v16) fun _ => VG.Spec.MlDsa.q) {f : Nat → Nat}
    (hf : Lanes (s.v d) f) (hlt : ∀ e < 4, f e < 2*VG.Spec.MlDsa.q)
    (k : ∀ s', VChg [t,d] s s' → Lanes (s'.v d) (fun e => f e % VG.Spec.MlDsa.q) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (csub d t ++ rest)) s Q := by
  refine wp_vop (d := t) rfl fun s₁ h₁ => wp_vop (d := d) rfl fun s₂ h₂ =>
    k s₂ (h₁.chg.trans h₂.chg) ?_
  have l₁ := lanes_sub hf hq
  rw [← h₁.v] at l₁
  rw [h₂.v]
  refine (lanes_umin (by rw [h₁.get d hdt]; exact hf) l₁).congr fun e he => ?_
  have := hlt e he
  change f e < 2*8380417 at this
  change min (f e) ((2^32 - 8380417 + f e) % 2^32) = f e % 8380417
  omega

/-- Seven instructions perform REDC on four independent lanes. -/
theorem mont_ok {d z : VReg}
    (hd : d ∉ [VReg.v2, .v3, .v4]) (hz : z ∉ [VReg.v2, .v3, .v4])
    (hq : s.v .v16 = ofVWords (BitVec.ofNat 32 VG.Spec.MlDsa.q) (BitVec.ofNat 32 VG.Spec.MlDsa.q)
      (BitVec.ofNat 32 VG.Spec.MlDsa.q) (BitVec.ofNat 32 VG.Spec.MlDsa.q))
    (hqi : s.v .v17 = ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
      (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv))
    (k : ∀ s', VChg [.v2,.v3,.v4,d] s s' →
      s'.v d = ofVWords (VG.Proof.MlDsa.AArch64.Arith.Neon.redc (VG.Proof.MlDsa.AArch64.Arith.Neon.product (vword (s.v d) 0) (vword (s.v z) 0)))
        (VG.Proof.MlDsa.AArch64.Arith.Neon.redc (VG.Proof.MlDsa.AArch64.Arith.Neon.product (vword (s.v d) 1) (vword (s.v z) 1)))
        (VG.Proof.MlDsa.AArch64.Arith.Neon.redc (VG.Proof.MlDsa.AArch64.Arith.Neon.product (vword (s.v d) 2) (vword (s.v z) 2)))
        (VG.Proof.MlDsa.AArch64.Arith.Neon.redc (VG.Proof.MlDsa.AArch64.Arith.Neon.product (vword (s.v d) 3) (vword (s.v z) 3))) →
      WP isa (.block rest) s' Q) : WP isa (.block (mont d z ++ rest)) s Q := by
  have hd2 : d ≠ .v2 := fun h => hd (by simp [h])
  have hd3 : d ≠ .v3 := fun h => hd (by simp [h])
  have hd4 : d ≠ .v4 := fun h => hd (by simp [h])
  have hz2 : z ≠ .v2 := fun h => hz (by simp [h])
  have hz3 : z ≠ .v3 := fun h => hz (by simp [h])
  have hz4 : z ≠ .v4 := fun h => hz (by simp [h])
  have eq_q : (BitVec.ofNat 32 VG.Spec.MlDsa.q).setWidth 64 = BitVec.ofNat 64 VG.Spec.MlDsa.q := by decide
  let p := fun e => VG.Proof.MlDsa.AArch64.Arith.Neon.product (vword (s.v d) e) (vword (s.v z) e)
  refine wp_vop (d := .v2) rfl fun s₁ h₁ => ?_
  have a₁ : s₁.v .v2 = ofVDwords (p 0) (p 1) := h₁.v
  refine wp_vop (d := .v3) rfl fun s₂ h₂ => ?_
  have a₂ : s₂.v .v3 = ofVDwords (p 2) (p 3) := by
    rw [h₂.v, h₁.get d hd2, h₁.get z hz2]
    rfl
  refine wp_vop (d := .v4) rfl fun s₃ h₃ => ?_
  have a₃ : s₃.v .v4 = ofVWords ((p 0).extractLsb' 0 32) ((p 1).extractLsb' 0 32)
      ((p 2).extractLsb' 0 32) ((p 3).extractLsb' 0 32) := by
    rw [h₃.v, h₂.get .v2, a₁, a₂]; exact VG.Proof.MlDsa.AArch64.Arith.Neon.unzip_wide false _ _ _ _
  refine wp_vop (d := .v4) rfl fun s₄ h₄ => ?_
  have a₄ : s₄.v .v4 = ofVWords (VG.Proof.MlDsa.AArch64.Arith.Neon.multiplier (p 0)) (VG.Proof.MlDsa.AArch64.Arith.Neon.multiplier (p 1))
      (VG.Proof.MlDsa.AArch64.Arith.Neon.multiplier (p 2)) (VG.Proof.MlDsa.AArch64.Arith.Neon.multiplier (p 3)) := by
    rw [h₄.v, a₃, h₃.get .v17, h₂.get .v17, h₁.get .v17, hqi, VG.Proof.MlDsa.AArch64.Arith.Neon.map2_words]
    rfl
  refine wp_vop (d := .v2) rfl fun s₅ h₅ => ?_
  have a₅ : s₅.v .v2 = ofVDwords
      (p 0 + (VG.Proof.MlDsa.AArch64.Arith.Neon.multiplier (p 0)).setWidth 64 * BitVec.ofNat 64 VG.Spec.MlDsa.q)
      (p 1 + (VG.Proof.MlDsa.AArch64.Arith.Neon.multiplier (p 1)).setWidth 64 * BitVec.ofNat 64 VG.Spec.MlDsa.q) := by
    rw [h₅.v, h₄.get .v2, h₃.get .v2, h₂.get .v2, a₁, a₄,
      h₄.get .v16, h₃.get .v16, h₂.get .v16, h₁.get .v16, hq]
    simp only [ite_true, ite_false, Bool.false_eq_true, Nat.zero_add, Nat.add_zero, Nat.reduceAdd, vdword_ofVDwords_0, vdword_ofVDwords_1, vword_ofVWords_0,
      vword_ofVWords_1, eq_q]
  refine wp_vop (d := .v3) rfl fun s₆ h₆ => ?_
  have a₆ : s₆.v .v3 = ofVDwords
      (p 2 + (VG.Proof.MlDsa.AArch64.Arith.Neon.multiplier (p 2)).setWidth 64 * BitVec.ofNat 64 VG.Spec.MlDsa.q)
      (p 3 + (VG.Proof.MlDsa.AArch64.Arith.Neon.multiplier (p 3)).setWidth 64 * BitVec.ofNat 64 VG.Spec.MlDsa.q) := by
    rw [h₆.v, h₅.get .v3, h₄.get .v3, h₃.get .v3, a₂, h₅.get .v4, a₄,
      h₅.get .v16, h₄.get .v16, h₃.get .v16, h₂.get .v16, h₁.get .v16, hq]
    simp only [ite_true, ite_false, Bool.false_eq_true, Nat.zero_add, Nat.add_zero, Nat.reduceAdd, vdword_ofVDwords_0, vdword_ofVDwords_1, vword_ofVWords_2,
      vword_ofVWords_3, eq_q]
  refine wp_vop (d := d) rfl fun s₇ h₇ => k s₇
    (VChg.mono (rs' := [.v2,.v3,.v4,d])
      ((((((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).trans h₅.chg).trans h₆.chg).trans h₇.chg)
      (by
        intro r hr
        simp only [List.mem_append, List.mem_cons, List.mem_singleton,
        List.mem_nil_iff, or_false] at *
        rcases hr with (((((h | h) | h) | h) | h) | h) | h <;> simp [h])) ?_
  rw [h₇.v, h₆.get .v2, a₅, a₆]
  exact VG.Proof.MlDsa.AArch64.Arith.Neon.unzip_wide true _ _ _ _

end
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lanes`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg Lanes wp_vop lanes_add lanes_sub)
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q)

structure VConsts (s : State) : Prop where
  q : s.v .v16 = ofVWords (BitVec.ofNat 32 VG.Spec.MlDsa.q) (BitVec.ofNat 32 VG.Spec.MlDsa.q)
    (BitVec.ofNat 32 VG.Spec.MlDsa.q) (BitVec.ofNat 32 VG.Spec.MlDsa.q)
  qi : s.v .v17 = ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
    (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)

theorem VConsts.chg {s s' : State} (hc : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s) {rs : List VReg} (h : VChg rs s s')
    (h16 : VReg.v16 ∉ rs := by decide) (h17 : VReg.v17 ∉ rs := by decide) : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s' :=
  ⟨by rw [h.get _ h16]; exact hc.q, by rw [h.get _ h17]; exact hc.qi⟩

theorem VConsts.lanes_q {s : State} (hc : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s) : Lanes (s.v .v16) fun _ => VG.Spec.MlDsa.q := by
  rw [hc.q]
  exact VG.Proof.MlKem.AArch64.lanes_dup.congr fun _ _ => by decide

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem mont_lanes {d z : VReg}
    (hd : d ∉ [VReg.v2,.v3,.v4]) (hz : z ∉ [VReg.v2,.v3,.v4]) (hc : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s)
    {A Z : Nat → Nat} (ha : Lanes (s.v d) A) (hzv : Lanes (s.v z) Z)
    (hzlt : ∀ e < 4, Z e < VG.Spec.MlDsa.q)
    (k : ∀ s', VChg [.v2,.v3,.v4,d] s s' → Lanes (s'.v d) (fun e => mont (A e * Z e)) →
      WP isa (.block rest) s' Q) : WP isa (.block (Impl.MlDsa.AArch64.Arith.Neon.mont d z ++ rest)) s Q := by
  refine VG.Proof.MlDsa.AArch64.Arith.Neon.mont_ok hd hz hc.q hc.qi fun s' h hval => k s' h ?_
  intro e he
  rw [hval, vword_ofVWords _ _ _ _ he]
  have hm (i : Nat) (hi : i < 4) :
      (VG.Proof.MlDsa.AArch64.Arith.Neon.redc (VG.Proof.MlDsa.AArch64.Arith.Neon.product (vword (s.v d) i) (vword (s.v z) i))).toNat = mont (A i * Z i) := by
    rw [VG.Proof.MlDsa.AArch64.Arith.Neon.mont_word_nat _ _ (by rw [hzv i hi]; exact hzlt i hi), ha i hi, hzv i hi]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
    exact hm _ (by decide)

theorem bfly_ok (hc : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s) {A B Z : Nat → Nat}
    (ha : Lanes (s.v .v0) A) (hb : Lanes (s.v .v1) B) (hz : Lanes (s.v .v18) Z)
    (halt : ∀ e < 4, A e < VG.Spec.MlDsa.q) (hzlt : ∀ e < 4, Z e < VG.Spec.MlDsa.q)
    (k : ∀ s', VChg [.v0,.v1,.v2,.v3,.v4,.v5] s s' →
      Lanes (s'.v .v0) (fun e => (A e + mont (B e*Z e)%VG.Spec.MlDsa.q)%VG.Spec.MlDsa.q) →
      Lanes (s'.v .v5) (fun e => (A e + VG.Spec.MlDsa.q - mont (B e*Z e)%VG.Spec.MlDsa.q)%VG.Spec.MlDsa.q) →
      WP isa (.block rest) s' Q) : WP isa (.block (VG.Impl.MlDsa.AArch64.Arith.Neon.bfly ++ rest)) s Q := by
  simp only [VG.Impl.MlDsa.AArch64.Arith.Neon.bfly, List.append_assoc, List.cons_append]
  have hm : ∀ e < 4, mont (B e*Z e) < 2*VG.Spec.MlDsa.q := fun e he =>
    mont_lt (by simpa only [Nat.mul_comm] using Nat.mul_lt_mul'' (hb.lt he) (hzlt e he))
  refine VG.Proof.MlDsa.AArch64.Arith.Neon.mont_lanes (by decide) (by decide) hc hb hz hzlt fun s₁ h₁ l₁ => ?_
  refine VG.Proof.MlDsa.AArch64.Arith.Neon.csub_ok (by decide) (hc.chg h₁).lanes_q l₁ hm fun s₂ h₂ l₂ => ?_
  have c₂ := hc.chg (h₁.trans h₂)
  have a₂ : Lanes (s₂.v .v0) A := by rw [h₂.get .v0, h₁.get .v0]; exact ha
  have tlt : ∀ e, mont (B e*Z e)%VG.Spec.MlDsa.q < VG.Spec.MlDsa.q := fun e => Nat.mod_lt _ (by decide)
  refine wp_vop (d := .v5) rfl fun s₃ h₃ => wp_vop (d := .v0) rfl fun s₄ h₄ => ?_
  have t₃ : Lanes (s₃.v .v1) (fun e => mont (B e*Z e)%VG.Spec.MlDsa.q) := by rw [h₃.get .v1]; exact l₂
  have a₃5 : Lanes (s₃.v .v5) A := by rw [h₃.v]; exact a₂
  have a₃ : Lanes (s₃.v .v0) A := by rw [h₃.get .v0]; exact a₂
  have sum : Lanes (s₄.v .v0) (fun e => A e + mont (B e*Z e)%VG.Spec.MlDsa.q) := by
    rw [h₄.v]
    exact (lanes_add a₃ t₃).congr fun e he => Nat.mod_eq_of_lt (by
      have ha' := halt e he; have ht' := tlt e; rw [VG.Proof.MlDsa.Arith.q_eq] at ha' ht' ⊢; omega)
  refine VG.Proof.MlDsa.AArch64.Arith.Neon.csub_ok (by decide) (c₂.chg (h₃.chg.trans h₄.chg)).lanes_q sum
    (fun e he => by have := halt e he; have := tlt e; omega) fun s₅ h₅ l₅ => ?_
  refine wp_vop (d := .v5) rfl fun s₆ h₆ => wp_vop (d := .v5) rfl fun s₇ h₇ => ?_
  have a₅ : Lanes (s₅.v .v5) A := by rw [h₅.get .v5, h₄.get .v5]; exact a₃5
  have c₅ := c₂.chg ((h₃.chg.trans h₄.chg).trans h₅)
  have a₆ : Lanes (s₆.v .v5) (fun e => A e + VG.Spec.MlDsa.q) := by
    rw [h₆.v]
    exact (lanes_add a₅ c₅.lanes_q).congr fun e he => Nat.mod_eq_of_lt (by
      have := halt e he; change A e < 8380417 at this; change A e + 8380417 < 2^32; omega)
  have t₆ : Lanes (s₆.v .v1) (fun e => mont (B e*Z e)%VG.Spec.MlDsa.q) := by
    rw [h₆.get .v1, h₅.get .v1, h₄.get .v1, h₃.get .v1]; exact l₂
  have diff : Lanes (s₇.v .v5) (fun e => A e + VG.Spec.MlDsa.q - mont (B e*Z e)%VG.Spec.MlDsa.q) := by
    rw [h₇.v]
    exact (lanes_sub a₆ t₆).congr fun e he => by
      have := halt e he; have := tlt e; rw [VG.Proof.MlDsa.Arith.q_eq] at *; omega
  refine VG.Proof.MlDsa.AArch64.Arith.Neon.csub_ok (by decide) (c₅.chg (h₆.chg.trans h₇.chg)).lanes_q diff
    (fun e he => by have := halt e he; have := tlt e; omega) fun s₈ h₈ l₈ => k s₈
      (((((((h₁.trans h₂).trans h₃.chg).trans h₄.chg).trans h₅).trans h₆.chg).trans h₇.chg).trans h₈).mono ?_ l₈
  rw [h₈.get .v0, h₇.get .v0, h₆.get .v0]; exact l₅

theorem bflyInv_ok (hc : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s) {A B Z : Nat → Nat}
    (ha : Lanes (s.v .v0) A) (hb : Lanes (s.v .v1) B) (hz : Lanes (s.v .v18) Z)
    (halt : ∀ e < 4, A e < VG.Spec.MlDsa.q) (hblt : ∀ e < 4, B e < VG.Spec.MlDsa.q) (hzlt : ∀ e < 4, Z e < VG.Spec.MlDsa.q)
    (k : ∀ s', VChg [.v0,.v2,.v3,.v4,.v5] s s' →
      Lanes (s'.v .v0) (fun e => (A e + B e)%VG.Spec.MlDsa.q) →
      Lanes (s'.v .v5) (fun e => mont ((A e + VG.Spec.MlDsa.q - B e)*Z e)%VG.Spec.MlDsa.q) →
      WP isa (.block rest) s' Q) : WP isa (.block (VG.Impl.MlDsa.AArch64.Arith.Neon.bflyInv ++ rest)) s Q := by
  simp only [VG.Impl.MlDsa.AArch64.Arith.Neon.bflyInv, List.append_assoc, List.cons_append]
  refine wp_vop (d := .v5) rfl fun s₁ h₁ => wp_vop (d := .v5) rfl fun s₂ h₂ => ?_
  have a₁ : Lanes (s₁.v .v5) (fun e => A e + VG.Spec.MlDsa.q) := by
    rw [h₁.v]
    exact (lanes_add ha hc.lanes_q).congr fun e he => Nat.mod_eq_of_lt (by
      have ha' := halt e he; rw [VG.Proof.MlDsa.Arith.q_eq] at ha' ⊢; omega)
  have b₁ : Lanes (s₁.v .v1) B := by rw [h₁.get .v1]; exact hb
  have diff : Lanes (s₂.v .v5) (fun e => A e + VG.Spec.MlDsa.q - B e) := by
    rw [h₂.v]
    exact (lanes_sub a₁ b₁).congr fun e he => by
      have ha' := halt e he; have hb' := hblt e he; rw [VG.Proof.MlDsa.Arith.q_eq] at ha' hb' ⊢; omega
  have c₂ := hc.chg (h₁.chg.trans h₂.chg)
  refine wp_vop (d := .v0) rfl fun s₃ h₃ => ?_
  have sum : Lanes (s₃.v .v0) (fun e => A e + B e) := by
    rw [h₃.v]
    exact (lanes_add (by rw [h₂.get .v0, h₁.get .v0]; exact ha)
      (by rw [h₂.get .v1, h₁.get .v1]; exact hb)).congr fun e he => Nat.mod_eq_of_lt (by
        have ha' := halt e he; have hb' := hblt e he; rw [VG.Proof.MlDsa.Arith.q_eq] at ha' hb'; omega)
  refine VG.Proof.MlDsa.AArch64.Arith.Neon.csub_ok (by decide) (c₂.chg h₃.chg).lanes_q sum
    (fun e he => by have := halt e he; have := hblt e he; omega) fun s₄ h₄ l₄ => ?_
  have c₄ := c₂.chg (h₃.chg.trans h₄)
  have diff₄ : Lanes (s₄.v .v5) (fun e => A e + VG.Spec.MlDsa.q - B e) := by
    rw [h₄.get .v5, h₃.get .v5]; exact diff
  have z₄ : Lanes (s₄.v .v18) Z := by
    rw [h₄.get .v18, h₃.get .v18, h₂.get .v18, h₁.get .v18]; exact hz
  refine VG.Proof.MlDsa.AArch64.Arith.Neon.mont_lanes (by decide) (by decide) c₄ diff₄ z₄ hzlt fun s₅ h₅ l₅ => ?_
  refine VG.Proof.MlDsa.AArch64.Arith.Neon.csub_ok (by decide) (c₄.chg h₅).lanes_q l₅
    (fun e he => mont_lt (by
      simpa only [Nat.mul_comm] using Nat.mul_lt_mul'' (diff₄.lt he) (hzlt e he)))
    fun s₆ h₆ l₆ => k s₆ (((((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄).trans h₅).trans h₆).mono ?_ l₆
  rw [h₆.get .v0, h₅.get .v0]; exact l₄

end
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Bfly`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg Lanes)
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q Zq)

def Coeffs (v : BitVec 128) (f : Nat → VG.Spec.MlDsa.Zq) : Prop := Lanes v fun e => (f e).val

def Zetas (v : BitVec 128) (f : Nat → VG.Spec.MlDsa.Zq) : Prop := Lanes v fun e => (f e).val*2^32%VG.Spec.MlDsa.q

def VBflyOk (bf : List Instr) (op : VG.Spec.MlDsa.Zq → VG.Spec.MlDsa.Zq → VG.Spec.MlDsa.Zq → VG.Spec.MlDsa.Zq × VG.Spec.MlDsa.Zq)
    (zt : VG.Spec.MlDsa.Zq → VG.Spec.MlDsa.Zq) : Prop :=
  ∀ (s : State), VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s → ∀ (a b z : Nat → VG.Spec.MlDsa.Zq), VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs (s.v .v0) a → VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs (s.v .v1) b →
    VG.Proof.MlDsa.AArch64.Arith.Neon.Zetas (s.v .v18) (fun e => zt (z e)) →
    WP isa (.block bf) s fun s' => VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs (s'.v .v0) (fun e => (op (a e) (b e) (z e)).1) ∧
      VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs (s'.v .v5) (fun e => (op (a e) (b e) (z e)).2) ∧
      VChg [.v0,.v1,.v2,.v3,.v4,.v5] s s'

theorem bfly_spec : VG.Proof.MlDsa.AArch64.Arith.Neon.VBflyOk Impl.MlDsa.AArch64.Arith.Neon.bfly
    (fun a b z => (a+z*b,a-z*b)) id := by
  intro s hc a b z ha hb hz
  refine VG.Proof.MlDsa.AArch64.Arith.Neon.bfly_ok hc ha hb hz (fun e _ => (a e).isLt)
    (fun _ _ => Nat.mod_lt _ (by decide)) (rest := []) fun s' h l0 l5 =>
      WP.block_nil_iff.mpr ⟨?_, ?_, h⟩
  · exact l0.congr fun e _ => by
      change ((a e).val+mont ((b e).val*((z e).val*2^32%VG.Spec.MlDsa.q))%VG.Spec.MlDsa.q)%VG.Spec.MlDsa.q = (a e+z e*b e).val
      rw [mont_mulR, VG.Proof.MlDsa.Arith.val_add', VG.Proof.MlDsa.Arith.val_mul, Nat.mul_comm (z e).val]
  · exact l5.congr fun e _ => by
      change ((a e).val+VG.Spec.MlDsa.q-mont ((b e).val*((z e).val*2^32%VG.Spec.MlDsa.q))%VG.Spec.MlDsa.q)%VG.Spec.MlDsa.q = (a e-z e*b e).val
      rw [mont_mulR, VG.Proof.MlDsa.Arith.val_sub, VG.Proof.MlDsa.Arith.val_mul, Nat.mul_comm (z e).val, VG.Proof.MlDsa.Arith.condSub_eq]
      have := (a e).isLt
      have := Nat.mod_lt ((b e).val*(z e).val) (show 0 < VG.Spec.MlDsa.q by decide)
      omega

theorem bflyInv_spec : VG.Proof.MlDsa.AArch64.Arith.Neon.VBflyOk Impl.MlDsa.AArch64.Arith.Neon.bflyInv
    (fun a b z => (a+b,z*(b-a))) (fun z => -z) := by
  intro s hc a b z ha hb hz
  refine VG.Proof.MlDsa.AArch64.Arith.Neon.bflyInv_ok hc ha hb hz (fun e _ => (a e).isLt) (fun e _ => (b e).isLt)
    (fun _ _ => Nat.mod_lt _ (by decide)) (rest := []) fun s' h l0 l5 =>
      WP.block_nil_iff.mpr ⟨?_, ?_, h.mono⟩
  · exact l0.congr fun e _ => (VG.Proof.MlDsa.Arith.val_add' _ _).symm
  · exact l5.congr fun e _ => by
      change mont (((a e).val+VG.Spec.MlDsa.q-(b e).val)*((-z e).val*2^32%VG.Spec.MlDsa.q))%VG.Spec.MlDsa.q = (z e*(b e-a e)).val
      rw [← neg_mul_sub, VG.Proof.MlDsa.Arith.val_mul, VG.Proof.MlDsa.Arith.val_sub, VG.Proof.MlDsa.Arith.condSub_eq]
      · rw [mont_mulR, Nat.mul_mod_mod, Nat.mul_comm]
      · have := (a e).isLt; have := (b e).isLt; omega
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (n Poly Zq PolyIs coeffAt)

theorem vword_read16 (m : Mem) (a : Addr) {e : Nat} (he : e < 4) :
    vword (m.read a 16) e = m.readW (a + BitVec.ofNat 64 (4*e)) 32 := by
  rw [VG.Proof.MlKem.AArch64.read16, vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem coeffs_load {m : Mem} {p : Addr} {F : Poly} (h : PolyIs m p F) {j : Nat}
    (hj : j+4 ≤ 256) : VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs (m.read (coeffAddr p j) 16) (fun e => F[j+e]!) := fun e he => by
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he, coeffAddr_add, ← coeffAt_eq]
  exact polyIs_toNat h (by rw [n_eq]; omega)

theorem readW_write16 (m : Mem) (a : Addr) (v : BitVec 128) {j : Nat} (hj : j < 4) :
    (m.write a 16 v).readW (a + BitVec.ofNat 64 (4*j)) 32 = vword v j := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vword, BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth,
    hi, decide_true, Bool.true_and]
  rw [VG.Proof.MlKem.AArch64.getLsbD_read _ _ _ _ (by omega)]
  simp only [Mem.write]
  rw [show a + BitVec.ofNat 64 (4*j) + BitVec.ofNat 64 (i/8) - a = BitVec.ofNat 64 (4*j+i/8) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left]]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [show 4*j+i/8 < 16 by omega, ite_true, BitVec.getLsbD_extractLsb']
  rw [decide_eq_true (by omega), Bool.true_and]
  exact congrArg _ (by omega)

theorem coeffAt_write16 (m : Mem) (p : Addr) {j : Nat} (hj : j+4 ≤ 256)
    (v : BitVec 128) {i : Nat} (hi : i < 256) :
    coeffAt (m.write (coeffAddr p j) 16 v) p i =
      if j ≤ i ∧ i < j+4 then vword v (i-j) else coeffAt m p i := by
  split
  · rename_i h
    rw [coeffAt_eq, show coeffAddr p i = coeffAddr p j + BitVec.ofNat 64 (4*(i-j)) by
      rw [coeffAddr_add, show j+(i-j) = i by omega]]
    exact VG.Proof.MlDsa.AArch64.Arith.Neon.readW_write16 _ _ _ (by omega)
  · have hw : m.write (coeffAddr p j) 16 v = m.writeW (coeffAddr p j) v := by
      simp only [Mem.writeW, BitVec.setWidth_eq]
    rw [hw]
    exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

theorem polyIs_write2 {m : Mem} {p : Addr} {P R : Poly} (hP : PolyIs m p P)
    {j j' : Nat} (hj : j+4 ≤ 256) (hj' : j'+4 ≤ 256) (hsep : j+4 ≤ j' ∨ j'+4 ≤ j)
    {x y : BitVec 128} {a b : Nat → Zq} (hx : VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs x a) (hy : VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs y b)
    (hR : ∀ i < 256, R[i]! = if j ≤ i ∧ i < j+4 then a (i-j)
      else if j' ≤ i ∧ i < j'+4 then b (i-j') else P[i]!) :
    PolyIs ((m.write (coeffAddr p j) 16 x).write (coeffAddr p j') 16 y) p R :=
  polyIs_of_toNat fun i hi => by
    rw [n_eq] at hi
    rw [VG.Proof.MlDsa.AArch64.Arith.Neon.coeffAt_write16 _ _ hj' _ hi, VG.Proof.MlDsa.AArch64.Arith.Neon.coeffAt_write16 _ _ hj _ hi, hR i hi]
    by_cases h1 : j' ≤ i ∧ i < j'+4
    · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_left h1]
      exact hy _ (by omega)
    · rw [ite_eq_right h1]
      by_cases h2 : j ≤ i ∧ i < j+4
      · rw [ite_eq_left h2, ite_eq_left h2]; exact hx _ (by omega)
      · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_right h1]
        exact polyIs_toNat hP (by rw [n_eq]; exact hi)

theorem vector_contains (p : Addr) {j : Nat} (hj : j+4 ≤ 256) :
    (pR p).Contains (coeffAddr p j) 16 := Offset.contains_base p (by omega) (by omega)

theorem frame_write2 {m m' : Mem} {p : Addr} (hf : Frame [pR p] m m') {j j' : Nat}
    (hj : j+4 ≤ 256) (hj' : j'+4 ≤ 256) (x y : BitVec 128) :
    Frame [pR p] m ((m'.write (coeffAddr p j) 16 x).write (coeffAddr p j') 16 y) :=
  (hf.write (List.mem_singleton_self _) x (VG.Proof.MlDsa.AArch64.Arith.Neon.vector_contains p hj)).write
    (List.mem_singleton_self _) y (VG.Proof.MlDsa.AArch64.Arith.Neon.vector_contains p hj')
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Step`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep wp_vop wp_ldrq wp_strq VChg)
open VG.Spec.MlDsa (q n Poly Zq PolyIs zetas)

/-- Pointer and counter updates leave all vector registers unchanged. -/
theorem bodyEnd_ok (s : State) :
    WP isa (.block [.addImm .x .x2 .x2 16, .subImm .x .x5 .x5 1]) s fun s' =>
      ((s'.gpr .x2 = s.gpr .x2 + 16 ∧ s'.gpr .x5 = s.gpr .x5 - 1 ∧ s'.mem = s.mem) ∧
        Keep [.x2,.x5] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun
  exact ⟨rfl,rfl⟩

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} {zt : Zq → Zq}
  (hbf : VG.Proof.MlDsa.AArch64.Arith.Neon.VBflyOk bf op zt) {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

theorem step_ok {fP : Addr} {len st u k : Nat} (hl : 0 < len) (hl4 : len%4 = 0)
    (hs : st+2*len ≤ 256) (hu : 4*u+4 ≤ len) {G : Poly} {s : State}
    (hc : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s) (hz : VG.Proof.MlDsa.AArch64.Arith.Neon.Zetas (s.v .v18) (fun _ => zt (VG.Spec.MlDsa.zetas k)))
    (hx : s.gpr .x2 = coeffAddr fP (st+4*u))
    (hP : PolyIs s.mem fP (blk G len k st (4*u))) (hw : pR fP ∈ s.wr) :
    WP isa (.block (body bf len)) s fun s' =>
      PolyIs s'.mem fP (blk G len k st (4*(u+1))) ∧
      Frame [pR fP] s.mem s'.mem ∧ VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s' ∧ s'.v .v18 = s.v .v18 ∧
      s'.gpr .x2 = coeffAddr fP (st+4*(u+1)) ∧ s'.gpr .x5 = s.gpr .x5 - 1 ∧
      Keep [.x2,.x5] s s' := by
  have j0 : st+4*u+4 ≤ 256 := by omega
  have j1 : st+4*u+len+4 ≤ 256 := by omega
  have off : 4*len%16 = 0 ∧ 4*len < 4096*16 := ⟨by omega, by omega⟩
  have a1 : coeffAddr fP (st+4*u) + BitVec.ofNat 64 (4*len) = coeffAddr fP (st+4*u+len) := coeffAddr_add _ _ _
  have r0 : InRegions (s.rd++s.wr) (coeffAddr fP (st+4*u)) 16 :=
    ⟨_,List.mem_append_right _ hw,VG.Proof.MlDsa.AArch64.Arith.Neon.vector_contains _ j0⟩
  have r1 : InRegions (s.rd++s.wr) (coeffAddr fP (st+4*u+len)) 16 :=
    ⟨_,List.mem_append_right _ hw,VG.Proof.MlDsa.AArch64.Arith.Neon.vector_contains _ j1⟩
  unfold body
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrq (by decide) (by rw [hx, BitVec.add_zero]) r0 fun s₁ h₁ =>
    wp_ldrq off (by rw [h₁.gpr, hx, a1])
      (by rw [h₁.rd,h₁.wr]; exact r1) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  have cc := hc.chg (h₁.chg.trans h₂.chg)
  have zz : VG.Proof.MlDsa.AArch64.Arith.Neon.Zetas (s₂.v .v18) (fun _ => zt (VG.Spec.MlDsa.zetas k)) := by rw [h₂.get .v18,h₁.get .v18]; exact hz
  have l0 : VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs (s₂.v .v0) (fun e => (blk G len k st (4*u))[st+4*u+e]!) := by
    rw [h₂.get .v0,h₁.v]; exact VG.Proof.MlDsa.AArch64.Arith.Neon.coeffs_load hP j0
  have l1 : VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs (s₂.v .v1) (fun e => (blk G len k st (4*u))[st+4*u+len+e]!) := by
    rw [h₂.v,h₁.mem]; exact VG.Proof.MlDsa.AArch64.Arith.Neon.coeffs_load hP j1
  refine WP.mono (hbf s₂ cc _ _ _ l0 l1 zz) fun s₃ ⟨la,lb,h₃⟩ => ?_
  have g₃ : s₃.gpr = s.gpr := h₃.gpr.trans (h₂.gpr.trans h₁.gpr)
  have m₃ : s₃.mem = s.mem := h₃.mem.trans (h₂.mem.trans h₁.mem)
  have rd₃ : s₃.rd = s.rd := h₃.rd.trans (h₂.rd.trans h₁.rd)
  have wr₃ : s₃.wr = s.wr := h₃.wr.trans (h₂.wr.trans h₁.wr)
  refine wp_strq (by decide) (by rw [g₃,hx,BitVec.add_zero])
    (by rw [wr₃]; exact ⟨_,hw,VG.Proof.MlDsa.AArch64.Arith.Neon.vector_contains _ j0⟩) fun s₄ h₄ =>
    wp_strq off (by rw [h₄.gpr,g₃,hx,a1])
      (by rw [h₄.wr,wr₃]; exact ⟨_,hw,VG.Proof.MlDsa.AArch64.Arith.Neon.vector_contains _ j1⟩) fun s₅ h₅ => ?_
  have mem₅ : s₅.mem = ((s.mem.write (coeffAddr fP (st+4*u)) 16 (s₃.v .v0)).write
      (coeffAddr fP (st+4*u+len)) 16 (s₃.v .v5)) := by
    rw [h₅.mem,h₄.mem,h₄.v,m₃]
  have c₅ : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s₅ := by
    have c₃ := cc.chg h₃
    exact ⟨by rw [h₅.v,h₄.v]; exact c₃.q, by rw [h₅.v,h₄.v]; exact c₃.qi⟩
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.bodyEnd_ok s₅) fun s₆ ⟨⟨⟨hx6,hcnt6,hm6⟩,h₆⟩,hv6⟩ =>
    ⟨?_, ?_, ⟨by rw [hv6]; exact c₅.q, by rw [hv6]; exact c₅.qi⟩,
      by rw [hv6,h₅.v,h₄.v,h₃.get .v18,h₂.get .v18,h₁.get .v18], ?_, ?_,
      (((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans h₆).mono⟩
  · rw [hm6,mem₅]
    refine VG.Proof.MlDsa.AArch64.Arith.Neon.polyIs_write2 hP j0 j1 (by omega) la lb fun i hi => ?_
    rw [show 4*(u+1) = 4*u+4 by omega,hblk.add,hblk.get _ _ _ _ _ hl (by omega)
      (by rw [n_eq]; omega) _ (by rw [n_eq]; exact hi)]
    by_cases c1 : st+4*u ≤ i ∧ i < st+4*u+4
    · rw [ite_eq_left c1,ite_eq_left c1,
        show st+4*u+(i-(st+4*u)) = i by omega,
        show st+4*u+len+(i-(st+4*u)) = i+len by omega]
    · rw [ite_eq_right c1,ite_eq_right c1]
      by_cases c2 : st+4*u+len ≤ i ∧ i < st+4*u+len+4
      · rw [ite_eq_left c2,ite_eq_left (by omega),
          show st+4*u+(i-(st+4*u+len)) = i-len by omega,
          show st+4*u+len+(i-(st+4*u+len)) = i by omega]
      · rw [ite_eq_right c2,ite_eq_right (by omega)]
  · rw [hm6,mem₅]; exact VG.Proof.MlDsa.AArch64.Arith.Neon.frame_write2 (Frame.refl _ _) j0 j1 _ _
  · rw [hx6,h₅.gpr,h₄.gpr,g₃,hx,show (16 : BitVec 64) = BitVec.ofNat 64 (4*4) from rfl,
      coeffAddr_add,show st+4*u+4 = st+4*(u+1) by omega]
  · rw [hcnt6,h₅.gpr,h₄.gpr,g₃]
end
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Table`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab)
open VG.Proof.MlKem.AArch64 (Keep wp_vop VChg)
open VG.Spec.MlDsa (q Zq zetas)

def TabZ (tab : Nat → Nat) (zt : Zq → Zq) : Prop :=
  ∀ k, tab k = (zt (VG.Spec.MlDsa.zetas k)).val*2^32%q

theorem zetaTab_eq : VG.Proof.MlDsa.AArch64.Arith.Neon.TabZ VG.Impl.MlDsa.AArch64.Arith.Neon.zetaTab id := by
  intro k
  change VG.Impl.MlDsa.AArch64.Arith.Neon.zetaTab k = (Spec.MlDsa.zetas k).val*2^32%q
  rw [VG.Impl.MlDsa.AArch64.Arith.Neon.zetaTab,← zetaNat_eq,zetaNat,Nat.mod_mul_mod]

theorem negZetaTab_eq : VG.Proof.MlDsa.AArch64.Arith.Neon.TabZ VG.Impl.MlDsa.AArch64.Arith.Neon.negZetaTab (fun z => -z) := by
  intro k
  rw [VG.Impl.MlDsa.AArch64.Arith.Neon.negZetaTab,← negZetaNat_eq,negZetaNat,zetaNat]

theorem loadZ_ok (up : Bool) (s : State)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x3) 4) :
    WP isa (.block [.ldr .w .x6 .x3 0,stepZ up]) s fun s' =>
      ((s'.gpr .x6 = (s.mem.readW (s.gpr .x3) 32).setWidth 64 ∧
        s'.gpr .x3 = (if up then s.gpr .x3+4 else s.gpr .x3-4) ∧ s'.mem = s.mem) ∧
        Keep [.x6,.x3] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by cases up <;> rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by cases up <;> rfl) (hv := by cases up <;> rfl)
  cases up <;> arun [stepZ,hin] <;> rfl

/-- A full-width vector of the table's zeta for a large NTT block. -/
theorem zetas_large_ok {tab : Nat → Nat} {zt : Zq → Zq} (htz : VG.Proof.MlDsa.AArch64.Arith.Neon.TabZ tab zt)
    {len : Nat} (hl1 : len ≠ 1) (hl2 : len ≠ 2) (up : Bool) {s : State} {p : Addr} {k : Nat}
    (hk : k < 256) (h3 : s.gpr .x3 = coeffAddr p k) (ht : Tab tab s.mem p 256)
    (hp : pR p ∈ s.rd++s.wr) (hc : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s) :
    WP isa (.block (Impl.MlDsa.AArch64.Arith.Neon.zetas len up)) s fun s' =>
      VG.Proof.MlDsa.AArch64.Arith.Neon.Zetas (s'.v .v18) (fun _ => zt (Spec.MlDsa.zetas k)) ∧ VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s' ∧
      s'.gpr .x3 = (if up then s.gpr .x3+4 else s.gpr .x3-4) ∧ s'.mem = s.mem ∧
      Keep [.x6,.x3] s s' := by
  simp only [Impl.MlDsa.AArch64.Arith.Neon.zetas,hl1,hl2,ite_false]
  have hread : (s.mem.readW (s.gpr .x3) 32).toNat = (zt (Spec.MlDsa.zetas k)).val*2^32%q := by
    rw [h3,← coeffAt_eq,ht k hk,BitVec.toNat_ofNat,htz k]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
  change WP isa (.block ([.ldr .w .x6 .x3 0,stepZ up] ++ [.vop (.dup .s4 .v18 .x6)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.loadZ_ok up s (by rw [h3]; exact ⟨_,hp,coeff_contains _ hk⟩))
    fun s₁ ⟨⟨⟨h6,h3',hm⟩,h₁⟩,hv⟩ => wp_vop (d := .v18) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨?_, ?_, by rw [h₂.gpr]; exact h3', by rw [h₂.mem]; exact hm,
        (h₁.trans h₂.keep).mono⟩
  · intro e he
    rw [h₂.v]
    change (vword (ofVWords ((s₁.gpr .x6).setWidth 32) ((s₁.gpr .x6).setWidth 32)
      ((s₁.gpr .x6).setWidth 32) ((s₁.gpr .x6).setWidth 32)) e).toNat = _
    rw [VG.Proof.MlKem.AArch64.vword_dup_s4 _ he,h6,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq,hread]
  · exact (⟨by rw [hv]; exact hc.q, by rw [hv]; exact hc.qi⟩ : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s₁).chg h₂.chg
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Block`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab wp_countdown imm16)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (Poly Zq PolyIs)

abbrev clob : List Reg := [.x2,.x3,.x4,.x5,.x6]

structure BInv (fP : Addr) (s s' : State) : Prop where
  keep : Keep VG.Proof.MlDsa.AArch64.Arith.Neon.clob s s'
  frame : Frame [pR fP] s.mem s'.mem
  consts : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s'

theorem BInv.refl {p : Addr} {s : State} (hc : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s) : VG.Proof.MlDsa.AArch64.Arith.Neon.BInv p s s :=
  ⟨Keep.refl _ _, Frame.refl _ _,hc⟩

theorem BInv.trans {p : Addr} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlDsa.AArch64.Arith.Neon.BInv p s₁ s₂) (h₂ : VG.Proof.MlDsa.AArch64.Arith.Neon.BInv p s₂ s₃) :
    VG.Proof.MlDsa.AArch64.Arith.Neon.BInv p s₁ s₃ := ⟨(h₁.keep.trans h₂.keep).mono,h₁.frame.trans h₂.frame,h₂.consts⟩

theorem counter5_ok (N : Nat) (hN : N < 65536) (s : State) :
    WP isa (.block [.movz .x .x5 (BitVec.ofNat 16 N) 0]) s fun s' =>
      ((s'.gpr .x5 = BitVec.ofNat 64 N ∧ s'.mem = s.mem) ∧ Keep [.x5] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [imm16 hN]

theorem blockEnd_ok (len : Nat) (hl : len ≤ 128) (s : State) :
    WP isa (.block [.addImm .x .x2 .x2 (4*len),.subImm .x .x4 .x4 1]) s fun s' =>
      ((s'.gpr .x2 = s.gpr .x2+BitVec.ofNat 64 (4*len) ∧ s'.gpr .x4 = s.gpr .x4-1 ∧
        s'.mem = s.mem) ∧ Keep [.x2,.x4] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [show 4*len < 4096 by omega]
  rfl

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} {zt : Zq → Zq}
  (hbf : VG.Proof.MlDsa.AArch64.Arith.Neon.VBflyOk bf op zt) {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

theorem block_ok {fP zP : Addr} {len st k : Nat} (h4 : 4 ≤ len) (hl : len ≤ 128)
    (hl4 : len%4 = 0) (hs : st+2*len ≤ 256) (hk : k < 256)
    {tab : Nat → Nat} (hzt : VG.Proof.MlDsa.AArch64.Arith.Neon.TabZ tab zt) (up : Bool) {G : Poly} {s : State}
    (hx : s.gpr .x2 = coeffAddr fP st) (h3 : s.gpr .x3 = coeffAddr zP k)
    (hc : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s) (hP : PolyIs s.mem fP G) (ht : Tab tab s.mem zP 256)
    (hw : pR fP ∈ s.wr) (hzp : pR zP ∈ s.rd++s.wr) :
    WP isa (block bf len up) s fun s' =>
      PolyIs s'.mem fP (blk G len k st len) ∧ s'.gpr .x2 = coeffAddr fP (st+2*len) ∧
      s'.gpr .x3 = (if up then s.gpr .x3+4 else s.gpr .x3-4) ∧
      s'.gpr .x4 = s.gpr .x4-1 ∧ VG.Proof.MlDsa.AArch64.Arith.Neon.BInv fP s s' := by
  have hN : len/4 < 65536 := by omega
  have hN0 : 0 < len/4 := by omega
  have hcov : 4*(len/4) = len := by omega
  unfold block
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.zetas_large_ok hzt (by omega) (by omega) up hk h3 ht hzp hc)
    fun s₁ ⟨lz,c₁,h31,hm₁,k₁⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.counter5_ok (len/4) hN s₁) fun s₂ ⟨⟨⟨hcnt,hm₂⟩,k₂⟩,hv₂⟩ => ?_
  have c₂ : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s₂ := ⟨by rw [hv₂]; exact c₁.q, by rw [hv₂]; exact c₁.qi⟩
  have z₂ : VG.Proof.MlDsa.AArch64.Arith.Neon.Zetas (s₂.v .v18) (fun _ => zt (Spec.MlDsa.zetas k)) := by rw [hv₂]; exact lz
  refine WP.seq (WP.mono (wp_countdown (cnt := .x5) (N := len/4) (by omega) hN0
    (fun u s' => PolyIs s'.mem fP (blk G len k st (4*u)) ∧
      s'.gpr .x2 = coeffAddr fP (st+4*u) ∧ s'.v .v18 = s₂.v .v18 ∧ Keep [.x2,.x5] s₂ s' ∧ VG.Proof.MlDsa.AArch64.Arith.Neon.BInv fP s₂ s')
    (fun u hu s' ⟨hp,hx',hv',hki,hi⟩ _ => ?_)
    ⟨by rw [hblk.zero,hm₂,hm₁]; exact hP,
      by rw [k₂.get .x2,k₁.get .x2,hx]; rfl,rfl,Keep.refl _ _,BInv.refl c₂⟩ hcnt)
    fun s₃ ⟨hp,hx3,hv3,hki3,hi3⟩ => ?_)
  · refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.step_ok hbf hblk (by omega) hl4 hs (by omega) hi.consts
      (by rw [hv']; exact z₂) hx' hp (by rw [hi.keep.wr,k₂.wr,k₁.wr]; exact hw))
      fun s'' ⟨hp',hf',hc',hv'',hx'',hcnt',hk'⟩ =>
        ⟨⟨hp',hx'',hv''.trans hv',(hki.trans hk').mono,hi.trans ⟨hk'.mono,hf',hc'⟩⟩,hcnt'⟩
  · refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.blockEnd_ok len hl s₃) fun s₄ ⟨⟨⟨hx4,hcnt4,hm4⟩,k₄⟩,hv4⟩ =>
      ⟨by rw [hm4]; simpa only [hcov] using hp, ?_, ?_, ?_,
        ⟨(((k₁.trans k₂).trans hi3.keep).trans k₄).mono, ?_,
          ⟨by rw [hv4]; exact hi3.consts.q, by rw [hv4]; exact hi3.consts.qi⟩⟩⟩
    · rw [hx4,hx3,hcov,coeffAddr_add,show st+len+len = st+2*len by omega]
    · rw [k₄.get .x3,hki3.get .x3,k₂.get .x3,h31]
    · rw [hcnt4,hki3.get .x4,k₂.get .x4,k₁.get .x4]
    · rw [hm4]; simpa only [hm₂,hm₁] using hi3.frame
end
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Layer`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab wp_countdown imm16)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (Poly Zq PolyIs)

def firstZ (len : Nat) (up : Bool) : Nat := if up then 128/len else 256/len-1

theorem preLayer_ok (len : Nat) (up : Bool) (hk : 4*VG.Proof.MlDsa.AArch64.Arith.Neon.firstZ len up < 4096) (s : State) :
    WP isa (.block [Impl.MlKem.AArch64.mov .x2 .x0,
      .addImm .x .x3 .x1 (4*VG.Proof.MlDsa.AArch64.Arith.Neon.firstZ len up)]) s fun s' =>
      ((s'.gpr .x2 = s.gpr .x0 ∧ s'.gpr .x3 = coeffAddr (s.gpr .x1) (VG.Proof.MlDsa.AArch64.Arith.Neon.firstZ len up) ∧
        s'.mem = s.mem) ∧ Keep [.x2,.x3] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [Impl.MlKem.AArch64.mov,hk]

theorem counter4_ok (N : Nat) (hN : N < 65536) (s : State) :
    WP isa (.block [.movz .x .x4 (BitVec.ofNat 16 N) 0]) s fun s' =>
      ((s'.gpr .x4 = BitVec.ofNat 64 N ∧ s'.mem = s.mem) ∧ Keep [.x4] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [imm16 hN]

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} {zt : Zq → Zq}
  (hbf : VG.Proof.MlDsa.AArch64.Arith.Neon.VBflyOk bf op zt) {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

theorem layer_large_ok {fP zP : Addr} {len : Nat} (hlen : len ∈ [4,8,16,32,64,128])
    {tab : Nat → Nat} (hzt : VG.Proof.MlDsa.AArch64.Arith.Neon.TabZ tab zt) (up : Bool) (zi : Nat → Nat)
    (hzi0 : zi 0 = VG.Proof.MlDsa.AArch64.Arith.Neon.firstZ len up) (hzi : ∀ c < 128/len, zi c < 256)
    (hstep : ∀ c < 128/len, (if up then coeffAddr zP (zi c)+4 else coeffAddr zP (zi c)-4) =
      coeffAddr zP (zi (c+1))) {F : Poly} {s : State}
    (h0 : s.gpr .x0 = fP) (h1 : s.gpr .x1 = zP) (hc : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s)
    (hP : PolyIs s.mem fP F) (ht : Tab tab s.mem zP 256) (hw : pR fP ∈ s.wr)
    (hzp : pR zP ∈ s.rd++s.wr) (hd : (pR zP).Disjoint (pR fP)) :
    WP isa (layer bf len up) s fun s' => PolyIs s'.mem fP (layF blk F len zi (128/len)) ∧ VG.Proof.MlDsa.AArch64.Arith.Neon.BInv fP s s' := by
  have hfacts : 4 ≤ len ∧ len%4 = 0 ∧ len ≤ 128 ∧ 2*len*(128/len) = 256 ∧
      0 < 128/len ∧ 128/len ≤ 32 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨h4,hl4,hl,hcov,hN0,hN⟩ := hfacts
  have hfirst : VG.Proof.MlDsa.AArch64.Arith.Neon.firstZ len up < 256 := hzi0 ▸ hzi 0 hN0
  unfold layer
  rw [ite_eq_right (by omega : ¬ len < 4)]
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.preLayer_ok len up (by omega) s) fun s₁ ⟨⟨⟨hx2,hx3,hm1⟩,k1⟩,hv1⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.counter4_ok (128/len) (by omega) s₁)
    fun s₂ ⟨⟨⟨hcnt,hm2⟩,k2⟩,hv2⟩ => ?_)
  have c2 : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s₂ := ⟨by rw [hv2,hv1]; exact hc.q, by rw [hv2,hv1]; exact hc.qi⟩
  refine WP.mono (wp_countdown (cnt := .x4) (N := 128/len) (by omega) hN0
    (fun c s' => PolyIs s'.mem fP (layF blk F len zi c) ∧
      s'.gpr .x2 = coeffAddr fP (2*len*c) ∧ s'.gpr .x3 = coeffAddr zP (zi c) ∧
      VG.Proof.MlDsa.AArch64.Arith.Neon.BInv fP s₂ s' ∧ Tab tab s'.mem zP 256)
    (fun c hcc s' ⟨hp,hx2',hx3',hi,ht'⟩ _ => ?_)
    ⟨by rw [hm2,hm1]; exact hP,
      by rw [k2.get .x2,hx2,h0]; simp only [coeffAddr,Nat.mul_zero,BitVec.add_zero],
      by rw [k2.get .x3,hx3,h1,hzi0],BInv.refl c2,by rw [hm2,hm1]; exact ht⟩ hcnt)
    fun s' ⟨hp,_,_,hi,_⟩ => ⟨hp,⟨((k1.trans k2).trans hi.keep).mono,
      by simpa only [hm2,hm1] using hi.frame,hi.consts⟩⟩
  have hst : 2*len*c+2*len ≤ 256 := by
    have hh := Nat.mul_le_mul_left (2*len) (show c+1 ≤ 128/len by omega)
    rw [Nat.mul_succ,hcov] at hh; exact hh
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.block_ok hbf hblk h4 hl hl4 hst (hzi c hcc) hzt up hx2' hx3' hi.consts hp ht'
    (by rw [hi.keep.wr,k2.wr,k1.wr]; exact hw)
    (by rw [hi.keep.rd,hi.keep.wr,k2.rd,k2.wr,k1.rd,k1.wr]; exact hzp))
    fun s'' ⟨hp',hx2'',hx3'',hc'',hi'⟩ =>
      ⟨⟨by rw [layF,VG.Proof.MlDsa.Arith.foldl_range_succ]; exact hp',by rw [hx2'',Nat.mul_succ],
        by rw [hx3'',hx3',hstep c hcc],hi.trans hi',ht'.frame hi'.frame (by simpa using hd) (by decide)⟩,hc''⟩
end
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedTable`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab)
open VG.Proof.MlKem.AArch64 (Keep VChg wp_vop wp_ldrq)
open VG.Spec.MlDsa (q Zq)

set_option linter.unusedSimpArgs false

theorem vword_ext8 (v : BitVec 128) {e : Nat} (he : e < 4) :
    vword (((v++v) >>> (8*8)).extractLsb' 0 128) e = vword v ((e+2)%4) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [vword,BitVec.getLsbD_extractLsb',BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceMod,Nat.zero_add]
  all_goals rw [BitVec.getLsbD_append]
  all_goals simp +arith [hi]
  all_goals simp [show i ≤ 31 by omega,show i ≤ 63 by omega,show i ≤ 95 by omega,show i ≤ 127 by omega]

theorem table_vec {tab : Nat → Nat} {zt : Zq → Zq} (hzt : VG.Proof.MlDsa.AArch64.Arith.Neon.TabZ tab zt)
    {m : Mem} {p : Addr} (ht : Tab tab m p 256) {k : Nat} (hk : k+4 ≤ 256) :
    VG.Proof.MlDsa.AArch64.Arith.Neon.Zetas (m.read (coeffAddr p k) 16) (fun e => zt (Spec.MlDsa.zetas (k+e))) := fun e he => by
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,coeffAddr_add,← coeffAt_eq,ht (k+e) (by omega),
    BitVec.toNat_ofNat,hzt (k+e)]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

theorem zetaPerms_ok {s : State} {F : Nat → Zq} (len : Nat) (hlen : len = 1 ∨ len = 2)
    (up : Bool) (hz : VG.Proof.MlDsa.AArch64.Arith.Neon.Zetas (s.v .v18) F) :
    WP isa (.block (zetaPerms len up)) s fun s' => VChg [.v18] s s' ∧
      VG.Proof.MlDsa.AArch64.Arith.Neon.Zetas (s'.v .v18) (fun e => F (if up then e/len else 4/len-1-e/len)) := by
  rcases hlen with rfl | rfl <;> cases up
  · change WP isa (.block [.vop (.rev .rev64s .v18 .v18),.vop (.ext .v18 .v18 .v18 8)]) s _
    refine wp_vop (d := .v18) rfl fun s₁ h₁ => wp_vop (d := .v18) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨(h₁.chg.trans h₂.chg).mono,?_⟩
    intro e he
    simp only [Nat.div_one,ite_true,ite_false,Nat.reduceDiv,Nat.reduceSub]
    change (vword (s₂.v .v18) e).toNat = (F (3-e)).val*2^32%q
    rw [h₂.v,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_ext8 _ he,h₁.v,VG.Proof.MlKem.AArch64.vword_rev64s _ (by omega)]
    have hi : (if ((e+2)%4)%2 = 0 then (e+2)%4+1 else (e+2)%4-1) = 3-e := by split <;> omega
    rw [hi]; exact hz _ (by omega)
  · change WP isa (.block []) s _
    refine WP.block_nil_iff.mpr ⟨VChg.refl _ _,?_⟩
    intro e he
    simp only [Nat.div_one,ite_true,ite_false,Nat.reduceDiv,Nat.reduceSub]
    change (vword (s.v .v18) e).toNat = (F e).val*2^32%q
    exact hz e he
  · change WP isa (.block [.vop (.perm .zip1 .s4 .v18 .v18 .v18),.vop (.ext .v18 .v18 .v18 8)]) s _
    refine wp_vop (d := .v18) rfl fun s₁ h₁ => wp_vop (d := .v18) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨(h₁.chg.trans h₂.chg).mono,?_⟩
    intro e he
    simp only [Nat.div_one,ite_true,ite_false,Nat.reduceDiv,Nat.reduceSub]
    change (vword (s₂.v .v18) e).toNat = (F (1-e/2)).val*2^32%q
    rw [h₂.v,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_ext8 _ he,h₁.v,VG.Proof.MlKem.AArch64.vword_zip1_s4 _ (by omega)]
    have hi : ((e+2)%4)/2 = 1-e/2 := by omega
    rw [hi]; exact hz _ (by omega)
  · change WP isa (.block [.vop (.perm .zip1 .s4 .v18 .v18 .v18)]) s _
    refine wp_vop (d := .v18) rfl fun s' h => WP.block_nil_iff.mpr ⟨h.chg,?_⟩
    intro e he
    simp only [Nat.div_one,ite_true,ite_false,Nat.reduceDiv,Nat.reduceSub]
    change (vword (s'.v .v18) e).toNat = (F (e/2)).val*2^32%q
    rw [h.v,VG.Proof.MlKem.AArch64.vword_zip1_s4 _ he]; exact hz _ (by omega)

def baseZ (len : Nat) (up : Bool) (k : Nat) : Nat := if up then k else k-(4/len-1)

theorem coeffAddr_sub (p : Addr) (k j : Nat) (hj : j ≤ k) :
    coeffAddr p k - BitVec.ofNat 64 (4*j) = coeffAddr p (k-j) := by
  have h : coeffAddr p (k-j) + BitVec.ofNat 64 (4*j) = coeffAddr p k := by
    rw [coeffAddr_add,Nat.sub_add_cancel hj]
  rw [← h,BitVec.add_sub_cancel]

theorem moveZ_ok (N : Nat) (hN : N < 4096) (up : Bool) (s : State) :
    WP isa (.block [if up then .addImm .x .x3 .x3 N else .subImm .x .x3 .x3 N]) s fun s' =>
      ((s'.gpr .x3 = (if up then s.gpr .x3+BitVec.ofNat 64 N else s.gpr .x3-BitVec.ofNat 64 N) ∧
        s'.mem = s.mem) ∧ Keep [.x3] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by cases up <;> rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by cases up <;> rfl) (hv := by cases up <;> rfl)
  cases up <;> arun [hN] <;> rfl

theorem zetaPre_ok (len : Nat) (hlen : len = 1 ∨ len = 2) (up : Bool) {p : Addr} {k : Nat} {s : State}
    (hb : up = false → 4/len ≤ k) (h3 : s.gpr .x3 = coeffAddr p k) :
    WP isa (.block (if up then [] else [.subImm .x .x3 .x3 (4*(4/len-1))])) s fun s' =>
      ((s'.gpr .x3 = coeffAddr p (VG.Proof.MlDsa.AArch64.Arith.Neon.baseZ len up k) ∧ s'.mem = s.mem) ∧ Keep [.x3] s s') ∧ s'.v = s.v := by
  cases up
  · have hN : 4*(4/len-1) < 4096 := by rcases hlen with rfl | rfl <;> decide
    refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.moveZ_ok _ hN false s) fun s' ⟨⟨⟨hx,hm⟩,hk⟩,hv⟩ => ⟨⟨⟨?_,hm⟩,hk⟩,hv⟩
    rw [hx,h3,VG.Proof.MlDsa.AArch64.Arith.Neon.coeffAddr_sub _ _ _ (by have := hb rfl; omega)]
    rfl
  · exact WP.block_nil_iff.mpr ⟨⟨⟨h3,rfl⟩,Keep.refl _ _⟩,rfl⟩

theorem zetaPost_ok (len : Nat) (hlen : len = 1 ∨ len = 2) (up : Bool) (s : State) :
    WP isa (.block [if up then .addImm .x .x3 .x3 (16/len) else .subImm .x .x3 .x3 4]) s fun s' =>
      ((s'.gpr .x3 = (if up then s.gpr .x3+BitVec.ofNat 64 (16/len) else s.gpr .x3-4) ∧
        s'.mem = s.mem) ∧ Keep [.x3] s s') ∧ s'.v = s.v := by
  cases up
  · exact VG.Proof.MlDsa.AArch64.Arith.Neon.moveZ_ok 4 (by decide) false s
  · exact VG.Proof.MlDsa.AArch64.Arith.Neon.moveZ_ok _ (by rcases hlen with rfl | rfl <;> decide) true s

theorem packedZetas_ok {tab : Nat → Nat} {zt : Zq → Zq} (hzt : VG.Proof.MlDsa.AArch64.Arith.Neon.TabZ tab zt)
    (len : Nat) (hlen : len = 1 ∨ len = 2) (up : Bool) {p : Addr} {k : Nat} {s : State}
    (hb : up = false → 4/len ≤ k) (hbound : VG.Proof.MlDsa.AArch64.Arith.Neon.baseZ len up k+4 ≤ 256)
    (h3 : s.gpr .x3 = coeffAddr p k) (ht : Tab tab s.mem p 256)
    (hp : pR p ∈ s.rd++s.wr) (hc : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s) :
    WP isa (.block (packedZetas len up)) s fun s' =>
      VG.Proof.MlDsa.AArch64.Arith.Neon.Zetas (s'.v .v18) (fun e => zt (Spec.MlDsa.zetas (if up then k+e/len else k-e/len))) ∧
      VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s' ∧ s'.gpr .x3 = coeffAddr p (if up then k+4/len else k-4/len) ∧
      s'.mem = s.mem ∧ Keep [.x3] s s' ∧ (∀ v, v ≠ .v18 → s'.v v = s.v v) := by
  unfold packedZetas
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.zetaPre_ok len hlen up hb h3) fun s₁ ⟨⟨⟨h31,hm1⟩,k1⟩,hv1⟩ => ?_
  simp only [List.cons_append,List.nil_append]
  refine wp_ldrq (by decide) (by rw [h31,BitVec.add_zero])
    (by rw [k1.rd,k1.wr]; exact ⟨_,hp,VG.Proof.MlDsa.AArch64.Arith.Neon.vector_contains _ hbound⟩) fun s₂ h2 => ?_
  have c2 : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s₂ :=
    (⟨by rw [hv1]; exact hc.q,by rw [hv1]; exact hc.qi⟩ : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s₁).chg h2.chg
  have z2 : VG.Proof.MlDsa.AArch64.Arith.Neon.Zetas (s₂.v .v18) (fun e => zt (Spec.MlDsa.zetas (VG.Proof.MlDsa.AArch64.Arith.Neon.baseZ len up k+e))) := by
    rw [h2.v,hm1]; exact VG.Proof.MlDsa.AArch64.Arith.Neon.table_vec hzt ht hbound
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.zetaPerms_ok len hlen up z2) fun s₃ ⟨h3v,z3⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.zetaPost_ok len hlen up s₃) fun s₄ ⟨⟨⟨h34,hm4⟩,k4⟩,hv4⟩ =>
    ⟨?_,⟨by rw [hv4]; exact (c2.chg h3v).q,by rw [hv4]; exact (c2.chg h3v).qi⟩,?_,
      by rw [hm4,h3v.mem,h2.mem,hm1],(((k1.trans h2.keep).trans h3v.keep).trans k4).mono,
      by intro v hv; rw [hv4,h3v.get v (by simp [hv]),h2.get v hv,hv1]⟩
  · rw [hv4]
    exact z3.congr fun e he => by
      have hi : VG.Proof.MlDsa.AArch64.Arith.Neon.baseZ len up k+(if up then e/len else 4/len-1-e/len) =
          if up then k+e/len else k-e/len := by
        rcases hlen with rfl | rfl <;> cases up <;>
          simp only [VG.Proof.MlDsa.AArch64.Arith.Neon.baseZ,Bool.false_eq_true,ite_true,ite_false,Nat.div_one,Nat.reduceDiv,Nat.reduceSub] at * <;>
          have hkk := hb (by trivial) <;> omega
      change (zt (Spec.MlDsa.zetas (VG.Proof.MlDsa.AArch64.Arith.Neon.baseZ len up k+(if up then e/len else 4/len-1-e/len)))).val*2^32%q = _
      rw [hi]
  · rw [h34,h3v.gpr,h2.gpr,h31]
    rcases hlen with rfl | rfl <;> cases up
    · simp only [VG.Proof.MlDsa.AArch64.Arith.Neon.baseZ,Bool.false_eq_true,ite_false,Nat.div_one,Nat.reduceDiv,Nat.reduceSub]
      rw [show (4 : BitVec 64) = BitVec.ofNat 64 (4*1) from rfl,VG.Proof.MlDsa.AArch64.Arith.Neon.coeffAddr_sub _ _ _ (by have := hb rfl; omega)]
      exact congrArg (coeffAddr p) (by omega)
    · simp only [VG.Proof.MlDsa.AArch64.Arith.Neon.baseZ,ite_true,Nat.div_one,Nat.reduceDiv]
      exact coeffAddr_add p k 4
    · simp only [VG.Proof.MlDsa.AArch64.Arith.Neon.baseZ,Bool.false_eq_true,ite_false,Nat.reduceDiv,Nat.reduceSub]
      rw [show (4 : BitVec 64) = BitVec.ofNat 64 (4*1) from rfl,VG.Proof.MlDsa.AArch64.Arith.Neon.coeffAddr_sub _ _ _ (by have := hb rfl; omega)]
      exact congrArg (coeffAddr p) (by omega)
    · simp only [VG.Proof.MlDsa.AArch64.Arith.Neon.baseZ,ite_true,Nat.reduceDiv]
      exact coeffAddr_add p k 2

end VG.Proof.MlDsa.AArch64.Arith.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedLanes`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Spec.MlDsa (Zq)

/-- Coefficient index of the lower butterfly operand in a packed group. -/
def lower (len e : Nat) : Nat := e+len*(e/len)

/-- Butterfly lane holding coefficient `r` of a packed group. -/
def lane (len r : Nat) : Nat := len*(r/(2*len))+r%len

def result (len : Nat) (A B : Nat → Zq) (r : Nat) : Zq :=
  if r%(2*len) < len then A (VG.Proof.MlDsa.AArch64.Arith.Neon.lane len r) else B (VG.Proof.MlDsa.AArch64.Arith.Neon.lane len r)

set_option linter.unusedSimpArgs false

theorem gather_ok {s : State} (len : Nat) (hlen : len = 1 ∨ len = 2) {F : Nat → Zq}
    (h6 : VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs (s.v .v6) F) (h7 : VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs (s.v .v7) (fun e => F (4+e))) :
    WP isa (.block (gather len)) s fun s' => VChg [.v0,.v1] s s' ∧
      VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs (s'.v .v0) (fun e => F (VG.Proof.MlDsa.AArch64.Arith.Neon.lower len e)) ∧
      VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs (s'.v .v1) (fun e => F (VG.Proof.MlDsa.AArch64.Arith.Neon.lower len e+len)) := by
  rcases hlen with rfl | rfl
  · change WP isa (.block [.vop (.perm .uzp1 .s4 .v0 .v6 .v7),.vop (.perm .uzp2 .s4 .v1 .v6 .v7)]) s _
    refine wp_vop (d := .v0) rfl fun s₁ h₁ => wp_vop (d := .v1) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨h₁.chg.trans h₂.chg,?_,?_⟩
    · intro e he
      rw [h₂.get .v0,h₁.v,VG.Proof.MlKem.AArch64.vword_uzp1_s4 _ _ he]
      split
      · rw [h6 _ (by omega)]; exact congrArg (fun i => (F i).val) (by simp [VG.Proof.MlDsa.AArch64.Arith.Neon.lower]; omega)
      · rw [h7 _ (by omega)]; exact congrArg (fun i => (F i).val) (by simp [VG.Proof.MlDsa.AArch64.Arith.Neon.lower]; omega)
    · intro e he
      rw [h₂.v,h₁.get .v6,h₁.get .v7,VG.Proof.MlKem.AArch64.vword_uzp2_s4 _ _ he]
      split
      · rw [h6 _ (by omega)]; exact congrArg (fun i => (F i).val) (by simp [VG.Proof.MlDsa.AArch64.Arith.Neon.lower]; omega)
      · rw [h7 _ (by omega)]; exact congrArg (fun i => (F i).val) (by simp [VG.Proof.MlDsa.AArch64.Arith.Neon.lower]; omega)
  · change WP isa (.block [.vop (.perm .trn1 .d2 .v0 .v6 .v7),.vop (.perm .trn2 .d2 .v1 .v6 .v7)]) s _
    refine wp_vop (d := .v0) rfl fun s₁ h₁ => wp_vop (d := .v1) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨h₁.chg.trans h₂.chg,?_,?_⟩
    · intro e he
      rw [h₂.get .v0,h₁.v,VG.Proof.MlKem.AArch64.vword_trn1_d2 _ _ he]
      split
      · rw [h6 _ (by omega)]; exact congrArg (fun i => (F i).val) (by simp [VG.Proof.MlDsa.AArch64.Arith.Neon.lower]; omega)
      · rw [h7 _ (by omega)]; exact congrArg (fun i => (F i).val) (by simp [VG.Proof.MlDsa.AArch64.Arith.Neon.lower]; omega)
    · intro e he
      rw [h₂.v,h₁.get .v6,h₁.get .v7,VG.Proof.MlKem.AArch64.vword_trn2_d2 _ _ he]
      split
      · rw [h6 _ (by omega)]; exact congrArg (fun i => (F i).val) (by simp [VG.Proof.MlDsa.AArch64.Arith.Neon.lower]; omega)
      · rw [h7 _ (by omega)]; exact congrArg (fun i => (F i).val) (by simp [VG.Proof.MlDsa.AArch64.Arith.Neon.lower]; omega)

theorem scatter_ok {s : State} (len : Nat) (hlen : len = 1 ∨ len = 2) {A B : Nat → Zq}
    (ha : VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs (s.v .v0) A) (hb : VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs (s.v .v5) B) :
    WP isa (.block (scatter len)) s fun s' => VChg [.v6,.v7] s s' ∧
      VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs (s'.v .v6) (VG.Proof.MlDsa.AArch64.Arith.Neon.result len A B) ∧
      VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs (s'.v .v7) (fun e => VG.Proof.MlDsa.AArch64.Arith.Neon.result len A B (4+e)) := by
  rcases hlen with rfl | rfl
  · change WP isa (.block [.vop (.perm .zip1 .s4 .v6 .v0 .v5),.vop (.perm .zip2 .s4 .v7 .v0 .v5)]) s _
    refine wp_vop (d := .v6) rfl fun s₁ h₁ => wp_vop (d := .v7) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨h₁.chg.trans h₂.chg,?_,?_⟩
    · intro e he
      rw [h₂.get .v6,h₁.v,VG.Proof.MlKem.AArch64.vword_zip1_s4' _ _ he]
      split <;> rename_i h
      · rw [ha _ (by omega)]; simp [VG.Proof.MlDsa.AArch64.Arith.Neon.result,VG.Proof.MlDsa.AArch64.Arith.Neon.lane,Nat.mod_one,h]
      · rw [hb _ (by omega)]; simp [VG.Proof.MlDsa.AArch64.Arith.Neon.result,VG.Proof.MlDsa.AArch64.Arith.Neon.lane,Nat.mod_one,h,show ¬ e%2 < 1 by omega]
    · intro e he
      rw [h₂.v,h₁.get .v0,h₁.get .v5,VG.Proof.MlKem.AArch64.vword_zip2_s4 _ _ he]
      split <;> rename_i h
      · rw [ha _ (by omega)]; simp [VG.Proof.MlDsa.AArch64.Arith.Neon.result,VG.Proof.MlDsa.AArch64.Arith.Neon.lane,Nat.mod_one,show (4+e)%2 < 1 by omega,show (4+e)/2 = 2+e/2 by omega]
      · rw [hb _ (by omega)]; simp [VG.Proof.MlDsa.AArch64.Arith.Neon.result,VG.Proof.MlDsa.AArch64.Arith.Neon.lane,Nat.mod_one,show ¬ (4+e)%2 < 1 by omega,show (4+e)/2 = 2+e/2 by omega]
  · change WP isa (.block [.vop (.perm .trn1 .d2 .v6 .v0 .v5),.vop (.perm .trn2 .d2 .v7 .v0 .v5)]) s _
    refine wp_vop (d := .v6) rfl fun s₁ h₁ => wp_vop (d := .v7) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨h₁.chg.trans h₂.chg,?_,?_⟩
    · intro e he
      rw [h₂.get .v6,h₁.v,VG.Proof.MlKem.AArch64.vword_trn1_d2 _ _ he]
      split <;> rename_i h
      · rw [ha _ (by omega)]; simp [VG.Proof.MlDsa.AArch64.Arith.Neon.result,VG.Proof.MlDsa.AArch64.Arith.Neon.lane,Nat.mod_one,show e%4 < 2 by omega,show e/4 = 0 by omega,show e%2 = e by omega]
      · rw [hb _ (by omega)]; simp [VG.Proof.MlDsa.AArch64.Arith.Neon.result,VG.Proof.MlDsa.AArch64.Arith.Neon.lane,Nat.mod_one,show ¬ e%4 < 2 by omega,show e/4 = 0 by omega,show e%2 = e-2 by omega]
    · intro e he
      rw [h₂.v,h₁.get .v0,h₁.get .v5,VG.Proof.MlKem.AArch64.vword_trn2_d2 _ _ he]
      split <;> rename_i h
      · rw [ha _ (by omega)]; simp [VG.Proof.MlDsa.AArch64.Arith.Neon.result,VG.Proof.MlDsa.AArch64.Arith.Neon.lane,Nat.mod_one,show (4+e)%4 < 2 by omega,show e%4 < 2 by omega,show (4+e)/4 = 1 by omega,show (4+e)%2 = e by omega]
        exact congrArg (fun i => (A i).val) (by omega)
      · rw [hb _ (by omega)]; simp [VG.Proof.MlDsa.AArch64.Arith.Neon.result,VG.Proof.MlDsa.AArch64.Arith.Neon.lane,Nat.mod_one,show ¬ (4+e)%4 < 2 by omega,show ¬ e%4 < 2 by omega,show (4+e)/4 = 1 by omega,show 2+(4+e)%2 = e by omega]
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedSpec`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Spec.MlDsa (Poly Zq zetas)
open VG.Proof.MlDsa.Arith
set_option linter.unusedSimpArgs false

/-- A packed batch reads only coefficients not visited by earlier batches. -/
theorem packed_input {blk : Poly → Nat → Nat → Nat → Nat → Poly}
    {op : Zq → Zq → Zq → Zq × Zq} (hblk : BlkOk blk op)
    (F : Poly) (zi : Nat → Nat) (len : Nat) (hlen : len = 1 ∨ len = 2)
    {u r : Nat} (hu : u < 32) (hr : r < 8) :
    (layF blk F len zi ((4/len)*u))[8*u+r]! = F[8*u+r]! := by
  rcases hlen with rfl | rfl
  · rw [layF1_get hblk F zi (by omega) (by omega)]
    simp only [Nat.div_one]; rw [ite_eq_right (by omega)]
  · rw [layF2_get hblk F zi (by omega) (by omega)]
    simp only [Nat.reduceDiv]; rw [ite_eq_right (by omega)]

/-- Lane indices and coefficient indices agree for both packed layer sizes. -/
theorem packed_indices (len : Nat) (hlen : len = 1 ∨ len = 2) (u r : Nat) :
    VG.Proof.MlDsa.AArch64.Arith.Neon.lower len (VG.Proof.MlDsa.AArch64.Arith.Neon.lane len r) = r-r%(2*len)+r%len ∧
    (4/len)*u + VG.Proof.MlDsa.AArch64.Arith.Neon.lane len r/len = (8*u+r)/(2*len) := by
  rcases hlen with rfl | rfl <;> simp only [VG.Proof.MlDsa.AArch64.Arith.Neon.lower,VG.Proof.MlDsa.AArch64.Arith.Neon.lane,Nat.div_one,Nat.mod_one,
    Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.reduceMul,Nat.reduceDiv] <;> omega

/-- One packed batch has the same result as its corresponding scalar blocks. -/
theorem packed_batch_get {blk : Poly → Nat → Nat → Nat → Nat → Poly}
    {op : Zq → Zq → Zq → Zq × Zq} (hblk : BlkOk blk op)
    (F : Poly) (zi : Nat → Nat) (len : Nat) (hlen : len = 1 ∨ len = 2)
    {u j : Nat} (hu : u < 32) (hj : j < 256) :
    let G := layF blk F len zi ((4/len)*u)
    let A := fun e => (op G[8*u+VG.Proof.MlDsa.AArch64.Arith.Neon.lower len e]! G[8*u+VG.Proof.MlDsa.AArch64.Arith.Neon.lower len e+len]!
      (VG.Spec.MlDsa.zetas (zi ((4/len)*u+e/len)))).1
    let B := fun e => (op G[8*u+VG.Proof.MlDsa.AArch64.Arith.Neon.lower len e]! G[8*u+VG.Proof.MlDsa.AArch64.Arith.Neon.lower len e+len]!
      (VG.Spec.MlDsa.zetas (zi ((4/len)*u+e/len)))).2
    (layF blk F len zi ((4/len)*(u+1)))[j]! =
      if 8*u ≤ j ∧ j < 8*u+8 then VG.Proof.MlDsa.AArch64.Arith.Neon.result len A B (j-8*u) else G[j]! := by
  dsimp only
  by_cases hin : 8*u ≤ j ∧ j < 8*u+8
  · rw [ite_eq_left hin]
    have hr : j-8*u < 8 := by omega
    have hi := VG.Proof.MlDsa.AArch64.Arith.Neon.packed_indices len hlen u (j-8*u)
    have hlow : VG.Proof.MlDsa.AArch64.Arith.Neon.lower len (VG.Proof.MlDsa.AArch64.Arith.Neon.lane len (j-8*u)) < 8 := by
      rcases hlen with rfl | rfl <;> simp only [VG.Proof.MlDsa.AArch64.Arith.Neon.lower,VG.Proof.MlDsa.AArch64.Arith.Neon.lane,Nat.div_one,Nat.mod_one,
        Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.reduceMul] <;> omega
    have hhigh : VG.Proof.MlDsa.AArch64.Arith.Neon.lower len (VG.Proof.MlDsa.AArch64.Arith.Neon.lane len (j-8*u))+len < 8 := by
      rcases hlen with rfl | rfl <;> simp only [VG.Proof.MlDsa.AArch64.Arith.Neon.lower,VG.Proof.MlDsa.AArch64.Arith.Neon.lane,Nat.div_one,Nat.mod_one,
        Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.reduceMul] <;> omega
    unfold VG.Proof.MlDsa.AArch64.Arith.Neon.result
    dsimp only
    rw [VG.Proof.MlDsa.AArch64.Arith.Neon.packed_input hblk F zi len hlen hu hlow]
    rw [show 8*u+VG.Proof.MlDsa.AArch64.Arith.Neon.lower len (VG.Proof.MlDsa.AArch64.Arith.Neon.lane len (j-8*u))+len =
      8*u+(VG.Proof.MlDsa.AArch64.Arith.Neon.lower len (VG.Proof.MlDsa.AArch64.Arith.Neon.lane len (j-8*u))+len) by omega,
      VG.Proof.MlDsa.AArch64.Arith.Neon.packed_input hblk F zi len hlen hu hhigh]
    have hz : (4/len)*u+VG.Proof.MlDsa.AArch64.Arith.Neon.lane len (j-8*u)/len = j/(2*len) := by
      rw [hi.2,show 8*u+(j-8*u) = j by omega]
    rw [hz]
    simp only [← Nat.add_assoc]
    rcases hlen with rfl | rfl
    · rw [layF1_get hblk F zi (by omega) hj,ite_eq_left (by omega)]
      by_cases he : j%2 = 0
      · simp only [ite_eq_left he]
        rw [ite_eq_left (by omega),show 8*u+VG.Proof.MlDsa.AArch64.Arith.Neon.lower 1 (VG.Proof.MlDsa.AArch64.Arith.Neon.lane 1 (j-8*u)) = j by
          simp only [VG.Proof.MlDsa.AArch64.Arith.Neon.lower,VG.Proof.MlDsa.AArch64.Arith.Neon.lane,Nat.div_one,Nat.mod_one,Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.reduceMul]; omega]
      · simp only [ite_eq_right he]
        rw [ite_eq_right (by omega),show 8*u+VG.Proof.MlDsa.AArch64.Arith.Neon.lower 1 (VG.Proof.MlDsa.AArch64.Arith.Neon.lane 1 (j-8*u)) = j-1 by
          simp only [VG.Proof.MlDsa.AArch64.Arith.Neon.lower,VG.Proof.MlDsa.AArch64.Arith.Neon.lane,Nat.div_one,Nat.mod_one,Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.reduceMul]; omega]
        simp only [Nat.reduceMul]
        rw [show j-1+1 = j by omega]
    · rw [layF2_get hblk F zi (by omega) hj,ite_eq_left (by omega)]
      by_cases he : j%4 < 2
      · simp only [ite_eq_left he]
        rw [ite_eq_left (by omega),show 8*u+VG.Proof.MlDsa.AArch64.Arith.Neon.lower 2 (VG.Proof.MlDsa.AArch64.Arith.Neon.lane 2 (j-8*u)) = j by
          simp only [VG.Proof.MlDsa.AArch64.Arith.Neon.lower,VG.Proof.MlDsa.AArch64.Arith.Neon.lane,Nat.reduceMul]; omega]
      · simp only [ite_eq_right he]
        rw [ite_eq_right (by omega),show 8*u+VG.Proof.MlDsa.AArch64.Arith.Neon.lower 2 (VG.Proof.MlDsa.AArch64.Arith.Neon.lane 2 (j-8*u)) = j-2 by
          simp only [VG.Proof.MlDsa.AArch64.Arith.Neon.lower,VG.Proof.MlDsa.AArch64.Arith.Neon.lane,Nat.reduceMul]; omega]
        simp only [Nat.reduceMul]
        rw [show j-2+2 = j by omega]
  · rw [ite_eq_right hin]
    rcases hlen with rfl | rfl
    · rw [layF1_get hblk F zi (by omega) hj,layF1_get hblk F zi (by omega) hj]
      simp only [Nat.div_one]
      by_cases h : j < 8*u <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
    · rw [layF2_get hblk F zi (by omega) hj,layF2_get hblk F zi (by omega) hj]
      simp only [Nat.reduceDiv]
      by_cases h : j < 8*u <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]

end VG.Proof.MlDsa.AArch64.Arith.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedStep`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab)
open VG.Proof.MlKem.AArch64 (Keep wp_ldrq wp_strq VChg)
open VG.Spec.MlDsa (Poly Zq PolyIs zetas)

/-- Advance to the next eight coefficients after a packed butterfly batch. -/
theorem packedEnd_ok (s : State) :
    WP isa (.block [.addImm .x .x2 .x2 32,.subImm .x .x5 .x5 1]) s fun s' =>
      ((s'.gpr .x2 = s.gpr .x2+32 ∧ s'.gpr .x5 = s.gpr .x5-1 ∧ s'.mem = s.mem) ∧
        Keep [.x2,.x5] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun
  exact ⟨rfl,rfl⟩

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} {zt : Zq → Zq}
  (hbf : VG.Proof.MlDsa.AArch64.Arith.Neon.VBflyOk bf op zt) {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

theorem packedStep_ok {fP zP : Addr} {len u k : Nat} (hlen : len = 1 ∨ len = 2)
    (hu : u < 32) {F : Poly} (zi : Nat → Nat) (up : Bool)
    (hzi : ∀ e < 4, zi ((4/len)*u+e/len) = if up then k+e/len else k-e/len)
    {tab : Nat → Nat} (hzt : VG.Proof.MlDsa.AArch64.Arith.Neon.TabZ tab zt) (hb : up = false → 4/len ≤ k)
    (hbound : VG.Proof.MlDsa.AArch64.Arith.Neon.baseZ len up k+4 ≤ 256) {s : State}
    (hc : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s) (hx : s.gpr .x2 = coeffAddr fP (8*u))
    (h3 : s.gpr .x3 = coeffAddr zP k)
    (hP : PolyIs s.mem fP (layF blk F len zi ((4/len)*u)))
    (ht : Tab tab s.mem zP 256) (hw : pR fP ∈ s.wr) (hzp : pR zP ∈ s.rd++s.wr) :
    WP isa (.block (packedBody bf len up)) s fun s' =>
      PolyIs s'.mem fP (layF blk F len zi ((4/len)*(u+1))) ∧
      s'.gpr .x2 = coeffAddr fP (8*(u+1)) ∧
      s'.gpr .x3 = coeffAddr zP (if up then k+4/len else k-4/len) ∧
      s'.gpr .x5 = s.gpr .x5-1 ∧ Keep [.x2,.x3,.x5] s s' ∧ VG.Proof.MlDsa.AArch64.Arith.Neon.BInv fP s s' := by
  let G := layF blk F len zi ((4/len)*u)
  have j0 : 8*u+4 ≤ 256 := by omega
  have j1 : 8*u+4+4 ≤ 256 := by omega
  have a1 : coeffAddr fP (8*u)+16 = coeffAddr fP (8*u+4) := coeffAddr_add _ _ 4
  have r0 : InRegions (s.rd++s.wr) (coeffAddr fP (8*u)) 16 :=
    ⟨_,List.mem_append_right _ hw,VG.Proof.MlDsa.AArch64.Arith.Neon.vector_contains _ j0⟩
  have r1 : InRegions (s.rd++s.wr) (coeffAddr fP (8*u+4)) 16 :=
    ⟨_,List.mem_append_right _ hw,VG.Proof.MlDsa.AArch64.Arith.Neon.vector_contains _ j1⟩
  unfold packedBody
  simp only [List.cons_append,List.nil_append,List.append_assoc]
  refine wp_ldrq (by decide) (by rw [hx,BitVec.add_zero]) r0 fun s₁ h₁ =>
    wp_ldrq (a := coeffAddr fP (8*u+4)) (by decide) (by rw [h₁.gpr,hx]; exact a1)
      (by rw [h₁.rd,h₁.wr]; exact r1) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  have hzcode : VG.Impl.MlDsa.AArch64.Arith.Neon.zetas len up = packedZetas len up := by
    rcases hlen with rfl | rfl <;> rfl
  rw [hzcode]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.packedZetas_ok (p := zP) (k := k) hzt len hlen up hb hbound
    (by rw [h₂.gpr,h₁.gpr]; exact h3) (by rw [h₂.mem,h₁.mem]; exact ht)
    (by rw [h₂.rd,h₂.wr,h₁.rd,h₁.wr]; exact hzp) (hc.chg (h₁.chg.trans h₂.chg)))
    fun s₃ ⟨lz,c₃,h33,hm₃,k₃,hv₃⟩ => ?_
  rw [WP.block_append_iff]
  have l6 : VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs (s₃.v .v6) (fun e => G[8*u+e]!) := by
    rw [hv₃ .v6 (by decide),h₂.get .v6,h₁.v]; exact VG.Proof.MlDsa.AArch64.Arith.Neon.coeffs_load hP j0
  have l7 : VG.Proof.MlDsa.AArch64.Arith.Neon.Coeffs (s₃.v .v7) (fun e => G[8*u+(4+e)]!) := by
    rw [hv₃ .v7 (by decide),h₂.v,h₁.mem]
    exact (VG.Proof.MlDsa.AArch64.Arith.Neon.coeffs_load hP j1).congr fun e _ => by dsimp only; rw [Nat.add_assoc]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.gather_ok len hlen l6 l7) fun s₄ ⟨h₄,la,lb⟩ => ?_
  rw [WP.block_append_iff]
  have z₄ : VG.Proof.MlDsa.AArch64.Arith.Neon.Zetas (s₄.v .v18) (fun e => zt (VG.Spec.MlDsa.zetas (zi ((4/len)*u+e/len)))) := by
    rw [h₄.get .v18]
    exact lz.congr fun e he => by dsimp only; rw [hzi e he]
  refine WP.mono (hbf s₄ (c₃.chg h₄) _ _ _ la lb z₄) fun s₅ ⟨va,vb,h₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.scatter_ok len hlen va vb) fun s₆ ⟨h₆,v6,v7⟩ => ?_
  have k06 : Keep [.x3] s s₆ := (((((h₁.keep.trans h₂.keep).trans k₃).trans h₄.keep).trans h₅.keep).trans h₆.keep).mono
  have g6 : s₆.gpr .x2 = coeffAddr fP (8*u) := by rw [k06.get .x2,hx]
  have m6 : s₆.mem = s.mem := by rw [h₆.mem,h₅.mem,h₄.mem,hm₃,h₂.mem,h₁.mem]
  refine wp_strq (by decide) (by rw [g6,BitVec.add_zero])
    (by rw [k06.wr]; exact ⟨_,hw,VG.Proof.MlDsa.AArch64.Arith.Neon.vector_contains _ j0⟩) fun s₇ h₇ =>
    wp_strq (a := coeffAddr fP (8*u+4)) (by decide) (by rw [h₇.gpr,g6]; exact a1)
      (by rw [h₇.wr,k06.wr]; exact ⟨_,hw,VG.Proof.MlDsa.AArch64.Arith.Neon.vector_contains _ j1⟩) fun s₈ h₈ => ?_
  have mem₈ : s₈.mem = (s.mem.write (coeffAddr fP (8*u)) 16 (s₆.v .v6)).write
      (coeffAddr fP (8*u+4)) 16 (s₆.v .v7) := by rw [h₈.mem,h₇.mem,h₇.v,m6]
  have c₈ : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s₈ := by
    have c₆ := ((c₃.chg h₄).chg h₅).chg h₆
    exact ⟨by rw [h₈.v,h₇.v]; exact c₆.q,by rw [h₈.v,h₇.v]; exact c₆.qi⟩
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.packedEnd_ok s₈) fun s₉ ⟨⟨⟨hx9,hcnt9,hm9⟩,k₉⟩,hv9⟩ =>
    ⟨?_,?_,?_,?_,(((k06.trans h₇.keep).trans h₈.keep).trans k₉).mono,
      ⟨(((k06.trans h₇.keep).trans h₈.keep).trans k₉).mono,?_,
        ⟨by rw [hv9]; exact c₈.q,by rw [hv9]; exact c₈.qi⟩⟩⟩
  · rw [hm9,mem₈]
    refine VG.Proof.MlDsa.AArch64.Arith.Neon.polyIs_write2 hP j0 j1 (by omega) v6 v7 fun j hj => ?_
    rw [VG.Proof.MlDsa.AArch64.Arith.Neon.packed_batch_get hblk F zi len hlen hu hj]
    by_cases c1 : 8*u ≤ j ∧ j < 8*u+4
    · rw [ite_eq_left (by omega),ite_eq_left c1]
      simp only [G,Nat.add_assoc]
    · rw [ite_eq_right c1]
      by_cases c2 : 8*u+4 ≤ j ∧ j < 8*u+8
      · rw [ite_eq_left (by omega),ite_eq_left (by omega),show 4+(j-(8*u+4)) = j-8*u by omega]
        simp only [G,Nat.add_assoc]
      · rw [ite_eq_right (by omega),ite_eq_right (by omega)]
  · rw [hx9,h₈.gpr,h₇.gpr,g6,show (32 : BitVec 64) = BitVec.ofNat 64 (4*8) from rfl,
      coeffAddr_add,show 8*u+8 = 8*(u+1) by omega]
  · rw [k₉.get .x3,h₈.gpr,h₇.gpr,h₆.gpr,h₅.gpr,h₄.gpr,h33]
  · rw [hcnt9,h₈.gpr,h₇.gpr,k06.get .x5]
  · rw [hm9,mem₈]; exact VG.Proof.MlDsa.AArch64.Arith.Neon.frame_write2 (Frame.refl _ _) j0 j1 _ _
end
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedLayer`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab wp_countdown)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (Poly Zq PolyIs)

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} {zt : Zq → Zq}
  (hbf : VG.Proof.MlDsa.AArch64.Arith.Neon.VBflyOk bf op zt) {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

/-- A complete length-one or length-two NTT layer, processed eight coefficients at a time. -/
theorem layer_packed_ok {fP zP : Addr} {len : Nat} (hlen : len = 1 ∨ len = 2)
    {tab : Nat → Nat} (hzt : VG.Proof.MlDsa.AArch64.Arith.Neon.TabZ tab zt) (up : Bool) (zi kz : Nat → Nat)
    (hk0 : kz 0 = VG.Proof.MlDsa.AArch64.Arith.Neon.firstZ len up)
    (hzi : ∀ u < 32, ∀ e < 4, zi ((4/len)*u+e/len) = if up then kz u+e/len else kz u-e/len)
    (hb : ∀ u < 32, up = false → 4/len ≤ kz u)
    (hbound : ∀ u < 32, VG.Proof.MlDsa.AArch64.Arith.Neon.baseZ len up (kz u)+4 ≤ 256)
    (hnext : ∀ u < 32, (if up then kz u+4/len else kz u-4/len) = kz (u+1))
    {F : Poly} {s : State} (h0 : s.gpr .x0 = fP) (h1 : s.gpr .x1 = zP)
    (hc : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s) (hP : PolyIs s.mem fP F) (ht : Tab tab s.mem zP 256)
    (hw : pR fP ∈ s.wr) (hzp : pR zP ∈ s.rd++s.wr)
    (hd : (pR zP).Disjoint (pR fP)) :
    WP isa (layer bf len up) s fun s' =>
      PolyIs s'.mem fP (layF blk F len zi (128/len)) ∧ VG.Proof.MlDsa.AArch64.Arith.Neon.BInv fP s s' := by
  have hf : 4*VG.Proof.MlDsa.AArch64.Arith.Neon.firstZ len up < 4096 := by
    rcases hlen with rfl | rfl <;> cases up <;> decide
  have hcov : (4/len)*32 = 128/len := by rcases hlen with rfl | rfl <;> decide
  have hsmall : len < 4 := by rcases hlen with rfl | rfl <;> decide
  unfold layer
  rw [ite_eq_left hsmall]
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.preLayer_ok len up hf s) fun s₁ ⟨⟨⟨hx2,hx3,hm1⟩,k1⟩,hv1⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.counter5_ok 32 (by decide) s₁)
    fun s₂ ⟨⟨⟨hcnt,hm2⟩,k2⟩,hv2⟩ => ?_)
  have c2 : VG.Proof.MlDsa.AArch64.Arith.Neon.VConsts s₂ := ⟨by rw [hv2,hv1]; exact hc.q,by rw [hv2,hv1]; exact hc.qi⟩
  refine WP.mono (wp_countdown (cnt := .x5) (N := 32) (by decide) (by decide)
    (fun u s' => PolyIs s'.mem fP (layF blk F len zi ((4/len)*u)) ∧
      s'.gpr .x2 = coeffAddr fP (8*u) ∧ s'.gpr .x3 = coeffAddr zP (kz u) ∧
      VG.Proof.MlDsa.AArch64.Arith.Neon.BInv fP s₂ s' ∧ Tab tab s'.mem zP 256)
    (fun u hu s' ⟨hp,hx2',hx3',hi,ht'⟩ _ => ?_)
    ⟨by rw [hm2,hm1]; exact hP,
      by rw [k2.get .x2,hx2,h0]; simp only [coeffAddr,Nat.mul_zero,BitVec.add_zero],
      by rw [k2.get .x3,hx3,h1,hk0],BInv.refl c2,by rw [hm2,hm1]; exact ht⟩ hcnt)
    fun s' ⟨hp,_,_,hi,_⟩ =>
      ⟨by simpa only [hcov] using hp,⟨((k1.trans k2).trans hi.keep).mono,
        by simpa only [hm2,hm1] using hi.frame,hi.consts⟩⟩
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.packedStep_ok hbf hblk hlen hu zi up (hzi u hu) hzt (hb u hu)
    (hbound u hu) hi.consts hx2' hx3' hp ht'
    (by rw [hi.keep.wr,k2.wr,k1.wr]; exact hw)
    (by rw [hi.keep.rd,hi.keep.wr,k2.rd,k2.wr,k1.rd,k1.wr]; exact hzp))
    fun s'' ⟨hp',hx2'',hx3'',hc'',_,hi'⟩ =>
      ⟨⟨hp',hx2'',by rw [hx3'',hnext u hu],hi.trans hi',
        ht'.frame hi'.frame (by simpa using hd) (by decide)⟩,hc''⟩
end
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Layers`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab)
open VG.Spec.MlDsa (Poly PolyIs)

private theorem lens_cases {len : Nat} (hl : len ∈ nttLens) :
    len = 128 ∨ len = 64 ∨ len = 32 ∨ len = 16 ∨ len = 8 ∨ len = 4 ∨ len = 2 ∨ len = 1 := by
  simpa only [nttLens,List.mem_cons,List.not_mem_nil,or_false] using hl

set_option linter.unusedSimpArgs false

theorem layer_fwd_ok {fP zP : Addr} {len : Nat} (hlen : len ∈ nttLens)
    {F : Poly} {s : State} (h0 : s.gpr .x0 = fP) (h1 : s.gpr .x1 = zP)
    (hc : VConsts s) (hP : PolyIs s.mem fP F) (ht : Tab zetaTab s.mem zP 256)
    (hw : pR fP ∈ s.wr) (hzp : pR zP ∈ s.rd++s.wr) (hd : (pR zP).Disjoint (pR fP)) :
    WP isa (layer bfly len true) s fun s' => PolyIs s'.mem fP (nttLayer F len) ∧ BInv fP s s' := by
  have hl := lens_cases hlen
  by_cases hsmall : len < 4
  · have hp : len = 1 ∨ len = 2 := by omega
    exact layer_packed_ok bfly_spec nttBlk_ok hp zetaTab_eq true
      (fun c => 128/len+c) (fun u => 128/len+(4/len)*u)
      (by simp [firstZ])
      (by intro u hu e he; simp only [ite_true]; omega)
      (by intro u hu h; contradiction)
      (by intro u hu; rcases hp with rfl | rfl <;> simp only [baseZ,ite_true,Nat.reduceDiv] <;> omega)
      (by intro u hu; simp only [ite_true,Nat.mul_add,Nat.mul_one]; omega) h0 h1 hc hP ht hw hzp hd
  · have hl' : len ∈ [4,8,16,32,64,128] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false]; omega
    exact layer_large_ok bfly_spec nttBlk_ok hl' zetaTab_eq true (fun c => 128/len+c)
      (by simp [firstZ])
      (by intro c hc; rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [Nat.reduceDiv] at * <;> omega)
      (by intro c hc; simp only [ite_true]; exact VG.Proof.MlDsa.AArch64.Arith.coeffAddr_next _ _)
      h0 h1 hc hP ht hw hzp hd

theorem layer_inv_ok {fP zP : Addr} {len : Nat} (hlen : len ∈ nttLens)
    {F : Poly} {s : State} (h0 : s.gpr .x0 = fP) (h1 : s.gpr .x1 = zP)
    (hc : VConsts s) (hP : PolyIs s.mem fP F) (ht : Tab negZetaTab s.mem zP 256)
    (hw : pR fP ∈ s.wr) (hzp : pR zP ∈ s.rd++s.wr) (hd : (pR zP).Disjoint (pR fP)) :
    WP isa (layer bflyInv len false) s fun s' => PolyIs s'.mem fP (nttInvLayer F len) ∧ BInv fP s s' := by
  have hl := lens_cases hlen
  by_cases hsmall : len < 4
  · have hp : len = 1 ∨ len = 2 := by omega
    exact layer_packed_ok bflyInv_spec nttInvBlk_ok hp negZetaTab_eq false
      (fun c => 256/len-1-c) (fun u => 256/len-1-(4/len)*u)
      (by simp [firstZ])
      (by intro u hu e he; simp only [Bool.false_eq_true,ite_false]; omega)
      (by intro u hu _; rcases hp with rfl | rfl <;> simp only [Nat.reduceDiv] <;> omega)
      (by intro u hu; rcases hp with rfl | rfl <;> simp only [baseZ,Bool.false_eq_true,ite_false,Nat.reduceDiv] <;> omega)
      (by intro u hu; simp only [Bool.false_eq_true,ite_false,Nat.mul_add,Nat.mul_one]; omega) h0 h1 hc hP ht hw hzp hd
  · have hl' : len ∈ [4,8,16,32,64,128] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false]; omega
    exact layer_large_ok bflyInv_spec nttInvBlk_ok hl' negZetaTab_eq false (fun c => 256/len-1-c)
      (by simp [firstZ])
      (by intro c hc; rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [Nat.reduceDiv] at * <;> omega)
      (by intro c hc; simp only [Bool.false_eq_true,ite_false]
          have hk : 1 ≤ 256/len-1-c := by
            rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp only [Nat.reduceDiv] at * <;> omega
          rw [show (4 : BitVec 64) = BitVec.ofNat 64 (4*1) from rfl,coeffAddr_sub _ _ _ hk]
          exact congrArg (coeffAddr zP) (by omega))
      h0 h1 hc hP ht hw hzp hd

end VG.Proof.MlDsa.AArch64.Arith.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.NttInv`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit`. -/
section

namespace VG
materialize_code Impl.MlDsa.AArch64.Arith.Neon.ntt
materialize_code Impl.MlDsa.AArch64.Arith.Neon.nttInv
end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Pro`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.AArch64.Arith (inPlaceK Tab storeTab_ok movW_ok)
open VG.Proof.MlKem.AArch64 (Keep wp_vop wp_scalar)
open VG.Spec.MlDsa (Poly PolyIs polyAt)

theorem consts_ok (s : State) :
    WP isa (.block consts) s fun s' => VConsts s' ∧ s'.mem = s.mem ∧ Keep [.x9,.x10] s s' := by
  unfold consts
  simp only [List.append_assoc]
  refine wp_scalar (by rfl) (movW_ok .x9 8380417 s) fun s₁ ⟨⟨h9,hm1⟩,k1⟩ hv1 => ?_
  refine wp_scalar (by rfl) (movW_ok .x10 4236238847 s₁) fun s₂ ⟨⟨h10,hm2⟩,k2⟩ hv2 => ?_
  refine wp_vop (d := .v16) rfl fun s₃ h3 => wp_vop (d := .v17) rfl fun s₄ h4 =>
    WP.block_nil_iff.mpr ⟨⟨?_,?_⟩,by rw [h4.mem,h3.mem,hm2,hm1],
      (((k1.trans k2).trans h3.keep).trans h4.keep).mono⟩
  · rw [h4.get .v16,h3.v,k2.get .x9,h9]
    rfl
  · rw [h4.v,h3.gpr,h10]
    rfl

/-- Initialize the Montgomery table and constants without changing the input polynomial. -/
theorem pro_ok {s : State} {t : Poly → Poly} (hp : (inPlaceK t).pre s) (tab : Nat → Nat) :
    WP isa (.block (pro tab)) s fun s' =>
      PolyIs s'.mem (s.gpr .x0) (polyAt s.mem (s.gpr .x0)) ∧
      Tab tab s'.mem (s.gpr .x1) 256 ∧ VConsts s' ∧
      Frame [pR (s.gpr .x1)] s.mem s'.mem ∧ Keep [.x9,.x10] s s' := by
  unfold pro
  rw [WP.block_append_iff]
  refine WP.mono (storeTab_ok tab (b := .x1) (by decide) s (by rw [hp.2.1]; simp))
    fun s₁ ⟨ht,hf,k1⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.consts_ok s₁) fun s₂ ⟨hc,hm2,k2⟩ =>
    ⟨?_,by rw [hm2]; exact ht,hc,by rw [hm2]; exact hf,(k1.trans k2).mono⟩
  rw [hm2]
  exact ⟨VG.Proof.MlDsa.Arith.reduced_frame hf (by simpa using hp.2.2.1) hp.2.2.2,
    VG.Proof.MlDsa.Arith.polyAt_frame hf (by simpa using hp.2.2.1)⟩
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Ntt`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (inPlaceK Tab)
open VG.Spec.MlDsa (Poly PolyIs polyAt)

theorem layers_ok (bf : List Instr) (up : Bool) (tab : Nat → Nat) (step : Poly → Nat → Poly)
    (hstep : ∀ {fP zP : Addr} {len : Nat}, len ∈ VG.Proof.MlDsa.Arith.nttLens → ∀ {F : Poly} {s : State},
      s.gpr .x0 = fP → s.gpr .x1 = zP → VConsts s → PolyIs s.mem fP F → Tab tab s.mem zP 256 →
      pR fP ∈ s.wr → pR zP ∈ s.rd++s.wr → (pR zP).Disjoint (pR fP) →
      WP isa (layer bf len up) s (fun s' => PolyIs s'.mem fP (step F len) ∧ BInv fP s s')) :
    ∀ (ls : List Nat), (∀ len ∈ ls, len ∈ VG.Proof.MlDsa.Arith.nttLens) → ∀ {fP zP : Addr} {F : Poly} {s : State},
      s.gpr .x0 = fP → s.gpr .x1 = zP → VConsts s → PolyIs s.mem fP F → Tab tab s.mem zP 256 →
      pR fP ∈ s.wr → pR zP ∈ s.rd++s.wr → (pR zP).Disjoint (pR fP) →
      WP isa (layers bf up ls) s (fun s' => PolyIs s'.mem fP (ls.foldl step F) ∧ BInv fP s s')
  | [], _, _, _, _, _, _, _, hc, hp, _, _, _, _ => WP.block_nil ⟨hp,BInv.refl hc⟩
  | len::ls, hls, _, _, _, _, h0, h1, hc, hp, ht, hw, hz, hd => by
    refine WP.seq (WP.mono (hstep (hls len (by simp)) h0 h1 hc hp ht hw hz hd)
      fun s₁ ⟨hp1,hi⟩ => ?_)
    exact WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.layers_ok bf up tab step hstep ls (fun l hl => hls l (List.mem_cons_of_mem _ hl))
      (by rw [hi.keep.get .x0,h0]) (by rw [hi.keep.get .x1,h1]) hi.consts hp1
      (ht.frame hi.frame (by simpa using hd) (by decide))
      (by rw [hi.keep.wr]; exact hw) (by rw [hi.keep.rd,hi.keep.wr]; exact hz) hd)
      fun _ ⟨hp2,hi2⟩ => ⟨hp2,hi.trans hi2⟩

theorem ntt_noCalls : VG.Impl.MlDsa.AArch64.Arith.Neon.ntt.noCalls = true := by lit_decide

theorem ntt_correct (s : State) (hs : (inPlaceK Spec.MlDsa.ntt).pre s) :
    ∃ t s', Exec isa VG.Impl.MlDsa.AArch64.Arith.Neon.ntt s t s' ∧ abiPreserved s s' ∧
      (inPlaceK Spec.MlDsa.ntt).post s s' := by
  have hw : pR (s.gpr .x0) ∈ s.wr := by rw [hs.2.1]; simp
  have hz : pR (s.gpr .x1) ∈ s.rd++s.wr := by rw [hs.1,hs.2.1]; simp
  have hrun : WP isa VG.Impl.MlDsa.AArch64.Arith.Neon.ntt s
      (fun s' => PolyIs s'.mem (s.gpr .x0) (nttLens.foldl VG.Proof.MlDsa.Arith.nttLayer (polyAt s.mem (s.gpr .x0)))) := by
    refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.pro_ok hs zetaTab)
      fun s₁ ⟨hp,ht,hc,_,hk⟩ => WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.layers_ok VG.Impl.MlDsa.AArch64.Arith.Neon.bfly true zetaTab VG.Proof.MlDsa.Arith.nttLayer
      (fun hl => layer_fwd_ok hl) VG.Proof.MlDsa.Arith.nttLens (fun _ h => h)
      (hk.get .x0) (hk.get .x1) hc hp ht (by rw [hk.wr]; exact hw)
      (by rw [hk.rd,hk.wr]; exact hz) hs.2.2.1.symm) (fun _ h => h.1))
  obtain ⟨t,s',he,hp⟩ := hrun
  refine ⟨t,s',he,VG.Proof.MlKem.AArch64.abi_of VG.Proof.MlDsa.AArch64.Arith.Neon.ntt_noCalls (by lit_decide) he (by lit_decide),?_⟩
  show PolyIs _ _ _
  rw [VG.Proof.MlDsa.Arith.ntt_eq_layers]
  exact hp

theorem ntt_ct : ConstantTime isa (inPlaceK Spec.MlDsa.ntt).pre (inPlaceK Spec.MlDsa.ntt).pub
    VG.Impl.MlDsa.AArch64.Arith.Neon.ntt :=
  VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x0,.x1])
    VG.Proof.MlDsa.AArch64.Arith.inPlace_agree (by taint_decide)

theorem ntt_verified : Verified AArch64.target VG.Impl.MlDsa.AArch64.Arith.Neon.ntt
    (Spec.MlDsa.nttContract AArch64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.AArch64.Arith.Neon.ntt_correct VG.Proof.MlDsa.AArch64.Arith.Neon.ntt_ct (by
    mldsa_implies [Spec.MlDsa.nttContract,Spec.MlDsa.inPlaceContract,Spec.MlDsa.inPlaceSig,inPlaceK,
      AArch64.abi,AArch64.argRegs] [VG.Proof.MlDsa.AArch64.Arith.inPlaceSat]
      using VG.Proof.MlDsa.AArch64.Arith.inPlaceSat)
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Scale`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (movW_ok wp_countdown)
open VG.Proof.MlKem.AArch64 (Keep Lanes wp_ldrq wp_strq wp_vop wp_scalar)
open VG.Spec.MlDsa (q Poly Zq PolyIs coeffAt)

def Scaled (G : Poly) (m : Mem) (p : Addr) (u : Nat) : Prop :=
  ∀ j < 256, (coeffAt m p j).toNat = if j < 4*u then (G[j]!*8347681).val else (G[j]!).val

/-- Four coefficients multiplied by 256⁻¹, with canonical outputs. -/
theorem scaleStep_ok {p : Addr} {G : Poly} {u : Nat} (hu : u < 64) {s : State}
    (hc : VConsts s) (hz : Lanes (s.v .v18) (fun _ => 16382))
    (hx : s.gpr .x2 = coeffAddr p (4*u)) (hp : VG.Proof.MlDsa.AArch64.Arith.Neon.Scaled G s.mem p u) (hw : pR p ∈ s.wr) :
    WP isa (.block scaleBody) s fun s' => VG.Proof.MlDsa.AArch64.Arith.Neon.Scaled G s'.mem p (u+1) ∧
      s'.gpr .x2 = coeffAddr p (4*(u+1)) ∧ s'.gpr .x5 = s.gpr .x5-1 ∧
      Frame [pR p] s.mem s'.mem ∧ VConsts s' ∧ s'.v .v18 = s.v .v18 ∧ Keep [.x2,.x5] s s' := by
  have hj : 4*u+4 ≤ 256 := by omega
  unfold scaleBody
  simp only [List.cons_append,List.nil_append,List.append_assoc]
  refine wp_ldrq (by decide) (by rw [hx,BitVec.add_zero])
    ⟨_,List.mem_append_right _ hw,vector_contains _ hj⟩ fun s₁ h1 => ?_
  have a1 : Lanes (s₁.v .v0) (fun e => (G[4*u+e]!).val) := by
    intro e he
    rw [h1.v,vword_read16 _ _ he,coeffAddr_add,← coeffAt_eq,hp _ (by omega),ite_eq_right (by omega)]
  have z1 : Lanes (s₁.v .v18) (fun _ => 16382) := by rw [h1.get .v18]; exact hz
  have hm : ∀ e < 4, VG.Proof.MlDsa.Arith.mont ((G[4*u+e]!).val*16382) < 2*q := by
    intro e he
    have ha : (G[4*u+e]!).val < 2^32 := Nat.lt_trans (G[4*u+e]!).isLt (by decide)
    have hzlt : 16382 < q := by decide
    have hb := Nat.mul_lt_mul'' hzlt ha
    exact mont_lt (by simpa only [Nat.mul_comm] using hb)
  refine mont_lanes (by decide) (by decide) (hc.chg h1.chg) a1 z1 (fun _ _ => by decide)
    fun s₂ h2 l2 => ?_
  refine csub_ok (by decide) ((hc.chg h1.chg).chg h2).lanes_q l2 hm fun s₃ h3 l3 => ?_
  have v3 : Coeffs (s₃.v .v0) (fun e => G[4*u+e]!*8347681) := l3.congr fun e _ => by
    dsimp only
    rw [show 16382 = (8347681 : Zq).val*2^32%q by decide,mont_mulR,val_mul]
  have g3 : s₃.gpr = s.gpr := h3.gpr.trans (h2.gpr.trans h1.gpr)
  have m3 : s₃.mem = s.mem := h3.mem.trans (h2.mem.trans h1.mem)
  have k3 : Keep [] s s₃ := ((h1.keep.trans h2.keep).trans h3.keep).mono
  refine wp_strq (by decide) (by rw [g3,hx,BitVec.add_zero])
    (by rw [k3.wr]; exact ⟨_,hw,vector_contains _ hj⟩) fun s₄ h4 => ?_
  refine WP.mono (bodyEnd_ok s₄) fun s₅ ⟨⟨⟨hx5,hcnt5,hm5⟩,k5⟩,hv5⟩ =>
    ⟨?_,?_,by rw [hcnt5,h4.gpr,g3],?_,
      ⟨by rw [hv5,h4.v]; exact (((hc.chg h1.chg).chg h2).chg h3).q,
        by rw [hv5,h4.v]; exact (((hc.chg h1.chg).chg h2).chg h3).qi⟩,
      by rw [hv5,h4.v,h3.get .v18,h2.get .v18,h1.get .v18],((k3.trans h4.keep).trans k5).mono⟩
  · intro j hj'
    rw [hm5,h4.mem,m3,coeffAt_write16 _ _ hj _ hj']
    by_cases h : 4*u ≤ j ∧ j < 4*u+4
    · rw [ite_eq_left h,ite_eq_left (by omega),v3 _ (by omega)]
      dsimp only
      rw [show 4*u+(j-4*u) = j by omega]
    · rw [ite_eq_right h,hp j hj']
      by_cases h' : j < 4*u <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
  · rw [hx5,h4.gpr,g3,hx,show (16 : BitVec 64) = BitVec.ofNat 64 (4*4) from rfl,
      coeffAddr_add,show 4*u+4 = 4*(u+1) by omega]
  · rw [hm5,h4.mem,m3]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (vector_contains p hj)

/-- Initialize the inverse scaling factor, pointer and loop counter. -/
theorem scalePro_ok (s : State) (hc : VConsts s) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Arith.movW .x6 16382 ++
      ([.vop (.dup .s4 .v18 .x6),Impl.MlKem.AArch64.mov .x2 .x0,.movz .x .x5 64 0] : List Instr))) s fun s' =>
      Lanes (s'.v .v18) (fun _ => 16382) ∧ s'.gpr .x2 = s.gpr .x0 ∧
      s'.gpr .x5 = 64 ∧ s'.mem = s.mem ∧ Keep [.x2,.x5,.x6] s s' ∧ VConsts s' := by
  refine wp_scalar (by rfl) (movW_ok .x6 16382 s) fun s₁ ⟨⟨h6,hm1⟩,k1⟩ hv1 => ?_
  refine wp_vop (d := .v18) rfl fun s₂ h2 => ?_
  have hscalar : WP isa (.block [Impl.MlKem.AArch64.mov .x2 .x0,.movz .x .x5 64 0]) s₂
      (fun s' => (s'.gpr .x2 = s₂.gpr .x0 ∧ s'.gpr .x5 = 64 ∧ s'.mem = s₂.mem) ∧ Keep [.x2,.x5] s₂ s') := by
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
    arun [Impl.MlKem.AArch64.mov]
  refine WP.mono (VG.Proof.MlKem.AArch64.WP.keepV (by rfl) hscalar)
    fun s₃ ⟨⟨⟨hx3,hcnt3,hm3⟩,k3⟩,hv3⟩ =>
      ⟨?_,by rw [hx3,h2.gpr,k1.get .x0],hcnt3,by rw [hm3,h2.mem,hm1],
        ((k1.trans h2.keep).trans k3).mono,
        ⟨by rw [hv3,h2.get .v16,hv1]; exact hc.q,by rw [hv3,h2.get .v17,hv1]; exact hc.qi⟩⟩
  rw [hv3,h2.v,h6]
  exact VG.Proof.MlKem.AArch64.lanes_dup.congr fun _ _ => by decide

/-- Scale all 256 coefficients by the modular inverse of 256. -/
theorem scale_ok {p : Addr} {G : Poly} {s : State} (h0 : s.gpr .x0 = p)
    (hc : VConsts s) (hp : PolyIs s.mem p G) (hw : pR p ∈ s.wr) :
    WP isa scale s fun s' => PolyIs s'.mem p (G.map (· * 8347681)) := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.scalePro_ok s hc) fun s₁ ⟨hz,hx,hcnt,hm,k1,c1⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .x5) (N := 64) (by decide) (by decide)
    (fun u s' => VG.Proof.MlDsa.AArch64.Arith.Neon.Scaled G s'.mem p u ∧ s'.gpr .x2 = coeffAddr p (4*u) ∧
      s'.v .v18 = s₁.v .v18 ∧ VConsts s' ∧ Keep [.x2,.x5] s₁ s')
    (fun u hu s' ⟨hp',hx',hz',hc',hk'⟩ _ => ?_)
    ⟨by intro j hj; rw [hm,ite_eq_right (by omega)]; exact polyIs_toNat hp hj,
      by rw [hx,h0]; simp only [coeffAddr,Nat.mul_zero,BitVec.add_zero],rfl,c1,Keep.refl _ _⟩ hcnt)
    fun s' ⟨hp',_,_,_,_⟩ => ?_
  · refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.scaleStep_ok hu hc' (by rw [hz']; exact hz) hx' hp'
      (by rw [hk'.wr,k1.wr]; exact hw)) fun s'' ⟨hp'',hx'',hcnt'',_,hc'',hz'',hk''⟩ =>
      ⟨⟨hp'',hx'',hz''.trans hz',hc'',(hk'.trans hk'').mono⟩,hcnt''⟩
  · refine polyIs_of_toNat fun j hj => ?_
    rw [hp' j hj,ite_eq_left (by rw [n_eq] at hj; omega),VG.Proof.MlDsa.Arith.map_mul_get _ _ hj]
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.NttInv`. -/
section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (inPlaceK)
open VG.Spec.MlDsa (PolyIs polyAt)

theorem nttInv_noCalls : VG.Impl.MlDsa.AArch64.Arith.Neon.nttInv.noCalls = true := by lit_decide

theorem nttInv_correct (s : State) (hs : (inPlaceK Spec.MlDsa.nttInv).pre s) :
    ∃ t s', Exec isa VG.Impl.MlDsa.AArch64.Arith.Neon.nttInv s t s' ∧ abiPreserved s s' ∧
      (inPlaceK Spec.MlDsa.nttInv).post s s' := by
  have hw : pR (s.gpr .x0) ∈ s.wr := by rw [hs.2.1]; simp
  have hz : pR (s.gpr .x1) ∈ s.rd++s.wr := by rw [hs.1,hs.2.1]; simp
  have hrun : WP isa VG.Impl.MlDsa.AArch64.Arith.Neon.nttInv s
      (fun s' => PolyIs s'.mem (s.gpr .x0)
        ((nttInvLens.foldl VG.Proof.MlDsa.Arith.nttInvLayer (polyAt s.mem (s.gpr .x0))).map (· * 8347681))) := by
    refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.pro_ok hs negZetaTab) fun s₁ ⟨hp,ht,hc,_,hk⟩ => ?_)
    refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Arith.Neon.layers_ok VG.Impl.MlDsa.AArch64.Arith.Neon.bflyInv false negZetaTab VG.Proof.MlDsa.Arith.nttInvLayer
      (fun hl => layer_inv_ok hl) VG.Proof.MlDsa.Arith.nttInvLens
      (by intro l hl; simpa [VG.Proof.MlDsa.Arith.nttInvLens,VG.Proof.MlDsa.Arith.nttLens,or_comm,or_left_comm,or_assoc] using hl)
      (hk.get .x0) (hk.get .x1) hc hp ht (by rw [hk.wr]; exact hw)
      (by rw [hk.rd,hk.wr]; exact hz) hs.2.2.1.symm) fun s₂ ⟨hp2,hi⟩ => ?_)
    exact VG.Proof.MlDsa.AArch64.Arith.Neon.scale_ok (by rw [hi.keep.get .x0,hk.get .x0]) hi.consts hp2
      (by rw [hi.keep.wr,hk.wr]; exact hw)
  obtain ⟨t,s',he,hp⟩ := hrun
  refine ⟨t,s',he,VG.Proof.MlKem.AArch64.abi_of VG.Proof.MlDsa.AArch64.Arith.Neon.nttInv_noCalls (by lit_decide) he (by lit_decide),?_⟩
  show PolyIs _ _ _
  rw [VG.Proof.MlDsa.Arith.nttInv_eq_layers]
  exact hp

theorem nttInv_ct : ConstantTime isa (inPlaceK Spec.MlDsa.nttInv).pre (inPlaceK Spec.MlDsa.nttInv).pub
    VG.Impl.MlDsa.AArch64.Arith.Neon.nttInv :=
  VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x0,.x1])
    VG.Proof.MlDsa.AArch64.Arith.inPlace_agree (by taint_decide)

theorem nttInv_verified : Verified AArch64.target VG.Impl.MlDsa.AArch64.Arith.Neon.nttInv
    (Spec.MlDsa.nttInvContract AArch64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.AArch64.Arith.Neon.nttInv_correct VG.Proof.MlDsa.AArch64.Arith.Neon.nttInv_ct (by
    mldsa_implies [Spec.MlDsa.nttInvContract,Spec.MlDsa.inPlaceContract,Spec.MlDsa.inPlaceSig,inPlaceK,
      AArch64.abi,AArch64.argRegs] [VG.Proof.MlDsa.AArch64.Arith.inPlaceSat]
      using VG.Proof.MlDsa.AArch64.Arith.inPlaceSat)
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

end
