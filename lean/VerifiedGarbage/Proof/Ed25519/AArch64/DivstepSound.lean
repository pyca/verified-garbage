module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Ends
public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Words
import VerifiedGarbage.Proof.Divstep.Iter
public import VerifiedGarbage.Proof.Divstep.Steps
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Ed25519.Group.Extended
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.Ring

/-!
# Ed25519 and X25519 on AArch64: the inversion by divsteps is correct

Each batch keeps the invariant `BatchInv`: `f` and `g` are those of `59 k` divsteps
from `(1, p, x)`, and `2^590 x a ≡ 2^(59 k) f`, `2^590 x b ≡ 2^(59 k) g` modulo `p`
(`batch_ok`). After 590 divsteps `g = 0` and `f = ±1`, so `x a ≡ ±1`, and
`x^(p - 2)` is the inverse, as `p` is prime.
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Divstep

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.Divstep
open VG.Proof.Ed25519.AArch64 Word64
open VG.Proof.Mont.AArch64 (KeepRegs)
open VG.Proof.Divstep (MSt msteps divsteps)
open VG.Spec.X25519 (P)
open VG.Proof.X25519 (toFe)

variable {large : Bool}

private theorem P_val : (P : Int) = 2 ^ 255 - 19 := by simp [P]
private theorem P_odd : (P : Int) % 2 = 1 := by rw [P_val]; norm_num

/-- The divsteps' `(d, f, g)` after `k` batches from `x`. -/
def dsI (x k : Nat) : Int × Int × Int := divsteps (59 * k) (1, P, x)

/-- `2^590`. -/
def scale : Int := 2 ^ 590

/-- What the code holds after `k` batches from `x`. -/
structure BatchInv (x k : Nat) (base : Addr) (s : State) : Prop where
  i : s.gpr .x20 = half (dsI x k).1
  f : sv (fe s.mem base oF) = (dsI x k).2.1
  g : sv (fe s.mem base oG) = (dsI x k).2.2
  al : fe s.mem base oA < abMax
  bl : fe s.mem base oB < abMax
  ca : scale * (x * fe s.mem base oA : Int) ≡ 2 ^ (59 * k) * (dsI x k).2.1 [ZMOD P]
  cb : scale * (x * fe s.mem base oB : Int) ≡ 2 ^ (59 * k) * (dsI x k).2.2 [ZMOD P]
  z : x = 0 → (fe s.mem base oA : Int) ≡ 0 [ZMOD P]

private theorem dsI_le {x : Nat} (hx : x < P) (k : Nat) : |(dsI x k).2.1| ≤ P ∧ |(dsI x k).2.2| ≤ P :=
  Divstep.divsteps_le (by decide) P_odd (by rw [abs_of_nonneg (by positivity)]) (by
    rw [abs_of_nonneg (by positivity)]; exact_mod_cast hx.le) _

private theorem small {f : Int} (h : |f| ≤ P) : |f| < 2 ^ 255 := by rw [P_val] at h; omega_using [h]

/-- The low word of a number in two's complement. -/
theorem low_word {m : Mem} {base : Addr} {o : Nat} {f : Int} (h : sv (fe m base o) = f) :
    ((word m base o).toNat : Int) % 2 ^ 64 = f % 2 ^ 64 := by
  obtain ⟨b, hb⟩ := sv_split (fe m base o)
  rw [h] at hb
  simp only [fe, val4] at hb
  push_cast at hb
  generalize ((word m base o).toNat : Int) = a at *
  generalize ((word m base (o + 8)).toNat : Int) = c at *
  generalize ((word m base (o + 16)).toNat : Int) = d at *
  generalize ((word m base (o + 24)).toNat : Int) = e at *
  omega_using [hb]

theorem batchStart_ok {s : State} {base : Addr} (hs : Scr s base large) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block batchStart) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j - 1) ∧ t.gpr .x2 = word s.mem base oF ∧ t.gpr .x3 = word s.mem base oG ∧
      Keeps [.x19, .x2, .x3] s t := by
  have hc := workSize_ge large
  have e : batchStart = [Impl.Weierstrass.AArch64.decCounter] ++ ([ld .x2 oF] ++ [ld .x3 oG]) := rfl
  rw [e, WP.block_append_iff]
  refine WP.mono (Weierstrass.AArch64.decCounter_ok s hj hj' h19) fun s₁ ⟨c, q₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (hs.of_keeps q₁ (by decide)) (d := oF) (by decide) (by unfold oF; omega_using [hc]) .x2)
    fun s₂ ⟨v₂, q₂⟩ => ?_
  have k₂ : Keeps [.x19, .x2] s s₂ := (q₁.mono (by decide)).trans (q₂.mono (by decide))
  refine WP.mono (ld_ok (hs.of_keeps k₂ (by decide)) (d := oG) (by decide) (by unfold oG; omega_using [hc]) .x3)
    fun s₃ ⟨v₃, q₃⟩ => ⟨?_, ?_, ?_, (k₂.mono (by decide)).trans (q₃.mono (by decide))⟩
  · rw [q₃.gpr _ (by decide), q₂.gpr _ (by decide), c]
  · rw [q₃.gpr _ (by decide), v₂, q₁.mem]
  · rw [v₃, k₂.mem]

/-- The congruence of a row of `a` and `b`. -/
private theorem row_cong {x A B : Nat} {u v f g f' c R m k : Int}
    (ca : k * (x * A : Int) ≡ c * f [ZMOD P]) (cb : k * (x * B : Int) ≡ c * g [ZMOD P])
    (hR : R = u * A + v * B + (2 ^ 255 - 19) * m) (hf : 2 ^ 59 * f' = u * f + v * g) :
    k * (x * R) ≡ c * 2 ^ 59 * f' [ZMOD P] := by
  have h := (ca.mul_left u).add (cb.mul_left v)
  have e1 : c * 2 ^ 59 * f' = u * (c * f) + v * (c * g) := by rw [mul_assoc, hf]; ring
  rw [e1]
  refine Int.ModEq.trans ?_ h
  rw [hR, ← P_val, Int.modEq_iff_dvd]
  exact ⟨-(k * x * m), by ring⟩

theorem batch_ok {x k : Nat} (hx : x < P) (hk : k < 10) {s : State} {base : Addr} (hs : Scr s base large)
    (hI : BatchInv x k base s) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64) (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block batch) s fun t =>
      BatchInv x (k + 1) base t ∧ t.gpr .x19 = BitVec.ofNat 64 (j - 1) ∧ Outside base 192 512 s.mem t.mem ∧
      KeepRegs invRegs s t := by
  obtain ⟨hi, hf, hg, al, bl, ca, cb, hz⟩ := hI
  have hs1 : dsI x (k + 1) = divsteps 59 (dsI x k) := by
    unfold dsI; rw [show 59 * (k + 1) = 59 * k + 59 by ring, Divstep.divsteps_add]
  obtain ⟨hod, hof⟩ : (dsI x k).1 % 2 = 1 ∧ (dsI x k).2.1 % 2 = 1 := Divstep.divsteps_odd (by decide) P_odd _
  obtain ⟨lf, lg⟩ := dsI_le hx (k + 1)
  have hd : |(dsI x k).1| ≤ 2 ^ 30 := by
    have h := Divstep.divsteps_d (1, (P : Int), (x : Int)) (59 * k)
    simp only [abs_one] at h
    have : (59 * k : Int) ≤ 59 * 9 := by exact_mod_cast (by omega_using [hk] : 59 * k ≤ 59 * 9)
    push_cast at h
    have h : |(dsI x k).1| ≤ 1 + 2 * (59 * k) := h
    linarith
  have hzero : x = 0 → (dsI x k).2.2 = 0 := fun hx0 => by
    unfold dsI; rw [hx0]; exact (Divstep.divsteps_zero (t := (1, (P : Int), ((0 : Nat) : Int))) (by simp) _).1
  rw [hs1] at lf lg
  generalize dsI x k = st at hi hf hg ca cb hs1 hod hof lf lg hd hzero
  obtain ⟨d, f, g⟩ := st
  simp only at hi hf hg ca cb hod hof hd hzero
  obtain ⟨m1, m2⟩ := Divstep.msteps_mat (d := d) (g := g) hof 59
  obtain ⟨b1, b2⟩ := Divstep.msteps_bnd d f g 59
  have hdfg := Divstep.msteps_dfg 59 (MSt.init d f g)
  have hg0 : g = 0 → (msteps 59 (MSt.init d f g)).v = 0 := fun hg => by
    subst hg; rw [MSt.init, Divstep.msteps_g0]; simp
  simp only [MSt.init] at hdfg
  rw [← hdfg] at hs1 lf lg
  simp only at lf lg
  simp only [batch, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (batchStart_ok hs hj hj' h19) fun s₁ ⟨c₁, f₁, g₁, q₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (words_ok s₁ (d := d) (f := f) (g := g) hd hod hof (by rw [q₁.gpr _ (by decide)]; exact hi)
    (by rw [f₁]; exact low_word hf) (by rw [g₁]; exact low_word hg)) fun s₂ ⟨i₂, M₂, q₂⟩ => ?_
  simp only [MSt.init] at i₂ M₂ m1 m2 b1 b2 hg0
  generalize msteps 59 ⟨d, f, g, 1, 0, 0, 1⟩ = T at *
  have k₂ : Keeps invRegs s s₂ := (q₁.mono (by decide)).trans (q₂.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (bias_ok s₂ M₂.u M₂.v M₂.q M₂.r (le_trans (le_add_of_nonneg_right (abs_nonneg _)) b1)
    (le_trans (le_add_of_nonneg_left (abs_nonneg _)) b1) (le_trans (le_add_of_nonneg_right (abs_nonneg _)) b2)
    (le_trans (le_add_of_nonneg_left (abs_nonneg _)) b2)) fun s₃ ⟨u₃, v₃, q₃, r₃, z₃, kp₃⟩ => ?_
  have k₃ : Keeps invRegs s s₃ := k₂.trans (kp₃.mono (by decide))
  have hs₃ := hs.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (updateFG_ok hs₃ z₃ u₃ v₃ q₃ r₃ (f' := T.f) (g' := T.g) (by rw [k₃.mem, hf, hg]; exact m1)
    (by rw [k₃.mem, hf, hg]; exact m2) (small lf) (small lg)) fun s₄ ⟨f₄, g₄, o₄, k₄⟩ => ?_
  have hs₄ := Scr.of_keepRegs' hs₃ k₄ (by decide)
  have W₄ : ∀ o, o = oA ∨ o = oB → fe s₄.mem base o = fe s.mem base o := by
    intro o ho
    have w : ∀ d, 256 ≤ d ∧ d + 8 ≤ 320 → word s₄.mem base d = word s.mem base d := fun d hd => by
      rw [← k₃.mem]
      refine (Mem.readW_congr fun i hi => (o₄ _ ?_).symm).symm
      rw [ofs_off base (by omega_using [hd, hi])]
      omega_using [hd, hi]
    rcases ho with rfl | rfl <;> simp only [fe] <;>
      rw [w _ (by decide), w _ (by decide), w _ (by decide), w _ (by decide)]
  have A₄ := W₄ oA (Or.inl rfl)
  have B₄ := W₄ oB (Or.inr rfl)
  refine WP.mono (updateAB_ok hs₄ (by rw [k₄.gpr _ (by decide), z₃]) (by rw [k₄.gpr _ (by decide)]; exact u₃)
    (by rw [k₄.gpr _ (by decide)]; exact v₃) (by rw [k₄.gpr _ (by decide)]; exact q₃)
    (by rw [k₄.gpr _ (by decide)]; exact r₃) b1 b2 (by rw [A₄]; exact al) (by rw [B₄]; exact bl))
    fun t ⟨l₅, l₅', ⟨ma, a₅⟩, ⟨mb, b₅⟩, o₅, k₅⟩ => ?_
  rw [A₄, B₄] at a₅ b₅
  have kt : KeepRegs invRegs s t := (⟨k₃.gpr, k₃.rd, k₃.wr, k₃.sp⟩ : KeepRegs invRegs s s₃).trans
    ((k₄.trans k₅).mono (by decide))
  have F₅ : fe t.mem base oF = fe s₄.mem base oF := o₅.fe (by decide) (by decide)
  have G₅ : fe t.mem base oG = fe s₄.mem base oG := o₅.fe (by decide) (by decide)
  have hP : (2 : Int) ^ (59 * (k + 1)) = 2 ^ (59 * k) * 2 ^ 59 := by rw [← pow_add]; ring_nf
  refine ⟨⟨?_, ?_, ?_, l₅, l₅', ?_, ?_, fun hx0 => ?_⟩, ?_, ?_, kt⟩
  · rw [hs1, k₅.gpr _ (by decide), k₄.gpr _ (by decide), kp₃.gpr _ (by decide), i₂]
  · rw [hs1, F₅, f₄]
  · rw [hs1, G₅, g₄]
  · rw [hs1, hP]; exact row_cong ca cb a₅ m1
  · rw [hs1, hP]; exact row_cong ca cb b₅ m2
  · rw [a₅, hg0 (hzero hx0), ← P_val, Int.modEq_iff_dvd]
    obtain ⟨n, hn⟩ := Int.modEq_iff_dvd.mp (hz hx0)
    exact ⟨T.u * n - ma, by linear_combination T.u * hn⟩
  · rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), kp₃.gpr _ (by decide), q₂.gpr _ (by decide), c₁]
  · intro y hy
    rw [o₅ y (by omega_using [hy]), o₄ y (by omega_using [hy]), k₃.mem]

/-! ## The result -/

private theorem b0_spec : scale * b0 ≡ 1 [ZMOD P] := by unfold Int.ModEq scale b0; decide +kernel

private theorem toZ_toFe (n : Nat) : Ed25519.toZ (toFe n) = (n : ZMod P) := by
  apply ZMod.val_injective
  rw [ZMod.val_natCast]
  rfl

/-- The result's residue, from the last invariant. -/
private theorem result {x A F R : Nat} (hx : x < P) (hA : A < abMax) (hF : F < 2 ^ 256) (hf : sv F = (dsI x 10).2.1)
    (ca : scale * (x * A : Int) ≡ 2 ^ (59 * 10) * (dsI x 10).2.1 [ZMOD P]) (hz : x = 0 → (A : Int) ≡ 0 [ZMOD P])
    (hR : R = if 2 ^ 255 ≤ F then 2 ^ 256 - 38 - A else A) : (R : ZMod P) = (x : ZMod P) ^ (P - 2) := by
  have twoP : ((2 ^ 256 - 38 : Nat) : ZMod P) = 0 := by
    rw [show (2 ^ 256 - 38 : Nat) = P * 2 by simp [P], Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have neg : ((2 ^ 256 - 38 - A : Nat) : ZMod P) = -(A : ZMod P) := by
    rw [Nat.cast_sub (by unfold abMax at hA; omega_using [hA]), twoP, zero_sub]
  by_cases h0 : x = 0
  · have ha := (ZMod.intCast_eq_intCast_iff _ _ _).2 (hz h0)
    push_cast at ha
    rw [hR, h0, Nat.cast_zero, zero_pow (by simp [P])]
    split
    · rw [neg, ha, neg_zero]
    · exact ha
  · have hdone := Divstep.divsteps_590 (f := (P : Int)) (g := (x : Int)) P_odd (by positivity)
      (by exact_mod_cast hx.le) (by rw [P_val]; norm_num) (n := 590) le_rfl
    have hcop : Int.gcd (P : Int) (x : Int) = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact Nat.coprime_of_lt_prime h0 hx Ed25519.prime_field
    have hs : dsI x 10 = divsteps 590 (1, (P : Int), (x : Int)) := rfl
    rw [hs] at hf ca
    generalize (divsteps 590 (1, (P : Int), (x : Int))).2.1 = f at hdone hf ca
    rw [hcop] at hdone
    have hf1 : f = 1 ∨ f = -1 := by omega_using [hdone]
    have hc := Divstep.cancel_pow2 (N := 59 * 10) P_odd (by rw [P_val]; norm_num) ca
    have hc := (ZMod.intCast_eq_intCast_iff _ _ _).2 hc
    push_cast at hc
    have hxR : (x : ZMod P) * (R : ZMod P) = 1 := by
      unfold sv at hf
      rcases hf1 with rfl | rfl
      · have : ¬ 2 ^ 255 ≤ F := fun h => by
          rw [ite_eq_right (by omega_using [h])] at hf
          omega_using [hf, hF]
        rw [hR, ite_eq_right this, hc, Int.cast_one]
      · have : 2 ^ 255 ≤ F := by
          by_contra h
          rw [ite_eq_left (by omega_using [h])] at hf
          omega_using [hf]
        rw [hR, ite_eq_left this, neg, mul_neg, hc, Int.cast_neg, Int.cast_one, neg_neg]
    have hX : (x : ZMod P) ≠ 0 := fun h => by rw [h, zero_mul] at hxR; exact zero_ne_one hxR
    calc (R : ZMod P) = (R : ZMod P) * x * (x : ZMod P) ^ (P - 2) := (Ed25519.mul_pow_inv hX _).symm
      _ = x * R * (x : ZMod P) ^ (P - 2) := by ring
      _ = (x : ZMod P) ^ (P - 2) := by rw [hxR, one_mul]

theorem invert_sound {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa VG.Impl.Ed25519.AArch64.Divstep.invert s fun t =>
      env t.mem base 15 = VG.Proof.X25519.invert (env s.mem base 2) ∧
      Outside base 192 512 s.mem t.mem ∧ KeepRegs invRegs s t := by
  unfold invert
  refine WP.seq (WP.mono (start_ok hs) fun a ⟨fa, aa, ba, ga, ia, ca, oa, ka⟩ => ?_)
  have hsa := Scr.of_keepRegs' hs ka (by decide)
  obtain ⟨x, hxe⟩ : ∃ x, x = fe s.mem base 128 % P := ⟨_, rfl⟩
  have hx : x < P := by rw [hxe]; exact Nat.mod_lt _ (by decide)
  rw [← hxe] at ga
  have hP : P = 2 ^ 255 - 19 := rfl
  have I0 : BatchInv x 0 base a := by
    have e : dsI x 0 = (1, (P : Int), (x : Int)) := rfl
    refine ⟨by rw [ia, e]; show (0 : BitVec 64) = half 1; decide, ?_, ?_, by rw [aa]; decide, by rw [ba]; decide, ?_, ?_, fun _ => by rw [aa]; rfl⟩
    · rw [fa, e]; show sv P = (P : Int); decide
    · rw [ga, e]; unfold sv; rw [ite_eq_left (by rw [hP] at hx; omega_using [hx])]
    · rw [aa, e]
      simp only [Nat.cast_zero, mul_zero, pow_zero, one_mul]
      exact (Int.emod_self.trans (by simp)).symm
    · rw [ba, e]
      simp only [mul_zero, pow_zero, one_mul]
      have h' := b0_spec.mul_left (x : Int)
      rw [mul_one] at h'
      rw [show scale * (x * b0) = x * (scale * b0) by ring]
      exact h'
  refine WP.seq (Weierstrass.AArch64.countLoop_ok (n := 10) (by decide)
    (Inv := fun j t => BatchInv x (10 - j) base t ∧ t.gpr .x19 = BitVec.ofNat 64 j ∧ Scr t base large ∧
      Outside base 192 512 a.mem t.mem ∧ KeepRegs invRegs a t)
    (fun j t h1 h10 ⟨It, ct, st, ot, kt⟩ => ?_)
    (fun t ⟨It, _, st, ot, kt⟩ => ?_) (by decide) ⟨I0, ca, hsa, Outside.refl _ _ _ _, fun _ _ => rfl, rfl, rfl, rfl⟩)
  · refine WP.mono (batch_ok hx (k := 10 - j) (by omega_using [h1]) st It h1 (by omega_using [h10]) ct)
      fun u ⟨Iu, cu, ou, ku⟩ => ⟨⟨?_, cu, Scr.of_keepRegs' st ku (by decide), ot.trans ou, kt.trans ku⟩, cu⟩
    rw [show 10 - (j - 1) = 10 - j + 1 by omega_using [h1, h10]]
    exact Iu
  · refine WP.mono (finish_ok st It.al) fun u ⟨vu, ou, ku⟩ => ⟨?_, (oa.trans ot).trans ou, (ka.trans kt).trans ku⟩
    rw [Nat.sub_zero] at It
    have hr := result hx It.al (val4_lt _ _ _ _) It.f It.ca It.z vu
    rw [X25519.invert_eq, ← Ed25519.toZ_inj, Ed25519.toZ_pow]
    show Ed25519.toZ (toFe (fe u.mem base 544)) = Ed25519.toZ (toFe (fe s.mem base 128)) ^ (P - 2)
    rw [toZ_toFe, toZ_toFe, hr, hxe, ZMod.natCast_mod]

instance sound : Sound where
  invert_ok hs := WP.mono (invert_sound hs) fun t ⟨v, o, k⟩ =>
    ⟨v, k.mono (by decide), k.gpr _ (by decide), o⟩

end VG.Proof.Ed25519.AArch64.Divstep
