module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Proof.Weierstrass.Booth
public import VerifiedGarbage.Proof.Weierstrass.JacMadd
import VerifiedGarbage.Proof.Weierstrass.CombPointW
import VerifiedGarbage.Proof.Weierstrass.CombDigitTopW
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Bits
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Fprog
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointFn
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.LadderPCall
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Mont.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-!
# The Booth comb with Jacobian mixed additions, on PPC64LE: correctness

`TCombCfg.combJ` (`Impl/Weierstrass/PPC64LE/TCombJ.lean`) computes `[k]G`,
with the statement of `TComb.comb_ok` (`combJ_ok`), for a configuration
that also meets `JConfig`:

* `bdigit_ok`, `bsign_ok`: Booth's digit of window `j`, its magnitude `bmag`
  (`Proof/Weierstrass/Booth.lean`) and the mask of its sign, from the table
  of the scalar's bits; `bentry_ok`: the signed entry in the point
  functions' `Q`, with `Z = 1`, or `O` for a zero digit;
* `maddCall_ok`: the call of the mixed addition `vg_<curve>_point_madd`
  (`maddJF`, `Proof/Weierstrass/JacMadd.lean`);
* `zMask_ok`, `nzOf_ok`, `zsel_ok`, `rsel_ok`: the masks of `R = O` and of a
  zero digit, and the selections by them;
* `bstep_math`, `bstep_ok`: a window takes `R`, Jacobian, from the sum of the
  digits below `j` to the sum to `j` (`JAcc`), the digits' bound ruling out
  equal points (`booth_ne`);
* `loopJ_ok`, `bout_ok`, `combJ_ok`: the windows, and `R` back to
  homogeneous coordinates (`InvJ.out`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.TCombJ

open VG VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass.PPC64LE.Point
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Point VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass.PPC64LE.TComb
open VG.Impl.Weierstrass.Point (elemBytes ownAt aAt b3At oAt pAt qAt)
open VG.Impl.Weierstrass.PPC64LE.Mont (own)
open Spec.Weierstrass

/-! ## Booth's digit -/

/-- The code's magnitude: `((v - (2^w & -s)) ^ -s) - (-s) = s ? 2^w - v : v`
for a bit `s` and `v ≤ 2^w`. -/
theorem bmagBV {w v s : Nat} (hw : w < 9) (hv : v ≤ 2 ^ w) (hs : s ≤ 1) :
    ((BitVec.ofNat 64 v - (BitVec.ofNat 64 (2 ^ w) &&& (0#64 - BitVec.ofNat 64 s))) ^^^
        (0#64 - BitVec.ofNat 64 s)) - (0#64 - BitVec.ofNat 64 s) =
      BitVec.ofNat 64 (if s = 1 then 2 ^ w - v else v) := by
  have h9 : 2 ^ w ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega_using [hw])
  obtain rfl | rfl : s = 0 ∨ s = 1 := by omega_using [hs]
  · simp
  · simp only [↓reduceIte]
    rw [show (0#64 - BitVec.ofNat 64 1) = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      BitVec.xor_allOnes]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_not, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_allOnes, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [hv, h9] : v < 2 ^ 64), Nat.mod_eq_of_lt (by omega_using [h9] : 2 ^ w < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega_using [h9] : 2 ^ w - v < 2 ^ 64)]
    omega_using [hv, h9]

/-- The last window's top bit, above the scalar's bits, is clear. -/
theorem bcar_last {w k J nbits : Nat} (hw : 1 ≤ w) (start : w * (J - 1) ≤ nbits)
    (short : nbits - w * (J - 1) < w) (hk : k < 2 ^ nbits) :
    bcar w k (J - 1 + 1) = 0 := by
  unfold bcar
  simp only [Nat.add_one_ne_zero, ↓reduceIte]
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) (by
    rw [Nat.mul_add, Nat.mul_one]; omega)))]

/-- The top bit of window `j`, `c_{j+1}`, is bit `w j + w - 1`. -/
theorem bcar_succ_bit {w : Nat} (hw : 1 ≤ w) (k j : Nat) :
    bcar w k (j + 1) = (k.testBit (w * j + (w - 1))).toNat := by
  unfold bcar
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.testBit_eq_decide_div_mod_eq]
  rw [show w * (j + 1) - 1 = w * j + (w - 1) by rw [Nat.mul_add, Nat.mul_one]; omega_using [hw]]
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ (w * j + (w - 1))) with h | h <;> simp [h]

/-- The bit below window `j ≥ 1`, `c_j`, is bit `w j - 1`. -/
theorem bcar_bit {w : Nat} (k : Nat) {j : Nat} (hj : j ≠ 0) :
    bcar w k j = (k.testBit (w * j - 1)).toNat := by
  unfold bcar
  simp only [hj, ↓reduceIte, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ (w * j - 1)) with h | h <;> simp [h]

/-- Window `j`'s bits and top bit: `r9 = W_j`, `r7 = c_{j+1}`. -/
theorem bwindow_ok (K : TCombCfg) {s : State} {base : Addr} {j k : Nat}
    (hs : Ws s base 8192) (h4 : At s base .r4 (K.w * j)) (hw : 1 ≤ K.w ∧ K.w < 9) (hj : j < K.J)
    (start : K.w * (K.J - 1) ≤ K.L.nbits) (cover : K.L.nbits ≤ K.w * K.J) (short : K.topBits < K.w)
    (ho : K.L.bits + K.w < 2 ^ 15) (hl : K.L.bits + K.L.nbits ≤ 8192) (hk : k < 2 ^ K.L.nbits)
    (last : isa.eval TCombCfg.isLast s = some (decide (j = K.J - 1)))
    (hb : ∀ i < K.L.nbits, s.mem (off base (K.L.bits + i)) = if k.testBit i then 1 else 0) :
    WP isa (.ite TCombCfg.isLast (.block (K.horner K.topBits ++ ([.li .r7 0] : List Instr)))
        (.block (K.horner K.w ++ K.topBit))) s fun t =>
      t.gpr .r9 = BitVec.ofNat 64 (combWin K.w k j) ∧
        t.gpr .r7 = BitVec.ofNat 64 (bcar K.w k (j + 1)) ∧ Kp [.r5, .r7, .r9] s t ∧ t.mem = s.mem := by
  let count := if j = K.J - 1 then K.topBits else K.w
  have bounds := windowBits_bounds hj start cover
  change count ≤ K.w ∧ K.w * j + count ≤ K.L.nbits ∧ (count = K.w ∨ K.w * j + count = K.L.nbits) at bounds
  let v := fun i => (k.testBit (K.w * j + i)).toNat
  have hv : ∀ i, v i ≤ 1 := fun i => by dsimp only [v]; cases k.testBit (K.w * j + i) <;> decide
  have bytes : ∀ i < count, s.mem (off base (K.L.bits + K.w * j + i)) = BitVec.ofNat 8 (v i) := by
    intro i hi
    rw [show K.L.bits + K.w * j + i = K.L.bits + (K.w * j + i) by omega_using [], hb _ (by omega_using [bounds, hi])]
    dsimp only [v]
    cases k.testBit (K.w * j + i) <;> rfl
  have hh := hornerWindow_ok K (s := s) (j := j) (count := count) hs h4 bounds.1 hw.2 ho (by omega_using [hl, bounds]) hv bytes
  have win : hornerVal v 0 count = combWin K.w k j := window_without_padding bounds.1 bounds.2.2 hk
  by_cases e : j = K.J - 1
  · refine WP.ite true (by rw [last]; simp [e]) (fun _ => ?_) (fun hf => by cases hf)
    simp only [count, e, ↓reduceIte] at hh win
    refine wp_append (WP.mono hh fun s₁ ⟨v₁, k₁, m₁⟩ => ?_)
    refine wp_step (exec_li (by decide)) (WP.block_nil ?_)
    simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    refine ⟨by rw [v₁, win, e], ?_, (k₁.mono (by decide)).trans (Kp.write _ _ (by decide)), m₁⟩
    rw [e, bcar_last hw.1 start short hk]
  · refine WP.ite false (by rw [last]; simp [e]) (fun ht => by cases ht) (fun _ => ?_)
    simp only [count, e, ↓reduceIte] at hh win
    refine wp_append (WP.mono hh fun s₁ ⟨v₁, k₁, m₁⟩ => ?_)
    have top : K.w * j + (K.w - 1) < K.L.nbits := by
      have : K.w * j + K.w ≤ K.L.nbits := by simpa only [count, e, ↓reduceIte] using bounds.2.1
      omega_using [hw, this]
    unfold TCombCfg.topBit
    refine wp_step (lbz_ok (k₁.ws hs) (k₁.at h4) (by decide) (d := K.L.bits + K.w - 1) (by omega_using [hl, top]))
      (WP.block_nil ?_)
    simp only [write_gpr, write_mem, ite_true, reduceCtorEq, ite_false]
    refine ⟨by rw [v₁, win], ?_, (k₁.mono (by decide)).trans (Kp.write _ _ (by decide)), m₁⟩
    rw [m₁, show K.w * j + (K.L.bits + K.w - 1) = K.L.bits + (K.w * j + (K.w - 1)) by omega_using [hw],
      hb _ top, bcar_succ_bit hw.1]
    cases k.testBit (K.w * j + (K.w - 1)) <;> rfl

/-- Booth's digit of window `j = r31`: `r9 = |d_j|`. -/
theorem bdigit_ok (K : TCombCfg) {s : State} {base : Addr} {j k : Nat} (carry : Bool)
    (hs : Ws s base 8192) (h3 : At s base .r3 0) (hw : 1 ≤ K.w ∧ K.w < 9) (hj : j < K.J)
    (hJ : K.J ≤ 2 ^ 15) (start : K.w * (K.J - 1) ≤ K.L.nbits) (cover : K.L.nbits ≤ K.w * K.J)
    (short : K.topBits < K.w) (ho : K.L.bits + K.w < 2 ^ 15) (hb1 : 1 ≤ K.L.bits)
    (hl : K.L.bits + K.L.nbits ≤ 8192) (hk : k < 2 ^ K.L.nbits) (hc : carry = decide (j ≠ 0))
    (gj : s.gpr .r31 = BitVec.ofNat 64 j)
    (hb : ∀ i < K.L.nbits, s.mem (off base (K.L.bits + i)) = if k.testBit i then 1 else 0) :
    WP isa (K.bdigit carry) s fun t =>
      t.gpr .r9 = BitVec.ofNat 64 (bmag K.w k j) ∧ Kp [.r4, .r5, .r6, .r7, .r9] s t ∧ t.mem = s.mem := by
  unfold TCombCfg.bdigit
  rw [WP.seq_iff]
  refine WP.mono (windowIndex_ok K h3 (by omega_using [hw]) gj) fun s₁ ⟨p₁, k₁, m₁⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (lastTest_ok K (j := j) (by omega_using [hj, hJ]) (by omega_using [hJ]) (by rw [k₁.g]; exact gj))
    fun s₂ ⟨z₂, k₂, m₂⟩ => ?_
  have k₁₂ : Kp [.r4, .r6] s s₂ := (k₁.mono (by decide)).trans (k₂.mono (by decide))
  rw [WP.seq_iff]
  refine WP.mono (bwindow_ok K (k₁₂.ws hs) (by rw [At, k₂.g]; exact p₁) hw hj start cover short ho hl hk z₂
    (by intro i hi; rw [m₂, m₁]; exact hb i hi)) fun s₃ ⟨v₃, c₃, k₃, m₃⟩ => ?_
  have hW := Nat.mod_lt (k / 2 ^ (K.w * j)) (Nat.two_pow_pos K.w)
  have hs1 := bcar_le K.w k (j + 1)
  have h2w : 2 ^ K.w ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega_using [hw])
  have h4 : At s₃ base .r4 (K.w * j) := by rw [At, k₃.g, k₂.g]; exact p₁
  have key : ∀ (u : State) (c : Nat), c ≤ 1 → u.gpr .r9 = BitVec.ofNat 64 (combWin K.w k j + c) →
      u.gpr .r7 = BitVec.ofNat 64 (bcar K.w k (j + 1)) → bcar K.w k j = c →
      WP isa (.block [.li .r5 0, .sub .r5 .r5 .r7, .li .r6 (2 ^ K.w), .logic .and .r6 .r6 .r5,
        .sub .r9 .r9 .r6, .logic .xor .r9 .r9 .r5, .sub .r9 .r9 .r5]) u fun t =>
          t.gpr .r9 = BitVec.ofNat 64 (bmag K.w k j) ∧ Kp [.r5, .r6, .r9] u t ∧ t.mem = u.mem := by
    intro u c hc1 g9 g7 hcar
    refine wp_step (exec_li (by decide)) ?_
    refine wp_step exec_sub ?_
    refine wp_step (exec_li (by omega_using [h2w])) ?_
    refine wp_step exec_logic ?_
    refine wp_step exec_sub ?_
    refine wp_step exec_logic ?_
    refine wp_step exec_sub (WP.block_nil ?_)
    refine ⟨?_, ?_, rfl⟩
    · simp only [write_gpr, ite_true, reduceCtorEq, ite_false, g9, g7]
      have hWc : combWin K.w k j < 2 ^ K.w := hW
      rw [bmagBV hw.2 (v := combWin K.w k j + c) (by omega_using [hc1, hWc]) hs1, bmag_eq hw.1, hcar]
    · exact (((((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans
        (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
        (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide)))
  have k₀₃ : Kp [.r4, .r5, .r6, .r7, .r9] s s₃ := (k₁₂.mono (by decide)).trans (k₃.mono (by decide))
  cases carry with
  | false =>
    have j0 : j = 0 := by simpa using hc
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    refine WP.mono (key s₃ 0 (by decide) (by rw [v₃, Nat.add_zero]) c₃ (by simp [bcar, j0]))
      fun t ⟨vt, kt, mt⟩ => ⟨vt, k₀₃.trans (kt.mono (by decide)), by rw [mt, m₃, m₂, m₁]⟩
  | true =>
    have j0 : j ≠ 0 := by simpa using hc
    simp only [↓reduceIte, List.cons_append, List.nil_append]
    have below : K.w * j - 1 < K.L.nbits := by
      have : K.w * j ≤ K.w * (K.J - 1) := Nat.mul_le_mul_left _ (by omega_using [hj])
      have : 1 ≤ K.w * j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega_using [hw]) j0)
      omega_arith
    refine wp_step (lbz_ok (k₃.ws (k₁₂.ws hs)) h4 (by decide) (d := K.L.bits - 1) (by omega_using [hb1, hl, below])) ?_
    refine wp_step exec_add ?_
    have hc1 := bcar_le K.w k j
    refine WP.mono (key _ (bcar K.w k j) hc1 ?_ (by simp only [write_gpr, reduceCtorEq, ite_false]; exact c₃) rfl)
      fun t ⟨vt, kt, mt⟩ => ⟨vt, ?_, ?_⟩
    · simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
      rw [v₃, m₃, m₂, m₁, show K.w * j + (K.L.bits - 1) = K.L.bits + (K.w * j - 1) by
        have : 1 ≤ K.w * j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega_using [hw]) j0)
        omega_using [hb1, this], hb _ below, bcar_bit k j0]
      have hWc : combWin K.w k j < 2 ^ K.w := hW
      cases k.testBit (K.w * j - 1) <;> (apply BitVec.eq_of_toNat_eq; simp <;> omega)
    · exact k₀₃.trans ((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans
        (kt.mono (by decide))))
    · rw [mt]; simp only [write_gpr, write_mem]; rw [m₃, m₂, m₁]

/-- The mask `r10` of window `j`'s digit being negative (its top bit, `c_{j+1}`). -/
theorem bsign_ok (K : TCombCfg) {s : State} {base : Addr} {j k : Nat}
    (hs : Ws s base 8192) (h3 : At s base .r3 0) (hw : 1 ≤ K.w ∧ K.w < 9) (hj : j < K.J)
    (hJ : K.J ≤ 2 ^ 15) (start : K.w * (K.J - 1) ≤ K.L.nbits) (cover : K.L.nbits ≤ K.w * K.J)
    (short : K.topBits < K.w) (hl : K.L.bits + K.L.nbits ≤ 8192) (hk : k < 2 ^ K.L.nbits)
    (gj : s.gpr .r31 = BitVec.ofNat 64 j)
    (hb : ∀ i < K.L.nbits, s.mem (off base (K.L.bits + i)) = if k.testBit i then 1 else 0) :
    WP isa K.bsign s fun t =>
      t.gpr .r10 = (if bcar K.w k (j + 1) = 0 then 0 else BitVec.allOnes 64) ∧
        Kp [.r4, .r6, .r10] s t ∧ t.mem = s.mem := by
  have bounds := windowBits_bounds hj start cover
  change (if j = K.J - 1 then K.topBits else K.w) ≤ K.w ∧
    K.w * j + (if j = K.J - 1 then K.topBits else K.w) ≤ K.L.nbits ∧
    ((if j = K.J - 1 then K.topBits else K.w) = K.w ∨
      K.w * j + (if j = K.J - 1 then K.topBits else K.w) = K.L.nbits) at bounds
  unfold TCombCfg.bsign
  rw [WP.seq_iff]
  refine WP.mono (lastTest_ok K (j := j) (by omega_using [hj, hJ]) (by omega_using [hJ]) gj) fun u ⟨zero, ku, mu⟩ => ?_
  by_cases last : j = K.J - 1
  · refine WP.ite true (by rw [zero]; simp [last]) (fun _ => ?_) (fun hf => by cases hf)
    refine wp_step (exec_li (by decide)) (WP.block_nil ?_)
    simp only [write_gpr, ite_true]
    rw [last, bcar_last hw.1 start short hk]
    exact ⟨rfl, (ku.mono (by decide)).trans (Kp.write _ _ (by decide)), mu⟩
  · refine WP.ite false (by rw [zero]; simp [last]) (fun ht => by cases ht) (fun _ => ?_)
    have top : K.w * j + (K.w - 1) < K.L.nbits := by
      have : K.w * j + K.w ≤ K.L.nbits := by simpa only [last, ↓reduceIte] using bounds.2.1
      omega_using [hw, this]
    refine wp_append (WP.mono (windowIndex_ok K (j := j) (ku.at h3) (by omega_using [hw]) (by rw [ku.g]; exact gj))
      fun s₁ ⟨p₁, k₁, m₁⟩ => ?_)
    refine wp_step (lbz_ok (k₁.ws (ku.ws hs)) p₁ (by decide) (d := K.L.bits + K.w - 1) (by omega_using [hl, top])) ?_
    refine wp_step (exec_li (by decide)) ?_
    refine wp_step exec_sub (WP.block_nil ?_)
    simp only [write_gpr, write_mem, ite_true, reduceCtorEq, ite_false]
    refine ⟨?_, (ku.mono (by decide)).trans ((k₁.mono (by decide)).trans (((Kp.write _ _ (by decide)).trans
      (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide)))), by rw [m₁, mu]⟩
    rw [m₁, mu, show K.w * j + (K.L.bits + K.w - 1) = K.L.bits + (K.w * j + (K.w - 1)) by omega_using [hw],
      hb _ top, bcar_succ_bit hw.1]
    cases k.testBit (K.w * j + (K.w - 1)) <;> rfl

/-- Booth's entry of window `j`: `|d_j|`'s entry of row `j` (`O` for `0`),
`y` negated where the window's top bit is set. -/
theorem boothEntry_rep {C : Curve} (hC : Law C) {w J j k R one : Nat}
    {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : CombOkW C w J tbl start) (unit : UnitMod C.p R) (hone : toM C.p R one = 1) (hj : j < J) (hw : 1 ≤ w)
    {x y z : Nat}
    (hx : x = (if bmag w k j = 0 then 0 else (combAt tbl j (bmag w k j - 1)).1 * R % C.p))
    (hy : y = (if bmag w k j = 0 then one else (combAt tbl j (bmag w k j - 1)).2 * R % C.p))
    (hz : z = (if bmag w k j = 0 then 0 else one)) (hlt : y < C.p) :
    Rep C (toM C.p R x) (toM C.p R (if bcar w k (j + 1) = 0 then y else (C.p - y) % C.p))
      (toM C.p R z) (bentry C w k j) := by
  have rep := combEntry_rep hC h unit hone hj (bmag_le hw k j)
  rw [← hx, ← hy, ← hz] at rep
  unfold bentry
  by_cases pos : bcar w k (j + 1) = 0
  · simp only [pos, ↓reduceIte, Nat.zero_ne_one]
    exact rep
  · have one : bcar w k (j + 1) = 1 := by have := bcar_le w k (j + 1); omega_using [pos, this]
    simp only [one, Nat.one_ne_zero, ↓reduceIte]
    have neg : toM C.p R ((C.p - y) % C.p) = -toM C.p R y := by
      have sub := toM_sub (m := C.p) (R := R) (A := 0) (B := y) (by omega_using [hlt])
      simp only [Nat.zero_add, toM_zero] at sub
      grind
    rw [neg]
    exact Rep.negY rep

/-- Booth's entry of window `j`, signed, in the point functions' `Q`. -/
theorem bentry_ok (K : TCombCfg) (carry : Bool) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : Config K C tbl start) (hC : Law C) {s : State} {base T : Addr} {k j : Nat}
    (i : CurveInputs K C tbl base T k s) (hj : j < K.J) (hk : k < 2 ^ K.L.nbits)
    (gj : s.gpr .r31 = BitVec.ofNat 64 j) (short : K.topBits < K.w) (hb1 : 1 ≤ K.L.bits)
    (hc : carry = decide (j ≠ 0))
    (hd : Region.Disjoint ⟨T, 8 * (tableWords K C tbl).length⟩ ⟨base, 8192⟩) :
    WP isa (K.bentry carry) s fun t =>
      Rk fnClob s t ∧ Unch base (loopWrites K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal t.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n) ∧
      (∀ x ∈ [K.Q.x, K.Q.y, K.Q.z], wordsVal t.mem base x K.L.M.n < C.p) ∧
      Rep C (tmv C K.L.M.n base t K.Q.x) (tmv C K.L.M.n base t K.Q.y) (tmv C K.L.M.n base t K.Q.z)
        (bentry C K.w k j) ∧
      wordsVal t.mem base K.Q.z K.L.M.n = (if bmag K.w k j = 0 then 0 else K.one) := by
  unfold TCombCfg.bentry
  have hp : 0 < C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  have hfit : C.p ≤ 2 ^ (64 * K.L.M.n) := Nat.le_of_lt h.modulus.m_lt
  have hl := lay_nums h.layout.point.k3 h.layout.point.k6
  obtain ⟨hqx, hqy, hqz, hqa, hown, hown', -, -, hq4⟩ := q_lay h.layout
  have lo := h.layout.low
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at lo
  obtain ⟨rx, ry, rz, zlo, nlo⟩ := lo
  have hbits := h.layout.point.bitsE
  have hb4 := h.layout.point.bits
  have nowrap := i.wsr.nowrap
  have hH15 : K.H + 1 ≤ 2 ^ 15 := by
    have := h.row
    have := Nat.le_mul_of_pos_left K.H (show 0 < 16 * K.L.M.n by have := h.layout.point.k3; omega_using [this])
    omega_arith
  refine WP.seq (WP.mono_syms (bdigit_ok K carry i.wsr.ws i.wsr.at3 ⟨h.w1, h.w9⟩ hj (Nat.le_of_lt h.J15) h.startBits
    h.coverBits short h.bitsOff hb1 hbits hk hc gj i.bits) fun u ⟨gu, ku, mu⟩ syu => ?_)
  have iu : CurveInputs K C tbl base T k u :=
    i.keep h.layout hd (ku.rk (rs' := fnClob)) (by decide) (by rw [mu]; exact Unch.refl _ _ _) syu
  refine WP.seq (WP.mono_syms (selectTable_ok K (a := bmag K.w k j) iu.wsr hq4 h.layout.al.1
    (by omega_using [hl, hqx]) (by omega_using [hl, zlo]) (.inl (by omega_using [hqx, zlo])) (Nat.lt_of_lt_of_le h.one_lt hfit) iu.zero
    (by have := h.layout.point.k3; omega_using [this]) (by have := h.layout.point.k6; omega_using [hl]) hH15 h.row (bmag_le h.w1 k j) gu
    (by rw [ku.g]; exact gj) iu.table iu.symbol h.tables.len h.tables.lenH hj (by have := h.J15; omega_using [this]) hp hfit hd)
    fun v ⟨xv, yv, zv, kv, ov⟩ syv => ?_)
  have ouv : Unch base (loopWrites K) u.mem v.mem :=
    ov.unch.cover fun w hw' => by
      rw [List.mem_singleton] at hw'; subst hw'
      exact ⟨(oAt K.L.M.n, 72 * K.L.M.n), by simp [loopWrites], by dsimp only; omega_using [hqx], by dsimp only; omega_using [hqx]⟩
  have iv : CurveInputs K C tbl base T k v := iu.keep h.layout hd kv (by decide) ouv syv
  have ylt : wordsVal v.mem base K.Q.y K.L.M.n < C.p := by
    rw [yv]; split
    · exact h.one_lt
    · exact Nat.mod_lt _ hp
  have oldR : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z],
      wordsVal v.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n := by
    intro x hx
    have lowx : x + 8 * K.L.M.n ≤ oAt K.L.M.n := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> with_reducible assumption
    rw [ov.wordsVal (.inl (by omega_using [hqx, lowx])) (by omega_using [hl, lowx]), mu]
  have mask : ∀ a, Rk fnClob v a → Unch base [(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] v.mem a.mem →
      WP isa K.bsign a fun b =>
        b.gpr .r10 = (if bcar K.w k (j + 1) = 0 then 0 else BitVec.allOnes 64) ∧ Kp [.r4, .r6, .r10] a b ∧
          b.mem = a.mem := by
    intro a ka ma
    have wa := iv.wsr.of_rk ka
    refine WP.mono (bsign_ok K wa.ws wa.at3 ⟨h.w1, h.w9⟩ hj (Nat.le_of_lt h.J15) h.startBits h.coverBits short hbits hk
      (by rw [ka.g, kv.g, ku.g]; exact gj) fun b hb => ?_) fun t ⟨v', k', m'⟩ => ⟨v', k', m'⟩
    rw [ma.byte (fun w hw' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
        rcases hw' with rfl | rfl <;> (right; dsimp only; omega_using [hb1, hl, hqx, hqa, hown, hown', rx, ry, rz, zlo, nlo, hbits, hb4, hb])) (by omega_using [hbits, hb]), iv.bits b hb]
  refine WP.mono (negate_ok K (bcar K.w k (j + 1) = 0) h.layout iv.wsr h.fieldM h.fieldK h.modulus iv.zero ylt mask)
    fun t ⟨kt, ot, rt, xt, yt, zt⟩ => ?_
  refine ⟨((ku.rk (rs' := fnClob)).trans ((kv.mono (by decide)).trans kt)), ?_,
    fun x hx => (rt x hx).trans (oldR x hx), ?_, ?_⟩
  · have ou : Unch base (loopWrites K) s.mem u.mem := by rw [mu]; exact Unch.refl _ _ _
    exact (ou.trans (ouv.trans ot)).cover fun w hw' => ⟨w, by
      simpa only [List.mem_append, or_self] using hw', Nat.le_refl _, Nat.le_refl _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [xt, yt, zt, xv, zv]
    refine ⟨?_, ?_, ?_⟩
    · split
      · exact hp
      · exact Nat.mod_lt _ hp
    · split
      · exact ylt
      · exact Nat.mod_lt _ hp
    · split
      · exact hp
      · exact h.one_lt
  · refine ⟨?_, by rw [zt, zv]⟩
    show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [xt, yt, zt]
    exact boothEntry_rep hC h.tables h.unit h.one hj h.w1 xv yv zv ylt


/-! ## The mixed addition, as a call -/

/-- The mixed addition's field operations, on the point functions' slots. -/
abbrev maddOps : List FOp := maddJ sId pId qId oId

theorem maddOps_opsOk : OpsOk maddOps := ⟨by decide, by decide, by decide⟩

theorem maddOps_run {m : Nat} [NeZero m] (E : Nat → Fin m) :
    (runOps maddOps E 0, runOps maddOps E 1, runOps maddOps E 2) = maddJF (E 3) (E 4) (E 5) (E 6) (E 7) :=
  rfl

/-- A call of `vg_<curve>_point_madd`, from the working space at `r3`: only
`fnClob`, `O` and the own working space change, and `O` holds `maddJF` of
`P` (Jacobian) and `Q`'s `x` and `y`. -/
theorem maddCallF_ok (F : Impl.Weierstrass.Mont.Modulus) (name : String) [NeZero F.m] (hM : ModOk F.k F.m)
    (hodd : F.m % 2 = 1) (hk3 : 3 ≤ F.k) (hk6 : F.k ≤ 6) {s : State} {base : Addr} (hw : WsReg s base)
    (hlt : ∀ x ∈ rIds, wordsVal s.mem base (enc F.k false x) F.k < F.m) :
    WP isa (.call name (fnOps F false maddOps)) s fun s' => Rk fnClob s s' ∧
      Outs base [(Impl.Weierstrass.Point.oAt F.k, 3 * Impl.Weierstrass.Point.elemBytes F.k),
        (Impl.Weierstrass.Point.ownAt F.k, 4096 - Impl.Weierstrass.Point.ownAt F.k)] s.mem s'.mem ∧
      (∀ j < 3, wordsVal s'.mem base (enc F.k false j) F.k < F.m) ∧
      (Eb F.k F.m false s'.mem base 0, Eb F.k F.m false s'.mem base 1,
        Eb F.k F.m false s'.mem base 2) =
        maddJF (Eb F.k F.m false s.mem base 3) (Eb F.k F.m false s.mem base 4)
          (Eb F.k F.m false s.mem base 5) (Eb F.k F.m false s.mem base 6)
          (Eb F.k F.m false s.mem base 7) := by
  have hcov : Covers [⟨base, 8192⟩] s.wr := Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hw.wr
  have g3 : ∀ t : State, (t.callEntry.withRegions [] [⟨base, 8192⟩]).gpr .r3 = t.gpr .r3 := fun t => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide)]
  refine WP.call (k := ⟨fun t => PrePt F.k F.m false t ∧ t.gpr .r3 = base ∧ t.mem = s.mem,
      fun t t' => (∀ r, r ∉ fnClob → t'.gpr r = t.gpr r) ∧
        Outs (t.gpr .r3) [(Impl.Weierstrass.Point.oAt F.k, 3 * Impl.Weierstrass.Point.elemBytes F.k),
          (Impl.Weierstrass.Point.ownAt F.k, 4096 - Impl.Weierstrass.Point.ownAt F.k)] t.mem t'.mem ∧
        (∀ j < 3, wordsVal t'.mem (t.gpr .r3) (enc F.k false j) F.k < F.m) ∧
        (toM F.m (2 ^ (64 * F.k)) (wordsVal t'.mem (t.gpr .r3) (enc F.k false 0) F.k),
          toM F.m (2 ^ (64 * F.k)) (wordsVal t'.mem (t.gpr .r3) (enc F.k false 1) F.k),
          toM F.m (2 ^ (64 * F.k)) (wordsVal t'.mem (t.gpr .r3) (enc F.k false 2) F.k)) =
        maddJF (Eb F.k F.m false t.mem (t.gpr .r3) 3) (Eb F.k F.m false t.mem (t.gpr .r3) 4)
          (Eb F.k F.m false t.mem (t.gpr .r3) 5) (Eb F.k F.m false t.mem (t.gpr .r3) 6)
          (Eb F.k F.m false t.mem (t.gpr .r3) 7),
      fun _ _ => True⟩)
    (fun t ⟨hp, _, _⟩ => by
      obtain ⟨tr, t', he, A, G, O, L, E⟩ := fnOps_ok hM hodd maddOps_opsOk hp
      exact ⟨tr, t', he, A, G, O, L, E.trans (maddOps_run _)⟩)
    (rd := []) (wr := [⟨base, 8192⟩])
    ⟨⟨by rw [State.withRegions_wr, g3, hw.r3], by rw [g3, hw.r3]; exact hw.nowrap, hk3, hk6,
        fun x hx => by
          rw [g3, hw.r3, State.withRegions_mem, State.callEntry_mem]
          exact hlt x hx⟩,
      by rw [g3, hw.r3],
      by rw [State.withRegions_mem, State.callEntry_mem]⟩
    (Covers.right hcov) hcov ?_ rfl
  intro s' r' w' p' _ _ _ ⟨G, O, L, E⟩
  simp only [State.withRegions_mem, State.callEntry_mem, g3, hw.r3, State.withRegions_gpr] at G O L E
  refine ⟨⟨fun r hr => ?_, r', w', p'⟩, O, L, E⟩
  have hl : r ∉ linkRegs := not_mem_sub hr
  rw [G r hr, State.callEntry_gpr _ hl]

/-- `maddCallF_ok` for the comb's call, of `n`-word numbers modulo `m`. -/
theorem maddCall_ok (K : TCombCfg) {n m : Nat} [NeZero m] (hk : K.F.k = n) (hm : K.F.m = m) (hM : ModOk n m)
    (hodd : m % 2 = 1) (hk3 : 3 ≤ n) (hk6 : n ≤ 6) {s : State} {base : Addr} (hw : WsReg s base)
    (hlt : ∀ x ∈ rIds, wordsVal s.mem base (enc n false x) n < m) :
    WP isa K.maddCall s fun s' => Rk fnClob s s' ∧
      Outs base [(Impl.Weierstrass.Point.oAt n, 3 * Impl.Weierstrass.Point.elemBytes n),
        (Impl.Weierstrass.Point.ownAt n, 4096 - Impl.Weierstrass.Point.ownAt n)] s.mem s'.mem ∧
      (∀ j < 3, wordsVal s'.mem base (enc n false j) n < m) ∧
      (Eb n m false s'.mem base 0, Eb n m false s'.mem base 1, Eb n m false s'.mem base 2) =
        maddJF (Eb n m false s.mem base 3) (Eb n m false s.mem base 4) (Eb n m false s.mem base 5)
          (Eb n m false s.mem base 6) (Eb n m false s.mem base 7) := by
  unfold TCombCfg.maddCall
  generalize K.maddName = name
  generalize K.F = F at hk hm
  obtain ⟨c, w, m', k', d⟩ := F
  dsimp only at hk hm
  subst hk hm
  exact maddCallF_ok _ name hM hodd hk3 hk6 hw hlt

/-! ## A window's arithmetic -/

/-- `[Σ_{i≤j} d_i 2^(wi)]G` from the sum below `j` and the entry `j`. -/
theorem bpart_succ_pt {C : Curve} (hC : Law C) (hG : onCurve C (G C) = true) {w : Nat} (hw : 1 ≤ w)
    (k j : Nat) :
    zmul (bpart w k (j + 1)) (G C) = Spec.Weierstrass.add (zmul (bpart w k j) (G C)) (bentry C w k j) := by
  rw [bentry_eq hw, hC.add_zmul hG, bpart_succ]

/-- A window: from `R` (Jacobian) for the sum below `j` and the entry `E`
(`Z = 1`, or `O` for a zero digit), `D = R + E` by `maddJF`, `D = E` if
`R = O`, and `R = D` unless the digit is zero, for the sum to `j`. -/
theorem bstep_math {C : Curve} (hC : Law C) (hG : onCurve C (G C) = true) (hM3 : AM3 C)
    {w J kmax k j : Nat} (hB : BoothOk C w J kmax) (hw : 1 ≤ w) (hk : k < kmax) (hj1 : 1 ≤ j) (hj : j < J)
    {X Y Z ex ey ez : Fe C} (hR : InvJ C X Y Z (zmul (bpart w k j) (G C)))
    (hE : Rep C ex ey ez (bentry C w k j)) (hez : ez = if bmag w k j = 0 then 0 else 1) :
    InvJ C
      (if bmag w k j = 0 then X else if Z = 0 then ex else (maddJF X Y Z ex ey).1)
      (if bmag w k j = 0 then Y else if Z = 0 then ey else (maddJF X Y Z ex ey).2.1)
      (if bmag w k j = 0 then Z else if Z = 0 then ez else (maddJF X Y Z ex ey).2.2)
      (zmul (bpart w k (j + 1)) (G C)) := by
  rw [bpart_succ_pt hC hG hw]
  by_cases h0 : bmag w k j = 0
  · simp only [h0, ↓reduceIte]
    have hQ : bentry C w k j = .infinity := by
      unfold bentry
      rw [h0, show combPtW C w j 0 = .infinity by simp [combPtW, Spec.Weierstrass.mul]]
      split <;> rfl
    rw [hQ, add_infinity]
    exact hR
  · simp only [h0, ↓reduceIte] at hez ⊢
    have hQa := Rep.eq_affine hC (hez ▸ hE)
    by_cases hz0 : Z = 0
    · simp only [hz0, ↓reduceIte]
      have hP : zmul (bpart w k j) (G C) = .infinity := by
        rw [hz0] at hR; exact InvJ.eq_infinity hR
      rw [hP, infinity_add']
      exact InvJ.of_rep01 hE (Or.inl hez)
    · simp only [hz0, ↓reduceIte]
      have hon : onCurve C (bentry C w k j) = true := by
        rw [bentry_eq hw]; exact hC.onCurve_zmul hG _
      have hne : zmul (bpart w k j) (G C) ≠ bentry C w k j := by
        rw [bentry_eq hw]
        exact booth_ne hC hG hB.n hB.n0 hB.cop hB.safe hw hB.J2 hB.kmax hk hj1 hj h0
      rw [hQa] at hon hne ⊢
      exact InvJ.madd hC hM3 (hC.onCurve_zmul hG _) hon hR hz0 hne

/-! ## The masks -/

/-- `subfc` from zero, then `subfe` of a register from itself: all ones
exactly for a nonzero `v`. -/
theorem nz_val {y : Nat} (hy : y < 2 ^ 64) (v : BitVec 64) :
    BitVec.ofNat 64 (y + (2 ^ 64 - 1 - y) + (decide (2 ^ 64 ≤ 0 + (2 ^ 64 - 1 - v.toNat) + 1)).toNat) =
      if v = 0 then 0 else BitVec.allOnes 64 := by
  have hv := v.isLt
  by_cases hz : v = 0
  · subst hz
    simp only [↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [h0, decide_eq_true (by omega_using [] : 2 ^ 64 ≤ 0 + (2 ^ 64 - 1 - 0) + 1)]
    simp only [Bool.toNat_true]
    omega_using [hy]
  · have hx : v.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq (by simpa using h))
    rw [decide_eq_false (by omega_using [hx] : ¬ 2 ^ 64 ≤ 0 + (2 ^ 64 - 1 - v.toNat) + 1)]
    simp only [hz, ↓reduceIte, Bool.toNat_false]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_allOnes]
    omega_using [hy]

/-- `r10` all ones exactly when `r` is nonzero. -/
theorem nzOf_ok {s : State} {r : Reg} (h5 : r ≠ .r5) :
    WP isa (.block (TCombCfg.nzOf r)) s fun t =>
      t.gpr .r10 = (if s.gpr r = 0 then 0 else BitVec.allOnes 64) ∧ Kp [.r5, .r10] s t ∧ t.mem = s.mem := by
  unfold TCombCfg.nzOf
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_subc ?_
  refine wp_step exec_sube (WP.block_nil ?_)
  refine ⟨?_, ?_, rfl⟩
  · simp only [write_gpr, RegUpd.gpr_writeCarry, RegUpd.ca_writeCarry, ite_true, ite_false, h5]
    rw [show (0#64).toNat = 0 from rfl]
    exact nz_val (s.gpr .r10).isLt (s.gpr r)
  · exact ((Kp.write _ _ (by decide)).trans (Kp.writeCarry _ _ (by decide))).trans (Kp.writeCarry _ _ (by decide))

/-- The OR of words `1 … k` of `[z]` into `r4`, through `r5`: `r4` stays zero
exactly when it was and those words are. -/
theorem orWords_ok {s : State} {base : Addr} (hs : Ws s base 8192) (h3 : At s base .r3 0) {z : Nat}
    (hz4 : z % 4 = 0) : ∀ (k : Nat), z + 8 * (k + 1) ≤ 8192 →
    WP isa (.block ((List.range k).flatMap (fun i =>
      [.load .d .r5 wb (z + 8 * (i + 1)), .logic .or .r4 .r4 .r5]))) s fun t =>
      (t.gpr .r4 = 0 ↔ s.gpr .r4 = 0 ∧ ∀ i < k, word s.mem base (z + 8 * (i + 1)) = 0) ∧
        Kp [.r4, .r5] s t ∧ t.mem = s.mem
  | 0, _ => WP.block_nil ⟨by simp, Kp.refl _ _, rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (orWords_ok hs h3 hz4 k (by omega_using [hk])) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine wp_step (ld0_ok (k₁.ws hs) (k₁.at h3) (by decide) (by omega_using [hz4]) (by omega_using [hk])) ?_
    refine wp_step exec_logic (WP.block_nil ?_)
    refine ⟨?_, (k₁.trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide)), m₁⟩
    have ev : ∀ x y : BitVec 64, (x ||| y = 0) = (x = 0 ∧ y = 0) := fun _ _ => propext BitVec.or_eq_zero_iff
    simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    rw [ev, e₁, m₁]
    constructor
    · rintro ⟨⟨h0, hi⟩, hl⟩
      exact ⟨h0, fun i hi' => if e : i < k then hi i e else by rw [show i = k by omega_using [hi', e]]; exact hl⟩
    · rintro ⟨h0, hi⟩
      exact ⟨⟨h0, fun i hi' => hi i (by omega_using [hi'])⟩, hi k (by omega_using [])⟩

/-- `r10` is the mask of `R`'s `Z` being nonzero. -/
theorem zMask_ok (K : TCombCfg) {s : State} {base : Addr} (hs : Ws s base 8192) (h3 : At s base .r3 0)
    (hn : 1 ≤ K.L.M.n) (hz4 : K.L.R.z % 4 = 0) (hz : K.L.R.z + 8 * K.L.M.n ≤ 8192) :
    WP isa (.block K.zMask) s fun t =>
      t.gpr .r10 = (if wordsVal s.mem base K.L.R.z K.L.M.n = 0 then 0 else BitVec.allOnes 64) ∧
        Kp [.r4, .r5, .r10] s t ∧ t.mem = s.mem := by
  unfold TCombCfg.zMask
  rw [List.append_assoc, List.singleton_append]
  refine wp_step (ld0_ok hs h3 (by decide) hz4 (by omega_using [hn, hz])) ?_
  rw [WP.block_append_iff]
  refine WP.mono (orWords_ok (hs.write _ _) (h3.write _) hz4 (K.L.M.n - 1) (by omega_using [hn, hz]))
    fun s₁ ⟨e₁, k₁, m₁⟩ => ?_
  refine WP.mono (nzOf_ok (r := .r4) (by decide)) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_
  refine ⟨?_, ((Kp.write _ _ (by decide)).trans k₁ |>.mono (by decide)).trans (k₂.mono (by decide)),
    by rw [m₂, m₁]; rfl⟩
  rw [e₂]
  have iff : s₁.gpr .r4 = 0 ↔ wordsVal s.mem base K.L.R.z K.L.M.n = 0 := by
    simp only [write_gpr, ite_true, write_mem] at e₁
    rw [e₁]
    constructor
    · rintro ⟨h0, hi⟩
      refine wordsVal_zero_words fun i hi' => ?_
      cases i with
      | zero => simpa using h0
      | succ i => exact hi i (by omega_using [hi'])
    · intro h
      have := words_zero_of_wordsVal h
      exact ⟨by simpa using this 0 (by omega_using [hn]), fun i hi => this (i + 1) (by omega_using [hi])⟩
  by_cases e : wordsVal s.mem base K.L.R.z K.L.M.n = 0
  · simp only [iff.mpr e, e, ↓reduceIte]
  · simp only [mt iff.mp e, e, ↓reduceIte]

/-! ## The selections of a window -/

/-- `selPt_ok` (`Proof/Weierstrass/PPC64LE/Copy.lean`) for `o` that may be
`a` or `b`: each coordinate of `o` at or below the same coordinate of `a`
and `b`, or apart from it, and apart from their later ones. -/
theorem selPt_ok' {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    (c : Bool) (hc : s.gpr .r10 = (if c then BitVec.allOnes 64 else 0)) {n : Nat} {o a b : Pt}
    (h4 : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z, b.x, b.y, b.z], d % 4 = 0)
    (hin : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z, b.x, b.y, b.z], d + 8 * n ≤ size)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (same : (o.x ≤ a.x ∨ a.x + 8 * n ≤ o.x) ∧ (o.x ≤ b.x ∨ b.x + 8 * n ≤ o.x) ∧
      (o.y ≤ a.y ∨ a.y + 8 * n ≤ o.y) ∧ (o.y ≤ b.y ∨ b.y + 8 * n ≤ o.y) ∧
      (o.z ≤ a.z ∨ a.z + 8 * n ≤ o.z) ∧ (o.z ≤ b.z ∨ b.z + 8 * n ≤ o.z))
    (later : (∀ e ∈ [a.y, a.z, b.y, b.z], o.x + 8 * n ≤ e ∨ e + 8 * n ≤ o.x) ∧
      (∀ e ∈ [a.z, b.z], o.y + 8 * n ≤ e ∨ e + 8 * n ≤ o.y)) :
    WP isa (.block (selPt n o a b)) s fun s' =>
      wordsVal s'.mem base o.x n = (if c then wordsVal s.mem base b.x n else wordsVal s.mem base a.x n) ∧
      wordsVal s'.mem base o.y n = (if c then wordsVal s.mem base b.y n else wordsVal s.mem base a.y n) ∧
      wordsVal s'.mem base o.z n = (if c then wordsVal s.mem base b.z n else wordsVal s.mem base a.z n) ∧
      Kp [.r4, .r5] s s' ∧
      Outs base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem s'.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin h4 later
  obtain ⟨iox, ioy, ioz, iax, iay, iaz, ibx, iby, ibz⟩ := hin
  obtain ⟨⟨xay, xaz, xby, xbz⟩, ⟨yaz, ybz⟩⟩ := later
  obtain ⟨xax, xbx, yay, yby, zaz, zbz⟩ := same
  obtain ⟨xy, xz, yz⟩ := hoo
  obtain ⟨fox, foy, foz, fax, fay, faz, fbx, fby, fbz⟩ := h4
  rw [selPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sel_ok c n hs h3 hc fox fax fbx (by omega_using [iox]) (by omega_using [iax])
    (by omega_using [ibx]) xax xbx) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok c n (k₁.ws hs) (k₁.at h3) (by rw [k₁.g, hc]) foy fay fby (by omega_using [ioy])
    (by omega_using [iay]) (by omega_using [iby]) yay yby) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  refine WP.mono (sel_ok c n (k₂.ws (k₁.ws hs)) (k₂.at (k₁.at h3)) (by rw [k₂.g, k₁.g, hc]) foz faz fbz
    (by omega_using [ioz]) (by omega_using [iaz]) (by omega_using [ibz]) zaz zbz) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · rw [O₃.wordsVal (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.wordsVal (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.wordsVal (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.wordsVal (d := b.y) (by omega_using [xby]) (by omega_using [iby, hn]),
      O₁.wordsVal (d := a.y) (by omega_using [xay]) (by omega_using [iay, hn])]
  · rw [e₃, O₂.wordsVal (d := b.z) (by omega_using [ybz]) (by omega_using [ibz, hn]),
      O₂.wordsVal (d := a.z) (by omega_using [yaz]) (by omega_using [iaz, hn]),
      O₁.wordsVal (d := b.z) (by omega_using [xbz]) (by omega_using [ibz, hn]),
      O₁.wordsVal (d := a.z) (by omega_using [xaz]) (by omega_using [iaz, hn])]
  · exact ((Outs.of_outside O₁ (by simp)).trans (Outs.of_outside O₂ (by simp))).trans
      (Outs.of_outside O₃ (by simp))

/-- The mask of `x ≠ 0`, as a `Bool`. -/
theorem nzMask_eq (x : Nat) :
    (if x = 0 then (0 : BitVec 64) else BitVec.allOnes 64) =
      if decide (x ≠ 0) then BitVec.allOnes 64 else 0 := by
  by_cases e : x = 0 <;> simp [e]

/-- `O = Q` if `R` is `O` (its `Z` zero). -/
theorem zsel_ok (K : TCombCfg) (h : Layout K) {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (K.zMask ++ selPt K.L.M.n K.O K.Q K.O)) s fun t =>
      wordsVal t.mem base K.O.x K.L.M.n = (if wordsVal s.mem base K.L.R.z K.L.M.n = 0
        then wordsVal s.mem base K.Q.x K.L.M.n else wordsVal s.mem base K.O.x K.L.M.n) ∧
      wordsVal t.mem base K.O.y K.L.M.n = (if wordsVal s.mem base K.L.R.z K.L.M.n = 0
        then wordsVal s.mem base K.Q.y K.L.M.n else wordsVal s.mem base K.O.y K.L.M.n) ∧
      wordsVal t.mem base K.O.z K.L.M.n = (if wordsVal s.mem base K.L.R.z K.L.M.n = 0
        then wordsVal s.mem base K.Q.z K.L.M.n else wordsVal s.mem base K.O.z K.L.M.n) ∧
      Kp [.r4, .r5, .r10] s t ∧
      Outs base [(K.O.x, 8 * K.L.M.n), (K.O.y, 8 * K.L.M.n), (K.O.z, 8 * K.L.M.n)] s.mem t.mem := by
  obtain ⟨hqx, hqy, hqz, hqa, -, -, -, -, hq4⟩ := q_lay h
  have := lay_nums h.point.k3 h.point.k6
  have hk3 := h.point.k3
  have rz := h.point.rz
  have rzl := h.point.al.2.2.2.2.2.2.2
  rw [WP.block_append_iff]
  refine WP.mono (zMask_ok K hw.ws hw.at3 (by omega_using [hk3]) rzl (by omega_using [this, rz])) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_
  rw [nzMask_eq] at e₁
  refine WP.mono (selPt_ok' (k₁.ws hw.ws) (k₁.at hw.at3) _ e₁ (n := K.L.M.n) (o := K.O) (a := K.Q) (b := K.O)
    (by simp only [O_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [hqx, hqy, hqz, this])
    (by simp only [O_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [hqx, hqy, hqz, this])
    (by simp only [O_eq]; omega_using [this]) (by simp only [O_eq]; omega_using [hqx, hqy, hqz, this])
    (by simp only [O_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [hqx, hqy, hqz, this]))
    fun t ⟨x, y, z, kt, ot⟩ => ?_
  rw [m₁] at x y z ot
  refine ⟨?_, ?_, ?_, (k₁.mono (by decide)).trans (kt.mono (by decide)), ot⟩ <;>
  · by_cases e : wordsVal s.mem base K.L.R.z K.L.M.n = 0 <;> simp_all

/-- `R = O` unless `r9` is zero, and `r6 = r31 - (J - 1)`. -/
theorem rsel_ok (K : TCombCfg) (h : Layout K) {s : State} {base : Addr} (hw : WsReg s base) {j : Nat}
    (hj : j < 2 ^ 64) (hJ : K.J - 1 ≤ 2 ^ 15) (gj : s.gpr .r31 = BitVec.ofNat 64 j) :
    WP isa (.block (TCombCfg.nzOf .r9 ++ selPt K.L.M.n K.L.R K.L.R K.O ++ K.lastTest)) s fun t =>
      wordsVal t.mem base K.L.R.x K.L.M.n = (if s.gpr .r9 = 0
        then wordsVal s.mem base K.L.R.x K.L.M.n else wordsVal s.mem base K.O.x K.L.M.n) ∧
      wordsVal t.mem base K.L.R.y K.L.M.n = (if s.gpr .r9 = 0
        then wordsVal s.mem base K.L.R.y K.L.M.n else wordsVal s.mem base K.O.y K.L.M.n) ∧
      wordsVal t.mem base K.L.R.z K.L.M.n = (if s.gpr .r9 = 0
        then wordsVal s.mem base K.L.R.z K.L.M.n else wordsVal s.mem base K.O.z K.L.M.n) ∧
      isa.eval TCombCfg.isLast t = some (decide (j = K.J - 1)) ∧
      Kp [.r4, .r5, .r6, .r10] s t ∧
      Outs base [(K.L.R.x, 8 * K.L.M.n), (K.L.R.y, 8 * K.L.M.n), (K.L.R.z, 8 * K.L.M.n)] s.mem t.mem := by
  have := lay_nums h.point.k3 h.point.k6
  have hR := h.point
  obtain ⟨-, -, -, -, -, rxl, ryl, rzl⟩ := hR.al
  have rne := hR.rne
  have rx := hR.rx
  have ry := hR.ry
  have rz := hR.rz
  have hlo := h.low
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (nzOf_ok (r := .r9) (by decide)) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_
  have e₁' : s₁.gpr .r10 = if decide (s.gpr .r9 ≠ 0) then BitVec.allOnes 64 else 0 := by
    rw [e₁]; by_cases e : s.gpr .r9 = 0 <;> simp [e]
  rw [WP.block_append_iff]
  refine WP.mono (selPt_ok' (k₁.ws hw.ws) (k₁.at hw.at3) _ e₁' (n := K.L.M.n) (o := K.L.R) (a := K.L.R)
    (b := K.O)
    (by simp only [O_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [this, rxl, ryl, rzl])
    (by simp only [O_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [this, rx, ry, rz])
    rne (by simp only [O_eq]; omega_using [rx, ry, rz])
    (by simp only [O_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [rne, rx, ry]))
    fun s₂ ⟨x, y, z, k₂, o₂⟩ => ?_
  refine WP.mono (lastTest_ok K hj hJ (by rw [k₂.g, k₁.g]; exact gj)) fun t ⟨lt, kt, mt⟩ => ?_
  rw [m₁] at x y z o₂
  rw [mt]
  refine ⟨?_, ?_, ?_, lt, ((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (kt.mono (by decide)),
    by rw [mt] at *; exact o₂⟩ <;>
  · by_cases e : s.gpr .r9 = 0 <;> simp_all

/-! ## A window -/

/-- `R` after the windows `0 … j`: `[Σ_{i≤j} d_i 2^(wi)]G`, Jacobian. -/
structure JAcc (K : TCombCfg) (C : Curve) (base : Addr) (k j : Nat) (s : State) : Prop where
  lt : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal s.mem base x K.L.M.n < C.p
  inv : InvJ C (tmv C K.L.M.n base s K.L.R.x) (tmv C K.L.M.n base s K.L.R.y) (tmv C K.L.M.n base s K.L.R.z)
    (zmul (bpart K.w k (j + 1)) (G C))

/-- A digit's magnitude is zero exactly when its register is. -/
theorem ofNat_eq_zero {b : Nat} (hb : b < 2 ^ 64) : BitVec.ofNat 64 b = 0 ↔ b = 0 := by
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at this
    exact this.trans rfl
  · intro e; rw [e]; rfl

/-- Window `j + 1`: `R` from the sum to `j` to the sum to `j + 1`, `r31 = j + 1`,
and `r6` zero exactly for the last window. -/
theorem bstep_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : Config K C tbl start) (hC : Law C) (hG : onCurve C (G C) = true) (hM3 : AM3 C) {kmax : Nat}
    (hB : BoothOk C K.w K.J kmax) (short : K.topBits < K.w) (hb1 : 1 ≤ K.L.bits)
    {s : State} {base T : Addr} {k j : Nat} (i : CurveInputs K C tbl base T k s) (acc : JAcc K C base k j s)
    (hj : j + 1 < K.J) (hk : k < 2 ^ K.L.nbits) (hkm : k < kmax) (gj : s.gpr .r31 = BitVec.ofNat 64 j)
    (hd : Region.Disjoint ⟨T, 8 * (tableWords K C tbl).length⟩ ⟨base, 8192⟩) :
    WP isa K.bstep s fun t =>
      Rk powClob s t ∧ Unch base (loopWrites K) s.mem t.mem ∧ CurveInputs K C tbl base T k t ∧
      JAcc K C base k (j + 1) t ∧ t.gpr .r31 = BitVec.ofNat 64 (j + 1) ∧
      isa.eval TCombCfg.isLast t = some (decide (j + 1 = K.J - 1)) := by
  apply WP.of_syms
  unfold TCombCfg.bstep
  have hp : 0 < C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  have hk3 := h.layout.point.k3
  have hk6 := h.layout.point.k6
  obtain ⟨h1, h2, he, hb3', ha', hq', hp', ho', -, -⟩ := lay_nums hk3 hk6
  obtain ⟨hqx, hqy, hqz, hqa, -, -, hb3, hoA, -⟩ := q_lay h.layout
  have low := h.layout.low
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at low
  obtain ⟨rx, ry, rz, -, -⟩ := low
  obtain ⟨-, -, -, -, -, rxl, ryl, rzl⟩ := h.layout.point.al
  have nowrap := i.wsr.nowrap
  -- `r31 = j + 1`
  refine WP.seq (wp_step (exec_addi' (by decide)) (WP.block_nil ?_))
  generalize hu : s.write .r31 (s.gpr .r31 + BitVec.ofNat 64 1) = u
  have ku : Kp [.r31] s u := by rw [← hu]; exact Kp.write _ _ (by decide)
  have gu : u.gpr .r31 = BitVec.ofNat 64 (j + 1) := by
    rw [← hu]; simp only [write_gpr, ite_true, gj]; rw [BitVec.ofNat_add]
  have mu : u.mem = s.mem := by rw [← hu]; rfl
  have syu : u.syms = s.syms := by rw [← hu]; rfl
  have iu : CurveInputs K C tbl base T k u :=
    i.keep h.layout hd (ku.rk (rs' := [.r31])) (by decide) (by rw [mu]; exact Unch.refl _ _ _) syu
  -- the entry `E` of window `j + 1` into `Q`
  refine WP.seq (WP.mono_syms (bentry_ok K true h hC iu hj hk gu short hb1 (by simp) hd)
    fun v ⟨kv, ov, rv, lv, pv, zv⟩ syv => ?_)
  have iv : CurveInputs K C tbl base T k v := iu.keep h.layout hd kv (by decide) ov syv
  -- `P = R`
  have cp := copyPt_conds (a := K.L.R) hk3 hk6 (.inl rfl) (by omega_using [ho', rx]) (by omega_using [ho', ry]) (by omega_using [ho', rz]) ⟨rxl, ryl, rzl⟩
  refine WP.seq (WP.mono_syms (copyPt_ok iv.wsr.ws iv.wsr.at3 (n := K.L.M.n) (o := K.P) (a := K.L.R)
    cp.1 cp.2.1 cp.2.2.1 cp.2.2.2) fun v₁ ⟨px, py, pz, k₁, o₁⟩ sy₁ => ?_)
  simp only [P_eq] at px py pz o₁
  have U₁ : Unch base (loopWrites K) v.mem v₁.mem := Unch.cover o₁ fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    refine ⟨(oAt K.L.M.n, 72 * K.L.M.n), by simp [loopWrites], ?_, ?_⟩ <;>
      rcases hw with rfl | rfl | rfl <;> (dsimp only; omega_arith)
  have i₁ : CurveInputs K C tbl base T k v₁ := iv.keep h.layout hd (k₁.rk (rs' := fnClob)) (by decide) U₁ sy₁
  have q₁ : ∀ x ∈ [K.Q.x, K.Q.y, K.Q.z, K.L.R.x, K.L.R.y, K.L.R.z],
      wordsVal v₁.mem base x K.L.M.n = wordsVal v.mem base x K.L.M.n := by
    intro x hx
    apply Unch.wordsVal o₁
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega_arith
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega_arith
  -- `O = P + E`
  have hlt₁ : ∀ x ∈ rIds, wordsVal v₁.mem base (enc K.L.M.n false x) K.L.M.n < C.p := by
    apply rIds_lt_of false
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    have hqa : qAt K.L.M.n = K.Q.x := by omega_using [hk3, hk6, h1, h2, he, hb3', ha', hq', hp', ho', hqx, hqa, rx, ry, rz]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [px, rv _ (by simp), mu]; exact acc.lt _ (by simp)
    · rw [py, rv _ (by simp), mu]; exact acc.lt _ (by simp)
    · rw [pz, rv _ (by simp), mu]; exact acc.lt _ (by simp)
    · rw [hqa, q₁ _ (by simp)]; exact lv _ (by simp)
    · rw [hqa, show K.Q.x + elemBytes K.L.M.n = K.Q.y by omega_using [he, hqy], q₁ _ (by simp)]; exact lv _ (by simp)
    · rw [hqa, show K.Q.x + 2 * elemBytes K.L.M.n = K.Q.z by omega_using [he, hqz], q₁ _ (by simp)]; exact lv _ (by simp)
    · rw [i₁.coeffA]; exact Nat.mod_lt _ hp
    · rw [i₁.coeffB]; exact Nat.mod_lt _ hp
  refine WP.seq (WP.mono_syms (maddCall_ok K h.fieldK h.fieldM h.modulus h.odd hk3 hk6 i₁.wsr hlt₁)
    fun v₂ ⟨k₂, o₂, l₂, e₂⟩ sy₂ => ?_)
  have U₂ : Unch base (loopWrites K) v₁.mem v₂.mem := Unch.cover o₂ fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨(oAt K.L.M.n, 72 * K.L.M.n), by simp [loopWrites], by dsimp only; omega_using [], by dsimp only; omega_using [hk3, hk6, h1, h2, he, hb3', ha', hq', hp', ho', hqx, hqa, rx, ry, rz]⟩
    · exact ⟨_, by simp [loopWrites], Nat.le_refl _, Nat.le_refl _⟩
  have i₂ : CurveInputs K C tbl base T k v₂ := i₁.keep h.layout hd k₂ (by decide) U₂ sy₂
  have q₂ : ∀ x ∈ [K.Q.x, K.Q.y, K.Q.z, K.L.R.x, K.L.R.y, K.L.R.z],
      wordsVal v₂.mem base x K.L.M.n = wordsVal v₁.mem base x K.L.M.n := by
    intro x hx
    apply Unch.wordsVal o₂
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega_arith
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega_arith
  -- `O = E` if `R = O`
  refine WP.seq (WP.mono_syms (zsel_ok K h.layout i₂.wsr) fun v₃ ⟨ox₃, oy₃, oz₃, k₃, o₃⟩ sy₃ => ?_)
  have U₃ : Unch base (loopWrites K) v₂.mem v₃.mem := Unch.cover o₃ fun w hw => by
    simp only [O_eq, List.mem_cons, List.not_mem_nil, or_false] at hw
    refine ⟨(oAt K.L.M.n, 72 * K.L.M.n), by simp [loopWrites], ?_, ?_⟩ <;>
      rcases hw with rfl | rfl | rfl <;> (dsimp only; omega_arith)
  have i₃ : CurveInputs K C tbl base T k v₃ := i₂.keep h.layout hd (k₃.rk (rs' := fnClob)) (by decide) U₃ sy₃
  have q₃ : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z],
      wordsVal v₃.mem base x K.L.M.n = wordsVal v₂.mem base x K.L.M.n := by
    intro x hx
    apply Unch.wordsVal o₃
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [O_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      rcases hx with rfl | rfl | rfl <;> omega_arith
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> omega_using [hk3, hk6, h1, h2, he, hb3', ha', hq', hp', ho', hqx, hqa, hb3, hoA, rx, ry, rz, rxl, ryl, rzl]
  have g₃ : v₃.gpr .r31 = BitVec.ofNat 64 (j + 1) := by rw [k₃.g, k₂.g, k₁.g, kv.g]; exact gu
  -- the digit again
  refine WP.seq (WP.mono_syms (bdigit_ok K true i₃.wsr.ws i₃.wsr.at3 ⟨h.w1, h.w9⟩ hj (Nat.le_of_lt h.J15)
    h.startBits h.coverBits short h.bitsOff hb1 h.layout.point.bitsE hk (by simp) g₃ i₃.bits)
    fun v₄ ⟨g9, k₄, m₄⟩ sy₄ => ?_)
  have i₄ : CurveInputs K C tbl base T k v₄ :=
    i₃.keep h.layout hd (k₄.rk (rs' := fnClob)) (by decide) (by rw [m₄]; exact Unch.refl _ _ _) sy₄
  -- `R = O` unless the digit is zero
  refine WP.mono_syms (rsel_ok K h.layout i₄.wsr (j := j + 1) (by have := h.J15; omega_using [hj, this]) (by have := h.J15; omega_using [this])
    (by rw [k₄.g]; exact g₃)) fun t ⟨xt, yt, zt, lt, kt, ot⟩ syt => fun syt' => ?_
  have U₅ : Unch base (loopWrites K) v₄.mem t.mem := Unch.cover ot fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> exact ⟨_, by simp [loopWrites], Nat.le_refl _, Nat.le_refl _⟩
  have keep : Rk powClob s t :=
    (ku.rk (by decide)).trans ((kv.mono (by decide)).trans ((k₁.rk (by decide)).trans ((k₂.mono (by decide)).trans
      ((k₃.rk (by decide)).trans ((k₄.rk (by decide)).trans (kt.rk (by decide)))))))
  have unch : Unch base (loopWrites K) s.mem t.mem := by
    have ou : Unch base (loopWrites K) s.mem u.mem := by rw [mu]; exact Unch.refl _ _ _
    have o₄ : Unch base (loopWrites K) v₃.mem v₄.mem := by rw [m₄]; exact Unch.refl _ _ _
    exact (ou.trans (ov.trans (U₁.trans (U₂.trans (U₃.trans (o₄.trans U₅)))))).cover fun w hw' => ⟨w, by
      simpa only [List.mem_append, or_self] using hw', Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨keep, unch, i.keep h.layout hd keep (by decide) unch syt', ?_, by rw [kt.g, k₄.g]; exact g₃, lt⟩
  -- the values
  have b64 : bmag K.w k (j + 1) < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (bmag_le h.w1 k (j + 1)) (Nat.pow_lt_pow_right (by decide) (by have := h.w9; omega_using [this]))
  simp only [g9, m₄, ofNat_eq_zero b64] at xt yt zt
  have rR : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z],
      wordsVal v₃.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n := fun x hx => by
    rw [q₃ x hx, q₂ x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with e | e | e <;> simp [e]),
      q₁ x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with e | e | e <;> simp [e]), rv x hx, mu]
  have rQ : ∀ x ∈ [K.Q.x, K.Q.y, K.Q.z],
      wordsVal v₂.mem base x K.L.M.n = wordsVal v.mem base x K.L.M.n := fun x hx => by
    rw [q₂ x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with e | e | e <;> simp [e]),
      q₁ x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with e | e | e <;> simp [e])]
  have rz₂ : wordsVal v₂.mem base K.L.R.z K.L.M.n = wordsVal s.mem base K.L.R.z K.L.M.n := by
    rw [← q₃ _ (by simp)]; exact rR _ (by simp)
  rw [rz₂] at ox₃ oy₃ oz₃
  have mE : (tmv C K.L.M.n base v₂ K.O.x, tmv C K.L.M.n base v₂ K.O.y, tmv C K.L.M.n base v₂ K.O.z) =
      maddJF (tmv C K.L.M.n base s K.L.R.x) (tmv C K.L.M.n base s K.L.R.y) (tmv C K.L.M.n base s K.L.R.z)
        (tmv C K.L.M.n base v K.Q.x) (tmv C K.L.M.n base v K.Q.y) := by
    have em := e₂
    simp only [Eb, enc_0, enc_1, enc_2, enc_3, enc_4, enc_5, enc_6, enc_7, Bool.false_eq_true, ↓reduceIte] at em
    rw [px, py, pz, rv _ (by simp), rv _ (by simp), rv _ (by simp), mu,
      show qAt K.L.M.n = K.Q.x by omega_using [hk3, hk6, h1, h2, he, hb3', ha', hq', hp', ho', hqx, hqa, rx, ry, rz], show K.Q.x + elemBytes K.L.M.n = K.Q.y by omega_using [he, hqy],
      q₁ _ (by simp), q₁ _ (by simp)] at em
    simp only [O_eq]
    exact em
  have lO : ∀ x ∈ [K.O.x, K.O.y, K.O.z], wordsVal v₂.mem base x K.L.M.n < C.p := by
    simp only [O_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    have l0 := l₂ 0 (by decide)
    have l1 := l₂ 1 (by decide)
    have l2 := l₂ 2 (by decide)
    rw [enc_0] at l0
    rw [enc_1] at l1
    rw [enc_2] at l2
    exact ⟨l0, l1, l2⟩
  have hz0 : (tmv C K.L.M.n base s K.L.R.z = 0) = (wordsVal s.mem base K.L.R.z K.L.M.n = 0) :=
    propext (toM_eq_zero_iff h.unit (acc.lt _ (by simp)))
  have hez : tmv C K.L.M.n base v K.Q.z = if bmag K.w k (j + 1) = 0 then 0 else 1 := by
    show toM _ _ _ = _
    rw [zv]
    split
    · exact toM_zero _ _
    · exact h.one
  have math := bstep_math hC hG hM3 hB h.w1 hkm (j := j + 1) (by omega_using []) hj acc.inv pv hez
  simp only [hz0] at math
  refine ⟨?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [xt, yt, zt, ox₃, oy₃, oz₃, rR K.L.R.x (by simp), rR K.L.R.y (by simp), rR K.L.R.z (by simp),
      rQ K.Q.x (by simp), rQ K.Q.y (by simp), rQ K.Q.z (by simp)]
    refine ⟨?_, ?_, ?_⟩ <;> split <;> (try split) <;>
      first | (apply acc.lt; simp; done) | (apply lv; simp; done) | (apply lO; simp; done)
  · have ex := congrArg Prod.fst mE
    have ey := congrArg (fun p => p.2.1) mE
    have ez := congrArg (fun p => p.2.2) mE
    dsimp only at ex ey ez
    have tx : tmv C K.L.M.n base t K.L.R.x = if bmag K.w k (j + 1) = 0 then tmv C K.L.M.n base s K.L.R.x
        else if wordsVal s.mem base K.L.R.z K.L.M.n = 0 then tmv C K.L.M.n base v K.Q.x
        else (maddJF (tmv C K.L.M.n base s K.L.R.x) (tmv C K.L.M.n base s K.L.R.y) (tmv C K.L.M.n base s K.L.R.z)
          (tmv C K.L.M.n base v K.Q.x) (tmv C K.L.M.n base v K.Q.y)).1 := by
      rw [← ex]
      show toM _ _ (wordsVal t.mem base K.L.R.x K.L.M.n) = _
      rw [xt, ox₃]
      split
      · rw [rR K.L.R.x (by simp)]
      · split
        · rw [rQ K.Q.x (by simp)]
        · rfl
    have ty : tmv C K.L.M.n base t K.L.R.y = if bmag K.w k (j + 1) = 0 then tmv C K.L.M.n base s K.L.R.y
        else if wordsVal s.mem base K.L.R.z K.L.M.n = 0 then tmv C K.L.M.n base v K.Q.y
        else (maddJF (tmv C K.L.M.n base s K.L.R.x) (tmv C K.L.M.n base s K.L.R.y) (tmv C K.L.M.n base s K.L.R.z)
          (tmv C K.L.M.n base v K.Q.x) (tmv C K.L.M.n base v K.Q.y)).2.1 := by
      rw [← ey]
      show toM _ _ (wordsVal t.mem base K.L.R.y K.L.M.n) = _
      rw [yt, oy₃]
      split
      · rw [rR K.L.R.y (by simp)]
      · split
        · rw [rQ K.Q.y (by simp)]
        · rfl
    have tz : tmv C K.L.M.n base t K.L.R.z = if bmag K.w k (j + 1) = 0 then tmv C K.L.M.n base s K.L.R.z
        else if wordsVal s.mem base K.L.R.z K.L.M.n = 0 then tmv C K.L.M.n base v K.Q.z
        else (maddJF (tmv C K.L.M.n base s K.L.R.x) (tmv C K.L.M.n base s K.L.R.y) (tmv C K.L.M.n base s K.L.R.z)
          (tmv C K.L.M.n base v K.Q.x) (tmv C K.L.M.n base v K.Q.y)).2.2 := by
      rw [← ez]
      show toM _ _ (wordsVal t.mem base K.L.R.z K.L.M.n) = _
      rw [zt, oz₃]
      split
      · rw [rR K.L.R.z (by simp)]
      · split
        · rw [rQ K.Q.z (by simp)]
        · rfl
    rw [tx, ty, tz]
    exact math

/-! ## The comb's configuration, and its end -/

/-- What the comb needs of its configuration, beyond `TComb`'s: the digits'
bound for the mixed additions (`BoothOk`), `a = -3`'s doubling-free formula
(`AM3`), a short last window, a byte below the table of bits, and the slots
of the final conversion (`R`, `-y`'s, zero) for the field functions. -/
structure JConfig (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) (start : Nat × Nat) : Prop where
  base : Config K C tbl start
  booth : BoothOk C K.w K.J (2 ^ K.L.nbits)
  am3 : AM3 C
  short : K.topBits < K.w
  bits1 : 1 ≤ K.L.bits
  outLay : Lay K.L.M (own K.L.M.n) (· ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.neg, K.zero])

/-- `R` to homogeneous coordinates: `(X Z : Y' : Z³)` for `Y'` one where
`Z` is zero, a representative of `R`'s point. -/
theorem bout_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (hJ : JConfig K C tbl start) (hC : Law C) {s : State} {base : Addr} {P : Point C} (hw : WsReg s base)
    (zero : wordsVal s.mem base K.zero K.L.M.n = 0)
    (lt : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal s.mem base x K.L.M.n < C.p)
    (inv : InvJ C (tmv C K.L.M.n base s K.L.R.x) (tmv C K.L.M.n base s K.L.R.y) (tmv C K.L.M.n base s K.L.R.z) P) :
    WP isa K.bout s fun t =>
      Rk powClob s t ∧ Unch base (writes K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal t.mem base x K.L.M.n < C.p) ∧
      Rep C (tmv C K.L.M.n base t K.L.R.x) (tmv C K.L.M.n base t K.L.R.y) (tmv C K.L.M.n base t K.L.R.z) P := by
  have h := hJ.base
  have hp : 0 < C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  have hk3 := h.layout.point.k3
  have hk6 := h.layout.point.k6
  have := lay_nums hk3 hk6
  obtain ⟨hqx, hqy, hqz, hqa, -, -, hb3, hoA, hq4⟩ := q_lay h.layout
  have low := h.layout.low
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at low lt
  obtain ⟨rx, ry, rz, zlo, nlo⟩ := low
  obtain ⟨ltx, lty, ltz⟩ := lt
  obtain ⟨-, -, -, -, -, rxl, ryl, rzl⟩ := h.layout.point.al
  obtain ⟨rxy, rxz, ryz⟩ := h.layout.point.rne
  have nap := h.layout.negApart
  have zap := h.layout.zeroApart
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at nap zap
  obtain ⟨nx, ny, nz, nzr⟩ := nap
  obtain ⟨zx, zy, zz⟩ := zap
  have fit := h.modulus.m_lt
  have nowrap := hw.nowrap
  unfold TCombCfg.bout
  -- `Y = 1` where `Z` is zero
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (zMask_ok K hw.ws hw.at3 (by omega_using [hk3, hk6, this, hqx, hqa, rx, ry, rz, zlo, nlo, rxy, rxz, ryz, nx, ny, nz, nzr, zx, zy, zz]) rzl (by omega_using [hk3, hk6, this, hqx, hqa, rx, ry, rz, zlo, nlo, rzl, rxy, rxz, ryz, nx, ny, nz, nzr, zx, zy, zz])) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_
  rw [nzMask_eq] at e₁
  have w₁ := hw.of_kp k₁
  rw [WP.block_append_iff]
  refine WP.mono (setConstW_ok w₁ (o := K.Q.y) (n := K.L.M.n) (by omega_using [hk3, hk6, this, hqx, hqy, hqa, rx, ry, rz, zlo, nlo, rxy, rxz, ryz, nx, ny, nz, nzr, zx, zy, zz])
    (Nat.lt_trans h.one_lt fit)) fun s₂ ⟨o₂, y₂, k₂⟩ => ?_
  have w₂ := w₁.of_kp k₂
  refine WP.mono (sel_ok (decide (wordsVal s.mem base K.L.R.z K.L.M.n ≠ 0)) K.L.M.n w₂.ws w₂.at3
    (by rw [k₂.g]; exact e₁) (o := K.L.R.y) (a := K.Q.y)
    (b := K.L.R.y) ryl (by omega_using [hk3, hk6, this, hqx, hqy, hqa, hq4, rx, ry, rz, zlo, nlo, rxy, rxz, ryz, nx, ny, nz, nzr, zx, zy, zz]) ryl (by omega_using [hk3, hk6, this, hqx, hqa, rx, ry, rz, zlo, nlo, ryl, rxy, rxz, ryz, nx, ny, nz, nzr, zx, zy, zz]) (by omega_using [hk3, hk6, this, hqx, hqy, hqa, rx, ry, rz, zlo, nlo, rxy, rxz, ryz, nx, ny, nz, nzr, zx, zy, zz]) (by omega_using [hk3, hk6, this, hqx, hqa, rx, ry, rz, zlo, nlo, ryl, rxy, rxz, ryz, nx, ny, nz, nzr, zx, zy, zz]) (by omega_using [hk3, hk6, this, hqx, hqy, hqa, rx, ry, rz, zlo, nlo, ryl, rxy, rxz, ryz, nx, ny, nz, nzr, zx, zy, zz]) (.inl (Nat.le_refl _)))
    fun s₃ ⟨y₃, k₃, o₃⟩ => ?_
  have w₃ := w₂.of_kp k₃
  -- what `s₃` holds
  have kept : ∀ x ∈ [K.L.R.x, K.L.R.z, K.zero],
      wordsVal s₃.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [o₃.wordsVal (by rcases hx with rfl | rfl | rfl <;> omega_arith) (by rcases hx with rfl | rfl | rfl <;> omega_arith),
      o₂.wordsVal (by rcases hx with rfl | rfl | rfl <;> omega_arith) (by rcases hx with rfl | rfl | rfl <;> omega_arith), m₁]
  have yv : wordsVal s₃.mem base K.L.R.y K.L.M.n = if wordsVal s.mem base K.L.R.z K.L.M.n = 0 then K.one
      else wordsVal s.mem base K.L.R.y K.L.M.n := by
    rw [y₃, o₂.wordsVal (by omega_using [hk3, hk6, this, hqx, hqy, hqa, rx, ry, rz, zlo, nlo, ryl, rxy, rxz, ryz, nx, ny, nz, nzr, zx, zy, zz]) (by omega_using [hk3, hk6, this, hqx, hqa, rx, ry, rz, zlo, nlo, ryl, rxy, rxz, ryz, nx, ny, nz, nzr, zx, zy, zz]), y₂, m₁]
    by_cases e : wordsVal s.mem base K.L.R.z K.L.M.n = 0 <;> simp [e]
  -- the field program
  have hk := h.fieldK
  have hm := h.fieldM
  generalize K.F = F at hk hm ⊢
  obtain ⟨c, wF, m', k', d⟩ := F
  dsimp only at hk hm
  subst hk hm
  let V : List Nat := [K.L.R.x, K.L.R.y, K.L.R.z, K.zero]
  have I₃ : Inv K.L.M.n base C.p (· ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.neg, K.zero]) V
      (fun x => tmv C K.L.M.n base s₃ x) s₃ := by
    refine ⟨w₃, by simp [V], ?_, fun _ _ => rfl⟩
    simp only [V, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [kept K.L.R.x (by simp), kept K.L.R.z (by simp), kept K.zero (by simp), yv, zero]
    refine ⟨ltx, ?_, ltz, hp⟩
    split
    · exact h.one_lt
    · exact lty
  have ne : K.L.R.x ≠ K.L.R.y ∧ K.L.R.x ≠ K.L.R.z ∧ K.L.R.y ≠ K.L.R.z ∧ K.neg ≠ K.L.R.x ∧
      K.neg ≠ K.L.R.y ∧ K.neg ≠ K.L.R.z ∧ K.zero ≠ K.L.R.x ∧ K.zero ≠ K.L.R.y ∧ K.zero ≠ K.L.R.z ∧
      K.zero ≠ K.neg := by omega_using [hk3, hk6, this, hqx, hqa, rx, ry, rz, zlo, nlo, rxl, ryl, rzl, rxy, rxz, ryz, nx, ny, nz, nzr, zx, zy, zz]
  obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉, n₁₀⟩ := ne
  have reads : readsOk (fromJ { K.L.S with t0 := K.neg } K.L.R ⟨K.zero, K.zero, K.zero⟩ K.L.R) V = true := by
    simp [readsOk, fromJ, FOp.ins, FOp.out, V]
  refine WP.mono (fprog_ok (M := K.L.M) (S := ⟨c, wF, C.p, K.L.M.n, d⟩) h.modulus rfl hJ.outLay h.unit _ I₃
    (by simp [fromJ, FOp.ins, FOp.out]) reads) fun t ⟨kt, It⟩ => ?_
  have val : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], tmv C K.L.M.n base t x =
      runOps (fromJ { K.L.S with t0 := K.neg } K.L.R ⟨K.zero, K.zero, K.zero⟩ K.L.R)
        (fun x => tmv C K.L.M.n base s₃ x) x := fun x hx =>
    It.val x (by
      rw [mem_validAfter]; left; simp only [V, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with e | e | e <;> simp [e])
  have ltt : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal t.mem base x K.L.M.n < C.p := fun x hx =>
    It.lt x (by
      rw [mem_validAfter]; left; simp only [V, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with e | e | e <;> simp [e])
  refine ⟨?_, ?_, ltt, ?_⟩
  · exact ⟨fun r hr => by
      rw [kt.gpr r (fun h' => hr (List.mem_cons_of_mem _ h')), k₃.gpr r (fun h' => hr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'; rcases h' with rfl | rfl <;> decide)),
        k₂.gpr r (fun h' => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h'; subst h'; decide)),
        k₁.gpr r (fun h' => hr (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h'; rcases h' with rfl | rfl | rfl <;> decide))],
      kt.rd.trans (k₃.rd.trans (k₂.rd.trans k₁.rd)), kt.wr.trans (k₃.wr.trans (k₂.wr.trans k₁.wr)),
      kt.sp.trans (k₃.sp.trans (k₂.sp.trans k₁.sp))⟩
  · have u₁ : Unch base (writes K) s.mem s₁.mem := by rw [m₁]; exact Unch.refl _ _ _
    have u₂ : Unch base (writes K) s₁.mem s₂.mem :=
      Unch.cover (W := [(K.Q.y, 8 * K.L.M.n)]) (Outs.of_outside o₂ (List.mem_singleton_self _)) fun w hw' => by
        rw [List.mem_singleton] at hw'; subst hw'
        exact ⟨(oAt K.L.M.n, 4096 - oAt K.L.M.n), by simp [writes], by dsimp only; omega_using [hqx, hqy], by dsimp only; omega_using [hk3, hk6, this, hqx, hqy, hqa, rx, ry, rz, zlo, nlo, rxy, rxz, ryz, nx, ny, nz, nzr, zx, zy, zz]⟩
    have u₃ : Unch base (writes K) s₂.mem s₃.mem :=
      Unch.cover (W := [(K.L.R.y, 8 * K.L.M.n)]) (Outs.of_outside o₃ (List.mem_singleton_self _)) fun w hw' => by
        rw [List.mem_singleton] at hw'; subst hw'
        exact ⟨_, by simp [writes], Nat.le_refl _, Nat.le_refl _⟩
    have u₄ : Unch base (writes K) s₃.mem t.mem := Unch.cover kt.mem fun w hw' => by
      simp only [fromJ, List.map_cons, List.map_nil, FOp.out, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, by simp [writes], Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨_, by simp [writes], Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨_, by simp [writes], Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨_, by simp [writes], Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨(oAt K.L.M.n, 4096 - oAt K.L.M.n), by simp [writes], by dsimp only; omega_using [this], by dsimp only; omega_using [hk3, hk6, this, hqx, hqa, rx, ry, rz, zlo, nlo, rxy, rxz, ryz, nx, ny, nz, nzr, zx, zy, zz]⟩
    exact (u₁.trans (u₂.trans (u₃.trans u₄))).cover fun w hw' => ⟨w, by
      simpa only [List.mem_append, or_self] using hw', Nat.le_refl _, Nat.le_refl _⟩
  · have out := InvJ.out hC inv
    have ex := val K.L.R.x (by simp)
    have ey := val K.L.R.y (by simp)
    have ez := val K.L.R.z (by simp)
    simp only [fromJ, runOps_cons, runOps_nil, FOp.run, Function.update_apply, n₁, n₂, n₃, n₇, n₉, n₁₀,
      Ne.symm n₁, Ne.symm n₂, Ne.symm n₃, Ne.symm n₄, Ne.symm n₅, Ne.symm n₆, ↓reduceIte] at ex ey ez
    rw [ex, ey, ez]
    have z₃ : tmv C K.L.M.n base s₃ K.zero = 0 := by
      show toM _ _ _ = _
      rw [kept _ (by simp), zero]; exact toM_zero _ _
    have tx : tmv C K.L.M.n base s₃ K.L.R.x = tmv C K.L.M.n base s K.L.R.x := by
      show toM _ _ _ = toM _ _ _; rw [kept _ (by simp)]
    have tz : tmv C K.L.M.n base s₃ K.L.R.z = tmv C K.L.M.n base s K.L.R.z := by
      show toM _ _ _ = toM _ _ _; rw [kept _ (by simp)]
    have ty : tmv C K.L.M.n base s₃ K.L.R.y =
        if tmv C K.L.M.n base s K.L.R.z = 0 then 1 else tmv C K.L.M.n base s K.L.R.y := by
      show toM _ _ _ = _
      rw [yv]
      by_cases e : wordsVal s.mem base K.L.R.z K.L.M.n = 0
      · have e' : tmv C K.L.M.n base s K.L.R.z = 0 := by show toM _ _ _ = _; rw [e]; exact toM_zero _ _
        simp only [e, e', ↓reduceIte]; exact h.one
      · have e' : tmv C K.L.M.n base s K.L.R.z ≠ 0 := fun h0 => e ((toM_eq_zero_iff h.unit ltz).mp h0)
        simp only [e, e', ↓reduceIte]
    rw [z₃, tx, tz, ty, Lean.Grind.Semiring.add_zero]
    exact out

/-! ## The loop, and the comb -/

/-- What holds after the windows `0 … j`, from `s₀`. -/
structure Done (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) (base T : Addr) (k : Nat)
    (s₀ : State) (j : Nat) (t : State) : Prop where
  keep : Rk powClob s₀ t
  unch : Unch base (writes K) s₀.mem t.mem
  inputs : CurveInputs K C tbl base T k t
  acc : JAcc K C base k j t
  r31 : t.gpr .r31 = BitVec.ofNat 64 j

/-- `r6 ≠ 0` is the negation of `r6 = 0`. -/
theorem eval_more {t : State} {b : Bool} (h : isa.eval TCombCfg.isLast t = some b) :
    isa.eval (.nonzero .d .r6) t = some (!b) := by
  rw [eval_nonzero]
  rw [eval_zero, Option.some.injEq] at h
  rw [bne, h]

/-- The windows `j + 1 … J - 1`. -/
theorem loopJ_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (hJ : JConfig K C tbl start) (hC : Law C) (hG : onCurve C (G C) = true)
    {s₀ : State} {base T : Addr} {k : Nat} (hk : k < 2 ^ K.L.nbits)
    (hd : Region.Disjoint ⟨T, 8 * (tableWords K C tbl).length⟩ ⟨base, 8192⟩) :
    ∀ (n j : Nat) (t : State), j + 1 + n = K.J - 1 → Done K C tbl base T k s₀ j t →
      WP isa (.loop K.bstep (.nonzero .d .r6)) t (Done K C tbl base T k s₀ (K.J - 1)) := by
  intro n j t hn hD
  refine WP.loop (M := isa) (fun (n : Nat) (t : State) => ∃ j, j + 1 + n = K.J - 1 ∧ Done K C tbl base T k s₀ j t)
    (fun n t ⟨j, hjn, D⟩ => ?_) n t ⟨j, hn, hD⟩
  refine WP.mono (bstep_ok K hJ.base hC hG hJ.am3 hJ.booth hJ.short hJ.bits1 D.inputs D.acc (by omega_using [hjn]) hk hk
    D.r31 hd) fun t' ⟨kt, ot, it, at', gt, lt⟩ => ?_
  have D' : Done K C tbl base T k s₀ (j + 1) t' :=
    ⟨D.keep.trans kt, (D.unch.trans (ot.cover hJ.base.layout.loop_cover)).cover fun w hw' => ⟨w, by
      simpa only [List.mem_append, or_self] using hw', Nat.le_refl _, Nat.le_refl _⟩, it, at', gt⟩
  have e := eval_more lt
  by_cases last : j + 1 = K.J - 1
  · refine .inl ⟨by rw [e]; simp [last], ?_⟩
    rw [← last]; exact D'
  · exact .inr ⟨by rw [e]; simp [last], n - 1, by omega_using [hjn, last], j + 1, by omega_using [hjn, last], D'⟩

/-- `R = O + E` for `R = O`: the entry. -/
theorem first_inv {C : Curve} (hC : Law C) (hG : onCurve C (G C) = true) {w k : Nat} (hw : 1 ≤ w)
    {X Y Z : Fe C} (hE : Rep C X Y Z (bentry C w k 0)) (hz : Z = 1 ∨ Z = 0) :
    InvJ C X Y Z (zmul (bpart w k (0 + 1)) (G C)) := by
  rw [bpart_succ_pt hC hG hw, bpart_zero, show ((0 : Int)) = ((0 : Nat) : Int) from rfl, zmul_natCast,
    show Spec.Weierstrass.mul 0 (G C) = .infinity by simp [Spec.Weierstrass.mul], infinity_add']
  exact InvJ.of_rep01 hE hz

/-- The comb: `R = [k]G`, for the scalar `k` of `nbits` bits whose table of
bits is at `bits`, reduced, with only the registers of `powClob` and the
memory of `writes` changed, as `comb_ok`. -/
theorem combJ_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (hJ : JConfig K C tbl start) (hC : Law C) (hG : onCurve C (G C) = true)
    {s : State} {base T : Addr} {k : Nat} (hw : WsReg s base)
    (ht : TableMem s T (tableWords K C tbl)) (sym : s.syms K.tsym = T)
    (hd : Region.Disjoint ⟨T, 8 * (tableWords K C tbl).length⟩ ⟨base, 8192⟩)
    (hk : k < 2 ^ K.L.nbits) (zero : wordsVal s.mem base K.zero K.L.M.n = 0)
    (bits : ∀ i < K.L.nbits, s.mem (off base (K.L.bits + i)) = if k.testBit i then 1 else 0)
    (coeffA : wordsVal s.mem base K.L.S.a K.L.M.n = C.a * 2 ^ (64 * K.L.M.n) % C.p)
    (coeffB : wordsVal s.mem base K.L.S.b3 K.L.M.n = (3 * C.b) * 2 ^ (64 * K.L.M.n) % C.p) :
    WP isa K.combJ s fun t =>
      Rk powClob s t ∧ Unch base (writes K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal t.mem base x K.L.M.n < C.p) ∧
      Rep C (tmv C K.L.M.n base t K.L.R.x) (tmv C K.L.M.n base t K.L.R.y) (tmv C K.L.M.n base t K.L.R.z)
        (mul k (G C)) := by
  have h := hJ.base
  have hp : 0 < C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  have hk3 := h.layout.point.k3
  have hk6 := h.layout.point.k6
  have := lay_nums hk3 hk6
  obtain ⟨hqx, hqy, hqz, hqa, -, -, hb3, hoA, hq4⟩ := q_lay h.layout
  have low := h.layout.low
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at low
  obtain ⟨rx, ry, rz, zlo, -⟩ := low
  obtain ⟨-, -, -, -, -, rxl, ryl, rzl⟩ := h.layout.point.al
  have hbits := h.layout.point.bits
  have hbe := h.layout.point.bitsE
  have nowrap := hw.nowrap
  unfold TCombCfg.combJ
  -- `a` and `3b` to the point functions' slots, and `r31 = 0`
  have start : WP isa (.block (ladderSetup K.L ++ [.li .r31 0])) s fun t => Kp [.r4, .r31] s t ∧
      Unch base [(oAt K.L.M.n, 4096 - oAt K.L.M.n)] s.mem t.mem ∧ CpOk K.L base t.mem s.mem ∧
      t.gpr .r31 = BitVec.ofNat 64 0 := by
    refine wp_append (WP.mono (ladderSetup_ok hw h.layout.point) fun u ⟨ku, ou, cp⟩ => ?_)
    refine wp_step (exec_li (by decide)) (WP.block_nil ⟨(ku.mono (by decide)).trans (Kp.write _ _ (by decide)),
      ou, cp, by simp only [write_gpr, ite_true]⟩)
  refine WP.seq (WP.mono_syms start fun u ⟨ku, ou, cp, gu⟩ syu => ?_)
  have ou' : Unch base (writes K) s.mem u.mem := ou.cover fun w hw' => by
    rw [List.mem_singleton] at hw'; subst hw'
    exact ⟨_, by simp [writes], Nat.le_refl _, Nat.le_refl _⟩
  have iu : CurveInputs K C tbl base T k u := by
    refine ⟨hw.of_kp ku, ht.unch (by rw [ku.rd, ku.wr]) ou' (fun w hw' => by
        have := h.layout.bounded w hw'; omega_using [this]) hd, by rw [syu]; exact sym, ?_, ?_, ?_, ?_⟩
    · rw [ou.wordsVal (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact .inl zlo) (by omega_using [this, zlo]), zero]
    · intro j hj
      rw [ou.byte (fun w hw' => by
        rw [List.mem_singleton] at hw'; subst hw'; right; dsimp only; omega_using [this, hbits]) (by omega_using [hbe, hj]), bits j hj]
    · exact cp.2.2.2.1.trans coeffA
    · exact cp.2.2.2.2.trans coeffB
  -- window 0's entry, to `R`
  refine WP.seq (WP.mono_syms (bentry_ok K false h hC iu (by have := hJ.booth.J2; omega_using [this]) hk gu hJ.short hJ.bits1
    (by simp) hd) fun v ⟨kv, ov, rv, lv, pv, zv⟩ syv => ?_)
  have iv : CurveInputs K C tbl base T k v := iu.keep h.layout hd kv (by decide) ov syv
  refine WP.seq (WP.mono_syms (copyPt_ok iv.wsr.ws iv.wsr.at3 (n := K.L.M.n) (o := K.L.R) (a := K.Q)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [hqy, hqz, hq4, rxl, ryl, rzl])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [hk3, hk6, this, hqx, hqy, hqz, hqa, hq4, rx, ry, rz, zlo, rxl, ryl, rzl])
    h.layout.point.rne
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [hk3, hk6, this, hqx, hqy, hqz, hqa, hq4, rx, ry, rz, zlo, rxl, ryl, rzl]))
    fun v₁ ⟨x₁, y₁, z₁, k₁, o₁⟩ sy₁ => ?_)
  have U₁ : Unch base (loopWrites K) v.mem v₁.mem := Unch.cover o₁ fun w hw' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl <;> exact ⟨_, by simp [loopWrites], Nat.le_refl _, Nat.le_refl _⟩
  have i₁ : CurveInputs K C tbl base T k v₁ := iv.keep h.layout hd (k₁.rk (rs' := fnClob)) (by decide) U₁ sy₁
  have keep₁ : Rk powClob s v₁ :=
    (ku.rk (by decide)).trans ((kv.mono (by decide)).trans (k₁.rk (by decide)))
  have ovU : Unch base (loopWrites K) u.mem v₁.mem := (ov.trans U₁).cover fun w hw' => ⟨w, by
    simpa only [List.mem_append, or_self] using hw', Nat.le_refl _, Nat.le_refl _⟩
  have unch₁ : Unch base (writes K) s.mem v₁.mem :=
    (ou'.trans (ovU.cover h.layout.loop_cover)).cover fun w hw' => ⟨w, by
      simpa only [List.mem_append, or_self] using hw', Nat.le_refl _, Nat.le_refl _⟩
  have acc₁ : JAcc K C base k 0 v₁ := by
    refine ⟨?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      rw [x₁, y₁, z₁]
      exact ⟨lv _ (by simp), lv _ (by simp), lv _ (by simp)⟩
    · show InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [x₁, y₁, z₁]
      refine first_inv hC hG h.w1 pv ?_
      show toM _ _ _ = 1 ∨ toM _ _ _ = 0
      rw [zv]
      split
      · exact .inr (toM_zero _ _)
      · exact .inl h.one
  have D₁ : Done K C tbl base T k s 0 v₁ :=
    ⟨keep₁, unch₁, i₁, acc₁, by rw [k₁.g, kv.g]; exact gu⟩
  -- the windows `1 … J - 1`, and `R` out of Jacobian coordinates
  have J2 := hJ.booth.J2
  refine WP.seq (WP.mono (loopJ_ok K hJ hC hG hk hd (K.J - 2) 0 v₁ (by omega_using [J2]) D₁) fun t D => ?_)
  refine WP.mono (bout_ok K hJ hC D.inputs.wsr D.inputs.zero D.acc.lt D.acc.inv) fun u ⟨ku', ou'', lu, ru⟩ =>
    ⟨D.keep.trans ku', (D.unch.trans ou'').cover fun w hw' => ⟨w, by
      simpa only [List.mem_append, or_self] using hw', Nat.le_refl _, Nat.le_refl _⟩, lu, ?_⟩
  have top : k < 2 ^ (K.w * K.J - 1) := by
    have hs := hJ.short
    have hst := h.startBits
    unfold TCombCfg.topBits at hs
    have e : K.w * K.J = K.w * (K.J - 1) + K.w := by
      rw [← Nat.mul_succ]; congr 1; omega_using [J2]
    exact Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) (by omega_using [hs, e]))
  rw [show K.J - 1 + 1 = K.J by omega_using [J2], bpart_top (by omega_using [J2]) top, zmul_natCast] at ru
  exact ru

end VG.Proof.Weierstrass.PPC64LE.TCombJ
