module

public import VerifiedGarbage.Proof.MlKem.X86_64.Lazy
public import VerifiedGarbage.Proof.MlKem.X86_64.DecMul
public import VerifiedGarbage.Proof.MlKem.X86_64.FinY
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.MlKem.X86_64.YNttPack
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: a row of `keygen_mul` in registers (`rowY`)

`rowY k` adds to `t[i]` the sum of the `k` products of row `i` of `Â` and
`ŝ`, 32 coefficients at a time, without the accumulator in memory. The
coefficients of `f` are loaded as pairs, a pair to a doubleword (`PLanes`),
so that `vpmaddwd` with the pairs `(g₀, g₁γ)` and `(g₁, g₀)` gives the two
coefficients of `BaseCaseMultiply` as doublewords, each congruent to its
coefficient and less than `2q²` (`RepD 2`, `pmadd_rep`); the `k ≤ 4`
products of a coefficient add up within `8q²` (`RepD.add`), and one
Montgomery reduction of the sum leaves a word congruent to the coefficient
times `2⁻¹⁶`, within `q` (`RepR 1`, `redD_rep`); then one Montgomery
multiplication by `R² mod q` makes it congruent to the coefficient
(`red2_rep`), which `vcadd` makes canonical (`cadd_rep`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open W (montW caddW r2W qW qinvW)

/-! ## Words congruent to coefficients times `2⁻¹⁶` -/

/-- The word `w` times `2¹⁶` is congruent to `v` modulo `q`, and `w` is less
than `b · q` in magnitude. -/
def RepR (b : Nat) (w : BitVec 16) (v : Zq) : Prop :=
  -((b : Int) * 3329) < w.toInt ∧ w.toInt < (b : Int) * 3329 ∧ (w.toInt * 65536 - (v.val : Int)) % 3329 = 0

/-- The doubleword `x` is congruent to `v` modulo `q`, and less than
`b · q²` in magnitude. -/
def RepD (b : Nat) (x : BitVec 32) (v : Zq) : Prop :=
  -((b : Int) * 11082241) < x.toInt ∧ x.toInt < (b : Int) * 11082241 ∧ (x.toInt - (v.val : Int)) % 3329 = 0

theorem toInt_add32 {a b : BitVec 32} (h1 : -2147483648 ≤ a.toInt + b.toInt) (h2 : a.toInt + b.toInt < 2147483648) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [BitVec.toInt_add]; exact Int.bmod_eq_of_le (by simpa using h1) (by simpa using h2)

theorem toInt_sub32 {a b : BitVec 32} (h1 : -2147483648 ≤ a.toInt - b.toInt) (h2 : a.toInt - b.toInt < 2147483648) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [BitVec.toInt_sub]; exact Int.bmod_eq_of_le (by simpa using h1) (by simpa using h2)

/-- The product of an integer in `(-q, q)` and one in `[0, q)` is less than
`q²` in magnitude. -/
theorem mul_qq {a b : Int} (ha1 : -3329 < a) (ha2 : a < 3329) (hb1 : 0 ≤ b) (hb2 : b < 3329) :
    -11082241 < a * b ∧ a * b < 11082241 := by
  have hn : (a * b).natAbs ≤ 3328 * 3328 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by omega_arith) (by omega_arith)
  have h1 := Int.le_natAbs (a := a * b)
  have h2 := Int.le_natAbs (a := -(a * b))
  rw [Int.natAbs_neg] at h2
  omega_arith

/-- The congruence of the first doubleword of `pmadd_rep`, on integers:
`2¹⁶ · 169 = 3327 q + 1`. -/
theorem pmadd_id0 {M A0 A1 B0 B1 G γ k kG : Int} (d : M * 65536 - B1 * G = 3329 * k)
    (hG : G - γ * 65536 = 3329 * kG) :
    B0 * A0 + M * A1 - (A0 * B0 + A1 * B1 * γ) =
      3329 * (A1 * (169 * (B1 * kG + k) - 3327 * (M - B1 * γ))) := by
  grind

/-- The two doublewords of `BaseCaseMultiply` that `pmaddwd` leaves, from the
words `a₀, a₁, b₀, b₁` and `γ · 2¹⁶ mod q`. -/
theorem pmadd_rep {a0 a1 b0 b1 g : BitVec 16} {x0 x1 y0 y1 γ : Zq} (ha0 : a0.toNat = x0.val)
    (ha1 : a1.toNat = x1.val) (hb0 : b0.toNat = y0.val) (hb1 : b1.toNat = y1.val)
    (hg : g.toNat = γ.val * 65536 % 3329) :
    RepD 2 (mulWordsSigned b0 a0 + mulWordsSigned (montW b1 g) a1) (x0 * y0 + x1 * y1 * γ) ∧
      RepD 2 (mulWordsSigned b1 a0 + mulWordsSigned b0 a1) (x0 * y1 + x1 * y0) := by
  obtain ⟨A0, A0l, A0h⟩ := W.toInt_lt_q ha0
  obtain ⟨A1, A1l, A1h⟩ := W.toInt_lt_q ha1
  obtain ⟨B0, B0l, B0h⟩ := W.toInt_lt_q hb0
  obtain ⟨B1, B1l, B1h⟩ := W.toInt_lt_q hb1
  have hgl : g.toNat < 3329 := by rw [hg]; exact Nat.mod_lt _ (by decide)
  have G := W.toInt_of_lt hgl
  rw [hg] at G
  have Gl : 0 ≤ g.toInt ∧ g.toInt < 3329 := by
    rw [G]; exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (Nat.mod_lt _ (by decide))⟩
  have kG : ∃ k : Int, g.toInt - (γ.val : Int) * 65536 = 3329 * k :=
    ⟨-((γ.val : Int) * 65536 / 3329), by rw [G]; omega_using []⟩
  obtain ⟨kG, hkG⟩ := kG
  obtain ⟨ml, mh, ⟨k, d⟩⟩ := W.mont_small (d := b1) (z := g) (by omega_using [B1l]) (by omega_using [B1h])
    (by omega_using [Gl]) (by omega_using [Gl])
  have p1 := mul_qq (a := b0.toInt) (b := a0.toInt) (by omega_using [B0l]) B0h A0l A0h
  have p2 := mul_qq ml mh A1l A1h
  have p3 := mul_qq (a := b1.toInt) (b := a0.toInt) (by omega_using [B1l]) B1h A0l A0h
  have p4 := mul_qq (a := b0.toInt) (b := a1.toInt) (by omega_using [B0l]) B0h A1l A1h
  have S1 := toInt_add32 (a := mulWordsSigned b0 a0) (b := mulWordsSigned (montW b1 g) a1)
    (by rw [W.toInt_mulWordsSigned, W.toInt_mulWordsSigned]; omega_using [p1, p2])
    (by rw [W.toInt_mulWordsSigned, W.toInt_mulWordsSigned]; omega_using [p1, p2])
  have S2 := toInt_add32 (a := mulWordsSigned b1 a0) (b := mulWordsSigned b0 a1)
    (by rw [W.toInt_mulWordsSigned, W.toInt_mulWordsSigned]; omega_using [p3, p4])
    (by rw [W.toInt_mulWordsSigned, W.toInt_mulWordsSigned]; omega_using [p3, p4])
  rw [W.toInt_mulWordsSigned, W.toInt_mulWordsSigned] at S1 S2
  have v1 : ((x0 * y0 + x1 * y1 * γ).val : Int) = ((x0.val * y0.val + x1.val * y1.val * γ.val : Nat) : Int) % 3329 := by
    rw [val_add', val_mul, val_mul, val_mul, W.mulmod, ← Nat.add_mod]; exact Int.natCast_emod _ _
  have v2 : ((x0 * y1 + x1 * y0).val : Int) = ((x0.val * y1.val + x1.val * y0.val : Nat) : Int) % 3329 := by
    rw [val_add', val_mul, val_mul, ← Nat.add_mod]; exact Int.natCast_emod _ _
  refine ⟨⟨by rw [S1]; omega_using [p1, p2], by rw [S1]; omega_using [p1, p2], ?_⟩,
    ⟨by rw [S2]; omega_using [p3, p4], by rw [S2]; omega_using [p3, p4], ?_⟩⟩
  · rw [S1, v1]
    have h := pmadd_id0 (A0 := a0.toInt) (A1 := a1.toInt) (B0 := b0.toInt) d hkG
    simp only [A0, A1, B0, B1] at h ⊢
    simp only [Int.natCast_add, Int.natCast_mul] at h ⊢
    generalize (x0.val : Int) * y0.val + x1.val * y1.val * γ.val = X at h ⊢
    omega_using [h]
  · rw [S2, v2]
    simp only [A0, A1, B0, B1]
    simp only [Int.natCast_add, Int.natCast_mul]
    have e : (y1.val : Int) * x0.val + (y0.val : Int) * x1.val = (x0.val : Int) * y1.val + (x1.val : Int) * y0.val := by
      rw [Int.mul_comm, Int.mul_comm (y0.val : Int)]
    rw [e]
    omega_using []

/-- The sum of two doublewords keeps their congruences, within the sum of
their bounds (at most `8q²`, so without overflow). -/
theorem RepD.add {b c : Nat} {x x' : BitVec 32} {v v' : Zq} (h : RepD b x v) (h' : RepD c x' v') (hbc : b + c ≤ 8) :
    RepD (b + c) (x + x') (v + v') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  have hb : ((b + c : Nat) : Int) * 11082241 ≤ 88657928 := by
    have := Int.ofNat_le.mpr hbc; push_cast at this ⊢; omega_arith
  have S := toInt_add32 (a := x) (b := x') (by push_cast at hb; omega_arith) (by push_cast at hb; omega_arith)
  have hv : ((v + v').val : Int) = ((v.val + v'.val : Nat) : Int) % 3329 := by
    rw [val_add']; exact Int.natCast_emod _ _
  refine ⟨by rw [S]; push_cast; omega_arith, by rw [S]; push_cast; omega_arith, ?_⟩
  rw [S, hv]
  push_cast
  omega_arith

/-- A doubleword that fits a signed word, as that word. -/
theorem toInt_setWidth16 {y : BitVec 32} (h1 : -32768 ≤ y.toInt) (h2 : y.toInt < 32768) :
    (y.setWidth 16).toInt = y.toInt := by
  have hy := y.isLt
  rw [W.toInt16, BitVec.toNat_setWidth, show (2 : Nat) ^ 16 = 65536 from rfl]
  rw [W.toInt32] at h1 h2 ⊢
  by_cases c : y.toNat < 2147483648
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c)] at h1 h2 ⊢
    by_cases c2 : y.toNat % 65536 < 32768
    · rw [ite_eq_left_of_eq_true _ _ (eq_true c2)]; omega_using [h2]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false c2)]; omega_using [h2, c2]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false c)] at h1 h2 ⊢
    by_cases c2 : y.toNat % 65536 < 32768
    · rw [ite_eq_left_of_eq_true _ _ (eq_true c2)]; omega_using [h1, c2]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false c2)]; omega_using [h1]

/-- The doubleword `predD` leaves of `x`: `(x - (x q⁻¹ mod± 2¹⁶) q) / 2¹⁶`. -/
def redD (x : BitVec 32) : BitVec 32 :=
  (x - mulWordsSigned ((mulWordsSigned (x.extractLsb' 0 16) qinvW).extractLsb' 0 16) qW).sshiftRight 16

/-- The word that `packssdw` makes of `redD x` represents `v` times `2⁻¹⁶`
within `q`, for a doubleword `x ≡ v` less than `8q²` in magnitude. -/
theorem redD_rep {b : Nat} {x : BitVec 32} {v : Zq} (h : RepD b x v) (hb : b ≤ 8) :
    RepR 1 (satSignedWord (redD x)) v := by
  obtain ⟨h1, h2, h3⟩ := h
  have hb' : (b : Int) * 11082241 ≤ 88657928 := by have := Int.ofNat_le.mpr hb; omega_arith
  generalize hL : x.extractLsb' 0 16 = L
  have hL' := W.toInt_lo x
  rw [hL] at hL'
  generalize hT : (mulWordsSigned L qinvW).extractLsb' 0 16 = T
  have hT' := W.toInt_lo (mulWordsSigned L qinvW)
  rw [hT, W.toInt_mulWordsSigned, W.qinvW_toInt] at hT'
  have bT := W.toInt16_bounds T
  have eM : (mulWordsSigned T qW).toInt = T.toInt * 3329 := by rw [W.toInt_mulWordsSigned, W.qW_toInt]
  have S := toInt_sub32 (a := x) (b := mulWordsSigned T qW) (by rw [eM]; omega_arith) (by rw [eM]; omega_arith)
  rw [eM] at S
  have hc : (x.toInt - T.toInt * 3329) % 65536 = 0 := by omega_arith
  have eR : (redD x).toInt = (x.toInt - T.toInt * 3329) / 65536 := by
    rw [redD, hL, hT, BitVec.toInt_sshiftRight, S, Int.shiftRight_eq_div_pow,
      show ((2 ^ 16 : Nat) : Int) = 65536 from rfl]
  have r1 : -3329 < (redD x).toInt := by rw [eR]; omega_arith
  have r2 : (redD x).toInt < 3329 := by rw [eR]; omega_arith
  have eS : (satSignedWord (redD x)).toInt = (redD x).toInt := by
    rw [satSignedWord, ifn (by omega_using [r2]), ifn (by omega_using [r1])]
    exact toInt_setWidth16 (by omega_using [r1]) (by omega_using [r2])
  refine ⟨by rw [eS]; omega_using [r1], by rw [eS]; omega_using [r2], ?_⟩
  rw [eS, eR]
  omega_arith

/-- `montW w (R² mod q)` represents `v` within `q` for a word `w` with
`w · 2¹⁶ ≡ v`. -/
theorem red2_rep {b : Nat} {w : BitVec 16} {v : Zq} (h : RepR b w v) (hb : b ≤ 9) : Rep 1 (montW w r2W) v := by
  obtain ⟨h1, h2, h3⟩ := h
  have hb' : (b : Int) * 3329 ≤ 29961 := by have := Int.ofNat_le.mpr hb; omega_arith
  have hr := W.r2W_toInt
  have hn : (w.toInt * r2W.toInt).natAbs ≤ 29961 * 1353 := by
    rw [Int.natAbs_mul, hr]; exact Nat.mul_le_mul (by omega_arith) (by decide)
  have n1 := Int.le_natAbs (a := w.toInt * r2W.toInt)
  have n2 := Int.le_natAbs (a := -(w.toInt * r2W.toInt))
  rw [Int.natAbs_neg] at n2
  obtain ⟨m1, m2, m3⟩ := W.montW_spec (d := w) (z := r2W) (by omega_arith) (by omega_arith)
  rw [hr] at m3
  have e := W.cancel_R (Y := (v.val : Int)) m3 (by omega_using [h3])
  refine ⟨by omega_using [m1], by omega_using [m2], ?_⟩
  omega_using [e]

/-! ## The SSE2 code of each lane -/

/-- `deintS` of `g`, with `xmm5` for its temporary (`xmm11` holds a sum). -/
theorem deintS_ok6' (s : State) :
    WP isa (.block (deintS .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm5)) s fun s' =>
      (s'.xmm .xmm6 = deE (s.xmm .xmm6) (s.xmm .xmm7) (s.xmm .xmm8) (s.xmm .xmm9) ∧
        s'.xmm .xmm10 = deO (s.xmm .xmm6) (s.xmm .xmm7) (s.xmm .xmm8) (s.xmm .xmm9)) ∧
      XOnly [.xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm5] s s' := by
  simp only [deintS]
  vrunm [eval_movdqa]
  exact ⟨⟨rfl, rfl⟩, by xonly⟩

theorem dword_pmaddwd (a b : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .pmaddwd a b) i = mulWordsSigned (word a (2 * i)) (word b (2 * i)) +
      mulWordsSigned (word a (2 * i + 1)) (word b (2 * i + 1)) := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [XBinOp.eval]

theorem dword_psrad (a : BitVec 128) (n : BitVec 8) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrad a n) i = (dword a i).sshiftRight (min n.toNat 32) := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [XShiftOp.eval]

/-- The doublewords of `x` are pairs of coefficients: `f₀ i` in the low word
of doubleword `i` and `f₁ i` in the high one. -/
def PLanes (x : BitVec 128) (f₀ f₁ : Nat → Zq) : Prop :=
  ∀ i < 4, (word x (2 * i)).toNat = (f₀ i).val ∧ (word x (2 * i + 1)).toNat = (f₁ i).val

/-- The doublewords of `x` are congruent to `f 0, …, f 3`, within `b q²`. -/
def DLanes (b : Nat) (x : BitVec 128) (f : Nat → Zq) : Prop := ∀ i < 4, RepD b (dword x i) (f i)

theorem word_qD0 {i : Nat} (hi : i < 4) : word qD (2 * i) = qW := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> decide

theorem word_qD1 {i : Nat} (hi : i < 4) : word qD (2 * i + 1) = 0 := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> decide

theorem mulWordsSigned_zero (a : BitVec 16) : mulWordsSigned a 0 = 0 := by
  rw [mulWordsSigned, show (0 : BitVec 16).signExtend 32 = 0 from by decide]
  exact BitVec.mul_zero

/-- What `predD` leaves in each doubleword. -/
theorem dword_predD (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrad (XBinOp.eval .psubd x (XBinOp.eval .pmaddwd (XBinOp.eval .pmullw x qinvV)
      (XShiftOp.eval .psrld qV 16))) 16) i = redD (dword x i) := by
  have w0 := word_dword x hi 0 (by decide)
  rw [Nat.add_zero, Nat.mul_zero] at w0
  have z : ∀ y : BitVec 32, y + 0 = y := fun y => BitVec.add_zero y
  rw [dword_psrad _ _ hi, dword_psubd _ _ hi, dword_pmaddwd _ _ hi, word_pmullw _ _ (by omega_arith),
    word_pmullw _ _ (by omega_arith), show XShiftOp.eval .psrld qV 16 = qD from by decide, word_qD0 hi, word_qD1 hi,
    mulWordsSigned_zero, z, word_qinvV (by omega_arith), w0]
  rfl

theorem ptermSet_ok {s : State} (hc : VConsts s) {x0 x1 y0 y1 γ : Nat → Zq}
    (h0 : PLanes (s.xmm .xmm0) x0 x1) (h1 : PLanes (s.xmm .xmm1) (fun i => x0 (4 + i)) (fun i => x1 (4 + i)))
    (h6 : Lanes (s.xmm .xmm6) y0) (h10 : Lanes (s.xmm .xmm10) y1) (h13 : ZLanes (s.xmm .xmm13) γ) :
    WP isa (.block ptermSet) s fun s' =>
      (DLanes 2 (s'.xmm .xmm11) (fun i => x0 i * y0 i + x1 i * y1 i * γ i) ∧
        DLanes 2 (s'.xmm .xmm2) (fun i => x0 (4 + i) * y0 (4 + i) + x1 (4 + i) * y1 (4 + i) * γ (4 + i)) ∧
        DLanes 2 (s'.xmm .xmm12) (fun i => x0 i * y1 i + x1 i * y0 i) ∧
        DLanes 2 (s'.xmm .xmm3) (fun i => x0 (4 + i) * y1 (4 + i) + x1 (4 + i) * y0 (4 + i))) ∧
      XOnly [.xmm4, .xmm5, .xmm11, .xmm2, .xmm12, .xmm3] s s' := by
  rw [ptermSet, pterm, WP.block_append_iff]
  refine WP.mono (movmont_ok (d := .xmm4) (src := .xmm10) (z := .xmm13) (t := .xmm5) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc) fun s1 ⟨l1, o1⟩ => ?_
  have e0 : s1.xmm .xmm0 = s.xmm .xmm0 := o1.xmm _ (by decide)
  have e1 : s1.xmm .xmm1 = s.xmm .xmm1 := o1.xmm _ (by decide)
  have e6 : s1.xmm .xmm6 = s.xmm .xmm6 := o1.xmm _ (by decide)
  have e10 : s1.xmm .xmm10 = s.xmm .xmm10 := o1.xmm _ (by decide)
  simp only [xmov, xb]
  vrun [eval_movdqa]
  rw [e0, e1, e6, e10]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
  · rw [dword_pmaddwd _ _ hi, word_punpcklwd _ _ (by omega_arith), word_punpcklwd _ _ (by omega_arith),
      ifp (by omega_arith), ifn (by omega_arith), show 2 * i / 2 = i by omega_arith,
      show (2 * i + 1) / 2 = i by omega_arith, l1 i (by omega_arith)]
    exact (pmadd_rep (h0 i hi).1 (h0 i hi).2 (h6 i (by omega_arith)) (h10 i (by omega_arith))
      (h13 i (by omega_arith))).1
  · rw [dword_pmaddwd _ _ hi, word_punpckhwd _ _ (by omega_arith), word_punpckhwd _ _ (by omega_arith),
      ifp (by omega_arith), ifn (by omega_arith), show 2 * i / 2 = i by omega_arith,
      show (2 * i + 1) / 2 = i by omega_arith, l1 (4 + i) (by omega_arith)]
    exact (pmadd_rep (h1 i hi).1 (h1 i hi).2 (h6 (4 + i) (by omega_arith)) (h10 (4 + i) (by omega_arith))
      (h13 (4 + i) (by omega_arith))).1
  · rw [dword_pmaddwd _ _ hi, word_punpcklwd _ _ (by omega_arith), word_punpcklwd _ _ (by omega_arith),
      ifp (by omega_arith), ifn (by omega_arith), show 2 * i / 2 = i by omega_arith,
      show (2 * i + 1) / 2 = i by omega_arith]
    exact (pmadd_rep (g := 0) (γ := 0) (h0 i hi).1 (h0 i hi).2 (h6 i (by omega_arith)) (h10 i (by omega_arith))
      (by decide)).2
  · rw [dword_pmaddwd _ _ hi, word_punpckhwd _ _ (by omega_arith), word_punpckhwd _ _ (by omega_arith),
      ifp (by omega_arith), ifn (by omega_arith), show 2 * i / 2 = i by omega_arith,
      show (2 * i + 1) / 2 = i by omega_arith]
    exact (pmadd_rep (g := 0) (γ := 0) (h1 i hi).1 (h1 i hi).2 (h6 (4 + i) (by omega_arith))
      (h10 (4 + i) (by omega_arith)) (by decide)).2
  · refine (o1.trans (rs' := [.xmm11, .xmm2, .xmm12, .xmm3]) ?_).mono (by simp)
    xonly

theorem ptermAdd_ok {s : State} (hc : VConsts s) {x0 x1 y0 y1 γ : Nat → Zq}
    (h0 : PLanes (s.xmm .xmm0) x0 x1) (h1 : PLanes (s.xmm .xmm1) (fun i => x0 (4 + i)) (fun i => x1 (4 + i)))
    (h6 : Lanes (s.xmm .xmm6) y0) (h10 : Lanes (s.xmm .xmm10) y1) (h13 : ZLanes (s.xmm .xmm13) γ)
    {c : Nat} (hc8 : c + 2 ≤ 8) {u0 u1 v0 v1 : Nat → Zq} (h11 : DLanes c (s.xmm .xmm11) u0)
    (h2 : DLanes c (s.xmm .xmm2) u1) (h12 : DLanes c (s.xmm .xmm12) v0) (h3 : DLanes c (s.xmm .xmm3) v1) :
    WP isa (.block ptermAdd) s fun s' =>
      (DLanes (c + 2) (s'.xmm .xmm11) (fun i => u0 i + (x0 i * y0 i + x1 i * y1 i * γ i)) ∧
        DLanes (c + 2) (s'.xmm .xmm2)
          (fun i => u1 i + (x0 (4 + i) * y0 (4 + i) + x1 (4 + i) * y1 (4 + i) * γ (4 + i))) ∧
        DLanes (c + 2) (s'.xmm .xmm12) (fun i => v0 i + (x0 i * y1 i + x1 i * y0 i)) ∧
        DLanes (c + 2) (s'.xmm .xmm3) (fun i => v1 i + (x0 (4 + i) * y1 (4 + i) + x1 (4 + i) * y0 (4 + i)))) ∧
      XOnly [.xmm4, .xmm5, .xmm7, .xmm8, .xmm9, .xmm11, .xmm2, .xmm12, .xmm3] s s' := by
  rw [ptermAdd, pterm, List.append_assoc, WP.block_append_iff]
  refine WP.mono (movmont_ok (d := .xmm4) (src := .xmm10) (z := .xmm13) (t := .xmm5) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc) fun s1 ⟨l1, o1⟩ => ?_
  have e0 : s1.xmm .xmm0 = s.xmm .xmm0 := o1.xmm _ (by decide)
  have e1 : s1.xmm .xmm1 = s.xmm .xmm1 := o1.xmm _ (by decide)
  have e6 : s1.xmm .xmm6 = s.xmm .xmm6 := o1.xmm _ (by decide)
  have e10 : s1.xmm .xmm10 = s.xmm .xmm10 := o1.xmm _ (by decide)
  have e11 : s1.xmm .xmm11 = s.xmm .xmm11 := o1.xmm _ (by decide)
  have e2 : s1.xmm .xmm2 = s.xmm .xmm2 := o1.xmm _ (by decide)
  have e12 : s1.xmm .xmm12 = s.xmm .xmm12 := o1.xmm _ (by decide)
  have e3 : s1.xmm .xmm3 = s.xmm .xmm3 := o1.xmm _ (by decide)
  simp only [xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [e0, e1, e6, e10, e11, e2, e12, e3]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
  · rw [dword_paddd _ _ hi, dword_pmaddwd _ _ hi, word_punpcklwd _ _ (by omega_arith),
      word_punpcklwd _ _ (by omega_arith), ifp (by omega_arith), ifn (by omega_arith),
      show 2 * i / 2 = i by omega_arith, show (2 * i + 1) / 2 = i by omega_arith, l1 i (by omega_arith)]
    exact (h11 i hi).add (pmadd_rep (h0 i hi).1 (h0 i hi).2 (h6 i (by omega_arith)) (h10 i (by omega_arith))
      (h13 i (by omega_arith))).1 hc8
  · rw [dword_paddd _ _ hi, dword_pmaddwd _ _ hi, word_punpckhwd _ _ (by omega_arith),
      word_punpckhwd _ _ (by omega_arith), ifp (by omega_arith), ifn (by omega_arith),
      show 2 * i / 2 = i by omega_arith, show (2 * i + 1) / 2 = i by omega_arith, l1 (4 + i) (by omega_arith)]
    exact (h2 i hi).add (pmadd_rep (h1 i hi).1 (h1 i hi).2 (h6 (4 + i) (by omega_arith))
      (h10 (4 + i) (by omega_arith)) (h13 (4 + i) (by omega_arith))).1 hc8
  · rw [dword_paddd _ _ hi, dword_pmaddwd _ _ hi, word_punpcklwd _ _ (by omega_arith),
      word_punpcklwd _ _ (by omega_arith), ifp (by omega_arith), ifn (by omega_arith),
      show 2 * i / 2 = i by omega_arith, show (2 * i + 1) / 2 = i by omega_arith]
    exact (h12 i hi).add (pmadd_rep (g := 0) (γ := 0) (h0 i hi).1 (h0 i hi).2 (h6 i (by omega_arith))
      (h10 i (by omega_arith)) (by decide)).2 hc8
  · rw [dword_paddd _ _ hi, dword_pmaddwd _ _ hi, word_punpckhwd _ _ (by omega_arith),
      word_punpckhwd _ _ (by omega_arith), ifp (by omega_arith), ifn (by omega_arith),
      show 2 * i / 2 = i by omega_arith, show (2 * i + 1) / 2 = i by omega_arith]
    exact (h3 i hi).add (pmadd_rep (g := 0) (γ := 0) (h1 i hi).1 (h1 i hi).2 (h6 (4 + i) (by omega_arith))
      (h10 (4 + i) (by omega_arith)) (by decide)).2 hc8
  · refine (o1.trans (rs' := [.xmm5, .xmm7, .xmm8, .xmm9, .xmm11, .xmm2, .xmm12, .xmm3]) ?_).mono (by simp)
    xonly

/-- `pred`: the sums as words, each representing its coefficient times
`2⁻¹⁶` within `q`: the first coefficients in `xmm11` and the second in
`xmm12`. -/
theorem pred_ok {s : State} (hc : VConsts s) {c : Nat} (hc8 : c ≤ 8) {u0 u1 v0 v1 : Nat → Zq}
    (h11 : DLanes c (s.xmm .xmm11) u0) (h2 : DLanes c (s.xmm .xmm2) u1) (h12 : DLanes c (s.xmm .xmm12) v0)
    (h3 : DLanes c (s.xmm .xmm3) v1) :
    WP isa (.block pred) s fun s' =>
      LanesR (RepR 1) (s'.xmm .xmm11) (fun e => if e < 4 then u0 e else u1 (e - 4)) ∧
      LanesR (RepR 1) (s'.xmm .xmm12) (fun e => if e < 4 then v0 e else v1 (e - 4)) ∧
      XOnly [.xmm7, .xmm5, .xmm11, .xmm2, .xmm12, .xmm3] s s' := by
  simp only [pred, predD, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv]
  refine ⟨fun e he => ?_, fun e he => ?_, by xonly⟩
  · rw [word_packssdw _ _ he]
    dsimp only
    split
    · rw [dword_predD _ (by omega_arith)]; exact redD_rep (h11 e (by omega_arith)) hc8
    · rw [dword_predD _ (by omega_arith)]; exact redD_rep (h2 (e - 4) (by omega_arith)) hc8
  · rw [word_packssdw _ _ he]
    dsimp only
    split
    · rw [dword_predD _ (by omega_arith)]; exact redD_rep (h12 e (by omega_arith)) hc8
    · rw [dword_predD _ (by omega_arith)]; exact redD_rep (h3 (e - 4) (by omega_arith)) hc8

/-- The sums, times `R² mod q` (in `xmm13`) and made canonical. -/
theorem accRed_ok {s : State} (hc : VConsts s) :
    WP isa (.block (vmont .xmm11 .xmm13 .xmm3 ++ vcadd .xmm11 .xmm3 ++ vmont .xmm12 .xmm13 .xmm3 ++
        vcadd .xmm12 .xmm3)) s fun s' =>
      (∀ i < 8, word (s'.xmm .xmm11) i = W.caddW (W.montW (word (s.xmm .xmm11) i) (word (s.xmm .xmm13) i))) ∧
      (∀ i < 8, word (s'.xmm .xmm12) i = W.caddW (W.montW (word (s.xmm .xmm12) i) (word (s.xmm .xmm13) i))) ∧
      XOnly [.xmm11, .xmm12, .xmm3] s s' := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (vmont_ok (d := .xmm11) (z := .xmm13) (t := .xmm3) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc) fun s1 ⟨l1, o1⟩ => ?_
  have c1 := o1.consts hc (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (vcadd_ok (d := .xmm11) (t := .xmm3) (by decide) (by decide) c1) fun s2 ⟨l2, o2⟩ => ?_
  have c2 := o2.consts c1 (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (vmont_ok (d := .xmm12) (z := .xmm13) (t := .xmm3) (by decide) (by decide) (by decide)
    (by decide) (by decide) c2) fun s3 ⟨l3, o3⟩ => ?_
  have c3 := o3.consts c2 (by decide) (by decide)
  refine WP.mono (vcadd_ok (d := .xmm12) (t := .xmm3) (by decide) (by decide) c3) fun s4 ⟨l4, o4⟩ =>
    ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [o4.xmm _ (by decide), o3.xmm _ (by decide), l2 i hi]; dsimp only; rw [l1 i hi]
  · rw [l4 i hi]; dsimp only
    rw [l3 i hi, o2.xmm _ (by decide), o1.xmm _ (by decide), o2.xmm _ (by decide), o1.xmm _ (by decide)]
  · exact (o1.trans (o2.trans (o3.trans o4))).mono (by simp)

/-- The sums' words interleaved: `vpunpck{l,h}wd` of `ymm11` and `ymm12`, in
a lane. -/
theorem unpkR_ok (t : State) :
    WP isa (.block [xb .movdqa .xmm10 .xmm11, xb .punpcklwd .xmm10 .xmm12, xb .movdqa .xmm9 .xmm11,
        xb .punpckhwd .xmm9 .xmm12]) t fun t' =>
      (t'.xmm .xmm10 = XBinOp.eval .punpcklwd (t.xmm .xmm11) (t.xmm .xmm12) ∧
        t'.xmm .xmm9 = XBinOp.eval .punpckhwd (t.xmm .xmm11) (t.xmm .xmm12)) ∧ XOnly [.xmm10, .xmm9] t t' := by
  simp only [xb]
  vrun [eval_movdqa]
  exact ⟨trivial, by xonly⟩

theorem lane_deintS6' : laneSseBlock (toY (deintS .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm5)) =
    some (deintS .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm5) := by decide +kernel
theorem lane_ptermSet : laneSseBlock (toY ptermSet) = some ptermSet := by decide +kernel
theorem lane_ptermAdd : laneSseBlock (toY ptermAdd) = some ptermAdd := by decide +kernel
theorem lane_pred : laneSseBlock (toY pred) = some pred := by decide +kernel
theorem lane_accRed : laneSseBlock (toY (vmont .xmm11 .xmm13 .xmm3 ++ vcadd .xmm11 .xmm3 ++
    vmont .xmm12 .xmm13 .xmm3 ++ vcadd .xmm12 .xmm3)) =
    some (vmont .xmm11 .xmm13 .xmm3 ++ vcadd .xmm11 .xmm3 ++ vmont .xmm12 .xmm13 .xmm3 ++ vcadd .xmm12 .xmm3) := by
  decide +kernel
theorem lane_unpkR : laneSseBlock [yb .vpunpcklwd .xmm10 .xmm11 .xmm12, yb .vpunpckhwd .xmm9 .xmm11 .xmm12] =
    some [xb .movdqa .xmm10 .xmm11, xb .punpcklwd .xmm10 .xmm12, xb .movdqa .xmm9 .xmm11,
      xb .punpckhwd .xmm9 .xmm12] := by
  decide +kernel

/-! ## A product of a block -/

theorem yload4o_ok {p : Reg} {o : Nat} {a b c d : XReg} (hd : [a, b, c, d].Nodup) {s : State}
    (h : ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 (o + 32 * t)) 32) :
    WP isa (.block (yload4o p o a b c d)) s fun s' =>
      (∀ l < 2, s'.lane a l = s.mem.readW (s.gpr p + BitVec.ofNat 64 (o + 32 * 0) + BitVec.ofNat 64 (16 * l)) 128 ∧
        s'.lane b l = s.mem.readW (s.gpr p + BitVec.ofNat 64 (o + 32 * 1) + BitVec.ofNat 64 (16 * l)) 128 ∧
        s'.lane c l = s.mem.readW (s.gpr p + BitVec.ofNat 64 (o + 32 * 2) + BitVec.ofNat 64 (16 * l)) 128 ∧
        s'.lane d l = s.mem.readW (s.gpr p + BitVec.ofNat 64 (o + 32 * 3) + BitVec.ofNat 64 (16 * l)) 128) ∧
      YOnly [a, b, c, d] s s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true, not_false_eq_true] at hd
  obtain ⟨⟨ab, ac, ad⟩, ⟨bc, bd⟩, cd⟩ := hd
  simp only [yload4o]
  rw [show ∀ x y z w : Instr, [x, y, z, w] = [x] ++ [y] ++ [z] ++ [w] from fun _ _ _ _ => rfl,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (yld_ok (off := o) (h 0 (by decide))) fun s1 ⟨l1, o1⟩ => ?_
  have r1 : InRegions (s1.rd ++ s1.wr) (s1.gpr p + BitVec.ofNat 64 (o + 32)) 32 := by
    rw [o1.rd, o1.wr, o1.gpr]; exact h 1 (by decide)
  refine WP.mono (yld_ok r1) fun s2 ⟨l2, o2⟩ => ?_
  have r2 : InRegions (s2.rd ++ s2.wr) (s2.gpr p + BitVec.ofNat 64 (o + 64)) 32 := by
    rw [o2.rd, o2.wr, o2.gpr, o1.rd, o1.wr, o1.gpr]; exact h 2 (by decide)
  refine WP.mono (yld_ok r2) fun s3 ⟨l3, o3⟩ => ?_
  have r3 : InRegions (s3.rd ++ s3.wr) (s3.gpr p + BitVec.ofNat 64 (o + 96)) 32 := by
    rw [o3.rd, o3.wr, o3.gpr, o2.rd, o2.wr, o2.gpr, o1.rd, o1.wr, o1.gpr]; exact h 3 (by decide)
  refine WP.mono (yld_ok r3) fun s4 ⟨l4, o4⟩ => ⟨fun l hl => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [o4.lane _ (by simpa using ad) l hl, o3.lane _ (by simpa using ac) l hl,
      o2.lane _ (by simpa using ab) l hl, l1 l hl, Nat.mul_zero, Nat.add_zero]
  · rw [o4.lane _ (by simpa using bd) l hl, o3.lane _ (by simpa using bc) l hl, l2 l hl,
      o1.gpr, o1.mem]
  · rw [o4.lane _ (by simpa using cd) l hl, l3 l hl, o2.gpr, o2.mem, o1.gpr, o1.mem]
  · rw [l4 l hl, o3.gpr, o3.mem, o2.gpr, o2.mem, o1.gpr, o1.mem]
  · exact ((o1.trans o2).trans (o3.trans o4)).mono (by simp)

/-- The address of the `t`-th load of `f` in a product at `d` bytes. -/
theorem addrO (p : Addr) (b d t : Nat) :
    coeffAddr p (32 * b) + BitVec.ofNat 64 (d + 32 * t) =
      coeffAddr (p + BitVec.ofNat 64 d) (32 * b) + BitVec.ofNat 64 (32 * t) := by
  simp only [coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (p + ·) (congrArg _ (by omega_arith))

theorem addrBF (p : Addr) (b d t : Nat) :
    coeffAddr p (32 * b) + BitVec.ofNat 64 (d + 32 * t) = p + BitVec.ofNat 64 d + BitVec.ofNat 64 (128 * b + 32 * t) := by
  simp only [coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (p + ·) (congrArg _ (by omega_arith))

/-- How the polynomials `f` of a row are stored, `o` bytes apart: their
predicate `Is` (with the frame it keeps, of `sz` bytes), the code `ld j` that
loads the 32 coefficients of a block of polynomial `j` from `rsi + o j` as
`rowLdY` does (as pairs, `PLanes`: those of the pairs `pairY b l 0, …, 3` in
lane `l` of `ymm0` and of the next four in `ymm1`), and the bytes `st`
(`stv`) of a block, which `rsi` moves on. -/
structure FRep (o : Nat) where
  ld : Nat → List Instr
  stv : BitVec 32
  st : Nat
  sz : Nat
  Is : Mem → Addr → Poly → Prop
  hst : BitVec.signExtend 64 stv = BitVec.ofNat 64 st
  frame : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' → ∀ {p : Addr} {F : Poly},
    (∀ r ∈ rs, Region.Disjoint ⟨p, sz⟩ r) → Is m p F → Is m' p F
  ok : ∀ {fB : Addr} {F : Poly} {b j : Nat} {s : State}, b < 8 →
    s.gpr .rsi = fB + BitVec.ofNat 64 (st * b) → Is s.mem (fB + BitVec.ofNat 64 (o * j)) F →
    InRegions (s.rd ++ s.wr) (fB + BitVec.ofNat 64 (o * j)) sz →
    WP isa (.block (ld j)) s fun s' =>
      (∀ l < 2, PLanes (s'.lane .xmm0 l) (fun i => F[2 * pairY b l i]!) (fun i => F[2 * pairY b l i + 1]!) ∧
        PLanes (s'.lane .xmm1 l) (fun i => F[2 * pairY b l (4 + i)]!) (fun i => F[2 * pairY b l (4 + i) + 1]!)) ∧
      YOnly [.xmm0, .xmm1, .xmm8, .xmm9] s s'

/-- What `rowLdY`'s `vpackssdw` do to each lane. -/
theorem packF_ok (s : State) :
    WP isa (.block [xb .packssdw .xmm0 .xmm1, xb .movdqa .xmm1 .xmm8, xb .packssdw .xmm1 .xmm9]) s fun s' =>
      (s'.xmm .xmm0 = XBinOp.eval .packssdw (s.xmm .xmm0) (s.xmm .xmm1) ∧
        s'.xmm .xmm1 = XBinOp.eval .packssdw (s.xmm .xmm8) (s.xmm .xmm9)) ∧ XOnly [.xmm0, .xmm1] s s' := by
  simp only [xb]
  vrun [eval_movdqa]
  exact ⟨trivial, by xonly⟩

theorem lane_packF : laneSseBlock [yb .vpackssdw .xmm0 .xmm0 .xmm1, yb .vpackssdw .xmm1 .xmm8 .xmm9] =
    some [xb .packssdw .xmm0 .xmm1, xb .movdqa .xmm1 .xmm8, xb .packssdw .xmm1 .xmm9] := by decide +kernel

/-- `rowLdY`: the coefficients of block `b` of `F` (`u32`s at `fB + o j`), as
pairs in `vbase`'s order. -/
theorem ld32_ok {o : Nat} {fB : Addr} {F : Poly} {b j : Nat} {s : State} (hb : b < 8)
    (hrsi : s.gpr .rsi = fB + BitVec.ofNat 64 (128 * b)) (hF : PolyIs s.mem (fB + BitVec.ofNat 64 (o * j)) F)
    (rF : InRegions (s.rd ++ s.wr) (fB + BitVec.ofNat 64 (o * j)) 1024) :
    WP isa (.block (rowLdY o j)) s fun s' =>
      (∀ l < 2, PLanes (s'.lane .xmm0 l) (fun i => F[2 * pairY b l i]!) (fun i => F[2 * pairY b l i + 1]!) ∧
        PLanes (s'.lane .xmm1 l) (fun i => F[2 * pairY b l (4 + i)]!) (fun i => F[2 * pairY b l (4 + i) + 1]!)) ∧
      YOnly [.xmm0, .xmm1, .xmm8, .xmm9] s s' := by
  have hrsi' : s.gpr .rsi = coeffAddr fB (32 * b) := by
    rw [hrsi, coeffAddr]; exact congrArg (fB + ·) (congrArg _ (by omega_arith))
  have rF' : ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (o * j + 32 * t)) 32 := fun t ht => by
    rw [hrsi', addrBF]; exact CallLay.inRegions_sub rF (by omega_arith) (by omega_arith)
  simp only [rowLdY]
  rw [WP.block_append_iff]
  refine WP.mono (yload4o_ok (p := .rsi) (a := .xmm0) (b := .xmm1) (c := .xmm8) (d := .xmm9) (by decide) rF')
    fun s1 ⟨A1, o1⟩ => ?_
  refine WP.mono (ylanes lane_packF (P := fun l t =>
      t.xmm .xmm0 = XBinOp.eval .packssdw (s1.lane .xmm0 l) (s1.lane .xmm1 l) ∧
      t.xmm .xmm1 = XBinOp.eval .packssdw (s1.lane .xmm8 l) (s1.lane .xmm9 l))
    fun l _ => packF_ok (s1.proj l)) fun s2 ⟨D2, o2⟩ => ⟨fun l hl => ?_, (o1.trans o2).mono (by simp)⟩
  -- the four coefficients of load `t` of the block, in lane `l`
  have rd : ∀ t, s.mem.readW (coeffAddr fB (32 * b) + BitVec.ofNat 64 (o * j + 32 * t) + BitVec.ofNat 64 (16 * l)) 128 =
      s.mem.readW (coeffAddr (fB + BitVec.ofNat 64 (o * j)) (32 * b + 8 * t + 4 * l)) 128 := fun t => by
    rw [addrO, show 32 * t = 4 * (8 * t) by omega_arith, coeffAddr_off, show 16 * l = 4 * (4 * l) by omega_arith,
      coeffAddr_off]
  have e0 : s2.lane .xmm0 l = _ := (D2 l hl).1
  have e1 : s2.lane .xmm1 l = _ := (D2 l hl).2
  have L0 := lanes_pack2 hF (j := 32 * b + 8 * 0 + 4 * l) (j' := 32 * b + 8 * 1 + 4 * l) (by omega_arith)
    (by omega_arith)
  have L1 := lanes_pack2 hF (j := 32 * b + 8 * 2 + 4 * l) (j' := 32 * b + 8 * 3 + 4 * l) (by omega_arith)
    (by omega_arith)
  rw [e0, e1, (A1 l hl).1, (A1 l hl).2.1, (A1 l hl).2.2.1, (A1 l hl).2.2.2, hrsi', rd, rd, rd, rd]
  refine ⟨fun i hi => ⟨?_, ?_⟩, fun i hi => ⟨?_, ?_⟩⟩
  · refine (L0 (2 * i) (by omega_arith)).trans (congrArg Fin.val ?_)
    dsimp only
    split <;> exact congrArg (F[·]!) (by unfold pairY; omega_arith)
  · refine (L0 (2 * i + 1) (by omega_arith)).trans (congrArg Fin.val ?_)
    dsimp only
    split <;> exact congrArg (F[·]!) (by unfold pairY; omega_arith)
  · refine (L1 (2 * i) (by omega_arith)).trans (congrArg Fin.val ?_)
    dsimp only
    split <;> exact congrArg (F[·]!) (by unfold pairY; omega_arith)
  · refine (L1 (2 * i + 1) (by omega_arith)).trans (congrArg Fin.val ?_)
    dsimp only
    split <;> exact congrArg (F[·]!) (by unfold pairY; omega_arith)

/-- The polynomials of `u32`s (`PolyIs`), `o` bytes apart. -/
def FRep.u32 (o : Nat) : FRep o where
  ld := rowLdY o
  stv := 128
  st := 128
  sz := 1024
  Is := PolyIs
  hst := by decide
  frame := fun hf _ _ hd h => polyIs_frame hf hd h
  ok := fun hb hrsi hF rF => ld32_ok hb hrsi hF rF

/-- The address of the `t`-th load of product `j` of block `b`. -/
theorem addrJ (p : Addr) (b j t : Nat) :
    coeffAddr p (32 * b) + BitVec.ofNat 64 (1024 * j + 32 * t) =
      coeffAddr (p + BitVec.ofNat 64 (1024 * j)) (32 * b) + BitVec.ofNat 64 (32 * t) := by
  simp only [coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (p + ·) (congrArg _ (by omega_arith))

/-- The operands of product `j` of block `b`: the pairs of coefficients of
`F` (stored as `R` says at `fB + o j`), and the even and the odd
coefficients of `G` (at `gB + 1024 j`), in `vbase`'s order. -/
theorem opsRg_ok {o : Nat} (R : FRep o) {fB gB : Addr} {F G : Poly} {b j : Nat} (hb : b < 8) {s : State}
    (hrsi : s.gpr .rsi = fB + BitVec.ofNat 64 (R.st * b)) (hrdx : s.gpr .rdx = coeffAddr gB (32 * b))
    (hF : R.Is s.mem (fB + BitVec.ofNat 64 (o * j)) F) (hG : PolyIs s.mem (gB + BitVec.ofNat 64 (1024 * j)) G)
    (rF : InRegions (s.rd ++ s.wr) (fB + BitVec.ofNat 64 (o * j)) R.sz)
    (rG : ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (1024 * j + 32 * t)) 32) :
    WP isa (.block (rowMulYg R.ld j)) s fun s' =>
      (∀ l < 2, PLanes (s'.lane .xmm0 l) (fun i => F[2 * pairY b l i]!) (fun i => F[2 * pairY b l i + 1]!) ∧
        PLanes (s'.lane .xmm1 l) (fun i => F[2 * pairY b l (4 + i)]!) (fun i => F[2 * pairY b l (4 + i) + 1]!) ∧
        Lanes (s'.lane .xmm6 l) (fun e => G[2 * pairY b l e]!) ∧
        Lanes (s'.lane .xmm10 l) (fun e => G[2 * pairY b l e + 1]!)) ∧
      YOnly [.xmm0, .xmm1, .xmm8, .xmm9, .xmm6, .xmm7, .xmm10, .xmm5] s s' := by
  have hj : 32 * b + 32 ≤ 256 := by omega_arith
  simp only [rowMulYg, List.append_assoc]
  -- the loads of `f`, its pairs of coefficients
  rw [WP.block_append_iff]
  refine WP.mono (R.ok hb hrsi hF rF) fun s2 ⟨D2, o2⟩ => ?_
  -- the loads of `g` and their lanes
  have rG' : ∀ t < 4, InRegions (s2.rd ++ s2.wr) (s2.gpr .rdx + BitVec.ofNat 64 (1024 * j + 32 * t)) 32 :=
    fun t ht => by rw [o2.rd, o2.wr, o2.gpr]; exact rG t ht
  rw [WP.block_append_iff]
  refine WP.mono (yload4o_ok (p := .rdx) (a := .xmm6) (b := .xmm7) (c := .xmm8) (d := .xmm9) (by decide) rG')
    fun s3 ⟨A3, o3⟩ => ?_
  refine WP.mono (ylanes lane_deintS6' (P := fun l t =>
      t.xmm .xmm6 = deE (s3.lane .xmm6 l) (s3.lane .xmm7 l) (s3.lane .xmm8 l) (s3.lane .xmm9 l) ∧
      t.xmm .xmm10 = deO (s3.lane .xmm6 l) (s3.lane .xmm7 l) (s3.lane .xmm8 l) (s3.lane .xmm9 l))
    fun l _ => deintS_ok6' (s3.proj l)) fun s4 ⟨D4, o4⟩ =>
      ⟨fun l hl => ?_, ((o2.trans o3).trans o4).mono (by simp)⟩
  have idx : ∀ e < 8, 32 * b + 8 * (2 * e / 4) + 4 * l + 2 * e % 4 = 2 * pairY b l e ∧
      32 * b + 8 * ((2 * e + 1) / 4) + 4 * l + (2 * e + 1) % 4 = 2 * pairY b l e + 1 := fun e _ => by
    unfold pairY; omega_arith
  have ad : ∀ (p : Addr) (t l : Nat), coeffAddr p (32 * b) + BitVec.ofNat 64 (1024 * j + 32 * t) +
      BitVec.ofNat 64 (16 * l) = coeffAddr (p + BitVec.ofNat 64 (1024 * j)) (32 * b) + BitVec.ofNat 64 (32 * t) +
        BitVec.ofNat 64 (16 * l) := fun p t l => by rw [addrJ]
  have d := deintY_of (m := s2.mem) (by rw [o2.mem]; exact hG) hj hl _ rfl
  have e6 : s4.lane .xmm6 l = _ := (D4 l hl).1
  have e10 : s4.lane .xmm10 l = _ := (D4 l hl).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [o4.lane _ (by decide) l hl, o3.lane _ (by decide) l hl]; exact (D2 l hl).1
  · rw [o4.lane _ (by decide) l hl, o3.lane _ (by decide) l hl]; exact (D2 l hl).2
  · rw [e6, (A3 l hl).1, (A3 l hl).2.1, (A3 l hl).2.2.1, (A3 l hl).2.2.2, o2.gpr, hrdx, ad, ad, ad, ad]
    exact fun e he => by rw [d.1 e he, (idx e he).1]
  · rw [e10, (A3 l hl).1, (A3 l hl).2.1, (A3 l hl).2.2.1, (A3 l hl).2.2.2, o2.gpr, hrdx, ad, ad, ad, ad]
    exact fun e he => by rw [d.2 e he, (idx e he).2]

/-! ## The products of a block -/

/-- The pairs of block `b` are among the 128 of a polynomial. -/
theorem pairY_lt4 {b l i : Nat} (hb : b < 8) (hl : l < 2) (hi : i < 4) : pairY b l i < 128 ∧ pairY b l (4 + i) < 128 := by
  unfold pairY; omega_arith

/-- The doublewords of the sums of the products `0, …, n` of a block, of
`dotP fs gs (n + 1)`: the first coefficients of the pairs in `xmm11` and
`xmm2`, the second in `xmm12` and `xmm3`, within `2(n + 1)q²`. -/
def SumsD (fs gs : List Poly) (b n l : Nat) (t : State) : Prop :=
  DLanes (2 * (n + 1)) (t.xmm .xmm11) (fun i => (dotP fs gs (n + 1))[2 * pairY b l i]!) ∧
    DLanes (2 * (n + 1)) (t.xmm .xmm2) (fun i => (dotP fs gs (n + 1))[2 * pairY b l (4 + i)]!) ∧
    DLanes (2 * (n + 1)) (t.xmm .xmm12) (fun i => (dotP fs gs (n + 1))[2 * pairY b l i + 1]!) ∧
    DLanes (2 * (n + 1)) (t.xmm .xmm3) (fun i => (dotP fs gs (n + 1))[2 * pairY b l (4 + i) + 1]!)

/-- The first product of a block, from its operands (`opsRg_ok`): the sums
of `dotP fs gs 1`. -/
theorem sumSet_ok {fs gs : List Poly} {b l : Nat} (hb : b < 8) (hl : l < 2) (hfl : 0 + 1 ≤ fs.length)
    (hgl : 0 + 1 ≤ gs.length) {t : State} (hc : VConsts t)
    (h0 : PLanes (t.xmm .xmm0) (fun i => fs[0]![2 * pairY b l i]!) (fun i => fs[0]![2 * pairY b l i + 1]!))
    (h1 : PLanes (t.xmm .xmm1) (fun i => fs[0]![2 * pairY b l (4 + i)]!) (fun i => fs[0]![2 * pairY b l (4 + i) + 1]!))
    (h6 : Lanes (t.xmm .xmm6) (fun e => gs[0]![2 * pairY b l e]!))
    (h10 : Lanes (t.xmm .xmm10) (fun e => gs[0]![2 * pairY b l e + 1]!))
    (h13 : ZLanes (t.xmm .xmm13) (fun e => gamma (pairY b l e))) :
    WP isa (.block ptermSet) t fun t' => SumsD fs gs b 0 l t' ∧
      XOnly [.xmm4, .xmm5, .xmm11, .xmm2, .xmm12, .xmm3] t t' := by
  have e1 : dotP fs gs (0 + 1) = multiplyNTTs fs[0]! gs[0]! := by
    rw [dotP_succ (by omega_arith) (by omega_arith), dotP_zero, zero_add_poly]
  refine WP.mono (ptermSet_ok hc (x0 := fun i => fs[0]![2 * pairY b l i]!)
    (x1 := fun i => fs[0]![2 * pairY b l i + 1]!) h0 h1 h6 h10 h13) fun _ ⟨⟨a0, a1, a2, a3⟩, c⟩ => ⟨?_, c⟩
  unfold SumsD
  rw [e1]
  exact ⟨fun i hi => rel_of_eq (a0 i hi) (prod_even _ _ (pairY_lt4 hb hl hi).1).symm,
    fun i hi => rel_of_eq (a1 i hi) (prod_even _ _ (pairY_lt4 hb hl hi).2).symm,
    fun i hi => rel_of_eq (a2 i hi) (prod_odd _ _ (pairY_lt4 hb hl hi).1).symm,
    fun i hi => rel_of_eq (a3 i hi) (prod_odd _ _ (pairY_lt4 hb hl hi).2).symm⟩

/-- Product `n + 1` of a block added to the sums of `dotP fs gs (n + 1)`. -/
theorem sumAdd_ok {fs gs : List Poly} {b l n : Nat} (hb : b < 8) (hl : l < 2) (hn : n + 1 + 1 ≤ 4)
    (hfl : n + 1 + 1 ≤ fs.length) (hgl : n + 1 + 1 ≤ gs.length) {t : State} (hc : VConsts t)
    (h0 : PLanes (t.xmm .xmm0) (fun i => fs[n + 1]![2 * pairY b l i]!) (fun i => fs[n + 1]![2 * pairY b l i + 1]!))
    (h1 : PLanes (t.xmm .xmm1) (fun i => fs[n + 1]![2 * pairY b l (4 + i)]!)
      (fun i => fs[n + 1]![2 * pairY b l (4 + i) + 1]!))
    (h6 : Lanes (t.xmm .xmm6) (fun e => gs[n + 1]![2 * pairY b l e]!))
    (h10 : Lanes (t.xmm .xmm10) (fun e => gs[n + 1]![2 * pairY b l e + 1]!))
    (h13 : ZLanes (t.xmm .xmm13) (fun e => gamma (pairY b l e))) (hs : SumsD fs gs b n l t) :
    WP isa (.block ptermAdd) t fun t' => SumsD fs gs b (n + 1) l t' ∧
      XOnly [.xmm4, .xmm5, .xmm7, .xmm8, .xmm9, .xmm11, .xmm2, .xmm12, .xmm3] t t' := by
  have e1 : dotP fs gs (n + 1 + 1) = VG.Spec.MlKem.add (dotP fs gs (n + 1)) (multiplyNTTs fs[n + 1]! gs[n + 1]!) :=
    dotP_succ (by omega_arith) (by omega_arith)
  refine WP.mono (ptermAdd_ok hc (x0 := fun i => fs[n + 1]![2 * pairY b l i]!)
    (x1 := fun i => fs[n + 1]![2 * pairY b l i + 1]!) h0 h1 h6 h10 h13 (show 2 * (n + 1) + 2 ≤ 8 by omega_arith)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2) fun _ ⟨⟨a0, a1, a2, a3⟩, c⟩ => ⟨?_, c⟩
  have lt : ∀ i < 4, 2 * pairY b l i + 1 < Spec.MlKem.n ∧ 2 * pairY b l (4 + i) + 1 < Spec.MlKem.n := fun i hi => by
    have := pairY_lt4 hb hl hi; rw [n_eq]; omega_arith
  unfold SumsD
  rw [e1]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · dsimp only
    rw [add_get _ _ (Nat.lt_of_succ_lt (lt i hi).1), prod_even _ _ (pairY_lt4 hb hl hi).1]; exact a0 i hi
  · dsimp only
    rw [add_get _ _ (Nat.lt_of_succ_lt (lt i hi).2), prod_even _ _ (pairY_lt4 hb hl hi).2]; exact a1 i hi
  · dsimp only
    rw [add_get _ _ (lt i hi).1, prod_odd _ _ (pairY_lt4 hb hl hi).1]; exact a2 i hi
  · dsimp only
    rw [add_get _ _ (lt i hi).2, prod_odd _ _ (pairY_lt4 hb hl hi).2]; exact a3 i hi

/-- The sums as words (`pred`): of `dotP fs gs (n + 1)`, times `2⁻¹⁶`, within `q`. -/
theorem sumRed_ok {fs gs : List Poly} {b l n : Nat} (hn : n + 1 ≤ 4) {t : State} (hc : VConsts t)
    (hs : SumsD fs gs b n l t) :
    WP isa (.block pred) t fun t' =>
      (LanesR (RepR 1) (t'.xmm .xmm11) (fun e => (dotP fs gs (n + 1))[2 * pairY b l e]!) ∧
        LanesR (RepR 1) (t'.xmm .xmm12) (fun e => (dotP fs gs (n + 1))[2 * pairY b l e + 1]!)) ∧
      XOnly [.xmm7, .xmm5, .xmm11, .xmm2, .xmm12, .xmm3] t t' := by
  refine WP.mono (pred_ok hc (show 2 * (n + 1) ≤ 8 by omega_arith) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2)
    fun _ ⟨a, b', c⟩ => ⟨⟨fun e he => rel_of_eq (a e he) ?_, fun e he => rel_of_eq (b' e he) ?_⟩, c⟩
  · dsimp only
    split
    · rfl
    · rw [show 4 + (e - 4) = e by omega_arith]
  · dsimp only
    split
    · rfl
    · rw [show 4 + (e - 4) = e by omega_arith]

/-- The sums of the products `0, …, n` of block `b`, of the polynomials `fs`
(from `fB`, stored as `R` says, `o` bytes apart) and `gs` (from `gB`), as
doublewords (`SumsD`). -/
theorem sumsRg_ok {o : Nat} (R : FRep o) {fB gB : Addr} {fs gs : List Poly} {b : Nat} (hb : b < 8) {s : State}
    (hrsi : s.gpr .rsi = fB + BitVec.ofNat 64 (R.st * b)) (hrdx : s.gpr .rdx = coeffAddr gB (32 * b))
    (hc : YConsts s) (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (fun e => gamma (pairY b l e))) :
    ∀ {n : Nat}, n + 1 ≤ 4 → n + 1 ≤ fs.length → n + 1 ≤ gs.length →
    (∀ j < n + 1, R.Is s.mem (fB + BitVec.ofNat 64 (o * j)) fs[j]!) →
    (∀ j < n + 1, PolyIs s.mem (gB + BitVec.ofNat 64 (1024 * j)) gs[j]!) →
    (∀ j < n + 1, InRegions (s.rd ++ s.wr) (fB + BitVec.ofNat 64 (o * j)) R.sz) →
    (∀ j < n + 1, ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (1024 * j + 32 * t)) 32) →
    WP isa (.block (rowSumsAux (rowMulYg R.ld) (n + 1))) s fun s' =>
      (∀ l < 2, SumsD fs gs b n l (s'.proj l)) ∧
      YOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12] s s' := by
  intro n
  induction n with
  | zero =>
    intro _ hfl hgl hF hG rF rG
    simp only [rowSumsAux, rowSum, List.nil_append, ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (opsRg_ok R (j := 0) (F := fs[0]!) (G := gs[0]!) hb hrsi hrdx (hF 0 (by decide)) (hG 0 (by decide))
      (rF 0 (by decide)) (rG 0 (by decide))) fun s1 ⟨V1, o1⟩ => ?_
    have c1 : YConsts s1 := o1.consts hc (by decide) (by decide)
    refine WP.mono (ylanes lane_ptermSet (P := fun l t => SumsD fs gs b 0 l t)
      fun l hl => sumSet_ok hb hl hfl hgl (c1 l hl) (V1 l hl).1 (V1 l hl).2.1 (V1 l hl).2.2.1 (V1 l hl).2.2.2
        (by rw [State.proj_xmm, o1.lane _ (by decide) l hl]; exact hz l hl))
      fun s2 ⟨S2, o2⟩ => ⟨S2, (o1.trans o2).mono (by simp)⟩
  | succ n ih =>
    intro hn hfl hgl hF hG rF rG
    rw [show rowSumsAux (rowMulYg R.ld) (n + 1 + 1) =
        rowSumsAux (rowMulYg R.ld) (n + 1) ++ rowSum (rowMulYg R.ld) (n + 1) from rfl, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith) (by omega_arith) (by omega_arith) (fun j hj => hF j (by omega_arith))
      (fun j hj => hG j (by omega_arith)) (fun j hj => rF j (by omega_arith)) (fun j hj => rG j (by omega_arith)))
      fun s1 ⟨A1, o1⟩ => ?_
    simp only [rowSum, Nat.add_one_ne_zero, ite_false]
    rw [WP.block_append_iff]
    refine WP.mono (opsRg_ok R (j := n + 1) (F := fs[n + 1]!) (G := gs[n + 1]!) hb (by rw [o1.gpr, hrsi])
      (by rw [o1.gpr, hrdx]) (by rw [o1.mem]; exact hF (n + 1) (by omega_arith))
      (by rw [o1.mem]; exact hG (n + 1) (by omega_arith)) (by rw [o1.rd, o1.wr]; exact rF (n + 1) (by omega_arith))
      (by rw [o1.rd, o1.wr, o1.gpr]; exact rG (n + 1) (by omega_arith))) fun s2 ⟨V2, o2⟩ => ?_
    have o12 := o1.trans o2
    have c2 : YConsts s2 := o12.consts hc (by decide) (by decide)
    have keep : ∀ l < 2, SumsD fs gs b n l (s2.proj l) := fun l hl => by
      have h := A1 l hl
      unfold SumsD at h ⊢
      rw [State.proj_xmm, State.proj_xmm, State.proj_xmm, State.proj_xmm, o2.lane _ (by decide) l hl,
        o2.lane _ (by decide) l hl, o2.lane _ (by decide) l hl, o2.lane _ (by decide) l hl]
      exact h
    refine WP.mono (ylanes lane_ptermAdd (P := fun l t => SumsD fs gs b (n + 1) l t)
      fun l hl => sumAdd_ok hb hl hn hfl hgl (c2 l hl) (V2 l hl).1 (V2 l hl).2.1 (V2 l hl).2.2.1 (V2 l hl).2.2.2
        (by rw [State.proj_xmm, o12.lane _ (by decide) l hl]; exact hz l hl) (keep l hl))
      fun s3 ⟨S3, o3⟩ => ⟨S3, (o12.trans o3).mono (by simp)⟩

/-- The products `0, …, n` of block `b`, of the polynomials `fs` (from `fB`,
stored as `R` says, `o` bytes apart) and `gs` (from `gB`), summed and reduced: the sums' words in `ymm11`
and `ymm12`, within `q`. -/
theorem prodsRg_ok {o : Nat} (R : FRep o) {fB gB : Addr} {fs gs : List Poly} {b : Nat} (hb : b < 8) {s : State}
    (hrsi : s.gpr .rsi = fB + BitVec.ofNat 64 (R.st * b)) (hrdx : s.gpr .rdx = coeffAddr gB (32 * b))
    (hc : YConsts s) (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (fun e => gamma (pairY b l e))) {n : Nat}
    (hn : n + 1 ≤ 4) (hfl : n + 1 ≤ fs.length) (hgl : n + 1 ≤ gs.length)
    (hF : ∀ j < n + 1, R.Is s.mem (fB + BitVec.ofNat 64 (o * j)) fs[j]!)
    (hG : ∀ j < n + 1, PolyIs s.mem (gB + BitVec.ofNat 64 (1024 * j)) gs[j]!)
    (rF : ∀ j < n + 1, InRegions (s.rd ++ s.wr) (fB + BitVec.ofNat 64 (o * j)) R.sz)
    (rG : ∀ j < n + 1, ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (1024 * j + 32 * t)) 32) :
    WP isa (.block (rowSums (rowMulYg R.ld) (n + 1))) s fun s' =>
      (∀ l < 2, LanesR (RepR 1) ((s'.proj l).xmm .xmm11) (fun e => (dotP fs gs (n + 1))[2 * pairY b l e]!) ∧
        LanesR (RepR 1) ((s'.proj l).xmm .xmm12) (fun e => (dotP fs gs (n + 1))[2 * pairY b l e + 1]!)) ∧
      YOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12] s s' := by
  rw [rowSums, WP.block_append_iff]
  refine WP.mono (sumsRg_ok R hb hrsi hrdx hc hz hn hfl hgl hF hG rF rG) fun s1 ⟨A1, o1⟩ => ?_
  refine WP.mono (ylanes lane_pred (P := fun l t =>
      LanesR (RepR 1) (t.xmm .xmm11) (fun e => (dotP fs gs (n + 1))[2 * pairY b l e]!) ∧
      LanesR (RepR 1) (t.xmm .xmm12) (fun e => (dotP fs gs (n + 1))[2 * pairY b l e + 1]!))
    fun l hl => sumRed_ok hn ((o1.consts hc (by decide) (by decide)) l hl) (A1 l hl))
    fun s2 ⟨V2, o2⟩ => ⟨V2, (o1.trans o2).mono (by simp)⟩

/-! ## A block of a row -/

namespace RowY

/-- `Ctx` of polynomials `f` stored as `R` says, `o` bytes apart. -/
structure CtxG {o : Nat} (R : FRep o) (k : Nat) (fB gB tP C : Addr) (fs gs : List Poly) (m₀ : Mem)
    (RD WR : List Region) : Prop where
  k1 : 1 ≤ k
  k4 : k ≤ 4
  fl : k ≤ fs.length
  gl : k ≤ gs.length
  F : ∀ j < k, R.Is m₀ (fB + BitVec.ofNat 64 (o * j)) fs[j]!
  G : ∀ j < k, PolyIs m₀ (gB + BitVec.ofNat 64 (1024 * j)) gs[j]!
  dF : ∀ j < k, (pR tP).Disjoint ⟨fB + BitVec.ofNat 64 (o * j), R.sz⟩
  dG : ∀ j < k, (pR tP).Disjoint (pR (gB + BitVec.ofNat 64 (1024 * j)))
  dT : (pR tP).Disjoint (tabR C)
  inF : ∀ j < k, InRegions (RD ++ WR) (fB + BitVec.ofNat 64 (o * j)) R.sz
  inG : ∀ j < k, InRegions (RD ++ WR) (gB + BitVec.ofNat 64 (1024 * j)) 1024
  inTab : InRegions (RD ++ WR) (C + BitVec.ofNat 64 3328) 256
  inT : InRegions WR tP 1024
  tab : TabY m₀ C
  red : Reduced m₀ tP

/-- After `b` blocks of a row. -/
structure Inv {o : Nat} (R : FRep o) (k : Nat) (fB gB tP C : Addr) (fs gs : List Poly) (m₀ : Mem) (RD WR : List Region) (b : Nat)
    (s : State) : Prop where
  rsi : s.gpr .rsi = fB + BitVec.ofNat 64 (R.st * b)
  rdx : s.gpr .rdx = coeffAddr gB (32 * b)
  rdi : s.gpr .rdi = coeffAddr tP (32 * b)
  r8 : s.gpr .r8 = wAddr (C + BitVec.ofNat 64 3328) (16 * b)
  rd : s.rd = RD
  wr : s.wr = WR
  c : YConsts s
  frame : Frame [pR tP] m₀ s.mem
  mem : FinY.MemOk m₀ tP (polyAt m₀ tP) (dotP fs gs k) (4 * b) s.mem

theorem addrB (p : Addr) (b j t : Nat) :
    coeffAddr p (32 * b) + BitVec.ofNat 64 (1024 * j + 32 * t) =
      p + BitVec.ofNat 64 (1024 * j) + BitVec.ofNat 64 (128 * b + 32 * t) := by
  simp only [coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (p + ·) (congrArg _ (by omega_arith))

theorem r2D : ofDwords (0x05490549 : BitVec 32) 0x05490549 0x05490549 0x05490549 = r2V := by decide

theorem lane_zero14 : laneSseBlock [yb .vpxor .xmm14 .xmm14 .xmm14] = some [xb .pxor .xmm14 .xmm14] := by
  decide +kernel

section
variable {o k : Nat} {R : FRep o} {fB gB tP C : Addr} {fs gs : List Poly} {m₀ : Mem} {RD WR : List Region}
  (hx : CtxG R k fB gB tP C fs gs m₀ RD WR)
include hx

set_option linter.unusedSimpArgs false in
theorem step {b : Nat} (hb : b < 8) {s : State} (hI : Inv R k fB gB tP C fs gs m₀ RD WR b s) :
    WP isa (.block (rowBodyYg R.ld R.stv k ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv R k fB gB tP C fs gs m₀ RD WR (b + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := hx.k1; omega_arith⟩
  have hrr : s.rd ++ s.wr = RD ++ WR := by rw [hI.rd, hI.wr]
  have dsj : ∀ {p : Addr}, (pR tP).Disjoint (pR p) → ∀ r ∈ [pR tP], (polyRegion p).Disjoint r := fun h r hr => by
    rw [List.mem_singleton.mp hr]; exact h.symm
  rw [show rowBodyYg R.ld R.stv (n + 1) ++ ([.alu .sub .rcx (.imm 1)] : List Instr) =
      [.vmovdquLoad .l256 .xmm13 (at_ .r8 0)] ++ (rowSums (rowMulYg R.ld) (n + 1) ++ (yconst .xmm13 0x05490549 ++
        (toY (vmont .xmm11 .xmm13 .xmm3 ++ vcadd .xmm11 .xmm3 ++ vmont .xmm12 .xmm13 .xmm3 ++ vcadd .xmm12 .xmm3) ++
        (yconst .xmm15 3329 ++ ([yb .vpxor .xmm14 .xmm14 .xmm14] ++
        ([yb .vpunpcklwd .xmm10 .xmm11 .xmm12, yb .vpunpckhwd .xmm9 .xmm11 .xmm12] ++
        (finQ .xmm10 .vpunpcklwd 0 ++ (finQ .xmm10 .vpunpckhwd 32 ++ (finQ .xmm9 .vpunpcklwd 64 ++
        (finQ .xmm9 .vpunpckhwd 96 ++ (yconsts ++ ([.alu .add .rsi (.imm R.stv), .alu .add .rdx (.imm 128),
          .alu .add .rdi (.imm 128), .alu .add .r8 (.imm 32), .alu .sub .rcx (.imm 1)] : List Instr))))))))))))
      from by simp [rowBodyYg], WP.block_append_iff]
  -- the `γ`s of block `b`
  have hz0 : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 0) 32 := by
    rw [hrr, hI.r8, wAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact CallLay.inRegions_sub hx.inTab (by omega_arith) (by omega_arith)
  refine WP.mono (yld_ok hz0) fun s1 ⟨Z1, o1⟩ => ?_
  have hTs : TabY s.mem C := tabY.frame hI.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hx.dT.symm)
    hx.tab
  have LZ : ∀ l < 2, ZLanes (s1.lane .xmm13 l) (fun e => gamma (pairY b l e)) := fun l hl e he => by
    rw [Z1 l hl, hI.r8, word_readW _ _ he, wAddr, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
      show 2 * (16 * b) + (0 + (16 * l + 2 * e)) = 2 * (16 * b + 8 * l + e) by omega_arith, ← wAddr, ← wordAt,
      hTs _ (by omega_arith), gTabY, gIdxY_eq hl he, gTab_eq]
  -- the products
  rw [WP.block_append_iff]
  have hF1 : ∀ j < n + 1, R.Is s1.mem (fB + BitVec.ofNat 64 (o * j)) fs[j]! := fun j hj => by
    rw [o1.mem]
    exact R.frame hI.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact (hx.dF j hj).symm) (hx.F j hj)
  have hG1 : ∀ j < n + 1, PolyIs s1.mem (gB + BitVec.ofNat 64 (1024 * j)) gs[j]! := fun j hj => by
    rw [o1.mem]; exact polyIs_frame hI.frame (dsj (hx.dG j hj)) (hx.G j hj)
  refine WP.mono (prodsRg_ok R hb (by rw [o1.gpr, hI.rsi]) (by rw [o1.gpr, hI.rdx])
    (o1.consts hI.c (by decide) (by decide)) LZ hx.k4 hx.fl hx.gl hF1 hG1
    (fun j hj => by rw [o1.rd, o1.wr, hrr]; exact hx.inF j hj)
    (fun j hj t ht => by
      rw [o1.rd, o1.wr, o1.gpr, hrr, hI.rdx, addrB]
      exact CallLay.inRegions_sub (hx.inG j hj) (by omega_arith) (by omega_arith))) fun s2 ⟨A2, o2⟩ => ?_
  have o12 := o1.trans o2
  have c2 : YConsts s2 := o12.consts hI.c (by decide) (by decide)
  -- `R² mod q`, and the sums reduced
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm13 _ s2) fun s3 ⟨R3, k3, m3, x3, lo3⟩ => ?_
  have c3 : YConsts s3 := fun l hl =>
    ⟨by rw [State.proj_xmm, lo3 _ (by decide) l hl, ← State.proj_xmm]; exact (c2 l hl).q,
      by rw [State.proj_xmm, lo3 _ (by decide) l hl, ← State.proj_xmm]; exact (c2 l hl).qinv⟩
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_accRed (P := fun l t =>
      (∀ i < 8, word (t.xmm .xmm11) i = W.caddW (W.montW (word ((s3.proj l).xmm .xmm11) i)
        (word ((s3.proj l).xmm .xmm13) i))) ∧
      (∀ i < 8, word (t.xmm .xmm12) i = W.caddW (W.montW (word ((s3.proj l).xmm .xmm12) i)
        (word ((s3.proj l).xmm .xmm13) i))))
    fun l hl => WP.mono (accRed_ok (c3 l hl)) fun _ ⟨a, b', c⟩ => ⟨⟨a, b'⟩, c⟩) fun s4 ⟨Q4, o4⟩ => ?_
  have can : ∀ l < 2, ∀ e < 8, (word (s4.lane .xmm11 l) e).toNat = ((dotP fs gs (n + 1))[2 * pairY b l e]!).val ∧
      (word (s4.lane .xmm12 l) e).toNat = ((dotP fs gs (n + 1))[2 * pairY b l e + 1]!).val := fun l hl e he => by
    have r13 : word ((s3.proj l).xmm .xmm13) e = r2W := by rw [State.proj_xmm, R3 l hl, r2D, word_r2V he]
    have a11 : (s3.proj l).xmm .xmm11 = (s2.proj l).xmm .xmm11 := by
      rw [State.proj_xmm, State.proj_xmm, lo3 _ (by decide) l hl]
    have a12 : (s3.proj l).xmm .xmm12 = (s2.proj l).xmm .xmm12 := by
      rw [State.proj_xmm, State.proj_xmm, lo3 _ (by decide) l hl]
    refine ⟨?_, ?_⟩
    · rw [← State.proj_xmm, (Q4 l hl).1 e he, r13, a11]
      exact cadd_rep (red2_rep ((A2 l hl).1 e he) (by decide))
    · rw [← State.proj_xmm, (Q4 l hl).2 e he, r13, a12]
      exact cadd_rep (red2_rep ((A2 l hl).2 e he) (by decide))
  -- `q` and zero, for the sums
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm15 _ s4) fun s5 ⟨lq, k5, m5, x5, lo5⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_zero14 (P := fun _ t => t.xmm .xmm14 = 0) fun l _ => FinY.zero14_ok _)
    fun s6 ⟨Z6, o6⟩ => ?_
  -- the sums' words in the order of the coefficients
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_unpkR (P := fun l t =>
      t.xmm .xmm10 = XBinOp.eval .punpcklwd ((s6.proj l).xmm .xmm11) ((s6.proj l).xmm .xmm12) ∧
      t.xmm .xmm9 = XBinOp.eval .punpckhwd ((s6.proj l).xmm .xmm11) ((s6.proj l).xmm .xmm12))
    fun l _ => unpkR_ok _) fun s7 ⟨U7, o7⟩ => ?_
  have e46 : ∀ r, r ≠ .xmm15 → r ≠ .xmm14 → ∀ l < 2, s6.lane r l = s4.lane r l := fun r h15 h14 l hl => by
    rw [o6.lane _ (by simpa using h14) l hl, lo5 _ h15 l hl]
  have hLH : ∀ q < 4, ∀ l < 2, ∀ e < 4,
      (word (if q < 2 then s7.lane .xmm10 l else s7.lane .xmm9 l) (4 * (q % 2) + e)).toNat =
        ((dotP fs gs (n + 1))[8 * (4 * b + q) + 4 * l + e]!).val := by
    intro q hq l hl e he
    have w := FinY.wv_of_w (F := dotP fs gs (n + 1)) (i := b) (A := s6.lane .xmm11 l) (B := s6.lane .xmm12 l) hl
      (fun h hh kk hkk => by
        rw [accIdx_eq hh hl hkk]
        rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl
        · rw [ifp rfl, e46 _ (by decide) (by decide) l hl]; exact (can l hl kk hkk).1
        · rw [ifn (by decide), e46 _ (by decide) (by decide) l hl]; exact (can l hl kk hkk).2) hq he
    have e10 : s7.lane .xmm10 l = XBinOp.eval .punpcklwd (s6.lane .xmm11 l) (s6.lane .xmm12 l) := by
      rw [← State.proj_xmm, (U7 l hl).1, State.proj_xmm, State.proj_xmm]
    have e9 : s7.lane .xmm9 l = XBinOp.eval .punpckhwd (s6.lane .xmm11 l) (s6.lane .xmm12 l) := by
      rw [← State.proj_xmm, (U7 l hl).2, State.proj_xmm, State.proj_xmm]
    by_cases hq2 : q < 2
    · rw [ifp hq2] at w ⊢; rw [e10]; exact w
    · rw [ifn hq2] at w ⊢; rw [e9]; exact w
  have o47 := o6.trans o7
  have hq7 : ∀ l < 2, s7.lane .xmm15 l = qD := fun l hl => by
    rw [o47.lane _ (by decide) l hl, lq l hl]; decide
  have hz7 : ∀ l < 2, s7.lane .xmm14 l = 0 := fun l hl => by
    rw [o7.lane _ (by decide) l hl, ← State.proj_xmm]; exact Z6 l hl
  -- the registers and memory the arithmetic left
  have g7 : ∀ r, r ≠ .rax → s7.gpr r = s.gpr r := fun r hr => by
    rw [o47.gpr, k5.gpr (by simpa using hr), o4.gpr, k3.gpr (by simpa using hr), o12.gpr]
  have m7 : s7.mem = s.mem := by rw [o47.mem, m5, o4.mem, m3, o12.mem]
  have hw7 : s7.wr = WR := by rw [o47.wr, k5.2.2, o4.wr, k3.2.2, o12.wr, hI.wr]
  have hrd7 : s7.rd = RD := by rw [o47.rd, k5.2.1, o4.rd, k3.2.1, o12.rd, hI.rd]
  have hrdi7 : s7.gpr .rdi = coeffAddr tP (32 * b) := by rw [g7 _ (by decide), hI.rdi]
  have hE : ∀ c < 256, (coeffAt m₀ tP c).toNat < q ∧ ((polyAt m₀ tP)[c]!).val = (coeffAt m₀ tP c).toNat :=
    fun c hc => ⟨hx.red c (by rw [n_eq]; exact hc), polyAt_val hx.red (by rw [n_eq]; exact hc)⟩
  have inT : ∀ qq < 4, InRegions WR (coeffAddr tP (8 * (4 * b + qq))) 32 := fun qq hq => by
    rw [coeffAddr]; exact CallLay.inRegions_sub hx.inT (by omega_arith) (by omega_arith)
  have hM7 : FinY.MemOk m₀ tP (polyAt m₀ tP) (dotP fs gs (n + 1)) (4 * b + 0) s7.mem := by rw [m7]; exact hI.mem
  have hop0 : ∀ a : BitVec 128, ∀ e < 4, (dword (XBinOp.eval .punpcklwd a 0) e).toNat = (word a (4 * 0 + e)).toNat :=
    fun a e he => by have := FinY.dword_unpk0 a (h := 0) (by decide) he; rwa [ifp rfl] at this
  have hop1 : ∀ a : BitVec 128, ∀ e < 4, (dword (XBinOp.eval .punpckhwd a 0) e).toNat = (word a (4 * 1 + e)).toNat :=
    fun a e he => by have := FinY.dword_unpk0 a (h := 1) (by decide) he; rwa [ifn (by decide)] at this
  -- coefficients `32b, …, 32b + 7`
  rw [WP.block_append_iff]
  refine WP.mono (FinY.finQ_step hE (w := .xmm10) (by decide) (xop := .punpcklwd) (by decide +kernel) hop0
    (j := 4 * b + 0) (by omega_arith) (by rw [hrdi7]; exact FinY.rdi_q _ _ _ _ rfl) hq7 hz7
    (fun l hl e he => by have := hLH 0 (by decide) l hl e he; rwa [ifp (by decide)] at this)
    (by rw [hw7]; exact inT 0 (by decide)) hM7) fun s8 ⟨M8, m8, g8, rd8, wr8, x8, ln8⟩ => ?_
  -- `32b + 8, …`
  rw [WP.block_append_iff]
  refine WP.mono (FinY.finQ_step hE (w := .xmm10) (by decide) (xop := .punpckhwd) (by decide +kernel) hop1
    (j := 4 * b + 1) (by omega_arith) (by rw [g8, hrdi7]; exact FinY.rdi_q _ _ _ _ rfl)
    (fun l hl => by rw [ln8 _ (by decide) l hl]; exact hq7 l hl)
    (fun l hl => by rw [ln8 _ (by decide) l hl]; exact hz7 l hl)
    (fun l hl e he => by
      have := hLH 1 (by decide) l hl e he; rw [ifp (by decide)] at this; rw [ln8 _ (by decide) l hl]; exact this)
    (by rw [wr8, hw7]; exact inT 1 (by decide)) M8) fun s9 ⟨M9, m9, g9, rd9, wr9, x9, ln9⟩ => ?_
  -- `32b + 16, …`
  rw [WP.block_append_iff]
  refine WP.mono (FinY.finQ_step hE (w := .xmm9) (by decide) (xop := .punpcklwd) (by decide +kernel) hop0
    (j := 4 * b + 2) (by omega_arith) (by rw [g9, g8, hrdi7]; exact FinY.rdi_q _ _ _ _ rfl)
    (fun l hl => by rw [ln9 _ (by decide) l hl, ln8 _ (by decide) l hl]; exact hq7 l hl)
    (fun l hl => by rw [ln9 _ (by decide) l hl, ln8 _ (by decide) l hl]; exact hz7 l hl)
    (fun l hl e he => by
      have := hLH 2 (by decide) l hl e he; rw [ifn (by decide)] at this
      rw [ln9 _ (by decide) l hl, ln8 _ (by decide) l hl]; exact this)
    (by rw [wr9, wr8, hw7]; exact inT 2 (by decide)) M9) fun s10 ⟨M10, m10, g10, rd10, wr10, x10, ln10⟩ => ?_
  -- `32b + 24, …`
  rw [WP.block_append_iff]
  refine WP.mono (FinY.finQ_step hE (w := .xmm9) (by decide) (xop := .punpckhwd) (by decide +kernel) hop1
    (j := 4 * b + 3) (by omega_arith) (by rw [g10, g9, g8, hrdi7]; exact FinY.rdi_q _ _ _ _ rfl)
    (fun l hl => by rw [ln10 _ (by decide) l hl, ln9 _ (by decide) l hl, ln8 _ (by decide) l hl]; exact hq7 l hl)
    (fun l hl => by rw [ln10 _ (by decide) l hl, ln9 _ (by decide) l hl, ln8 _ (by decide) l hl]; exact hz7 l hl)
    (fun l hl e he => by
      have := hLH 3 (by decide) l hl e he; rw [ifn (by decide)] at this
      rw [ln10 _ (by decide) l hl, ln9 _ (by decide) l hl, ln8 _ (by decide) l hl]; exact this)
    (by rw [wr10, wr9, wr8, hw7]; exact inT 3 (by decide)) M10) fun s11 ⟨M11, m11, g11, rd11, wr11, x11, ln11⟩ => ?_
  -- the constants back
  rw [WP.block_append_iff]
  refine WP.mono (yconsts_ok s11) fun s12 ⟨c12, m12, k12⟩ => ?_
  have g12 : ∀ r, r ≠ .rax → s12.gpr r = s.gpr r := fun r hr => by
    rw [k12.gpr (by simpa using hr), g11, g10, g9, g8, g7 r hr]
  have sx32 : BitVec.signExtend 64 (32 : BitVec 32) = BitVec.ofNat 64 (2 * 16) := by decide
  have sx128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 (4 * 32) := by decide
  have cT : ∀ qq < 4, (pR tP).Contains (coeffAddr tP (8 * (4 * b + qq))) 32 := fun qq hq =>
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  vrunm [sx32, sx128, R.hst]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, fun l hl => ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [g12 _ (by decide), hI.rsi, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [g12 _ (by decide), hI.rdx, coeffAddr_off, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [g12 _ (by decide), hI.rdi, coeffAddr_off, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [g12 _ (by decide), hI.r8, wAddr_add, Nat.mul_succ]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; rw [k12.2.1, rd11, rd10, rd9, rd8, hrd7]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; rw [k12.2.2, wr11, wr10, wr9, wr8, hw7]
  · exact ⟨(c12 l hl).q, (c12 l hl).qinv⟩
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    rw [m12, m11, m10, m9, m8, m7]
    exact (((hI.frame.writeW (List.mem_singleton_self _) _ (cT 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (cT 1 (by decide))).writeW (List.mem_singleton_self _) _
      (cT 2 (by decide))).writeW (List.mem_singleton_self _) _ (cT 3 (by decide))
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    rw [m12, show 4 * (b + 1) = 4 * b + 3 + 1 by omega_arith]; exact M11
  · rw [g12 _ (by decide)]
  · rw [g12 _ (by decide)]

end

/-! ## A row -/

theorem coeffAddr_zero (p : Addr) : coeffAddr p (32 * 0) = p := by simp [coeffAddr]

theorem wAddr_zero (p : Addr) : wAddr p (16 * 0) = p := by simp [wAddr]

/-- `rowYg R.ld R.stv k`: `t` at `tP` plus the sum of the products of the
`k` polynomials from `fB` (stored as `R` says) and from `gB`. -/
theorem rowYg_ok {o k : Nat} (R : FRep o) {fB gB tP C : Addr} {fs gs : List Poly} {s : State}
    (hx : CtxG R k fB gB tP C fs gs s.mem s.rd s.wr) (hrsi : s.gpr .rsi = fB) (hrdx : s.gpr .rdx = gB)
    (hrdi : s.gpr .rdi = tP) (hrcx : s.gpr .rcx = C) :
    WP isa (rowYg R.ld R.stv k) s fun s' => PolyIs s'.mem tP (VG.Spec.MlKem.add (polyAt s.mem tP) (dotP fs gs k)) ∧
      Frame [pR tP] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold rowYg
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (yconsts_ok s) fun s1 ⟨c1, m1, k1⟩ => ?_
  have sx : BitVec.signExtend 64 (BitVec.ofNat 32 3328) = BitVec.ofNat 64 3328 := by decide
  refine WP.mono (Q := fun (s2 : State) => s2.gpr .r8 = C + BitVec.ofNat 64 3328 ∧ s2.gpr .rsi = fB ∧
      s2.gpr .rdx = gB ∧ s2.gpr .rdi = tP ∧ s2.rd = s.rd ∧ s2.wr = s.wr ∧ s2.mem = s.mem ∧ YConsts s2)
    (by
      simp only [leaR, oTabY]
      vrunm [sx]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun l hl => ⟨(c1 l hl).q, (c1 l hl).qinv⟩⟩
      · rw [k1.gpr (by decide), hrcx]
      · rw [k1.gpr (by decide), hrsi]
      · rw [k1.gpr (by decide), hrdx]
      · rw [k1.gpr (by decide), hrdi]
      · exact k1.2.1
      · exact k1.2.2
      · exact m1) fun s2 ⟨h8, h2si, h2dx, h2di, h2rd, h2wr, h2m, c2⟩ => ?_
  refine WP.seq (WP.mono (wp_rcxLoopY (N := 8) (by decide) (by decide) (Inv R k fB gB tP C fs gs s.mem s.rd s.wr)
    (fun u o hy _ =>
      { rsi := by rw [o.keep.gpr (by decide), h2si, Nat.mul_zero, add_ofNat_zero]
        rdx := by rw [o.keep.gpr (by decide), h2dx, coeffAddr_zero]
        rdi := by rw [o.keep.gpr (by decide), h2di, coeffAddr_zero]
        r8 := by rw [o.keep.gpr (by decide), h8, wAddr_zero]
        rd := by rw [o.keep.2.1, h2rd]
        wr := by rw [o.keep.2.2, h2wr]
        c := fun l hl =>
          ⟨by rw [State.proj_xmm, show u.lane .xmm15 l = s2.lane .xmm15 l by simp only [State.lane]; rw [o.xmm, hy],
              ← State.proj_xmm]; exact (c2 l hl).q,
            by rw [State.proj_xmm, show u.lane .xmm14 l = s2.lane .xmm14 l by simp only [State.lane]; rw [o.xmm, hy],
              ← State.proj_xmm]; exact (c2 l hl).qinv⟩
        frame := by rw [o.mem, h2m]; exact Frame.refl _ _
        mem := fun c _ => ⟨fun h => absurd h (by omega_arith), fun _ => by rw [o.mem, h2m]⟩ })
    fun b hb u hI => step hx hb hI) fun u hI => ?_)
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr) (by vrunm; exact ⟨rfl, rfl, rfl⟩)
    fun u' ⟨hm', hrd', hwr'⟩ => ⟨?_, by rw [hm']; exact hI.frame, by rw [hrd', hI.rd], by rw [hwr', hI.wr]⟩
  rw [hm']
  exact polyIs_of_toNat fun c hc => (hI.mem c (by rw [n_eq] at hc; exact hc)).1 (by rw [n_eq] at hc; omega_arith)

end RowY

end VG.Proof.MlKem.X86_64
