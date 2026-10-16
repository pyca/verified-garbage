module

public import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
public import VerifiedGarbage.Proof.MlKem.X86_64.Lazy
public import VerifiedGarbage.Proof.MlKem.X86_64.AccY
meta import VerifiedGarbage.Proof.MlKem.X86_64.AccY
public import VerifiedGarbage.Impl.MlKem.X86_64.KpkeAccY
meta import VerifiedGarbage.Impl.MlKem.X86_64.KpkeAccY
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-KEM on x86-64: a row of `keygen_mul` in registers (`rowY`)

`rowY k` adds to `t[i]` the sum of the `k` products of row `i` of `Â` and
`ŝ`, 32 coefficients at a time, without the accumulator in memory: each
product is `vbase` without its last Montgomery multiplications by `R² mod q`
(`vbaseL`), whose words are only congruent to the product's coefficients
times `2⁻¹⁶`, within `2q` (`RepR 2`, `baseL_rep`); the `k ≤ 4` products of
a word add up within `8q` (`RepR.add`), and one Montgomery multiplication by
`R² mod q` makes the sum congruent to the coefficient within `q`
(`red2_rep`), which `vcadd` makes canonical (`cadd_rep`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG.Spec.MlKem
open W (montW caddW r2W)

/-! ## Words congruent to coefficients times `2⁻¹⁶` -/

/-- The word `w` times `2¹⁶` is congruent to `v` modulo `q`, and `w` is less
than `b · q` in magnitude. -/
def RepR (b : Nat) (w : BitVec 16) (v : Zq) : Prop :=
  -((b : Int) * 3329) < w.toInt ∧ w.toInt < (b : Int) * 3329 ∧ (w.toInt * 65536 - (v.val : Int)) % 3329 = 0

/-- The congruence of the first word of `baseL_rep`, on integers. -/
theorem baseL_id0 {M1 M2 M3 Gi A0 B0 A1 B1 γ k1 k2 k3 kG : Int} (d1 : M1 * 65536 - A1 * B1 = 3329 * k1)
    (d2 : M2 * 65536 - M1 * Gi = 3329 * k2) (d3 : M3 * 65536 - A0 * B0 = 3329 * k3)
    (hG : Gi - γ * 65536 = 3329 * kG) :
    M3 * 65536 + M2 * 65536 - (A0 * B0 + A1 * B1 * γ) = 3329 * (k3 + k2 + γ * k1 + M1 * kG) := by
  grind

/-- The congruence of the second word of `baseL_rep`, on integers. -/
theorem baseL_id1 {N1 N2 A0 B1 A1 B0 j1 j2 : Int} (e1 : N1 * 65536 - A0 * B1 = 3329 * j1)
    (e2 : N2 * 65536 - A1 * B0 = 3329 * j2) : N1 * 65536 + N2 * 65536 - (A0 * B1 + A1 * B0) = 3329 * (j1 + j2) := by
  grind

/-- The two words of `BaseCaseMultiply` before their multiplications by `R²
mod q` (`vbaseL`), from the words `a₀, a₁, b₀, b₁` and `γ · 2¹⁶ mod q`. -/
theorem baseL_rep {a0 a1 b0 b1 g : BitVec 16} {x0 x1 y0 y1 γ : Zq} (ha0 : a0.toNat = x0.val)
    (ha1 : a1.toNat = x1.val) (hb0 : b0.toNat = y0.val) (hb1 : b1.toNat = y1.val)
    (hg : g.toNat = γ.val * 65536 % 3329) :
    RepR 2 (montW a0 b0 + montW (montW a1 b1) g) (x0 * y0 + x1 * y1 * γ) ∧
      RepR 2 (montW a0 b1 + montW a1 b0) (x0 * y1 + x1 * y0) := by
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
  obtain ⟨m1l, m1h, ⟨k1, d1⟩⟩ := W.mont_small (d := a1) (z := b1) (by omega_using [A1l]) (by omega_using [A1h])
    (by omega_using [B1l]) (by omega_using [B1h])
  obtain ⟨m2l, m2h, ⟨k2, d2⟩⟩ := W.mont_small (d := montW a1 b1) (z := g) (by omega_using [m1l])
    (by omega_using [m1h]) (by omega_using [Gl]) (by omega_using [Gl])
  obtain ⟨m3l, m3h, ⟨k3, d3⟩⟩ := W.mont_small (d := a0) (z := b0) (by omega_using [A0l]) (by omega_using [A0h])
    (by omega_using [B0l]) (by omega_using [B0h])
  obtain ⟨n1l, n1h, ⟨j1, e1⟩⟩ := W.mont_small (d := a0) (z := b1) (by omega_using [A0l]) (by omega_using [A0h])
    (by omega_using [B1l]) (by omega_using [B1h])
  obtain ⟨n2l, n2h, ⟨j2, e2⟩⟩ := W.mont_small (d := a1) (z := b0) (by omega_using [A1l]) (by omega_using [A1h])
    (by omega_using [B0l]) (by omega_using [B0h])
  have S1 := W.toInt_add16 (a := montW a0 b0) (b := montW (montW a1 b1) g) (by omega_using [m3l, m2l])
    (by omega_using [m3h, m2h])
  have S2 := W.toInt_add16 (a := montW a0 b1) (b := montW a1 b0) (by omega_using [n1l, n2l])
    (by omega_using [n1h, n2h])
  simp only [A0, A1, B0, B1] at d1 d3 e1 e2
  have v1 : ((x0 * y0 + x1 * y1 * γ).val : Int) = ((x0.val * y0.val + x1.val * y1.val * γ.val : Nat) : Int) % 3329 := by
    rw [val_add', val_mul, val_mul, val_mul, W.mulmod, ← Nat.add_mod]; exact Int.natCast_emod _ _
  have v2 : ((x0 * y1 + x1 * y0).val : Int) = ((x0.val * y1.val + x1.val * y0.val : Nat) : Int) % 3329 := by
    rw [val_add', val_mul, val_mul, ← Nat.add_mod]; exact Int.natCast_emod _ _
  refine ⟨⟨by rw [S1]; omega_using [m3l, m2l], by rw [S1]; omega_using [m3h, m2h], ?_⟩,
    ⟨by rw [S2]; omega_using [n1l, n2l], by rw [S2]; omega_using [n1h, n2h], ?_⟩⟩
  · rw [S1, v1]
    have h := baseL_id0 d1 d2 d3 hkG
    simp only [Int.natCast_add, Int.natCast_mul] at h ⊢
    generalize (x0.val : Int) * y0.val + x1.val * y1.val * γ.val = X at h ⊢
    omega_using [h]
  · rw [S2, v2]
    have h := baseL_id1 e1 e2
    simp only [Int.natCast_add, Int.natCast_mul] at h ⊢
    generalize (x0.val : Int) * y1.val + x1.val * y0.val = X at h ⊢
    omega_using [h]

/-- The sum of two words keeps their congruences, within the sum of their
bounds (at most `9q`, so without overflow). -/
theorem RepR.add {b c : Nat} {w w' : BitVec 16} {v v' : Zq} (h : RepR b w v) (h' : RepR c w' v') (hbc : b + c ≤ 9) :
    RepR (b + c) (w + w') (v + v') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  have hb : ((b + c : Nat) : Int) * 3329 ≤ 29961 := by
    have := Int.ofNat_le.mpr hbc; push_cast at this ⊢; omega
  have S := W.toInt_add16 (a := w) (b := w') (by push_cast at hb; omega) (by push_cast at hb; omega)
  have hv : ((v + v').val : Int) = ((v.val + v'.val : Nat) : Int) % 3329 := by
    rw [val_add']; exact Int.natCast_emod _ _
  refine ⟨by rw [S]; push_cast; omega, by rw [S]; push_cast; omega, ?_⟩
  rw [S, hv]
  push_cast
  omega

/-- `montW w (R² mod q)` represents `v` within `q` for a word `w` with
`w · 2¹⁶ ≡ v`. -/
theorem red2_rep {b : Nat} {w : BitVec 16} {v : Zq} (h : RepR b w v) (hb : b ≤ 9) : Rep 1 (montW w r2W) v := by
  obtain ⟨h1, h2, h3⟩ := h
  have hb' : (b : Int) * 3329 ≤ 29961 := by have := Int.ofNat_le.mpr hb; omega
  have hr := W.r2W_toInt
  have hn : (w.toInt * r2W.toInt).natAbs ≤ 29961 * 1353 := by
    rw [Int.natAbs_mul, hr]; exact Nat.mul_le_mul (by omega) (by decide)
  have n1 := Int.le_natAbs (a := w.toInt * r2W.toInt)
  have n2 := Int.le_natAbs (a := -(w.toInt * r2W.toInt))
  rw [Int.natAbs_neg] at n2
  obtain ⟨m1, m2, m3⟩ := W.montW_spec (d := w) (z := r2W) (by omega) (by omega)
  rw [hr] at m3
  have e := W.cancel_R (Y := (v.val : Int)) m3 (by omega_using [h3])
  refine ⟨by omega_using [m1], by omega_using [m2], ?_⟩
  omega_using [e]

/-! ## The SSE2 code of each lane -/

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-- `deintS` of `g`, with `xmm5` for its temporary (`xmm11` holds a sum). -/
theorem deintS_ok6' (s : State) :
    WP isa (.block (deintS .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm5)) s fun s' =>
      (s'.xmm .xmm6 = deE (s.xmm .xmm6) (s.xmm .xmm7) (s.xmm .xmm8) (s.xmm .xmm9) ∧
        s'.xmm .xmm10 = deO (s.xmm .xmm6) (s.xmm .xmm7) (s.xmm .xmm8) (s.xmm .xmm9)) ∧
      XOnly [.xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm5] s s' := by
  simp only [deintS]
  vrunm [eval_movdqa]
  exact ⟨⟨rfl, rfl⟩, by xonly⟩

/-- `vbaseL`: `BaseCaseMultiply` on the eight pairs of lanes, but for the
multiplications by `R² mod q`. -/
theorem vbaseL_ok {s : State} (hc : VConsts s) {x0 x1 y0 y1 γ : Nat → Zq}
    (h0 : Lanes (s.xmm .xmm0) x0) (h4 : Lanes (s.xmm .xmm4) x1) (h6 : Lanes (s.xmm .xmm6) y0)
    (h10 : Lanes (s.xmm .xmm10) y1) (h13 : ZLanes (s.xmm .xmm13) γ) :
    WP isa (.block vbaseL) s fun s' => LanesR (RepR 2) (s'.xmm .xmm1) (fun i => x0 i * y0 i + x1 i * y1 i * γ i) ∧
      LanesR (RepR 2) (s'.xmm .xmm2) (fun i => x0 i * y1 i + x1 i * y0 i) ∧
      XOnly [.xmm1, .xmm2, .xmm3, .xmm4] s s' := by
  simp only [vbaseL, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (movmont_ok (d := .xmm1) (src := .xmm4) (z := .xmm10) (t := .xmm2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc) fun s1 ⟨l1, o1⟩ => ?_
  have c1 := o1.consts hc (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (vmont_ok (d := .xmm1) (z := .xmm13) (t := .xmm2) (by decide) (by decide) (by decide)
    (by decide) (by decide) c1) fun s2 ⟨l2, o2⟩ => ?_
  have c2 := o2.consts c1 (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movmont_ok (d := .xmm2) (src := .xmm0) (z := .xmm6) (t := .xmm3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) c2) fun s3 ⟨l3, o3⟩ => ?_
  have c3 := o3.consts c2 (by decide) (by decide)
  rw [WP.block_append_iff, block_cons_iff]
  refine WP.mono (paddw_ok (d := .xmm1) (e := .xmm2)) fun s4 ⟨l4, o4⟩ => ?_
  have c4 := o4.consts c3 (by decide) (by decide)
  refine WP.mono (movmont_ok (d := .xmm2) (src := .xmm0) (z := .xmm10) (t := .xmm3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) c4) fun s5 ⟨l5, o5⟩ => ?_
  have c5 := o5.consts c4 (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (vmont_ok (d := .xmm4) (z := .xmm6) (t := .xmm3) (by decide) (by decide) (by decide)
    (by decide) (by decide) c5) fun s6 ⟨l6, o6⟩ => ?_
  refine WP.mono (paddw_ok (d := .xmm2) (e := .xmm4)) fun s7 ⟨l7, o7⟩ => ?_
  -- the registers each step reads
  have e0 : s4.xmm .xmm0 = s.xmm .xmm0 := by
    rw [o4.xmm _ (by decide), o3.xmm _ (by decide), o2.xmm _ (by decide), o1.xmm _ (by decide)]
  have e6 : s5.xmm .xmm6 = s.xmm .xmm6 := by
    rw [o5.xmm _ (by decide), o4.xmm _ (by decide), o3.xmm _ (by decide), o2.xmm _ (by decide),
      o1.xmm _ (by decide)]
  have e10 : s4.xmm .xmm10 = s.xmm .xmm10 := by
    rw [o4.xmm _ (by decide), o3.xmm _ (by decide), o2.xmm _ (by decide), o1.xmm _ (by decide)]
  have e4 : s5.xmm .xmm4 = s.xmm .xmm4 := by
    rw [o5.xmm _ (by decide), o4.xmm _ (by decide), o3.xmm _ (by decide), o2.xmm _ (by decide),
      o1.xmm _ (by decide)]
  have v1 : ∀ i < 8, word (s7.xmm .xmm1) i = W.montW (word (s.xmm .xmm0) i) (word (s.xmm .xmm6) i) +
      W.montW (W.montW (word (s.xmm .xmm4) i) (word (s.xmm .xmm10) i)) (word (s.xmm .xmm13) i) := fun i hi => by
    rw [o7.xmm _ (by decide), o6.xmm _ (by decide), o5.xmm _ (by decide), l4 i hi, o3.xmm _ (by decide), l2 i hi,
      l3 i hi]
    dsimp only
    rw [l1 i hi, o1.xmm _ (by decide), o2.xmm _ (by decide), o1.xmm _ (by decide), BitVec.add_comm]
    dsimp only
    rw [o2.xmm .xmm6 (by decide), o1.xmm .xmm6 (by decide)]
  have v2 : ∀ i < 8, word (s7.xmm .xmm2) i = W.montW (word (s.xmm .xmm0) i) (word (s.xmm .xmm10) i) +
      W.montW (word (s.xmm .xmm4) i) (word (s.xmm .xmm6) i) := fun i hi => by
    rw [l7 i hi, o6.xmm _ (by decide), l6 i hi, l5 i hi]
    dsimp only
    rw [e0, e10, e4, e6]
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [v1 i hi]
    exact (baseL_rep (h0 i hi) (h4 i hi) (h6 i hi) (h10 i hi) (h13 i hi)).1
  · rw [v2 i hi]
    exact (baseL_rep (h0 i hi) (h4 i hi) (h6 i hi) (h10 i hi) (h13 i hi)).2
  · refine ((o1.trans (o2.trans (o3.trans (o4.trans (o5.trans (o6.trans o7)))))).mono ?_)
    simp

/-- The first product of a row, to the sums. -/
theorem accSet_ok (s : State) :
    WP isa (.block [xb .movdqa .xmm11 .xmm1, xb .movdqa .xmm12 .xmm2]) s fun s' =>
      (s'.xmm .xmm11 = s.xmm .xmm1 ∧ s'.xmm .xmm12 = s.xmm .xmm2) ∧ XOnly [.xmm11, .xmm12] s s' := by
  simp only [xb]
  vrun [eval_movdqa]
  exact ⟨trivial, by xonly⟩

/-- A product added to the sums, word by word. -/
theorem accAdd_ok (s : State) :
    WP isa (.block [xb .paddw .xmm11 .xmm1, xb .paddw .xmm12 .xmm2]) s fun s' =>
      (∀ i < 8, word (s'.xmm .xmm11) i = word (s.xmm .xmm11) i + word (s.xmm .xmm1) i) ∧
      (∀ i < 8, word (s'.xmm .xmm12) i = word (s.xmm .xmm12) i + word (s.xmm .xmm2) i) ∧
      XOnly [.xmm11, .xmm12] s s' := by
  rw [block_cons_iff]
  refine WP.mono (paddw_ok (d := .xmm11) (e := .xmm1)) fun s1 ⟨l1, o1⟩ => ?_
  refine WP.mono (paddw_ok (d := .xmm12) (e := .xmm2)) fun s2 ⟨l2, o2⟩ => ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [o2.xmm _ (by decide), l1 i hi]
  · rw [l2 i hi, o1.xmm _ (by decide), o1.xmm _ (by decide)]
  · exact (o1.trans o2).mono (by simp)

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
theorem lane_vbaseL : laneSseBlock (toY vbaseL) = some vbaseL := by decide +kernel
theorem lane_accSet : laneSseBlock [.vop (.vmovdqa .l256 .xmm11 .xmm1), .vop (.vmovdqa .l256 .xmm12 .xmm2)] =
    some [xb .movdqa .xmm11 .xmm1, xb .movdqa .xmm12 .xmm2] := by decide +kernel
theorem lane_accAdd : laneSseBlock [yb .vpaddw .xmm11 .xmm11 .xmm1, yb .vpaddw .xmm12 .xmm12 .xmm2] =
    some [xb .paddw .xmm11 .xmm1, xb .paddw .xmm12 .xmm2] := by decide +kernel
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

/-- The address of the `t`-th load of product `j` of block `b`. -/
theorem addrJ (p : Addr) (b j t : Nat) :
    coeffAddr p (32 * b) + BitVec.ofNat 64 (1024 * j + 32 * t) =
      coeffAddr (p + BitVec.ofNat 64 (1024 * j)) (32 * b) + BitVec.ofNat 64 (32 * t) := by
  simp only [coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (p + ·) (congrArg _ (by omega))

/-- Product `j` of block `b`, of `F` (at `fB + 1024 j`) and `G` (at
`gB + 1024 j`), in `ymm1` and `ymm2`, within `2q`. -/
theorem mulR_ok {fB gB : Addr} {F G : Poly} {b j : Nat} (hb : b < 8) {s : State}
    (hrsi : s.gpr .rsi = coeffAddr fB (32 * b)) (hrdx : s.gpr .rdx = coeffAddr gB (32 * b))
    (hF : PolyIs s.mem (fB + BitVec.ofNat 64 (1024 * j)) F) (hG : PolyIs s.mem (gB + BitVec.ofNat 64 (1024 * j)) G)
    (rF : ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (1024 * j + 32 * t)) 32)
    (rG : ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (1024 * j + 32 * t)) 32)
    (hc : YConsts s) (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (fun e => gamma (pairY b l e))) :
    WP isa (.block (rowMulY j)) s fun s' =>
      (∀ l < 2, LanesR (RepR 2) ((s'.proj l).xmm .xmm1) (fun e => (multiplyNTTs F G)[2 * pairY b l e]!) ∧
        LanesR (RepR 2) ((s'.proj l).xmm .xmm2) (fun e => (multiplyNTTs F G)[2 * pairY b l e + 1]!)) ∧
      YOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7, .xmm8, .xmm9, .xmm10] s s' := by
  have hj : 32 * b + 32 ≤ 256 := by omega
  simp only [rowMulY, List.append_assoc]
  -- the loads of `f` and their lanes
  rw [WP.block_append_iff]
  refine WP.mono (yload4o_ok (p := .rsi) (a := .xmm0) (b := .xmm1) (c := .xmm2) (d := .xmm3) (by decide) rF)
    fun s1 ⟨A1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_deintS0 (P := fun l t =>
      t.xmm .xmm0 = deE (s1.lane .xmm0 l) (s1.lane .xmm1 l) (s1.lane .xmm2 l) (s1.lane .xmm3 l) ∧
      t.xmm .xmm4 = deO (s1.lane .xmm0 l) (s1.lane .xmm1 l) (s1.lane .xmm2 l) (s1.lane .xmm3 l))
    fun l _ => deintS_ok0 (s1.proj l)) fun s2 ⟨D2, o2⟩ => ?_
  -- the loads of `g` and their lanes
  have rG' : ∀ t < 4, InRegions (s2.rd ++ s2.wr) (s2.gpr .rdx + BitVec.ofNat 64 (1024 * j + 32 * t)) 32 :=
    fun t ht => by rw [o2.rd, o2.wr, o2.gpr, o1.rd, o1.wr, o1.gpr]; exact rG t ht
  rw [WP.block_append_iff]
  refine WP.mono (yload4o_ok (p := .rdx) (a := .xmm6) (b := .xmm7) (c := .xmm8) (d := .xmm9) (by decide) rG')
    fun s3 ⟨A3, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_deintS6' (P := fun l t =>
      t.xmm .xmm6 = deE (s3.lane .xmm6 l) (s3.lane .xmm7 l) (s3.lane .xmm8 l) (s3.lane .xmm9 l) ∧
      t.xmm .xmm10 = deO (s3.lane .xmm6 l) (s3.lane .xmm7 l) (s3.lane .xmm8 l) (s3.lane .xmm9 l))
    fun l _ => deintS_ok6' (s3.proj l)) fun s4 ⟨D4, o4⟩ => ?_
  have o14 := ((o1.trans o2).trans o3).trans o4
  have c4 : YConsts s4 := o14.consts hc (by decide) (by decide)
  have idx : ∀ l < 2, ∀ e < 8, 32 * b + 8 * (2 * e / 4) + 4 * l + 2 * e % 4 = 2 * pairY b l e ∧
      32 * b + 8 * ((2 * e + 1) / 4) + 4 * l + (2 * e + 1) % 4 = 2 * pairY b l e + 1 := fun l _ e _ => by
    unfold pairY; omega
  have ad : ∀ (p : Addr) (t l : Nat), coeffAddr p (32 * b) + BitVec.ofNat 64 (1024 * j + 32 * t) +
      BitVec.ofNat 64 (16 * l) = coeffAddr (p + BitVec.ofNat 64 (1024 * j)) (32 * b) + BitVec.ofNat 64 (32 * t) +
        BitVec.ofNat 64 (16 * l) := fun p t l => by rw [addrJ]
  have LF : ∀ l < 2, Lanes (s4.lane .xmm0 l) (fun e => F[2 * pairY b l e]!) ∧
      Lanes (s4.lane .xmm4 l) (fun e => F[2 * pairY b l e + 1]!) := fun l hl => by
    have d := deintY_of hF hj hl _ rfl
    rw [o4.lane _ (by decide) l hl, o3.lane _ (by decide) l hl, o4.lane _ (by decide) l hl,
      o3.lane _ (by decide) l hl]
    have e0 : s2.lane .xmm0 l = _ := (D2 l hl).1
    have e4 : s2.lane .xmm4 l = _ := (D2 l hl).2
    rw [e0, e4, (A1 l hl).1, (A1 l hl).2.1, (A1 l hl).2.2.1, (A1 l hl).2.2.2, hrsi, ad, ad, ad, ad]
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · rw [d.1 e he, (idx l hl e he).1]
    · rw [d.2 e he, (idx l hl e he).2]
  have LG : ∀ l < 2, Lanes (s4.lane .xmm6 l) (fun e => G[2 * pairY b l e]!) ∧
      Lanes (s4.lane .xmm10 l) (fun e => G[2 * pairY b l e + 1]!) := fun l hl => by
    have d := deintY_of (m := s2.mem) (by rw [o2.mem, o1.mem]; exact hG) hj hl _ rfl
    have e6 : s4.lane .xmm6 l = _ := (D4 l hl).1
    have e10 : s4.lane .xmm10 l = _ := (D4 l hl).2
    rw [e6, e10, (A3 l hl).1, (A3 l hl).2.1, (A3 l hl).2.2.1, (A3 l hl).2.2.2, o2.gpr, o1.gpr, hrdx, ad, ad, ad,
      ad]
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · rw [d.1 e he, (idx l hl e he).1]
    · rw [d.2 e he, (idx l hl e he).2]
  have LZ : ∀ l < 2, ZLanes (s4.lane .xmm13 l) (fun e => gamma (pairY b l e)) := fun l hl => by
    rw [o14.lane _ (by decide) l hl]; exact hz l hl
  refine WP.mono (ylanes lane_vbaseL (P := fun l t =>
      LanesR (RepR 2) (t.xmm .xmm1) (fun e => (multiplyNTTs F G)[2 * pairY b l e]!) ∧
      LanesR (RepR 2) (t.xmm .xmm2) (fun e => (multiplyNTTs F G)[2 * pairY b l e + 1]!))
    fun l hl => WP.mono (vbaseL_ok (c4 l hl) (LF l hl).1 (LF l hl).2 (LG l hl).1 (LG l hl).2 (LZ l hl))
      fun _ ⟨a, b', c⟩ => ⟨⟨fun e he => rel_of_eq (a e he) (prod_even _ _ (by unfold pairY; omega)).symm,
        fun e he => rel_of_eq (b' e he) (prod_odd _ _ (by unfold pairY; omega)).symm⟩, c⟩)
    fun s5 ⟨V5, o5⟩ => ⟨V5, (o14.trans o5).mono (by simp)⟩

end VG.Proof.MlKem.X86_64
