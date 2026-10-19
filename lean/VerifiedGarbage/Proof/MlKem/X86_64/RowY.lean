module

meta import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
public import VerifiedGarbage.Proof.MlKem.X86_64.Lazy
meta import VerifiedGarbage.Proof.MlKem.X86_64.AccY
public import VerifiedGarbage.Proof.MlKem.X86_64.DecMul
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecMul
public import VerifiedGarbage.Proof.MlKem.X86_64.FinY
meta import VerifiedGarbage.Proof.MlKem.X86_64.FinY
import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Impl.MlKem.X86_64.KpkeAccY
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlKem.X86_64.YNttPack
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

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

/-- The address of the `t`-th load of `f` in a product at `d` bytes. -/
theorem addrO (p : Addr) (b d t : Nat) :
    coeffAddr p (32 * b) + BitVec.ofNat 64 (d + 32 * t) =
      coeffAddr (p + BitVec.ofNat 64 d) (32 * b) + BitVec.ofNat 64 (32 * t) := by
  simp only [coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (p + ·) (congrArg _ (by omega))

theorem addrBF (p : Addr) (b d t : Nat) :
    coeffAddr p (32 * b) + BitVec.ofNat 64 (d + 32 * t) = p + BitVec.ofNat 64 d + BitVec.ofNat 64 (128 * b + 32 * t) := by
  simp only [coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (p + ·) (congrArg _ (by omega))

/-- How the polynomials `f` of a row are stored, `o` bytes apart: their
predicate `Is` (with the frame it keeps, of `sz` bytes), the code `ld j` that
loads the 32 coefficients of a block of polynomial `j` from `rsi + o j` as
`rowLdY` does, and the bytes `st` (`stv`) of a block, which `rsi` moves on. -/
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
      (∀ l < 2, Lanes (s'.lane .xmm0 l) (fun e => F[2 * pairY b l e]!) ∧
        Lanes (s'.lane .xmm4 l) (fun e => F[2 * pairY b l e + 1]!)) ∧
      YOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5] s s'

/-- `rowLdY`: the even and the odd coefficients of block `b` of `F`
(`u32`s at `fB + o j`), in `vbase`'s order. -/
theorem ld32_ok {o : Nat} {fB : Addr} {F : Poly} {b j : Nat} {s : State} (hb : b < 8)
    (hrsi : s.gpr .rsi = fB + BitVec.ofNat 64 (128 * b)) (hF : PolyIs s.mem (fB + BitVec.ofNat 64 (o * j)) F)
    (rF : InRegions (s.rd ++ s.wr) (fB + BitVec.ofNat 64 (o * j)) 1024) :
    WP isa (.block (rowLdY o j)) s fun s' =>
      (∀ l < 2, Lanes (s'.lane .xmm0 l) (fun e => F[2 * pairY b l e]!) ∧
        Lanes (s'.lane .xmm4 l) (fun e => F[2 * pairY b l e + 1]!)) ∧
      YOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5] s s' := by
  have hj : 32 * b + 32 ≤ 256 := by omega
  have hrsi' : s.gpr .rsi = coeffAddr fB (32 * b) := by
    rw [hrsi, coeffAddr]; exact congrArg (fB + ·) (congrArg _ (by omega))
  have rF' : ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (o * j + 32 * t)) 32 := fun t ht => by
    rw [hrsi', addrBF]; exact CallLay.inRegions_sub rF (by omega) (by omega)
  simp only [rowLdY]
  rw [WP.block_append_iff]
  refine WP.mono (yload4o_ok (p := .rsi) (a := .xmm0) (b := .xmm1) (c := .xmm2) (d := .xmm3) (by decide) rF')
    fun s1 ⟨A1, o1⟩ => ?_
  refine WP.mono (ylanes lane_deintS0 (P := fun l t =>
      t.xmm .xmm0 = deE (s1.lane .xmm0 l) (s1.lane .xmm1 l) (s1.lane .xmm2 l) (s1.lane .xmm3 l) ∧
      t.xmm .xmm4 = deO (s1.lane .xmm0 l) (s1.lane .xmm1 l) (s1.lane .xmm2 l) (s1.lane .xmm3 l))
    fun l _ => deintS_ok0 (s1.proj l)) fun s2 ⟨D2, o2⟩ => ⟨fun l hl => ?_, (o1.trans o2).mono (by simp)⟩
  have idx : ∀ e < 8, 32 * b + 8 * (2 * e / 4) + 4 * l + 2 * e % 4 = 2 * pairY b l e ∧
      32 * b + 8 * ((2 * e + 1) / 4) + 4 * l + (2 * e + 1) % 4 = 2 * pairY b l e + 1 := fun e _ => by
    unfold pairY; omega
  have ad : ∀ (p : Addr) (t l : Nat), coeffAddr p (32 * b) + BitVec.ofNat 64 (o * j + 32 * t) +
      BitVec.ofNat 64 (16 * l) = coeffAddr (p + BitVec.ofNat 64 (o * j)) (32 * b) + BitVec.ofNat 64 (32 * t) +
        BitVec.ofNat 64 (16 * l) := fun p t l => by rw [addrO]
  have d := deintY_of hF hj hl _ rfl
  have e0 : s2.lane .xmm0 l = _ := (D2 l hl).1
  have e4 : s2.lane .xmm4 l = _ := (D2 l hl).2
  rw [e0, e4, (A1 l hl).1, (A1 l hl).2.1, (A1 l hl).2.2.1, (A1 l hl).2.2.2, hrsi', ad, ad, ad, ad]
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [d.1 e he, (idx e he).1]
  · rw [d.2 e he, (idx e he).2]

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
  exact congrArg (p + ·) (congrArg _ (by omega))

/-- Product `j` of block `b`, of `F` (stored as `R` says at `fB + o j`) and
`G` (at `gB + 1024 j`), in `ymm1` and `ymm2`, within `2q`. -/
theorem mulRg_ok {o : Nat} (R : FRep o) {fB gB : Addr} {F G : Poly} {b j : Nat} (hb : b < 8) {s : State}
    (hrsi : s.gpr .rsi = fB + BitVec.ofNat 64 (R.st * b)) (hrdx : s.gpr .rdx = coeffAddr gB (32 * b))
    (hF : R.Is s.mem (fB + BitVec.ofNat 64 (o * j)) F) (hG : PolyIs s.mem (gB + BitVec.ofNat 64 (1024 * j)) G)
    (rF : InRegions (s.rd ++ s.wr) (fB + BitVec.ofNat 64 (o * j)) R.sz)
    (rG : ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (1024 * j + 32 * t)) 32)
    (hc : YConsts s) (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (fun e => gamma (pairY b l e))) :
    WP isa (.block (rowMulYg R.ld j)) s fun s' =>
      (∀ l < 2, LanesR (RepR 2) ((s'.proj l).xmm .xmm1) (fun e => (multiplyNTTs F G)[2 * pairY b l e]!) ∧
        LanesR (RepR 2) ((s'.proj l).xmm .xmm2) (fun e => (multiplyNTTs F G)[2 * pairY b l e + 1]!)) ∧
      YOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7, .xmm8, .xmm9, .xmm10] s s' := by
  have hj : 32 * b + 32 ≤ 256 := by omega
  simp only [rowMulYg, List.append_assoc]
  -- the loads of `f`, its even and odd coefficients
  rw [WP.block_append_iff]
  refine WP.mono (R.ok hb hrsi hF rF) fun s2 ⟨D2, o2⟩ => ?_
  -- the loads of `g` and their lanes
  have rG' : ∀ t < 4, InRegions (s2.rd ++ s2.wr) (s2.gpr .rdx + BitVec.ofNat 64 (1024 * j + 32 * t)) 32 :=
    fun t ht => by rw [o2.rd, o2.wr, o2.gpr]; exact rG t ht
  rw [WP.block_append_iff]
  refine WP.mono (yload4o_ok (p := .rdx) (a := .xmm6) (b := .xmm7) (c := .xmm8) (d := .xmm9) (by decide) rG')
    fun s3 ⟨A3, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_deintS6' (P := fun l t =>
      t.xmm .xmm6 = deE (s3.lane .xmm6 l) (s3.lane .xmm7 l) (s3.lane .xmm8 l) (s3.lane .xmm9 l) ∧
      t.xmm .xmm10 = deO (s3.lane .xmm6 l) (s3.lane .xmm7 l) (s3.lane .xmm8 l) (s3.lane .xmm9 l))
    fun l _ => deintS_ok6' (s3.proj l)) fun s4 ⟨D4, o4⟩ => ?_
  have o14 := (o2.trans o3).trans o4
  have c4 : YConsts s4 := o14.consts hc (by decide) (by decide)
  have idx : ∀ l < 2, ∀ e < 8, 32 * b + 8 * (2 * e / 4) + 4 * l + 2 * e % 4 = 2 * pairY b l e ∧
      32 * b + 8 * ((2 * e + 1) / 4) + 4 * l + (2 * e + 1) % 4 = 2 * pairY b l e + 1 := fun l _ e _ => by
    unfold pairY; omega
  have ad : ∀ (p : Addr) (t l : Nat), coeffAddr p (32 * b) + BitVec.ofNat 64 (1024 * j + 32 * t) +
      BitVec.ofNat 64 (16 * l) = coeffAddr (p + BitVec.ofNat 64 (1024 * j)) (32 * b) + BitVec.ofNat 64 (32 * t) +
        BitVec.ofNat 64 (16 * l) := fun p t l => by rw [addrJ]
  have LF : ∀ l < 2, Lanes (s4.lane .xmm0 l) (fun e => F[2 * pairY b l e]!) ∧
      Lanes (s4.lane .xmm4 l) (fun e => F[2 * pairY b l e + 1]!) := fun l hl => by
    rw [o4.lane _ (by decide) l hl, o3.lane _ (by decide) l hl, o4.lane _ (by decide) l hl,
      o3.lane _ (by decide) l hl]
    exact D2 l hl
  have LG : ∀ l < 2, Lanes (s4.lane .xmm6 l) (fun e => G[2 * pairY b l e]!) ∧
      Lanes (s4.lane .xmm10 l) (fun e => G[2 * pairY b l e + 1]!) := fun l hl => by
    have d := deintY_of (m := s2.mem) (by rw [o2.mem]; exact hG) hj hl _ rfl
    have e6 : s4.lane .xmm6 l = _ := (D4 l hl).1
    have e10 : s4.lane .xmm10 l = _ := (D4 l hl).2
    rw [e6, e10, (A3 l hl).1, (A3 l hl).2.1, (A3 l hl).2.2.1, (A3 l hl).2.2.2, o2.gpr, hrdx, ad, ad, ad, ad]
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

/-! ## The products of a block -/

theorem pairY_lt {b l e : Nat} (hb : b < 8) (hl : l < 2) (he : e < 8) : 2 * pairY b l e + 1 < n := by
  rw [n_eq]; unfold pairY; omega

/-- The products `0, …, n` of block `b`, of the polynomials `fs` (from `fB`,
stored as `R` says, `o` bytes apart) and `gs` (from `gB`), summed in `ymm11` and `ymm12`, within
`2(n + 1)q`. -/
theorem prodsRg_ok {o : Nat} (R : FRep o) {fB gB : Addr} {fs gs : List Poly} {b : Nat} (hb : b < 8) {s : State}
    (hrsi : s.gpr .rsi = fB + BitVec.ofNat 64 (R.st * b)) (hrdx : s.gpr .rdx = coeffAddr gB (32 * b))
    (hc : YConsts s) (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (fun e => gamma (pairY b l e))) :
    ∀ {n : Nat}, n + 1 ≤ 4 → n + 1 ≤ fs.length → n + 1 ≤ gs.length →
    (∀ j < n + 1, R.Is s.mem (fB + BitVec.ofNat 64 (o * j)) fs[j]!) →
    (∀ j < n + 1, PolyIs s.mem (gB + BitVec.ofNat 64 (1024 * j)) gs[j]!) →
    (∀ j < n + 1, InRegions (s.rd ++ s.wr) (fB + BitVec.ofNat 64 (o * j)) R.sz) →
    (∀ j < n + 1, ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (1024 * j + 32 * t)) 32) →
    WP isa (.block (rowSums (rowMulYg R.ld) (n + 1))) s fun s' =>
      (∀ l < 2, LanesR (RepR (2 * (n + 1))) ((s'.proj l).xmm .xmm11)
          (fun e => (dotP fs gs (n + 1))[2 * pairY b l e]!) ∧
        LanesR (RepR (2 * (n + 1))) ((s'.proj l).xmm .xmm12)
          (fun e => (dotP fs gs (n + 1))[2 * pairY b l e + 1]!)) ∧
      YOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12] s s' := by
  intro n
  induction n with
  | zero =>
    intro _ hfl hgl hF hG rF rG
    have e1 : dotP fs gs (0 + 1) = multiplyNTTs fs[0]! gs[0]! := by
      rw [dotP_succ (by omega) (by omega), dotP_zero, zero_add_poly]
    rw [e1]
    simp only [rowSums, rowSum, List.nil_append, ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (mulRg_ok R (j := 0) (F := fs[0]!) (G := gs[0]!) hb hrsi hrdx (hF 0 (by decide)) (hG 0 (by decide)) (rF 0 (by decide))
      (rG 0 (by decide)) hc hz) fun s1 ⟨V1, o1⟩ => ?_
    refine WP.mono (ylanes lane_accSet (P := fun l t =>
        t.xmm .xmm11 = (s1.proj l).xmm .xmm1 ∧ t.xmm .xmm12 = (s1.proj l).xmm .xmm2)
      fun l _ => accSet_ok (s1.proj l)) fun s2 ⟨S2, o2⟩ => ⟨fun l hl => ?_, (o1.trans o2).mono (by simp)⟩
    rw [(S2 l hl).1, (S2 l hl).2]
    exact V1 l hl
  | succ n ih =>
    intro hn hfl hgl hF hG rF rG
    have e1 : dotP fs gs (n + 1 + 1) = VG.Spec.MlKem.add (dotP fs gs (n + 1)) (multiplyNTTs fs[n + 1]! gs[n + 1]!) :=
      dotP_succ (by omega) (by omega)
    rw [show rowSums (rowMulYg R.ld) (n + 1 + 1) = rowSums (rowMulYg R.ld) (n + 1) ++ rowSum (rowMulYg R.ld) (n + 1)
      from rfl, WP.block_append_iff]
    refine WP.mono (ih (by omega) (by omega) (by omega) (fun j hj => hF j (by omega)) (fun j hj => hG j (by omega))
      (fun j hj => rF j (by omega)) (fun j hj => rG j (by omega))) fun s1 ⟨A1, o1⟩ => ?_
    simp only [rowSum, Nat.add_one_ne_zero, ite_false]
    rw [WP.block_append_iff]
    refine WP.mono (mulRg_ok R (j := n + 1) (F := fs[n + 1]!) (G := gs[n + 1]!) hb (by rw [o1.gpr, hrsi]) (by rw [o1.gpr, hrdx])
      (by rw [o1.mem]; exact hF (n + 1) (by omega)) (by rw [o1.mem]; exact hG (n + 1) (by omega))
      (by rw [o1.rd, o1.wr]; exact rF (n + 1) (by omega))
      (by rw [o1.rd, o1.wr, o1.gpr]; exact rG (n + 1) (by omega)) (o1.consts hc (by decide) (by decide))
      (fun l hl => by rw [o1.lane _ (by decide) l hl]; exact hz l hl)) fun s2 ⟨V2, o2⟩ => ?_
    refine WP.mono (ylanes lane_accAdd (P := fun l t =>
        (∀ i < 8, word (t.xmm .xmm11) i = word ((s2.proj l).xmm .xmm11) i + word ((s2.proj l).xmm .xmm1) i) ∧
        (∀ i < 8, word (t.xmm .xmm12) i = word ((s2.proj l).xmm .xmm12) i + word ((s2.proj l).xmm .xmm2) i))
      fun l _ => WP.mono (accAdd_ok (s2.proj l)) fun _ ⟨a, b', c⟩ => ⟨⟨a, b'⟩, c⟩)
      fun s3 ⟨S3, o3⟩ => ⟨fun l hl => ⟨fun e he => ?_, fun e he => ?_⟩, ((o1.trans o2).trans o3).mono (by simp)⟩
    · have a11 : (s2.proj l).xmm .xmm11 = (s1.proj l).xmm .xmm11 := by
        rw [State.proj_xmm, State.proj_xmm, o2.lane _ (by decide) l hl]
      rw [(S3 l hl).1 e he, a11, e1]
      dsimp only
      rw [add_get _ _ (pairY_lt hb hl he |> Nat.lt_of_succ_lt)]
      exact (RepR.add ((A1 l hl).1 e he) ((V2 l hl).1 e he) (show 2 * (n + 1) + 2 ≤ 9 by omega))
    · have a12 : (s2.proj l).xmm .xmm12 = (s1.proj l).xmm .xmm12 := by
        rw [State.proj_xmm, State.proj_xmm, o2.lane _ (by decide) l hl]
      rw [(S3 l hl).2 e he, a12, e1]
      dsimp only
      rw [add_get _ _ (pairY_lt hb hl he)]
      exact (RepR.add ((A1 l hl).2 e he) ((V2 l hl).2 e he) (show 2 * (n + 1) + 2 ≤ 9 by omega))

/-! ## A block of a row -/

namespace RowY

/-- What a row needs of its arguments: `t` at `tP`, the `k` polynomials of
`fs` from `fB` and of `gs` from `gB` (1024 bytes apart), the table of the
`γ`s at `C + 3328`, in the memory `m₀` and the regions `RD` and `WR`. -/
structure Ctx (k : Nat) (fB gB tP C : Addr) (fs gs : List Poly) (m₀ : Mem) (RD WR : List Region) : Prop where
  k1 : 1 ≤ k
  k4 : k ≤ 4
  fl : k ≤ fs.length
  gl : k ≤ gs.length
  F : ∀ j < k, PolyIs m₀ (fB + BitVec.ofNat 64 (1024 * j)) fs[j]!
  G : ∀ j < k, PolyIs m₀ (gB + BitVec.ofNat 64 (1024 * j)) gs[j]!
  dF : ∀ j < k, (pR tP).Disjoint (pR (fB + BitVec.ofNat 64 (1024 * j)))
  dG : ∀ j < k, (pR tP).Disjoint (pR (gB + BitVec.ofNat 64 (1024 * j)))
  dT : (pR tP).Disjoint (tabR C)
  inF : ∀ j < k, InRegions (RD ++ WR) (fB + BitVec.ofNat 64 (1024 * j)) 1024
  inG : ∀ j < k, InRegions (RD ++ WR) (gB + BitVec.ofNat 64 (1024 * j)) 1024
  inTab : InRegions (RD ++ WR) (C + BitVec.ofNat 64 3328) 256
  inT : InRegions WR tP 1024
  tab : TabY m₀ C
  red : Reduced m₀ tP

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

theorem Ctx.toG {k : Nat} {fB gB tP C : Addr} {fs gs : List Poly} {m₀ : Mem} {RD WR : List Region}
    (h : Ctx k fB gB tP C fs gs m₀ RD WR) : CtxG (FRep.u32 1024) k fB gB tP C fs gs m₀ RD WR :=
  ⟨h.k1, h.k4, h.fl, h.gl, h.F, h.G, h.dF, h.dG, h.dT, h.inF, h.inG, h.inTab, h.inT, h.tab, h.red⟩

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
  exact congrArg (p + ·) (congrArg _ (by omega))

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
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := hx.k1; omega⟩
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
    exact CallLay.inRegions_sub hx.inTab (by omega) (by omega)
  refine WP.mono (yld_ok hz0) fun s1 ⟨Z1, o1⟩ => ?_
  have hTs : TabY s.mem C := tabY.frame hI.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hx.dT.symm)
    hx.tab
  have LZ : ∀ l < 2, ZLanes (s1.lane .xmm13 l) (fun e => gamma (pairY b l e)) := fun l hl e he => by
    rw [Z1 l hl, hI.r8, word_readW _ _ he, wAddr, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
      show 2 * (16 * b) + (0 + (16 * l + 2 * e)) = 2 * (16 * b + 8 * l + e) by omega, ← wAddr, ← wordAt,
      hTs _ (by omega), gTabY, gIdxY_eq hl he, gTab_eq]
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
      exact CallLay.inRegions_sub (hx.inG j hj) (by omega) (by omega))) fun s2 ⟨A2, o2⟩ => ?_
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
  have hk9 : 2 * (n + 1) ≤ 9 := by have := hx.k4; omega
  have can : ∀ l < 2, ∀ e < 8, (word (s4.lane .xmm11 l) e).toNat = ((dotP fs gs (n + 1))[2 * pairY b l e]!).val ∧
      (word (s4.lane .xmm12 l) e).toNat = ((dotP fs gs (n + 1))[2 * pairY b l e + 1]!).val := fun l hl e he => by
    have r13 : word ((s3.proj l).xmm .xmm13) e = r2W := by rw [State.proj_xmm, R3 l hl, r2D, word_r2V he]
    have a11 : (s3.proj l).xmm .xmm11 = (s2.proj l).xmm .xmm11 := by
      rw [State.proj_xmm, State.proj_xmm, lo3 _ (by decide) l hl]
    have a12 : (s3.proj l).xmm .xmm12 = (s2.proj l).xmm .xmm12 := by
      rw [State.proj_xmm, State.proj_xmm, lo3 _ (by decide) l hl]
    refine ⟨?_, ?_⟩
    · rw [← State.proj_xmm, (Q4 l hl).1 e he, r13, a11]
      exact cadd_rep (red2_rep ((A2 l hl).1 e he) hk9)
    · rw [← State.proj_xmm, (Q4 l hl).2 e he, r13, a12]
      exact cadd_rep (red2_rep ((A2 l hl).2 e he) hk9)
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
        rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
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
    rw [coeffAddr]; exact CallLay.inRegions_sub hx.inT (by omega) (by omega)
  have hM7 : FinY.MemOk m₀ tP (polyAt m₀ tP) (dotP fs gs (n + 1)) (4 * b + 0) s7.mem := by rw [m7]; exact hI.mem
  have hop0 : ∀ a : BitVec 128, ∀ e < 4, (dword (XBinOp.eval .punpcklwd a 0) e).toNat = (word a (4 * 0 + e)).toNat :=
    fun a e he => by have := FinY.dword_unpk0 a (h := 0) (by decide) he; rwa [ifp rfl] at this
  have hop1 : ∀ a : BitVec 128, ∀ e < 4, (dword (XBinOp.eval .punpckhwd a 0) e).toNat = (word a (4 * 1 + e)).toNat :=
    fun a e he => by have := FinY.dword_unpk0 a (h := 1) (by decide) he; rwa [ifn (by decide)] at this
  -- coefficients `32b, …, 32b + 7`
  rw [WP.block_append_iff]
  refine WP.mono (FinY.finQ_step hE (w := .xmm10) (by decide) (xop := .punpcklwd) (by decide +kernel) hop0
    (j := 4 * b + 0) (by omega) (by rw [hrdi7]; exact FinY.rdi_q _ _ _ _ rfl) hq7 hz7
    (fun l hl e he => by have := hLH 0 (by decide) l hl e he; rwa [ifp (by decide)] at this)
    (by rw [hw7]; exact inT 0 (by decide)) hM7) fun s8 ⟨M8, m8, g8, rd8, wr8, x8, ln8⟩ => ?_
  -- `32b + 8, …`
  rw [WP.block_append_iff]
  refine WP.mono (FinY.finQ_step hE (w := .xmm10) (by decide) (xop := .punpckhwd) (by decide +kernel) hop1
    (j := 4 * b + 1) (by omega) (by rw [g8, hrdi7]; exact FinY.rdi_q _ _ _ _ rfl)
    (fun l hl => by rw [ln8 _ (by decide) l hl]; exact hq7 l hl)
    (fun l hl => by rw [ln8 _ (by decide) l hl]; exact hz7 l hl)
    (fun l hl e he => by
      have := hLH 1 (by decide) l hl e he; rw [ifp (by decide)] at this; rw [ln8 _ (by decide) l hl]; exact this)
    (by rw [wr8, hw7]; exact inT 1 (by decide)) M8) fun s9 ⟨M9, m9, g9, rd9, wr9, x9, ln9⟩ => ?_
  -- `32b + 16, …`
  rw [WP.block_append_iff]
  refine WP.mono (FinY.finQ_step hE (w := .xmm9) (by decide) (xop := .punpcklwd) (by decide +kernel) hop0
    (j := 4 * b + 2) (by omega) (by rw [g9, g8, hrdi7]; exact FinY.rdi_q _ _ _ _ rfl)
    (fun l hl => by rw [ln9 _ (by decide) l hl, ln8 _ (by decide) l hl]; exact hq7 l hl)
    (fun l hl => by rw [ln9 _ (by decide) l hl, ln8 _ (by decide) l hl]; exact hz7 l hl)
    (fun l hl e he => by
      have := hLH 2 (by decide) l hl e he; rw [ifn (by decide)] at this
      rw [ln9 _ (by decide) l hl, ln8 _ (by decide) l hl]; exact this)
    (by rw [wr9, wr8, hw7]; exact inT 2 (by decide)) M9) fun s10 ⟨M10, m10, g10, rd10, wr10, x10, ln10⟩ => ?_
  -- `32b + 24, …`
  rw [WP.block_append_iff]
  refine WP.mono (FinY.finQ_step hE (w := .xmm9) (by decide) (xop := .punpckhwd) (by decide +kernel) hop1
    (j := 4 * b + 3) (by omega) (by rw [g10, g9, g8, hrdi7]; exact FinY.rdi_q _ _ _ _ rfl)
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
    Offset.contains_base _ (by omega) (by omega)
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
    rw [m12, show 4 * (b + 1) = 4 * b + 3 + 1 by omega]; exact M11
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
        mem := fun c _ => ⟨fun h => absurd h (by omega), fun _ => by rw [o.mem, h2m]⟩ })
    fun b hb u hI => step hx hb hI) fun u hI => ?_)
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr) (by vrunm; exact ⟨rfl, rfl, rfl⟩)
    fun u' ⟨hm', hrd', hwr'⟩ => ⟨?_, by rw [hm']; exact hI.frame, by rw [hrd', hI.rd], by rw [hwr', hI.wr]⟩
  rw [hm']
  exact polyIs_of_toNat fun c hc => (hI.mem c (by rw [n_eq] at hc; exact hc)).1 (by rw [n_eq] at hc; omega)

end RowY

end VG.Proof.MlKem.X86_64
