import VerifiedGarbage.Proof.MlKem.X86_64.AddSub
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.MlKem.X86_64.Mul
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.VMul`. -/
section

/-!
# ML-KEM on x86-64: `BaseCaseMultiply` on words

The words `vbase` computes for a pair (`baseW`): with `mont(x, y) = x · y ·
2⁻¹⁶ mod q`, `mont(mont(a₀, b₀) + mont(mont(a₁, b₁), γ · 2¹⁶), R²)` is `a₀b₀ +
a₁b₁γ` and `mont(mont(a₀, b₁) + mont(a₁, b₀), R²)` is `a₀b₁ + a₁b₀`, modulo
`q`.
-/

namespace VG.Proof.MlKem.X86_64.W

open VG VG.X86_64 VG.Proof.MlKem
open VG.Spec.MlKem (Zq)

/-- `R² mod q`, in a word. -/
def r2W : BitVec 16 := 1353#16

/-- `montW d z` for `d ∈ (-2q, 2q)` and `z ∈ (-q, q)`. -/
theorem mont_small {d z : BitVec 16} (hd1 : -(2 * 3329) < d.toInt) (hd2 : d.toInt < 2 * 3329)
    (hz1 : -3329 < z.toInt) (hz2 : z.toInt < 3329) :
    -3329 < (montW d z).toInt ∧ (montW d z).toInt < 3329 ∧
      3329 ∣ (montW d z).toInt * 65536 - d.toInt * z.toInt := by
  have hn : (d.toInt * z.toInt).natAbs ≤ 6657 * 3328 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by bdd_omega) (by bdd_omega)
  have h1 := Int.le_natAbs (a := d.toInt * z.toInt)
  have h2 := Int.le_natAbs (a := -(d.toInt * z.toInt))
  rw [Int.natAbs_neg] at h2
  obtain ⟨m1, m2, m3⟩ := montW_spec (d := d) (z := z) (by bdd_omega) (by bdd_omega)
  exact ⟨m1, m2, Int.dvd_of_emod_eq_zero m3⟩

theorem toInt_lt_q {a : BitVec 16} {x : Zq} (h : a.toNat = x.val) : a.toInt = x.val ∧ 0 ≤ a.toInt ∧ a.toInt < 3329 := by
  have hx := x.isLt
  have e := toInt_of_lt (a := a) (by rw [h]; exact hx)
  rw [h] at e
  exact ⟨e, by rw [e]; exact Int.natCast_nonneg _, by rw [e]; exact Int.ofNat_lt.mpr hx⟩

/-- The value of a word in `[0, q)` from its value modulo `q`. -/
theorem cadd_val {m : BitVec 16} (h1 : -3329 < m.toInt) (h2 : m.toInt < 3329) {T : Int} {v : Zq}
    (hd : 3329 ∣ m.toInt - T) (hv : (v.val : Int) = T % 3329) : (caddW m).toNat = v.val := by
  have c := caddW_spec (Int.le_of_lt h1) h2
  have n := toNat_of_toInt (a := caddW m) (by rw [c]; exact Int.emod_nonneg _ (by decide))
  rw [c] at n
  obtain ⟨k, hk⟩ := hd
  omega

theorem mulmod (a b n : Nat) : a % n * b % n = a * b % n := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem r2W_toInt : r2W.toInt = 1353 := by decide

/-- The two words of `BaseCaseMultiply` (`vbase`), from the words `a₀, a₁,
b₀, b₁` and `γ · 2¹⁶ mod q`. -/
theorem baseW {a0 a1 b0 b1 g : BitVec 16} {x0 x1 y0 y1 γ : Zq} (ha0 : a0.toNat = x0.val)
    (ha1 : a1.toNat = x1.val) (hb0 : b0.toNat = y0.val) (hb1 : b1.toNat = y1.val)
    (hg : g.toNat = γ.val * 65536 % 3329) :
    (caddW (montW (montW a0 b0 + montW (montW a1 b1) g) VG.Proof.MlKem.X86_64.W.r2W)).toNat = (x0 * y0 + x1 * y1 * γ).val ∧
      (caddW (montW (montW a0 b1 + montW a1 b0) VG.Proof.MlKem.X86_64.W.r2W)).toNat = (x0 * y1 + x1 * y0).val := by
  obtain ⟨A0, A0l, A0h⟩ := VG.Proof.MlKem.X86_64.W.toInt_lt_q ha0
  obtain ⟨A1, A1l, A1h⟩ := VG.Proof.MlKem.X86_64.W.toInt_lt_q ha1
  obtain ⟨B0, B0l, B0h⟩ := VG.Proof.MlKem.X86_64.W.toInt_lt_q hb0
  obtain ⟨B1, B1l, B1h⟩ := VG.Proof.MlKem.X86_64.W.toInt_lt_q hb1
  have hgl : g.toNat < 3329 := by rw [hg]; exact Nat.mod_lt _ (by decide)
  have G := toInt_of_lt hgl
  rw [hg] at G
  have Gl : 0 ≤ g.toInt ∧ g.toInt < 3329 := by
    rw [G]; exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (Nat.mod_lt _ (by decide))⟩
  have hγ := γ.isLt
  have kG : ∃ k : Int, g.toInt - (γ.val : Int) * 65536 = 3329 * k :=
    ⟨-((γ.val : Int) * 65536 / 3329), by rw [G]; omega_using []⟩
  obtain ⟨kG, hkG⟩ := kG
  have r2l : -3329 < r2W.toInt ∧ r2W.toInt < 3329 := by rw [VG.Proof.MlKem.X86_64.W.r2W_toInt]; decide
  -- the products
  obtain ⟨m1l, m1h, ⟨k1, d1⟩⟩ := VG.Proof.MlKem.X86_64.W.mont_small (d := a1) (z := b1) (by omega_using [A1l]) (by omega_using [A1h])
    (by omega_using [B1l]) (by omega_using [B1h])
  obtain ⟨m2l, m2h, ⟨k2, d2⟩⟩ := VG.Proof.MlKem.X86_64.W.mont_small (d := montW a1 b1) (z := g) (by omega_using [m1l])
    (by omega_using [m1h]) (by omega_using [Gl]) (by omega_using [Gl])
  obtain ⟨m3l, m3h, ⟨k3, d3⟩⟩ := VG.Proof.MlKem.X86_64.W.mont_small (d := a0) (z := b0) (by omega_using [A0l]) (by omega_using [A0h])
    (by omega_using [B0l]) (by omega_using [B0h])
  obtain ⟨n1l, n1h, ⟨j1, e1⟩⟩ := VG.Proof.MlKem.X86_64.W.mont_small (d := a0) (z := b1) (by omega_using [A0l]) (by omega_using [A0h])
    (by omega_using [B1l]) (by omega_using [B1h])
  obtain ⟨n2l, n2h, ⟨j2, e2⟩⟩ := VG.Proof.MlKem.X86_64.W.mont_small (d := a1) (z := b0) (by omega_using [A1l]) (by omega_using [A1h])
    (by omega_using [B0l]) (by omega_using [B0h])
  have S1 := toInt_add16 (a := montW a0 b0) (b := montW (montW a1 b1) g) (by omega_using [m3l, m2l])
    (by omega_using [m3h, m2h])
  have S2 := toInt_add16 (a := montW a0 b1) (b := montW a1 b0) (by omega_using [n1l, n2l])
    (by omega_using [n1h, n2h])
  obtain ⟨m4l, m4h, ⟨k4, d4⟩⟩ := VG.Proof.MlKem.X86_64.W.mont_small (d := montW a0 b0 + montW (montW a1 b1) g) (z := VG.Proof.MlKem.X86_64.W.r2W)
    (by rw [S1]; omega_using [m3l, m2l]) (by rw [S1]; omega_using [m3h, m2h]) r2l.1 r2l.2
  obtain ⟨n4l, n4h, ⟨j4, e4⟩⟩ := VG.Proof.MlKem.X86_64.W.mont_small (d := montW a0 b1 + montW a1 b0) (z := VG.Proof.MlKem.X86_64.W.r2W)
    (by rw [S2]; omega_using [n1l, n2l]) (by rw [S2]; omega_using [n1h, n2h]) r2l.1 r2l.2
  rw [S1, VG.Proof.MlKem.X86_64.W.r2W_toInt] at d4
  rw [S2, VG.Proof.MlKem.X86_64.W.r2W_toInt] at e4
  simp only [A0, A1, B0, B1] at d1 d3 e1 e2
  refine ⟨VG.Proof.MlKem.X86_64.W.cadd_val m4l m4h (T := ((x0.val * y0.val + x1.val * y1.val * γ.val : Nat) : Int)) ?_ ?_,
    VG.Proof.MlKem.X86_64.W.cadd_val n4l n4h (T := ((x0.val * y1.val + x1.val * y0.val : Nat) : Int)) ?_ ?_⟩
  · generalize (montW (montW a0 b0 + montW (montW a1 b1) g) VG.Proof.MlKem.X86_64.W.r2W).toInt = M4 at *
    generalize (montW (montW a1 b1) g).toInt = M2 at *
    generalize (montW a0 b0).toInt = M3 at *
    generalize (montW a1 b1).toInt = M1 at *
    generalize g.toInt = Gi at *
    refine ⟨-3327 * M4 + 169 * k4 + 49 * (M3 + M2) + k3 + k2 + M1 * kG + γ.val * k1, ?_⟩
    simp only [Int.natCast_add, Int.natCast_mul]
    grind
  · rw [val_add', val_mul, val_mul, val_mul, VG.Proof.MlKem.X86_64.W.mulmod, ← Nat.add_mod]; exact Int.natCast_emod _ _
  · generalize (montW (montW a0 b1 + montW a1 b0) VG.Proof.MlKem.X86_64.W.r2W).toInt = M4 at *
    generalize (montW a0 b1).toInt = N1 at *
    generalize (montW a1 b0).toInt = N2 at *
    refine ⟨-3327 * M4 + 169 * j4 + 49 * (N1 + N2) + j1 + j2, ?_⟩
    simp only [Int.natCast_add, Int.natCast_mul]
    grind
  · rw [val_add', val_mul, val_mul, ← Nat.add_mod]; exact Int.natCast_emod _ _

end VG.Proof.MlKem.X86_64.W

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- `R² mod q` in every word. -/
def r2V : BitVec 128 := 0x05490549054905490549054905490549#128

theorem word_r2V {i : Nat} (hi : i < 8) : word VG.Proof.MlKem.X86_64.r2V i = W.r2W := by
  rcases (by bdd_omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `d ← mont(src, z)`. -/
theorem movmont_ok {d src z t : XReg} (h1 : z ≠ d) (h2 : t ≠ d) (h3 : z ≠ t) (h5 : XReg.xmm15 ≠ d)
    (h6 : XReg.xmm14 ≠ t) (h7 : XReg.xmm15 ≠ t) (h8 : XReg.xmm14 ≠ d) {s : State} (hc : VConsts s) :
    WP isa (.block (xmov d src :: vmont d z t)) s fun s' =>
      WLanes (s'.xmm d) (fun i => W.montW (word (s.xmm src) i) (word (s.xmm z) i)) ∧ XOnly [d, t] s s' := by
  rw [show xmov d src :: vmont d z t = [xmov d src] ++ vmont d z t from rfl, WP.block_append_iff]
  simp only [xmov, xb]
  vrun
  refine WP.mono (vmont_ok h2 h3 h5 h6 h7 (hc.setXmm h8 h5 _)) fun s' ⟨l, o⟩ => ⟨fun i hi => ?_, ?_⟩
  · rw [l i hi, xmm_setXmm, xmm_setXmm, ifp rfl, ifn h1]; dsimp only; rw [word_movdqa]
  · exact ((XOnly.setXmm (by simp) (XOnly.refl [d] s) _).trans o).mono (by simp)

/-- `d ← d + e`, on words. -/
theorem paddw_ok {d e : XReg} {s : State} :
    WP isa (.block [xb .paddw d e]) s fun s' =>
      (∀ i < 8, word (s'.xmm d) i = word (s.xmm d) i + word (s.xmm e) i) ∧ XOnly [d] s s' := by
  simp only [xb]
  vrun
  exact ⟨fun i hi => word_paddw (a := s.xmm d) (b := s.xmm e) hi, by xonly⟩

theorem block_cons_iff {i : Instr} {l : List Instr} {s : State} {Q : State → Prop} :
    WP isa (.block (i :: l)) s Q ↔ WP isa (.block [i]) s fun s1 => WP isa (.block l) s1 Q := by
  rw [← WP.block_append_iff]; rfl

/-- `vbase`: `BaseCaseMultiply` on the eight pairs of lanes. -/
theorem vbase_ok {s : State} (hc : VConsts s) (hr : s.xmm .xmm12 = VG.Proof.MlKem.X86_64.r2V) {x0 x1 y0 y1 γ : Nat → Zq}
    (h0 : Lanes (s.xmm .xmm0) x0) (h4 : Lanes (s.xmm .xmm4) x1) (h6 : Lanes (s.xmm .xmm6) y0)
    (h10 : Lanes (s.xmm .xmm10) y1) (h13 : ZLanes (s.xmm .xmm13) γ) :
    WP isa (.block vbase) s fun s' => Lanes (s'.xmm .xmm1) (fun i => x0 i * y0 i + x1 i * y1 i * γ i) ∧
      Lanes (s'.xmm .xmm2) (fun i => x0 i * y1 i + x1 i * y0 i) ∧
      XOnly [.xmm1, .xmm2, .xmm3, .xmm4] s s' := by
  simp only [vbase, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.movmont_ok (d := .xmm1) (src := .xmm4) (z := .xmm10) (t := .xmm2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc) fun s1 ⟨l1, o1⟩ => ?_
  have c1 := o1.consts hc (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (vmont_ok (d := .xmm1) (z := .xmm13) (t := .xmm2) (by decide) (by decide) (by decide)
    (by decide) (by decide) c1) fun s2 ⟨l2, o2⟩ => ?_
  have c2 := o2.consts c1 (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.movmont_ok (d := .xmm2) (src := .xmm0) (z := .xmm6) (t := .xmm3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) c2) fun s3 ⟨l3, o3⟩ => ?_
  have c3 := o3.consts c2 (by decide) (by decide)
  rw [WP.block_append_iff, VG.Proof.MlKem.X86_64.block_cons_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.paddw_ok (d := .xmm1) (e := .xmm2)) fun s4 ⟨l4, o4⟩ => ?_
  have c4 := o4.consts c3 (by decide) (by decide)
  refine WP.mono (VG.Proof.MlKem.X86_64.movmont_ok (d := .xmm2) (src := .xmm0) (z := .xmm10) (t := .xmm3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) c4) fun s5 ⟨l5, o5⟩ => ?_
  have c5 := o5.consts c4 (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (vmont_ok (d := .xmm4) (z := .xmm6) (t := .xmm3) (by decide) (by decide) (by decide)
    (by decide) (by decide) c5) fun s6 ⟨l6, o6⟩ => ?_
  have c6 := o6.consts c5 (by decide) (by decide)
  rw [WP.block_append_iff, VG.Proof.MlKem.X86_64.block_cons_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.paddw_ok (d := .xmm2) (e := .xmm4)) fun s7 ⟨l7, o7⟩ => ?_
  have c7 := o7.consts c6 (by decide) (by decide)
  refine WP.mono (vmont_ok (d := .xmm1) (z := .xmm12) (t := .xmm3) (by decide) (by decide) (by decide)
    (by decide) (by decide) c7) fun s8 ⟨l8, o8⟩ => ?_
  have c8 := o8.consts c7 (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (vcadd_ok (d := .xmm1) (t := .xmm3) (by decide) (by decide) c8) fun s9 ⟨l9, o9⟩ => ?_
  have c9 := o9.consts c8 (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (vmont_ok (d := .xmm2) (z := .xmm12) (t := .xmm3) (by decide) (by decide) (by decide)
    (by decide) (by decide) c9) fun s10 ⟨l10, o10⟩ => ?_
  have c10 := o10.consts c9 (by decide) (by decide)
  refine WP.mono (vcadd_ok (d := .xmm2) (t := .xmm3) (by decide) (by decide) c10) fun s11 ⟨l11, o11⟩ => ?_
  -- the registers each step reads
  have e0 : s4.xmm .xmm0 = s.xmm .xmm0 := by
    rw [o4.xmm _ (by decide), o3.xmm _ (by decide), o2.xmm _ (by decide), o1.xmm _ (by decide)]
  have e6 : s5.xmm .xmm6 = s.xmm .xmm6 := by
    rw [o5.xmm _ (by decide), o4.xmm _ (by decide), o3.xmm _ (by decide), o2.xmm _ (by decide),
      o1.xmm _ (by decide)]
  have e10 : s4.xmm .xmm10 = s.xmm .xmm10 := by
    rw [o4.xmm _ (by decide), o3.xmm _ (by decide), o2.xmm _ (by decide), o1.xmm _ (by decide)]
  have e12 : ∀ t, t = s7 ∨ t = s9 → t.xmm .xmm12 = VG.Proof.MlKem.X86_64.r2V := by
    rintro t (rfl | rfl)
    · rw [o7.xmm _ (by decide), o6.xmm _ (by decide), o5.xmm _ (by decide), o4.xmm _ (by decide),
        o3.xmm _ (by decide), o2.xmm _ (by decide), o1.xmm _ (by decide), hr]
    · rw [o9.xmm _ (by decide), o8.xmm _ (by decide), o7.xmm _ (by decide), o6.xmm _ (by decide),
        o5.xmm _ (by decide), o4.xmm _ (by decide), o3.xmm _ (by decide), o2.xmm _ (by decide),
        o1.xmm _ (by decide), hr]
  have e4 : s5.xmm .xmm4 = s.xmm .xmm4 := by
    rw [o5.xmm _ (by decide), o4.xmm _ (by decide), o3.xmm _ (by decide), o2.xmm _ (by decide),
      o1.xmm _ (by decide)]
  have v1 : ∀ i < 8, word (s9.xmm .xmm1) i = W.caddW (W.montW (W.montW (word (s.xmm .xmm0) i)
      (word (s.xmm .xmm6) i) + W.montW (W.montW (word (s.xmm .xmm4) i) (word (s.xmm .xmm10) i))
        (word (s.xmm .xmm13) i)) W.r2W) := fun i hi => by
    rw [l9 i hi]; dsimp only; rw [l8 i hi]; dsimp only
    rw [e12 s7 (.inl rfl), VG.Proof.MlKem.X86_64.word_r2V hi, o7.xmm _ (by decide), o6.xmm _ (by decide), o5.xmm _ (by decide),
      l4 i hi, o3.xmm _ (by decide), l2 i hi, l3 i hi]
    dsimp only
    rw [l1 i hi, o1.xmm _ (by decide), o2.xmm _ (by decide), o1.xmm _ (by decide), BitVec.add_comm]
    dsimp only
    rw [o2.xmm .xmm6 (by decide), o1.xmm .xmm6 (by decide)]
  have v2 : ∀ i < 8, word (s11.xmm .xmm2) i = W.caddW (W.montW (W.montW (word (s.xmm .xmm0) i)
      (word (s.xmm .xmm10) i) + W.montW (word (s.xmm .xmm4) i) (word (s.xmm .xmm6) i)) W.r2W) :=
    fun i hi => by
      rw [l11 i hi]; dsimp only; rw [l10 i hi]; dsimp only
      rw [e12 s9 (.inr rfl), VG.Proof.MlKem.X86_64.word_r2V hi, o9.xmm _ (by decide), o8.xmm _ (by decide), l7 i hi,
        o6.xmm _ (by decide), l6 i hi, l5 i hi]
      dsimp only
      rw [e0, e10, e4, e6]
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [o11.xmm _ (by decide), o10.xmm _ (by decide), v1 i hi]
    exact (W.baseW (h0 i hi) (h4 i hi) (h6 i hi) (h10 i hi) (h13 i hi)).1
  · rw [v2 i hi]
    exact (W.baseW (h0 i hi) (h4 i hi) (h6 i hi) (h10 i hi) (h13 i hi)).2
  · refine ((o1.trans (o2.trans (o3.trans (o4.trans (o5.trans (o6.trans (o7.trans (o8.trans
      (o9.trans (o10.trans o11)))))))))).mono ?_)
    simp

/-! ## Loads and stores -/

/-- The words `deint` leaves of the even doublewords of `l0, …, l3`. -/
def deE (l0 l1 l2 l3 : BitVec 128) : BitVec 128 :=
  XBinOp.eval .packssdw (XBinOp.eval .punpcklqdq (shufDwords l0 0xD8) (shufDwords l1 0xD8))
    (XBinOp.eval .punpcklqdq (shufDwords l2 0xD8) (shufDwords l3 0xD8))

/-- The words `deint` leaves of the odd doublewords of `l0, …, l3`. -/
def deO (l0 l1 l2 l3 : BitVec 128) : BitVec 128 :=
  XBinOp.eval .packssdw (XBinOp.eval .punpckhqdq (shufDwords l0 0xD8) (shufDwords l1 0xD8))
    (XBinOp.eval .punpckhqdq (shufDwords l2 0xD8) (shufDwords l3 0xD8))

theorem shuf_d8 (a : BitVec 128) : shufDwords a 0xD8 = ofDwords (dword a 0) (dword a 2) (dword a 1) (dword a 3) := by
  apply ext_dword <;> simp [dword_shufDwords]

theorem deint_lanes {l0 l1 l2 l3 : BitVec 128} {c : Nat → Nat}
    (h0 : ∀ j < 4, (dword l0 j).toNat = c j) (h1 : ∀ j < 4, (dword l1 j).toNat = c (4 + j))
    (h2 : ∀ j < 4, (dword l2 j).toNat = c (8 + j)) (h3 : ∀ j < 4, (dword l3 j).toNat = c (12 + j))
    (hs : ∀ k < 16, c k < 32768) :
    (∀ e < 8, (word (VG.Proof.MlKem.X86_64.deE l0 l1 l2 l3) e).toNat = c (2 * e)) ∧
      (∀ e < 8, (word (VG.Proof.MlKem.X86_64.deO l0 l1 l2 l3) e).toNat = c (2 * e + 1)) := by
  have lo : ∀ a b : BitVec 128, XBinOp.eval .punpcklqdq (shufDwords a 0xD8) (shufDwords b 0xD8) =
      ofDwords (dword a 0) (dword a 2) (dword b 0) (dword b 2) := fun a b => by
    rw [punpcklqdq_eq, VG.Proof.MlKem.X86_64.shuf_d8, VG.Proof.MlKem.X86_64.shuf_d8]; simp
  have hi : ∀ a b : BitVec 128, XBinOp.eval .punpckhqdq (shufDwords a 0xD8) (shufDwords b 0xD8) =
      ofDwords (dword a 1) (dword a 3) (dword b 1) (dword b 3) := fun a b => by
    rw [punpckhqdq_eq, VG.Proof.MlKem.X86_64.shuf_d8, VG.Proof.MlKem.X86_64.shuf_d8]; simp
  have sm : ∀ a b c d : BitVec 32, a.toNat < 32768 → b.toNat < 32768 → c.toNat < 32768 → d.toNat < 32768 →
      ∀ j < 4, (dword (ofDwords a b c d) j).toNat < 32768 := fun a b c d ha hb hc hd j hj => by
    rcases cases4 hj with rfl | rfl | rfl | rfl <;> simpa
  have t0 : ∀ j < 4, (dword l0 j).toNat < 32768 := fun j hj => by rw [h0 j hj]; exact hs j (by bdd_omega)
  have t1 : ∀ j < 4, (dword l1 j).toNat < 32768 := fun j hj => by rw [h1 j hj]; exact hs _ (by bdd_omega)
  have t2 : ∀ j < 4, (dword l2 j).toNat < 32768 := fun j hj => by rw [h2 j hj]; exact hs _ (by bdd_omega)
  have t3 : ∀ j < 4, (dword l3 j).toNat < 32768 := fun j hj => by rw [h3 j hj]; exact hs _ (by bdd_omega)
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [VG.Proof.MlKem.X86_64.deE, lo, lo, word_packssdw_small _ _ he (sm _ _ _ _ (t0 0 (by decide)) (t0 2 (by decide))
      (t1 0 (by decide)) (t1 2 (by decide))) (sm _ _ _ _ (t2 0 (by decide)) (t2 2 (by decide))
      (t3 0 (by decide)) (t3 2 (by decide)))]
    rcases (by bdd_omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Nat.reduceLT, ite_true, ite_false, Nat.reduceSub, dword_ofDwords_0, dword_ofDwords_1,
        dword_ofDwords_2, dword_ofDwords_3, h0 _ (by decide : 0 < 4), h0 _ (by decide : 2 < 4),
        h1 _ (by decide : 0 < 4), h1 _ (by decide : 2 < 4), h2 _ (by decide : 0 < 4), h2 _ (by decide : 2 < 4),
        h3 _ (by decide : 0 < 4), h3 _ (by decide : 2 < 4)]
  · rw [VG.Proof.MlKem.X86_64.deO, hi, hi, word_packssdw_small _ _ he (sm _ _ _ _ (t0 1 (by decide)) (t0 3 (by decide))
      (t1 1 (by decide)) (t1 3 (by decide))) (sm _ _ _ _ (t2 1 (by decide)) (t2 3 (by decide))
      (t3 1 (by decide)) (t3 3 (by decide)))]
    rcases (by bdd_omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Nat.reduceLT, ite_true, ite_false, Nat.reduceSub, dword_ofDwords_0, dword_ofDwords_1,
        dword_ofDwords_2, dword_ofDwords_3, h0 _ (by decide : 1 < 4), h0 _ (by decide : 3 < 4),
        h1 _ (by decide : 1 < 4), h1 _ (by decide : 3 < 4), h2 _ (by decide : 1 < 4), h2 _ (by decide : 3 < 4),
        h3 _ (by decide : 1 < 4), h3 _ (by decide : 3 < 4)]
theorem deintF_ok {s : State} (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 16)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 16) 16)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 32) 16)
    (h3 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 48) 16) :
    WP isa (.block (deint .rsi .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5)) s fun s' =>
      s'.xmm .xmm0 = VG.Proof.MlKem.X86_64.deE (s.mem.readW (s.gpr .rsi) 128) (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 16) 128)
        (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 32) 128) (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 48) 128) ∧
      s'.xmm .xmm4 = VG.Proof.MlKem.X86_64.deO (s.mem.readW (s.gpr .rsi) 128) (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 16) 128)
        (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 32) 128) (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 48) 128) ∧
      XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5] s s' := by
  simp only [deint]
  vrunm [h0, h1, h2, h3, eval_movdqa]
  exact ⟨rfl, rfl, by xonly⟩
theorem deintG_ok {s : State} (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx) 16)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 16) 16)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 32) 16)
    (h3 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 48) 16) :
    WP isa (.block (deint .rdx .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm11)) s fun s' =>
      s'.xmm .xmm6 = VG.Proof.MlKem.X86_64.deE (s.mem.readW (s.gpr .rdx) 128) (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 16) 128)
        (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 32) 128) (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 48) 128) ∧
      s'.xmm .xmm10 = VG.Proof.MlKem.X86_64.deO (s.mem.readW (s.gpr .rdx) 128) (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 16) 128)
        (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 32) 128) (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 48) 128) ∧
      XOnly [.xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  simp only [deint]
  vrunm [h0, h1, h2, h3, eval_movdqa]
  exact ⟨rfl, rfl, by xonly⟩

theorem off16 (H : Addr) (j t : Nat) : coeffAddr H j + BitVec.ofNat 64 (16 * t) = coeffAddr H (j + 4 * t) := by
  rw [show 16 * t = 4 * (4 * t) by bdd_omega, coeffAddr_off]

/-- Four stores of 16 bytes to coefficients `j, …, j + 15` of the polynomial at `H`. -/
theorem store4 (m : Mem) (H : Addr) {j : Nat} (hj : j + 16 ≤ 256) (Y0 Y1 Y2 Y3 : BitVec 128) :
    let m' := (((m.writeW (coeffAddr H j) Y0).writeW (coeffAddr H j + BitVec.ofNat 64 16) Y1).writeW
      (coeffAddr H j + BitVec.ofNat 64 32) Y2).writeW (coeffAddr H j + BitVec.ofNat 64 48) Y3
    (∀ k < 256, k < j ∨ j + 16 ≤ k → coeffAt m' H k = coeffAt m H k) ∧
      (∀ k < 16, coeffAt m' H (j + k) = dword ([Y0, Y1, Y2, Y3][k / 4]!) (k % 4)) ∧
      Frame [pR H] m m' := by
  intro m'
  have a1 := VG.Proof.MlKem.X86_64.off16 H j 1
  have a2 := VG.Proof.MlKem.X86_64.off16 H j 2
  have a3 := VG.Proof.MlKem.X86_64.off16 H j 3
  simp only [Nat.mul_one] at a1
  simp only [show 16 * 2 = 32 from rfl, show 16 * 3 = 48 from rfl, show 4 * 2 = 8 from rfl,
    show 4 * 3 = 12 from rfl] at a2 a3
  simp only [m', a1, a2, a3]
  refine ⟨fun k hk ho => ?_, fun k hk => ?_, ?_⟩
  · rw [coeffAt_write128 _ _ (by bdd_omega) _ hk, coeffAt_write128 _ _ (by bdd_omega) _ hk,
      coeffAt_write128 _ _ (by bdd_omega) _ hk, coeffAt_write128 _ _ (by bdd_omega) _ hk]
    simp (disch := bdd_omega) only [ite_eq_right]
  · rw [coeffAt_write128 _ _ (by bdd_omega) _ (by bdd_omega), coeffAt_write128 _ _ (by bdd_omega) _ (by bdd_omega),
      coeffAt_write128 _ _ (by bdd_omega) _ (by bdd_omega), coeffAt_write128 _ _ (by bdd_omega) _ (by bdd_omega)]
    rcases (by bdd_omega : k < 4 ∨ (4 ≤ k ∧ k < 8) ∨ (8 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 16)) with h | h | h | h
    · simp (disch := bdd_omega) only [ite_eq_left, ite_eq_right]
      rw [show j + k - j = k % 4 by bdd_omega, show k / 4 = 0 by bdd_omega]; rfl
    · simp (disch := bdd_omega) only [ite_eq_left, ite_eq_right]
      rw [show j + k - (j + 4) = k % 4 by bdd_omega, show k / 4 = 1 by bdd_omega]; rfl
    · simp (disch := bdd_omega) only [ite_eq_left, ite_eq_right]
      rw [show j + k - (j + 8) = k % 4 by bdd_omega, show k / 4 = 2 by bdd_omega]; rfl
    · simp (disch := bdd_omega) only [ite_eq_left]
      rw [show j + k - (j + 12) = k % 4 by bdd_omega, show k / 4 = 3 by bdd_omega]; rfl
  · exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by bdd_omega) (by bdd_omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by bdd_omega) (by bdd_omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by bdd_omega) (by bdd_omega)) |>.writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by bdd_omega) (by bdd_omega))

/-- The words `vinter` interleaves, as the `u32` it stores for each. -/
theorem inter_val (X1 X2 : BitVec 128) {k : Nat} (hk : k < 16) :
    (dword ([XBinOp.eval .punpcklwd (XBinOp.eval .punpcklwd X1 X2) 0,
      XBinOp.eval .punpckhwd (XBinOp.eval .punpcklwd X1 X2) 0,
      XBinOp.eval .punpcklwd (XBinOp.eval .punpckhwd X1 X2) 0,
      XBinOp.eval .punpckhwd (XBinOp.eval .punpckhwd X1 X2) 0][k / 4]!) (k % 4)).toNat =
      (word (if k % 2 = 0 then X1 else X2) (k / 2)).toNat := by
  rcases (by bdd_omega : k < 4 ∨ (4 ≤ k ∧ k < 8) ∨ (8 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 16)) with h | h | h | h
  · rw [show k / 4 = 0 by bdd_omega]
    simp only [List.getElem!_cons_zero]
    rw [dword_punpcklwd0 _ (by bdd_omega), word_punpcklwd _ _ (by bdd_omega), show k % 4 / 2 = k / 2 by bdd_omega,
      show k % 4 % 2 = k % 2 by bdd_omega]
    split <;> rfl
  · rw [show k / 4 = 1 by bdd_omega]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    rw [dword_punpckhwd0 _ (by bdd_omega), word_punpcklwd _ _ (by bdd_omega), show (4 + k % 4) / 2 = k / 2 by bdd_omega,
      show (4 + k % 4) % 2 = k % 2 by bdd_omega]
    split <;> rfl
  · rw [show k / 4 = 2 by bdd_omega]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    rw [dword_punpcklwd0 _ (by bdd_omega), word_punpckhwd _ _ (by bdd_omega), show 4 + k % 4 / 2 = k / 2 by bdd_omega,
      show k % 4 % 2 = k % 2 by bdd_omega]
    split <;> rfl
  · rw [show k / 4 = 3 by bdd_omega]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    rw [dword_punpckhwd0 _ (by bdd_omega), word_punpckhwd _ _ (by bdd_omega),
      show 4 + (4 + k % 4) / 2 = k / 2 by bdd_omega, show (4 + k % 4) % 2 = k % 2 by bdd_omega]
    split <;> rfl

theorem vinter_ok {s : State} {H : Addr} {j : Nat} (hj : j + 16 ≤ 256) (hdi : s.gpr .rdi = coeffAddr H j)
    (hw : pR H ∈ s.wr) :
    WP isa (.block vinter) s fun s' =>
      (∀ k < 256, k < j ∨ j + 16 ≤ k → coeffAt s'.mem H k = coeffAt s.mem H k) ∧
      (∀ k < 16, (coeffAt s'.mem H (j + k)).toNat =
        (word (if k % 2 = 0 then s.xmm .xmm1 else s.xmm .xmm2) (k / 2)).toNat) ∧
      Frame [pR H] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr ∧
      ∀ r, r ∉ [XReg.xmm1, .xmm3, .xmm4, .xmm5, .xmm6] → s'.xmm r = s.xmm r := by
  have w : ∀ t < 4, InRegions s.wr (coeffAddr H j + BitVec.ofNat 64 (16 * t)) 16 := fun t ht => by
    rw [VG.Proof.MlKem.X86_64.off16]; exact ⟨_, hw, Offset.contains_base _ (by bdd_omega) (by bdd_omega)⟩
  have w0 : InRegions s.wr (coeffAddr H j) 16 := by
    have := w 0 (by decide); rwa [Nat.mul_zero, add_ofNat_zero] at this
  simp only [vinter]
  vrunm [hdi, eval_movdqa, pxor_self, w0, w 1 (by decide), w 2 (by decide), w 3 (by decide)]
  obtain ⟨o, v, f⟩ := VG.Proof.MlKem.X86_64.store4 s.mem H hj
    (XBinOp.eval .punpcklwd (XBinOp.eval .punpcklwd (s.xmm .xmm1) (s.xmm .xmm2)) 0)
    (XBinOp.eval .punpckhwd (XBinOp.eval .punpcklwd (s.xmm .xmm1) (s.xmm .xmm2)) 0)
    (XBinOp.eval .punpcklwd (XBinOp.eval .punpckhwd (s.xmm .xmm1) (s.xmm .xmm2)) 0)
    (XBinOp.eval .punpckhwd (XBinOp.eval .punpckhwd (s.xmm .xmm1) (s.xmm .xmm2)) 0)
  refine ⟨o, fun k hk => by rw [v k hk]; exact VG.Proof.MlKem.X86_64.inter_val _ _ hk, f, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr`. -/
section

/-!
# ML-KEM on x86-64: code with MXCSR `0x1FBF`

`withMxcsr r 768 c` (see `Impl/MlKem/X86_64/Vec.lean`) runs `c` from a state
that differs from its own only in `rax`, `r11` and the eight bytes `mxR` of
`scratch`, and after it changes only those bytes and MXCSR (`withMxcsr_ok`).
That it keeps MXCSR's control bits is `ctlOk`
(`Proof/Framework/X86_64/Mxcsr.lean`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-! ## MXCSR -/

/-- The bytes of `scratch` through which `withMxcsr` loads MXCSR. -/
abbrev mxR (sP : Addr) : Region := ⟨sP + BitVec.ofNat 64 768, 8⟩

theorem mx_in {sP : Addr} {rs : List Region} (hw : pR sP ∈ rs) (d : Nat) (hd : 768 ≤ d ∧ d ≤ 772) :
    InRegions rs (sP + BitVec.ofNat 64 d) 4 :=
  ⟨_, hw, Offset.contains_base sP (by omega) (by omega)⟩

theorem mx_sub (sP : Addr) : Region.Sub (VG.Proof.MlKem.X86_64.mxR sP) (pR sP) := Offset.sub_base sP (by decide)

theorem ldmxcsr_ok (v : BitVec 32) :
    BitVec.extractLsb' 16 16 (BitVec.setWidth 32 (BitVec.setWidth 64 (v &&& 0xFFFF))) = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_and, hi, decide_true,
    Bool.true_and]
  rw [show (0xFFFF : BitVec 32).getLsbD (16 + i) = false by revert i; decide]
  simp

/-- `withMxcsr` runs `c` from `s` but for `rax`, `r11` and `mxR`, and
changes nothing more than `mxR` and MXCSR after it. -/
theorem withMxcsr_ok {c : Prog isa} {r : Reg} (hr : r ≠ .r11 ∧ r ≠ .rax) (rs : List Reg)
    (hrs : r ∉ rs ∧ Reg.r11 ∉ rs) {sP : Addr} {s : State} {Q : State → Prop}
    (hsi : s.gpr r = sP) (hw : pR sP ∈ s.wr) (hk : writesOnly rs c = true)
    (hc : ∀ s1, Keep [.rax, .r11] s s1 → Frame [VG.Proof.MlKem.X86_64.mxR sP] s.mem s1.mem → WP isa c s1 Q) :
    WP isa (withMxcsr r 768 c) s fun s' => ∃ s2, Q s2 ∧ Frame [VG.Proof.MlKem.X86_64.mxR sP] s2.mem s'.mem ∧ Keep [] s2 s' := by
  have h0 := VG.Proof.MlKem.X86_64.mx_in hw 768 (by decide)
  have h0' := VG.Proof.MlKem.X86_64.mx_in (List.mem_append_right s.rd hw) 768 (by decide)
  have h4 := VG.Proof.MlKem.X86_64.mx_in hw 772 (by decide)
  simp only [withMxcsr]
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r11 = (s.mxcsr &&& 0xFFFF).setWidth 64 ∧ Keep [.r11] s s1 ∧
    Frame [VG.Proof.MlKem.X86_64.mxR sP] s.mem s1.mem) (by
      vrunm [hsi, h0, h0', Mem.readW_writeW_self32, hr.1]
      refine ⟨by rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq],
        ⟨fun r hr => ?_, rfl, rfl⟩, (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Offset.contains sP (by decide) (by decide) (by decide))⟩
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h11, k1, f1⟩ => ?_)
  have hsi1 : s1.gpr r = sP := by rw [k1.gpr (by simpa using hr.1), hsi]
  have h4' : InRegions s1.wr (sP + BitVec.ofNat 64 (768 + 4)) 4 := by rw [k1.2.2]; exact h4
  have h4'' : InRegions (s1.rd ++ s1.wr) (sP + BitVec.ofNat 64 (768 + 4)) 4 :=
    let ⟨r, hr, hc⟩ := h4'; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.seq (WP.seq (WP.mono (Q := fun (s2 : State) => Keep [.rax] s1 s2 ∧ Frame [VG.Proof.MlKem.X86_64.mxR sP] s1.mem s2.mem)
    (by
      vrunm [hsi1, h4', h4'', Mem.readW_writeW_self32, hr.2]
      refine ⟨⟨fun r hr => ?_, rfl, rfl⟩, (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains sP (by decide) (by decide) (by decide))⟩
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s2 ⟨k2, f2⟩ => ?_))
  refine WP.seq (WP.mono (WP.keep _ (hc s2 ((k1.trans k2).mono (by simp)) (f1.trans f2)) hk)
    fun s3 ⟨hq, k3⟩ => ?_)
  have k23 := k2.trans k3
  have hsi3 : s3.gpr r = sP := by rw [k23.gpr (by simp [hr.2, hrs.1]), hsi1]
  have h113 : s3.gpr .r11 = BitVec.setWidth 64 (s.mxcsr &&& 65535) := by rw [k23.gpr (by simp [hrs.2]), h11]
  have h03 : InRegions s3.wr (sP + BitVec.ofNat 64 768) 4 := by rw [k23.2.2, k1.2.2]; exact h0
  have h03' : InRegions (s3.rd ++ s3.wr) (sP + BitVec.ofNat 64 768) 4 :=
    let ⟨r, hr, hc⟩ := h03; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (Q := fun s4 => s4 = s3) (by vrunm) fun s4 h4 => ?_
  subst h4
  vrunm [hsi3, h113, h03, h03', Mem.readW_writeW_self32, VG.Proof.MlKem.X86_64.ldmxcsr_ok]
  exact ⟨_, hq, (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains sP (by decide) (by decide) (by decide)), fun _ _ => rfl, rfl, rfl⟩

/-! ## Regions of `scratch` -/

theorem pR_sub_tab (sP : Addr) : Region.Sub ⟨sP, 256⟩ (pR sP) := Region.sub_prefix (by decide)

theorem pR_sub_S (sP : Addr) : Region.Sub (sR (spW sP)) (pR sP) := Offset.sub_base sP (by decide)

/-- The regions of `scratch` within it, and `f`. -/
theorem frame_fs {fP sP : Addr} {m m' : Mem} {rs : List Region} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (pR fP) ∨ Region.Sub r (pR sP)) : Frame [pR fP, pR sP] m m' :=
  h.sub fun r hr => (hs r hr).elim (fun h => ⟨_, List.mem_cons_self .., h⟩)
    fun h => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.Mul`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_multiply_ntts`

Each iteration of the loop loads 16 coefficients of `f` and of `g` into the
words of their pairs (`deintF_ok`, `deintG_ok`), multiplies the eight pairs
(`vbase_ok`) and stores the 16 coefficients of `h` (`vinter_ok`): `Mul.step`.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- `vg_mlkem_multiply_ntts(h = rdi, f = rsi, g = rdx, scratch = rcx)`. -/
def mulK : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rsi), pR (s.gpr .rdx)] ∧ s.wr = [pR (s.gpr .rdi), pR (s.gpr .rcx)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rdx)) ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rcx)) ∧
    (pR (s.gpr .rdx)).Disjoint (pR (s.gpr .rcx)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rdx)) ∧ (retR s).Disjoint (pR (s.gpr .rcx)) ∧
    Reduced s.mem (s.gpr .rsi) ∧ Reduced s.mem (s.gpr .rdx)
  post s s' := PolyIs s'.mem (s.gpr .rdi) (multiplyNTTs (polyAt s.mem (s.gpr .rsi)) (polyAt s.mem (s.gpr .rdx)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

theorem gammaTab_eq {i : Nat} : gammaTab i = (gamma i).val := by
  rw [gamma, val_pow]; rfl

theorem gTab_eq (i : Nat) : gTab i = (gamma i).val * 65536 % 3329 := by rw [gTab, VG.Proof.MlKem.X86_64.gammaTab_eq]

theorem gTab_lt (i : Nat) : gTab i < 65536 := by
  have : gTab i < 3329 := Nat.mod_lt _ (by decide)
  omega

namespace Mul

section
variable (s₀ : State)
abbrev hP : Addr := s₀.gpr .rdi
abbrev fP : Addr := s₀.gpr .rsi
abbrev gP : Addr := s₀.gpr .rdx
abbrev sP : Addr := s₀.gpr .rcx
abbrev F : Poly := polyAt s₀.mem (VG.Proof.MlKem.X86_64.Mul.fP s₀)
abbrev G : Poly := polyAt s₀.mem (VG.Proof.MlKem.X86_64.Mul.gP s₀)
end

/-- After `i` groups of 16 coefficients. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = coeffAddr (VG.Proof.MlKem.X86_64.Mul.fP s₀) (16 * i)
  rdx : s.gpr .rdx = coeffAddr (VG.Proof.MlKem.X86_64.Mul.gP s₀) (16 * i)
  rdi : s.gpr .rdi = coeffAddr (VG.Proof.MlKem.X86_64.Mul.hP s₀) (16 * i)
  r8 : s.gpr .r8 = wAddr (VG.Proof.MlKem.X86_64.Mul.sP s₀) (8 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : VConsts s
  r2 : s.xmm .xmm12 = VG.Proof.MlKem.X86_64.r2V
  frame : Frame [pR (VG.Proof.MlKem.X86_64.Mul.hP s₀), pR (VG.Proof.MlKem.X86_64.Mul.sP s₀)] s₀.mem s.mem
  tab : ∀ k < 128, (wordAt s.mem (VG.Proof.MlKem.X86_64.Mul.sP s₀) k).toNat = gTab k
  done : ∀ k < 16 * i, (coeffAt s.mem (VG.Proof.MlKem.X86_64.Mul.hP s₀) k).toNat = ((multiplyNTTs (VG.Proof.MlKem.X86_64.Mul.F s₀) (VG.Proof.MlKem.X86_64.Mul.G s₀))[k]!).val

section
variable {s₀ : State} (hp : mulK.pre s₀)
include hp

theorem inRd {p : Addr} (hp' : p = VG.Proof.MlKem.X86_64.Mul.fP s₀ ∨ p = VG.Proof.MlKem.X86_64.Mul.gP s₀) {j : Nat} (hj : j + 16 ≤ 256) {t : Nat} (ht : t < 4) :
    InRegions (s₀.rd ++ s₀.wr) (coeffAddr p j + BitVec.ofNat 64 (16 * t)) 16 := by
  rw [VG.Proof.MlKem.X86_64.off16, hp.1, hp.2.1]
  rcases hp' with rfl | rfl
  · exact ⟨pR _, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · exact ⟨pR _, by simp, Offset.contains_base _ (by omega) (by omega)⟩

/-- `f` and `g` are not written. -/
theorem coeffFG {m : Mem} (hf : Frame [pR (VG.Proof.MlKem.X86_64.Mul.hP s₀), pR (VG.Proof.MlKem.X86_64.Mul.sP s₀)] s₀.mem m) {p : Addr} (hp' : p = VG.Proof.MlKem.X86_64.Mul.fP s₀ ∨ p = VG.Proof.MlKem.X86_64.Mul.gP s₀)
    {k : Nat} (hk : k < 256) : (coeffAt m p k).toNat = ((polyAt s₀.mem p)[k]!).val := by
  have hd : ∀ r ∈ [pR (VG.Proof.MlKem.X86_64.Mul.hP s₀), pR (VG.Proof.MlKem.X86_64.Mul.sP s₀)], (polyRegion p).Disjoint r := by
    rcases hp' with rfl | rfl
    · simpa using ⟨hp.2.2.1.symm, hp.2.2.2.2.2.1⟩
    · simpa using ⟨hp.2.2.2.1.symm, hp.2.2.2.2.2.2.1⟩
  have hr : Reduced s₀.mem p := by
    rcases hp' with rfl | rfl
    · exact hp.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hp.2.2.2.2.2.2.2.2.2.2.2.2
  rw [coeffAt_congr (bytes_frame hf hd (by decide)) (by rw [n_eq]; exact hk),
    polyAt_val hr (by rw [n_eq]; exact hk)]

/-- The 16 coefficients from `j` of `f` or `g`, as `deint_lanes` takes them. -/
theorem loads {m : Mem} (hf : Frame [pR (VG.Proof.MlKem.X86_64.Mul.hP s₀), pR (VG.Proof.MlKem.X86_64.Mul.sP s₀)] s₀.mem m) {p : Addr} (hp' : p = VG.Proof.MlKem.X86_64.Mul.fP s₀ ∨ p = VG.Proof.MlKem.X86_64.Mul.gP s₀)
    {j : Nat} (hj : j + 16 ≤ 256) {t : Nat} (ht : t < 4) :
    ∀ e < 4, (dword (m.readW (coeffAddr p j + BitVec.ofNat 64 (16 * t)) 128) e).toNat =
      ((polyAt s₀.mem p)[j + (4 * t + e)]!).val := fun e he => by
  rw [VG.Proof.MlKem.X86_64.off16, dword_readW _ _ he, coeffAddr_off, ← coeffAt_eq, Nat.add_assoc, VG.Proof.MlKem.X86_64.Mul.coeffFG hp hf hp' (by omega)]

omit hp in
/-- A value of the product, from the lanes `vbase` leaves. -/
theorem prod_val {i : Nat} (hi : i < 16) {X1 X2 : BitVec 128} {F G : Poly}
    (h1 : Lanes X1 fun e => F[16 * i + 2 * e]! * G[16 * i + 2 * e]! +
      F[16 * i + 2 * e + 1]! * G[16 * i + 2 * e + 1]! * gamma (8 * i + e))
    (h2 : Lanes X2 fun e => F[16 * i + 2 * e]! * G[16 * i + 2 * e + 1]! + F[16 * i + 2 * e + 1]! * G[16 * i + 2 * e]!)
    {k : Nat} (hk : k < 16) :
    (word (if k % 2 = 0 then X1 else X2) (k / 2)).toNat = ((multiplyNTTs F G)[16 * i + k]!).val := by
  rw [multiplyNTTs_get F G (by rw [n_eq]; omega)]
  split
  · rename_i he
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), h1 _ (by omega)]
    dsimp only
    rw [show 16 * i + 2 * (k / 2) = 16 * i + k by omega, show (16 * i + k) / 2 = 8 * i + k / 2 by omega]
  · rename_i he
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), h2 _ (by omega)]
    dsimp only
    rw [show 16 * i + 2 * (k / 2) = 16 * i + k - 1 by omega, show 16 * i + k - 1 + 1 = 16 * i + k by omega]

theorem step {i : Nat} (hi : i < 16) {s : State} (hI : VG.Proof.MlKem.X86_64.Mul.Inv s₀ i s) :
    WP isa (.block (mulBody ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      VG.Proof.MlKem.X86_64.Mul.Inv s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hrr : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [hI.rd, hI.wr]
  have hj : 16 * i + 16 ≤ 256 := by omega
  have rF : ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (16 * t)) 16 := fun t ht => by
    rw [hrr, hI.rsi]; exact VG.Proof.MlKem.X86_64.Mul.inRd hp (.inl rfl) hj ht
  have rG : ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (16 * t)) 16 := fun t ht => by
    rw [hrr, hI.rdx]; exact VG.Proof.MlKem.X86_64.Mul.inRd hp (.inr rfl) hj ht
  have r0 : ∀ {a : Addr}, InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (16 * 0)) 16 →
      InRegions (s.rd ++ s.wr) a 16 := fun h => by rwa [Nat.mul_zero, add_ofNat_zero] at h
  simp only [mulBody, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.deintF_ok (r0 (rF 0 (by decide))) (rF 1 (by decide)) (rF 2 (by decide)) (rF 3 (by decide)))
    fun s1 ⟨e0, e4, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.deintG_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact r0 (rG 0 (by decide)))
    (by rw [o1.rd, o1.wr, o1.gpr]; exact rG 1 (by decide)) (by rw [o1.rd, o1.wr, o1.gpr]; exact rG 2 (by decide))
    (by rw [o1.rd, o1.wr, o1.gpr]; exact rG 3 (by decide))) fun s2 ⟨e6, e10, o2⟩ => ?_
  have o12 := o1.trans o2
  have hz : InRegions (s2.rd ++ s2.wr) (s2.gpr .r8) 16 := by
    rw [o12.rd, o12.wr, o12.gpr, hrr, hI.r8, hp.1, hp.2.1]
    exact ⟨pR (VG.Proof.MlKem.X86_64.Mul.sP s₀), by simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s3 : State) => s3.xmm .xmm13 = s2.mem.readW (s2.gpr .r8) 128 ∧ XOnly [.xmm13] s2 s3)
    (by vrunm [hz]; xonly) fun s3 ⟨e13, o3⟩ => ?_
  have o123 := o12.trans o3
  -- the lanes `vbase` multiplies
  have LF : ∀ t < 4, ∀ e < 4, (dword (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (16 * t)) 128) e).toNat =
      ((VG.Proof.MlKem.X86_64.Mul.F s₀)[16 * i + (4 * t + e)]!).val := fun t ht => by rw [hI.rsi]; exact VG.Proof.MlKem.X86_64.Mul.loads hp hI.frame (.inl rfl) hj ht
  have LG : ∀ t < 4, ∀ e < 4, (dword (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (16 * t)) 128) e).toNat =
      ((VG.Proof.MlKem.X86_64.Mul.G s₀)[16 * i + (4 * t + e)]!).val := fun t ht => by rw [hI.rdx]; exact VG.Proof.MlKem.X86_64.Mul.loads hp hI.frame (.inr rfl) hj ht
  have DF := VG.Proof.MlKem.X86_64.deint_lanes (c := fun k => ((VG.Proof.MlKem.X86_64.Mul.F s₀)[16 * i + k]!).val)
    (fun e he => by have := LF 0 (by decide) e he; simpa only [Nat.mul_zero, add_ofNat_zero, Nat.zero_add] using this)
    (fun e he => LF 1 (by decide) e he) (fun e he => LF 2 (by decide) e he) (fun e he => LF 3 (by decide) e he)
    (fun k _ => by have := val_lt ((VG.Proof.MlKem.X86_64.Mul.F s₀)[16 * i + k]!); omega)
  have DG := VG.Proof.MlKem.X86_64.deint_lanes (c := fun k => ((VG.Proof.MlKem.X86_64.Mul.G s₀)[16 * i + k]!).val)
    (fun e he => by have := LG 0 (by decide) e he; simpa only [Nat.mul_zero, add_ofNat_zero, Nat.zero_add] using this)
    (fun e he => LG 1 (by decide) e he) (fun e he => LG 2 (by decide) e he) (fun e he => LG 3 (by decide) e he)
    (fun k _ => by have := val_lt ((VG.Proof.MlKem.X86_64.Mul.G s₀)[16 * i + k]!); omega)
  have x0 : s3.xmm .xmm0 = s1.xmm .xmm0 := by rw [o3.xmm _ (by decide), o2.xmm _ (by decide)]
  have x4 : s3.xmm .xmm4 = s1.xmm .xmm4 := by rw [o3.xmm _ (by decide), o2.xmm _ (by decide)]
  have x6 : s3.xmm .xmm6 = s2.xmm .xmm6 := o3.xmm _ (by decide)
  have x10 : s3.xmm .xmm10 = s2.xmm .xmm10 := o3.xmm _ (by decide)
  rw [o1.gpr, o1.mem] at e6 e10
  have hZ : ZLanes (s3.xmm .xmm13) (fun e => gamma (8 * i + e)) := fun e he => by
    rw [e13, o12.mem, o12.gpr, hI.r8, word_readW _ _ he, wAddr_add, ← wordAt, hI.tab _ (by omega), VG.Proof.MlKem.X86_64.gTab_eq]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.vbase_ok (x0 := fun e => (VG.Proof.MlKem.X86_64.Mul.F s₀)[16 * i + 2 * e]!) (x1 := fun e => (VG.Proof.MlKem.X86_64.Mul.F s₀)[16 * i + 2 * e + 1]!)
    (y0 := fun e => (VG.Proof.MlKem.X86_64.Mul.G s₀)[16 * i + 2 * e]!) (y1 := fun e => (VG.Proof.MlKem.X86_64.Mul.G s₀)[16 * i + 2 * e + 1]!)
    (o123.consts hI.c (by decide) (by decide)) (by rw [o123.xmm _ (by decide), hI.r2])
    (fun e he => by rw [x0, e0]; exact DF.1 e he) (fun e he => by rw [x4, e4]; exact DF.2 e he)
    (fun e he => by rw [x6, e6]; exact DG.1 e he) (fun e he => by rw [x10, e10]; exact DG.2 e he) hZ)
    fun s4 ⟨h1, h2, o4⟩ => ?_
  have o1234 := o123.trans o4
  have hw4 : pR (VG.Proof.MlKem.X86_64.Mul.hP s₀) ∈ s4.wr := by rw [o1234.wr, hI.wr, hp.2.1]; simp
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.vinter_ok hj (by rw [o1234.gpr, hI.rdi]) hw4)
    fun s5 ⟨out, inr, f5, g5, rd5, wr5, mx5, x5⟩ => ?_
  have sx64 : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (4 * 16) := by decide
  vrunm [g5, o1234.gpr, sx64]
  have tS : ∀ k < 128, wordAt s5.mem (VG.Proof.MlKem.X86_64.Mul.sP s₀) k = wordAt s.mem (VG.Proof.MlKem.X86_64.Mul.sP s₀) k := fun k hk => by
    rw [wordAt, f5.readW (r := pR (VG.Proof.MlKem.X86_64.Mul.sP s₀)) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.2.2.2.2.1.symm) (by decide), o1234.mem]; rfl
  constructor
  all_goals try simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.rd_setReg, RegUpd.rd_setFlags,
    RegUpd.wr_setReg, RegUpd.wr_setFlags, RegUpd.xmm_setReg, RegUpd.xmm_setFlags, setReg_mem, setFlags_mem,
    reduceCtorEq, ite_true, ite_false]
  case rsi => rw [hI.rsi, coeffAddr_off, Nat.mul_succ]
  case rdx => rw [hI.rdx, coeffAddr_off, Nat.mul_succ]
  case rdi => rw [hI.rdi, coeffAddr_off, Nat.mul_succ]
  case r8 => rw [hI.r8, show (16 : BitVec 64) = BitVec.ofNat 64 (2 * 8) from rfl, wAddr_add, Nat.mul_succ]
  case rd => rw [rd5, o1234.rd, hI.rd]
  case wr => rw [wr5, o1234.wr, hI.wr]
  case c =>
    refine ⟨?_, ?_⟩ <;> simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]
    · rw [x5 _ (by decide), o1234.xmm _ (by decide), hI.c.q]
    · rw [x5 _ (by decide), o1234.xmm _ (by decide), hI.c.qinv]
  case r2 => rw [x5 _ (by decide), o1234.xmm _ (by decide), hI.r2]
  case frame => exact hI.frame.trans (by rw [← o1234.mem]; exact f5.mono (by simp))
  case tab => exact fun k hk => by rw [tS k hk]; exact hI.tab k hk
  case done =>
    intro k hk
    by_cases hk' : k < 16 * i
    · rw [out k (by omega) (.inl hk'), o1234.mem]; exact hI.done k hk'
    · obtain ⟨k', rfl⟩ : ∃ k', k = 16 * i + k' := ⟨k - 16 * i, by omega⟩
      rw [inr k' (by omega)]
      exact VG.Proof.MlKem.X86_64.Mul.prod_val hi h1 h2 (by omega)

theorem correct : ∃ t s', Exec isa Impl.MlKem.X86_64.multiplyNTTs s₀ t s' ∧ abiPreserved s₀ s' ∧
    mulK.post s₀ s' := by
  have hw : pR (VG.Proof.MlKem.X86_64.Mul.sP s₀) ∈ s₀.wr := by rw [hp.2.1]; simp
  have hW : WP isa Impl.MlKem.X86_64.multiplyNTTs s₀ fun s' => ∃ s3,
      (PolyIs s3.mem (VG.Proof.MlKem.X86_64.Mul.hP s₀) (multiplyNTTs (VG.Proof.MlKem.X86_64.Mul.F s₀) (VG.Proof.MlKem.X86_64.Mul.G s₀)) ∧ Frame [pR (VG.Proof.MlKem.X86_64.Mul.hP s₀), pR (VG.Proof.MlKem.X86_64.Mul.sP s₀)] s₀.mem s3.mem) ∧
      Frame [VG.Proof.MlKem.X86_64.mxR (VG.Proof.MlKem.X86_64.Mul.sP s₀)] s3.mem s'.mem ∧ Keep [] s3 s' := by
    unfold Impl.MlKem.X86_64.multiplyNTTs
    refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r10 = VG.Proof.MlKem.X86_64.Mul.sP s₀ ∧ s1.mem = s₀.mem ∧
      s1.xmm = s₀.xmm ∧ Keep [.r10] s₀ s1) (by
        vrunm
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_singleton] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s1 ⟨h10, hm1, _, k1⟩ => ?_)
    refine VG.Proof.MlKem.X86_64.withMxcsr_ok (by decide) [.rax, .rcx, .rdx, .rdi, .rsi, .r8, .r9] (by decide) h10
      (by rw [k1.2.2]; exact hw) ?_ fun s2 k2 f2 => ?_
    · decide +kernel
    have k12 := k1.trans k2
    have h10' : s2.gpr .r10 = VG.Proof.MlKem.X86_64.Mul.sP s₀ := by rw [k2.gpr (by decide), h10]
    refine WP.seq ?_
    simp only [mulPro, List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (wordTab_gen gTab VG.Proof.MlKem.X86_64.gTab_lt (by decide) h10' (by rw [k12.2.2]; exact hw))
      fun s3 ⟨ht, f3, k3, _, _⟩ => ?_
    have h10'' : s3.gpr .r10 = VG.Proof.MlKem.X86_64.Mul.sP s₀ := by rw [k3.gpr (by decide), h10']
    refine WP.mono (Q := fun (s4 : State) => VConsts s4 ∧ s4.xmm .xmm12 = VG.Proof.MlKem.X86_64.r2V ∧ s4.gpr .r8 = VG.Proof.MlKem.X86_64.Mul.sP s₀ ∧
      s4.mem = s3.mem ∧ Keep [.rax, .r8] s3 s4) (by
        simp only [vconsts]
        vrunm [h10'']
        refine ⟨⟨?_, ?_⟩, fun r hr => ?_, rfl, rfl⟩
        · simp only [RegUpd.xmm_setReg, xmm_setXmm, ite_true, ite_false, reduceCtorEq]
          decide
        · simp only [RegUpd.xmm_setReg, xmm_setXmm, ite_true, ite_false, reduceCtorEq]
          decide
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_setXmm, hr, ite_false])
      fun s4 ⟨hc4, hr4, h84, hm4, k4⟩ => ?_
    have k14 := (k12.trans k3).trans k4
    refine WP.mono (wp_rcxLoop (N := 16) (by decide) (by decide) (VG.Proof.MlKem.X86_64.Mul.Inv s₀) (fun s g _ => ?_)
      fun i hi s hI => VG.Proof.MlKem.X86_64.Mul.step hp hi hI) fun s5 hI => ⟨?_, hI.frame⟩
    · have k := k14.trans g.keep
      refine ⟨?_, ?_, ?_, ?_, by rw [k.2.1], by rw [k.2.2], ?_, ?_, ?_, ?_, fun _ h => absurd h (by omega)⟩
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [g.keep.gpr (by decide), h84]; exact (add_ofNat_zero _).symm
      · exact ⟨by rw [g.xmm]; exact hc4.q, by rw [g.xmm]; exact hc4.qinv⟩
      · rw [g.xmm]; exact hr4
      · rw [g.mem, hm4, ← hm1]
        refine (VG.Proof.MlKem.X86_64.frame_fs (fP := VG.Proof.MlKem.X86_64.Mul.hP s₀) f2 ?_).trans (VG.Proof.MlKem.X86_64.frame_fs f3 ?_) <;>
          intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
        exacts [.inr (VG.Proof.MlKem.X86_64.mx_sub _), .inr (VG.Proof.MlKem.X86_64.pR_sub_tab _)]
      · intro k hk; rw [g.mem, hm4]; exact ht k hk
    · exact polyIs_of_toNat fun k hk => hI.done k (by rw [n_eq] at hk; omega)
  obtain ⟨t, s', he, ⟨s3, ⟨hP', hf⟩, hf', -⟩, hk⟩ :=
    WP.keep [.rax, .rcx, .rdx, .rdi, .rsi, .r8, .r9, .r10, .r11] hW (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide)
    (hf.trans (hf'.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩))
    (by simpa using ⟨hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1⟩)), ?_⟩
  · rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.X86_64.mx_sub _
  · exact polyIs_frame hf' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.2.2.2.2.1.sub_right (VG.Proof.MlKem.X86_64.mx_sub _)) hP'

end

end Mul

theorem mul_correct (s : State) (hs : mulK.pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.multiplyNTTs s t s' ∧ abiPreserved s s' ∧ mulK.post s s' :=
  Mul.correct hs

theorem mul_ct : ConstantTime isa mulK.pre mulK.pub Impl.MlKem.X86_64.multiplyNTTs :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2])
    (by taint_decide)

/-- A state satisfying the precondition. -/
def mulSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0x4000, 1024⟩]

theorem mul_verified :
    Verified X86_64.target Impl.MlKem.X86_64.multiplyNTTs (Spec.MlKem.mulContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlKem.X86_64.mul_correct VG.Proof.MlKem.X86_64.mul_ct (by
    mlkem_implies [Spec.MlKem.mulContract, Spec.MlKem.mulSig, VG.Proof.MlKem.X86_64.mulK, X86_64.abi, X86_64.argRegs]
      [mulSat] using VG.Proof.MlKem.X86_64.mulSat)

end VG.Proof.MlKem.X86_64

end
