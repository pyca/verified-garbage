module
public import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
public import VerifiedGarbage.Proof.Weierstrass.Booth
public import VerifiedGarbage.Proof.Weierstrass.X86.TComb

public import VerifiedGarbage.Proof.Weierstrass.Law3
import VerifiedGarbage.Proof.Ecdsa.X86.Stages
import VerifiedGarbage.Proof.Ecdsa.X86.Lays

/-! # Layout and table facts for the x86 fixed-base comb -/

@[expose] public section

namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

/-- What the code needs of a comb's shape: its windows cover the scalar's
`64 n` bits, the last one in part. The comb with Booth's digits clears the
bits past them, in the word past the table of bits; the comb by complete
additions reads only the scalar's bits, so its top window must be partial. -/
structure CombOk (c : Cfg) (d : CombData) : Prop where
  w : 1 ≤ d.w ∧ d.w < 9
  cover : 64 * c.n ≤ d.w * c.combJ d.w ∧ d.w * c.combJ d.w ≤ 64 * c.n + 8
  jac : d.jac = true → d.w * c.combJ d.w ≤ 64 * c.n + 4
  top : d.jac = false → d.w * (c.combJ d.w - 1) ≤ 64 * c.n ∧ 64 * c.n < d.w * c.combJ d.w

/-- What the comb needs of its tables: they are `G`'s, and for the comb with
Booth's digits and Jacobian additions, `G` has the prime order `n` (no digit's
term meets the sum below it) and `a = -3`. -/
def CombTbls (c : Cfg) : Prop :=
  ∀ d, c.comb = some d → CombOkW c.C d.w (c.combJ d.w) d.tbl d.start ∧
    (d.jac = true → BoothOk c.C d.w (c.combJ d.w) (2 ^ (64 * c.n)) ∧ AM3 c.C)

variable {c : Cfg}

/-- A curve the proof supports, with a comb: its tables change nothing of what the proof needs
of the curve. -/
theorem CfgOk.withComb (h : CfgOk c) (d : CombData) : CfgOk { c with comb := some d } := by
  rcases h with ⟨a, b, c', d', e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t⟩
  exact ⟨a, b, c', d', e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t⟩

theorem combW_eq (c : Cfg) (d : CombData) : combW (c.combCfg d).toComb = slW c [RX, RY, RZ, TX, TY, TZ, PT,
    T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP] := rfl

theorem combSlots_eq (c : Cfg) (d : CombData) : combSlots (c.combCfg d).toComb = [AP, EM, ZERO, RX, RY,
    RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ].map c.sl := rfl

/-- The comb with Booth's digits clears at most the word past the table of `k`'s bits. -/
theorem zw_le {d : CombData} (hd : CombOk c d) (hj : d.jac = true) : 4 * (c.combCfg d).zw ≤ 4 := by
  have := hd.cover
  have := hd.jac hj
  show 4 * ((d.w * c.combJ d.w - 64 * c.n + 3) / 4) ≤ 4
  omega_using [this]

/-- The words past the scalar's bits that a comb's windows cover. -/
theorem zw_le8 {d : CombData} (hd : CombOk c d) : 4 * (c.combCfg d).zw ≤ 8 := by
  have := hd.cover
  show 4 * ((d.w * c.combJ d.w - 64 * c.n + 3) / 4) ≤ 8
  omega_using [this]

theorem combJ_bounds {d : CombData} (hc : CfgOk c) (hd : CombOk c d) :
    1 ≤ c.combJ d.w ∧ c.combJ d.w ≤ 64 * c.n + 8 := by
  have h0 := hc.n0
  have hc' := hd.cover
  have hw := hd.w
  have : c.combJ d.w ≤ d.w * c.combJ d.w := Nat.le_mul_of_pos_left _ (by omega_using [hw])
  refine ⟨Nat.pos_of_ne_zero fun h => ?_, by omega_using [hc', this]⟩
  rw [h, Nat.mul_zero] at hc'; omega_using [h0, hc']

theorem combLay {d : CombData} (hc : CfgOk c) (hd : CombOk c d) : CombLay (c.combCfg d).toComb size := by
  have hn := hc.n0
  have h7 := hc.n10
  have hJ : (c.combCfg d).toComb.J = c.combJ d.w := by rw [TCombCfg.toComb_J]; rfl
  have hJb := combJ_bounds hc hd
  refine ⟨?_, rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (lr := [AP, EM, RX, RY, RZ, TX, TY, TZ]) rfl rfl (by decide) (by decide), ?_,
    map_sl_nodup hn (l := [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (by decide), ⟨by rw [hJ]; omega_using [hJb], by rw [hJ]; omega_using [h7, hJb]⟩, ?_, ?_, ?_⟩
  · exact lay_map hc rfl rfl rfl (l := [AP, EM, ZERO, RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3,
      T4, T5, DX, DY, DZ]) (by decide)
  · exact map_sl_disj hn (l₁ := [AP, EM, ZERO])
      (l₂ := [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ]) (by decide)
  · rw [hJ]; show c.wk + 4 * c.combJ d.w ≤ 8192; rw [wk_eq]; omega_using [h7, hJb]
  · show c.wk + 3 < 4096; rw [wk_eq]; omega_using [hn]
  · intro w hw
    rw [combW_eq] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have hl : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP], i < 45 := by
      decide
    exact Or.inr (sl_below_wk c (hl i hi))

/-- The comb's slots are below the functions' own working space. -/
theorem combWsl (hc : CfgOk c) (d : CombData) :
    ∀ x, x ∈ combSlots (c.combCfg d).toComb → x + 8 * (c.combCfg d).M.n ≤ (c.combCfg d).wk := by
  have h7 := hc.n10
  rw [combSlots_eq]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  have : ∀ i ∈ [AP, EM, ZERO, RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ], i < 45 := by decide
  exact sl_below_wk c (this i hi)

theorem tcombLay {d : CombData} (hc : CfgOk c) (hd : CombOk c d) : TCombLay (c.combCfg d) size := by
  have hn := hc.n0
  have h7 := hc.n10
  have hz := zw_le8 hd
  have hbits : (c.combCfg d).bits = bitsAt c.n 0 := rfl
  have hk : (c.combCfg d).kbytes = 64 * c.n := rfl
  have hl : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP], i < 45 := by decide
  refine ⟨combLay hc hd, rfl, combWsl hc d, sl_below_wk c (i := MP) (by decide),
    sl_below_wk c (i := TMP) (by decide), .inr (wk_below_bits c 0), (by change 64 ≤ 8192; decide),
    ?_, ?_, ?_, hd.w, hd.cover.1, ?_, ?_, ?_, ?_,
    ⟨hn, show c.n ≤ 12 by omega_using [h7]⟩, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact .inl (by change 64 ≤ c.sl MP; rw [sl_eq]; omega_using [])
    · exact .inl (by change 64 ≤ c.sl TMP; rw [sl_eq]; omega_using [])
    · rw [combSlots_eq] at hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact .inl (by change 64 ≤ c.sl i; rw [sl_eq]; omega_using [])
  · change 64 ≤ c.wk; rw [wk_eq]; omega_using [h7]
  · exact .inl (by change 64 ≤ bitsAt c.n 0; rw [bitsAt_eq]; omega_using [])
  · rw [hbits, hk, bitsAt_eq]; change _ ≤ 8192; omega_using [h7, hz]
  · rw [hbits, hk, bitsAt_eq]; omega_using []
  · intro w hw
    rw [combW_eq] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact .inr (by rw [hbits]; exact sl_below_bits c (hl i hi) 0 0)
  · intro x hx
    rw [hbits, hk]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .inr (sl_below_bits c (i := MP) (by decide) 0 _)
    · rw [combSlots_eq] at hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have : ∀ i ∈ [AP, EM, ZERO, RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ], i < 45 := by decide
      exact .inr (sl_below_bits c (this i hi) 0 _)
  · show 64 + 8 * c.n * 21 = 64 + 8 * c.n * 20 + 8 * c.n
    rw [Nat.mul_succ]; omega_using []
  · show 16 * c.n * 2 ^ (d.w - 1) < 2 ^ 31
    have : 2 ^ (d.w - 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by have := hd.w; omega_using [this])
    have : 16 * c.n * 2 ^ (d.w - 1) ≤ 16 * 9 * 2 ^ 7 := Nat.mul_le_mul (by omega_using [h7]) this
    omega_using [this]

theorem mont_lt (hc : CfgOk c) (x : Nat) : c.mont x < c.C.p :=
  Nat.mod_lt _ (by have := hc.p_ge; omega_using [this])

/-- The comb's constants, from its tables' facts. -/
theorem tcombVals {d : CombData} (hc : CfgOk c) (hC : Law c.C)
    (hd : CombOkW c.C d.w (c.combJ d.w) d.tbl d.start) : TCombVals (c.combCfg d) c.C d.tbl where
  len := hd.len
  lenH := hd.lenH
  unit := unitMod_pow_two hc.p_odd _
  one_lt := mont_lt hc 1
  one := by
    show toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1
    rw [toM_cmont hc]; rfl
  entry j hj m hm := by
    rw [combPtW, show (c.combCfg d).w = d.w from rfl, hd.entry j hj m hm]
    exact rep_affine' hC _ _
  start_lt := ⟨mont_lt hc _, mont_lt hc _⟩
  start := by
    show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (c.mont d.start.1))
      (toM c.C.p (2 ^ (64 * c.n)) (c.mont d.start.2)) 1 _
    rw [toM_cmont hc, toM_cmont hc, show (c.combCfg d).H = 2 ^ (d.w - 1) from rfl,
      show (c.combCfg d).w = d.w from rfl, show (c.combCfg d).J = c.combJ d.w from rfl, hd.start]
    exact rep_affine' hC _ _
  fn := hc.fp


end VG.Proof.Ecdsa.X86
