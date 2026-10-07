import VerifiedGarbage.Proof.Ecdsa.X86.Stages
import VerifiedGarbage.Proof.Weierstrass.X86.TComb

/-! # Layout and table facts for the x86 fixed-base comb -/
namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

structure CombOk (c : Cfg) (d : CombData) : Prop where
  w : 1 ≤ d.w ∧ d.w < 9
  cover : 64 * c.n ≤ d.w * c.combJ d.w ∧ d.w * c.combJ d.w ≤ 64 * c.n + 4
  n : c.n ≤ 6

def CombTbls (c : Cfg) : Prop :=
  ∀ d, c.comb = some d → CombOkW c.C d.w (c.combJ d.w) d.tbl d.start

variable {c : Cfg}

theorem combW_eq (c : Cfg) (d : CombData) : combW (c.combCfg d).toComb = slW c [RX, RY, RZ, TX, TY, TZ, PT,
    T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP] := rfl

theorem combSlots_eq (c : Cfg) (d : CombData) : combSlots (c.combCfg d).toComb = [AP, EM, ZERO, RX, RY,
    RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ].map c.sl := rfl

/-- The comb clears at most the word past the table of `k`'s bits. -/
theorem zw_le {d : CombData} (hd : CombOk c d) : 4 * (c.combCfg d).zw ≤ 4 := by
  have := hd.cover
  show 4 * ((d.w * c.combJ d.w - 64 * c.n + 3) / 4) ≤ 4
  omega

theorem combJ_bounds {d : CombData} (hc : CfgOk c) (hd : CombOk c d) :
    1 ≤ c.combJ d.w ∧ c.combJ d.w ≤ 64 * c.n + 8 := by
  have h0 := hc.n0
  have hc' := hd.cover
  have hw := hd.w
  have : c.combJ d.w ≤ d.w * c.combJ d.w := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨Nat.pos_of_ne_zero fun h => ?_, by omega⟩
  rw [h, Nat.mul_zero] at hc'; omega

theorem combLay {d : CombData} (hc : CfgOk c) (hd : CombOk c d) : CombLay (c.combCfg d).toComb size := by
  have hn := hc.n0
  have h7 := hc.n10
  have hJ : (c.combCfg d).toComb.J = c.combJ d.w := by rw [TCombCfg.toComb_J]; rfl
  have hJb := combJ_bounds hc hd
  refine ⟨?_, rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (lr := [AP, EM, RX, RY, RZ, TX, TY, TZ]) rfl rfl (by decide) (by decide), ?_,
    map_sl_nodup hn (l := [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (by decide), ⟨by rw [hJ]; omega, by rw [hJ]; omega⟩, ?_, ?_, ?_⟩
  · exact lay_map hc rfl rfl rfl (l := [AP, EM, ZERO, RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3,
      T4, T5, DX, DY, DZ]) (by decide)
  · exact map_sl_disj hn (l₁ := [AP, EM, ZERO])
      (l₂ := [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ]) (by decide)
  · rw [hJ]; show bitsAt c.n 0 + 4 * c.combJ d.w ≤ 8192; rw [bitsAt_eq]; omega
  · show bitsAt c.n 0 + 3 < 4096; rw [bitsAt_eq]; omega
  · intro w hw
    rw [combW_eq] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have hl : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP], i < 45 := by
      decide
    exact Or.inr (sl_below_bits c (hl i hi) 0 0)

theorem combWk (hc : CfgOk c) (d : CombData) :
    WkOk (c.combCfg d).M size (c.combCfg d).wk (· ∈ combSlots (c.combCfg d).toComb) where
  le := wk_le c hc.n10 rfl
  mo := sl_below_wk c (i := MP) (by decide)
  tmp := sl_below_wk c (i := TMP) (by decide)
  sl := by
    rw [combSlots_eq]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have : ∀ i ∈ [AP, EM, ZERO, RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ], i < 45 := by decide
    exact sl_below_wk c (this i hi)

theorem tcombLay {d : CombData} (hc : CfgOk c) (hd : CombOk c d) : TCombLay (c.combCfg d) size := by
  have hn := hc.n0
  have h7 := hc.n10
  have hz := zw_le hd
  have hbits : (c.combCfg d).bits = bitsAt c.n 0 := rfl
  have hk : (c.combCfg d).kbytes = 64 * c.n := rfl
  have hl : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP], i < 45 := by decide
  refine ⟨combLay hc hd, combWk hc d, ?_, (by change 64 ≤ 8192; decide),
    ?_, ?_, ?_, hd.w, hd.cover.1, ?_, ?_, ?_, ?_, ⟨hn, hd.n⟩, ?_, ?_⟩
  · change bitsAt c.n 0 + 64 * c.n + 4 * (c.combCfg d).zw ≤ c.wk
    rw [bitsAt_eq, wk_eq]; omega
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact .inl (by change 64 ≤ c.sl MP; rw [sl_eq]; omega)
    · exact .inl (by change 64 ≤ c.sl TMP; rw [sl_eq]; omega)
    · rw [combSlots_eq] at hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact .inl (by change 64 ≤ c.sl i; rw [sl_eq]; omega)
  · change 64 ≤ c.wk; rw [wk_eq]; omega
  · exact .inl (by change 64 ≤ bitsAt c.n 0; rw [bitsAt_eq]; omega)
  · rw [hbits, hk, bitsAt_eq]; change _ ≤ 8192; omega
  · rw [hbits, hk, bitsAt_eq]; omega
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
    rw [Nat.mul_succ]; omega
  · show 16 * c.n * 2 ^ (d.w - 1) < 2 ^ 31
    have : 2 ^ (d.w - 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by have := hd.w; omega)
    have : 16 * c.n * 2 ^ (d.w - 1) ≤ 16 * 6 * 2 ^ 7 := Nat.mul_le_mul (by have := hd.n; omega) this
    omega

theorem mont_lt (hc : CfgOk c) (x : Nat) : c.mont x < c.C.p :=
  Nat.mod_lt _ (by have := hc.p_ge; omega)

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


end VG.Proof.Ecdsa.X86
