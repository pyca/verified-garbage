import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb

/-!
# ECDSA on x86-64: the fixed-base comb's slots and constants

For a curve with a comb (`Cfg.comb = some d`): the comb's slots are numbered
slots, apart as `tcomb_ok` needs (`tcombLay`), its table of bits is the
first table (`bitsAt c.n 0`, and the word past it), its constants, the
curve's tables, are what `tcomb_ok` needs (`tcombVals`) if the tables are
right (`CombOk`), and the tables the calling convention gives are where the
comb reads them (`tbl_of`).
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

theorem combW_eq (c : Cfg) (d : CombData) : combW (c.combCfg d).toComb = slW c [RX, RY, RZ, TX, TY, TZ, PT,
    T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP] := rfl

theorem combSlots_eq (c : Cfg) (d : CombData) : combSlots (c.combCfg d).toComb = [AP, B3P, ZERO, RX, RY,
    RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ].map c.sl := rfl

theorem tcombW_eq (c : Cfg) (d : CombData) : tcombW (c.combCfg d) = slW c [RX, RY, RZ, TX, TY, TZ, PT,
    T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP] ++ [(bitsAt c.n 0 + 64 * c.n, 8 * (c.combCfg d).zw)] := rfl

/-- The comb clears at most the word past the table of `k`'s bits. -/
theorem zw_le {d : CombData} (hd : CombOk c d) : 8 * (c.combCfg d).zw ≤ 8 := by
  have := hd.cover
  show 8 * ((d.w * c.combJ d.w - 64 * c.n + 7) / 8) ≤ 8
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
      (lr := [AP, B3P, RX, RY, RZ, TX, TY, TZ]) rfl rfl (by decide) (by decide), ?_,
    map_sl_nodup hn (l := [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (by decide), ⟨by rw [hJ]; omega, by rw [hJ]; omega⟩, ?_, ?_, ?_⟩
  · exact lay_map hc rfl rfl rfl (l := [AP, B3P, ZERO, RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3,
      T4, T5, DX, DY, DZ]) (by decide)
  · exact map_sl_disj hn (l₁ := [AP, B3P, ZERO])
      (l₂ := [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ]) (by decide)
  · rw [hJ]; show bitsAt c.n 0 + 4 * c.combJ d.w ≤ 8192; rw [bitsAt_eq]; omega
  · show bitsAt c.n 0 + 3 < 4096; rw [bitsAt_eq]; omega
  · intro w hw
    rw [combW_eq] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have hl : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP], i < 45 := by
      decide
    exact Or.inr (sl_below_bits c (hl i hi) 0 0)

theorem tcombLay {d : CombData} (hc : CfgOk c) (hd : CombOk c d) : TCombLay (c.combCfg d) size := by
  have hn := hc.n0
  have h7 := hc.n10
  have hb := bitsAt_le_pad c h7 (j := 0) (by decide)
  have hz := zw_le hd
  have hl : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP], i < 45 := by
    decide
  have hk : (c.combCfg d).kbytes = 64 * c.n := rfl
  have hbits : (c.combCfg d).bits = bitsAt c.n 0 := rfl
  have hw := hd.w
  have hcov := hd.cover
  refine ⟨combLay hc hd, hw, hcov.1, ?_, ?_, ?_, ?_, ⟨hn, by show c.n ≤ 14; omega⟩, ?_, ?_⟩
  · rw [hbits, hk]; omega
  · rw [hbits, hk, bitsAt_eq]; omega
  · intro w hw
    rw [combW_eq] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact Or.inr (by rw [hbits]; exact sl_below_bits c (hl i hi) 0 0)
  · intro x hx
    rw [hbits, hk]
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inr (sl_below_bits c (i := MP) (by decide) 0 _)
    · rw [combSlots_eq] at hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have : ∀ i ∈ [AP, B3P, ZERO, RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ],
        i < 45 := by decide
      exact Or.inr (sl_below_bits c (this i hi) 0 _)
  · show 64 + 8 * c.n * 21 = 64 + 8 * c.n * 20 + 8 * c.n; rw [Nat.mul_succ]; omega
  · show 16 * c.n * 2 ^ (d.w - 1) < 2 ^ 31
    have : 2 ^ (d.w - 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    have : 16 * c.n * 2 ^ (d.w - 1) ≤ 16 * 9 * 2 ^ 7 := Nat.mul_le_mul (by omega) this
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

/-- The tables, from the facts the calling convention gives at `s₀`
(`TblsHeld`), at a state that may read their region and whose memory changed
only in the working space at `base`, a writable region at `s₀`. -/
theorem tbl_of_held {d : CombData} (hcd : c.comb = some d) {s₀ s : State} {base : Addr}
    (ht : TblsHeld c s₀ s₀.wr) (hsc : (⟨base, size⟩ : Region) ∈ s₀.wr)
    (hrd : ∀ r ∈ Abi.constRegions (fun n => s₀.syms n) c.combConsts, r ∈ s.rd)
    (hu : Unch base [(0, size)] s₀.mem s.mem) :
    TblMem s (s₀.syms d.tsym) (c.combWords d) ∧ ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs base (s₀.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) := by
  have hcc : c.combConsts = [(d.tsym, c.combWords d)] := by simp [Cfg.combConsts, hcd]
  obtain ⟨held, fit⟩ := ht
  rw [hcc] at held fit hrd
  obtain ⟨hf, hdj⟩ := fit _ (List.mem_singleton_self _)
  have hsc' : Region.Disjoint ⟨s₀.syms d.tsym, 8 * (c.combWords d).length⟩ ⟨base, size⟩ := hdj _ hsc
  dsimp only at hf
  have hout : ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs base (s₀.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) :=
    fun i hi b hb => by
      have hc : (⟨s₀.syms d.tsym, 8 * (c.combWords d).length⟩ : Region).Contains
          (s₀.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) 1 := by
        rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
      have := hsc' _ hc
      simp only [Region.Contains] at this
      unfold ofs; omega
  refine ⟨⟨⟨⟨s₀.syms d.tsym, 8 * (c.combWords d).length⟩,
    List.mem_append_left _ (hrd _ (by simp [Abi.constRegions])),
    by simp [Region.Contains]⟩, fun i hi => ?_⟩, hout⟩
  rw [← held _ (List.mem_singleton_self _) i hi]
  refine Mem.readW_congr fun b hb => (hu _ fun w hw => ?_)
  rw [List.mem_singleton.mp hw]
  exact Or.inr (by have := hout i hi b (by omega); dsimp only; omega)

/-- The tables, from the arguments' facts, at a state whose regions are the
arguments' and whose memory changed only in the working space. -/
theorem tbl_of {d : CombData} (hcd : c.comb = some d) {s₀ s : State} (hp : Pre c s₀) (hrd : s.rd = s₀.rd)
    (hu : Unch (s₀.gpr .r8) [(0, size)] s₀.mem s.mem) :
    TblMem s (s₀.syms d.tsym) (c.combWords d) ∧ ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs (s₀.gpr .r8) (s₀.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) :=
  tbl_of_held hcd hp.tbls (by rw [hp.wr]; simp) (fun r hr => by rw [hrd, hp.rd]; simp [hr]) hu

/-- The cleared word of the table of bits is apart from the slots. -/
theorem apart_zw (d : CombData) {i : Nat} (hi : i < 45) :
    ∀ w ∈ [(bitsAt c.n 0 + 64 * c.n, 8 * (c.combCfg d).zw)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inl (sl_below_bits c hi 0 _)

theorem fixedOk_tcombW (d : CombData) : FixedOk c (tcombW (c.combCfg d)) := by
  rw [tcombW_eq]
  refine FixedOk.append (fixedOk_slW (by decide)) fun w hw => ?_
  rw [List.mem_singleton.mp hw]
  exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_bits c (by decide) 0 _))

/-- The tables of bits `1` and `2` are apart from the cleared word. -/
theorem tbl_apart_zw {d : CombData} (hd : CombOk c d) {j t : Nat} (hj : j = 1 ∨ j = 2) :
    ∀ w ∈ [(bitsAt c.n 0 + 64 * c.n, 8 * (c.combCfg d).zw)],
      bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  have := zw_le hd
  simp only [bitsAt_eq]
  rcases hj with rfl | rfl <;> exact Or.inr (by omega)

end VG.Proof.Ecdsa.X86_64
