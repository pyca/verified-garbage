import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

/-!
# ECDSA on AArch64: the fixed-base comb's slots and constants

The comb's slots are numbered slots, apart as `tcomb_ok` needs (`tcombLay`),
its table of bits is the first table (`bitsAt c.n 0`, and one word of the
next), and its constants, the curve's tables, are what `tcomb_ok` needs
(`tcombVals`) if the tables are right (`CombOkW`, which a curve's own facts
prove).
-/

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

theorem combJ_eq (c : Cfg) : c.combCfg.J = Cfg.combJ c.n := rfl

theorem combW_eq (c : Cfg) : combW c.combCfg.toComb = slW c [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3,
    T4, T5, DX, DY, DZ, TMP] := rfl

theorem combSlots_eq (c : Cfg) : combSlots c.combCfg.toComb = [AP, BM, ZERO, RX, RY, RZ, TX, TY, TZ, PT,
    T0, T1, T2, T3, T4, T5, DX, DY, DZ].map c.sl := rfl

theorem tcombW_eq (c : Cfg) : tcombW c.combCfg = slW c [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3,
    T4, T5, DX, DY, DZ, TMP] ++ [(bitsAt c.n 0 + 64 * c.n, 8 * c.combCfg.zw)] := rfl

theorem zw_le {c : Cfg} (hn : 0 < c.n) : 8 * c.combCfg.zw ≤ 64 * c.n := by
  show 8 * ((7 * ((64 * c.n + 6) / 7) - 64 * c.n + 7) / 8) ≤ 64 * c.n
  omega_arith

theorem combLay (hc : BaseCfgOk c) : CombLay c.combCfg.toComb size := by
  have hn := hc.n0
  have h7 := hc.n10
  have hJ : c.combCfg.toComb.J = Cfg.combJ c.n := by rw [TCombCfg.toComb_J]; rfl
  have hb := bitsAt0_le c h7
  refine ⟨?_, rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (lr := [AP, BM, RX, RY, RZ, TX, TY, TZ]) rfl rfl (by decide) (by decide), ?_,
    map_sl_nodup hn (l := [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (by decide), ⟨by rw [hJ]; unfold Cfg.combJ; omega_arith, by rw [hJ]; unfold Cfg.combJ; omega_arith⟩, ?_, ?_, ?_⟩
  · exact lay_map hc rfl rfl rfl (l := [AP, BM, ZERO, RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3,
      T4, T5, DX, DY, DZ]) (by decide)
  · exact map_sl_disj hn (l₁ := [AP, BM, ZERO])
      (l₂ := [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ]) (by decide)
  · rw [hJ]; show bitsAt c.n 0 + 4 * ((64 * c.n + 6) / 7) ≤ 8192; omega_arith
  · show bitsAt c.n 0 + 3 < 4096; omega_arith
  · intro w hw
    rw [combW_eq] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have hl : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP], i < 45 := by
      decide
    exact sl_bits0 c (hl i hi) (by rw [hJ]; unfold Cfg.combJ; omega_arith)

theorem tcombLay (hc : BaseCfgOk c) : TCombLay c.combCfg size := by
  have hn := hc.n0
  have h7 := hc.n10
  have hb := bitsAt_le c h7 (j := 1) (by decide)
  have hb4 := bitsAt0_le c h7
  have hb0 : bitsAt c.n 1 = bitsAt c.n 0 + 64 * c.n := by rw [bitsAt_eq, bitsAt_eq]; omega_arith
  have hz := zw_le hn
  have hl : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP], i < 45 := by
    decide
  have hk : c.combCfg.kbytes = 64 * c.n := rfl
  have hbits : c.combCfg.bits = bitsAt c.n 0 := rfl
  have hw : c.combCfg.w = 7 := rfl
  have hJ : c.combCfg.J = (64 * c.n + 6) / 7 := rfl
  have h2 := hc.n2
  refine ⟨combLay hc, ⟨by rw [hw]; decide, by rw [hw]; decide⟩, ?_, ?_, ?_, ?_, ?_, ?_, by show c.n ≤ 9; omega_arith,
    fun h => ⟨by rcases h2 with h2 | h2 <;> [exact absurd (show c.n % 2 = 1 from h) (by omega_arith); exact h2],
      by show 64 + 8 * c.n * 21 = 64 + 8 * c.n * 20 + 8 * c.n; rw [Nat.mul_succ]; omega_arith⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [hk, hw, hJ]; omega_arith
  · rw [hbits, hk]; show _ ≤ 8192; omega_arith
  · rw [hbits, hk, ← hb0]; exact bitsAt_mod8 c 1
  · rw [hbits, hw, hJ]; omega_arith
  · intro w hw
    rw [combW_eq] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    rw [hbits, hk]
    have : 8 * c.combCfg.zw ≤ 8 := by
      show 8 * ((7 * ((64 * c.n + 6) / 7) - 64 * c.n + 7) / 8) ≤ 8; omega_arith
    exact (sl_bits0 c (hl i hi) (L := 64 * c.n + 8 * c.combCfg.zw) (by omega_arith)).imp
      (fun h => by omega_arith) id
  · intro x hx
    rw [hbits, hk]
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inr (sl_below_bits c (i := MP) (by decide) 0 _)
    · rw [combSlots_eq] at hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have : ∀ i ∈ [AP, BM, ZERO, RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ],
        i < 45 ∧ i ≠ TMP := by decide
      exact Or.inr (sl_below_bits c (this i hi).1 0 _ (this i hi).2)
  · show (64 + 8 * c.n * 20) % 16 = 0; omega_arith
  · intro h; have : c.n % 2 = 0 := h; show (64 + 8 * c.n * 21) % 16 = 0; omega_arith
  · show 16 * c.n * 2 ^ (7 - 1) ≤ 32768; omega_arith
  · show 16 * c.n * 2 ^ (7 - 1) < 65536; omega_arith

theorem combA (hc : BaseCfgOk c) : CombA c.combCfg.toComb where
  sl := by
    rw [combSlots_eq]
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact sl_mod8 c i
  mod := MP'_A c
  call f m' h := by
    refine ⟨(hc.call_p f m' h).2, fun x hx => ?_⟩
    rw [combSlots_eq] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have : ∀ i ∈ [AP, BM, ZERO, RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ],
      i < 45 ∧ i ≠ TMP := by decide
    exact sl_own c hc.n10 (this i hi).1 (this i hi).2

theorem mont_zero (c : Cfg) : c.mont 0 = 0 := by simp [Cfg.mont]

theorem mont_lt (hc : BaseCfgOk c) (x : Nat) : c.mont x < c.C.p :=
  Nat.mod_lt _ (by have := hc.p_ge; omega_arith)

/-- The comb's constants, from its tables' facts. -/
theorem tcombVals (hc : BaseCfgOk c) (hC : Law c.C) (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start) :
    TCombVals c.combCfg c.C c.tbl where
  len := hT.len
  lenH := hT.lenH
  tbl_lt := hT.lt
  unit := unitMod_pow_two hc.p_odd _
  one_lt := mont_lt hc 1
  one := by
    show toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1
    rw [toM_cmont hc]; rfl
  entry j hj m hm := by
    rw [combPtW, show c.combCfg.w = Cfg.combW from rfl, hT.entry j hj m hm]
    exact rep_affine' hC _ _
  start_lt := ⟨mont_lt hc _, mont_lt hc _⟩
  start := by
    show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (c.mont c.start.1))
      (toM c.C.p (2 ^ (64 * c.n)) (c.mont c.start.2)) 1 _
    rw [toM_cmont hc, toM_cmont hc, show c.combCfg.H = 2 ^ (Cfg.combW - 1) from rfl,
      show c.combCfg.w = Cfg.combW from rfl, show c.combCfg.J = Cfg.combJ c.n from rfl, hT.start]
    exact rep_affine' hC _ _

/-- The tables, from the arguments' facts, at a state whose regions are the
arguments' and whose memory changed only in the working space. -/
theorem tbl_of {s₀ s : State} {T base : Addr} (hp : TblPre c s₀ T base) (hrd : s.rd = s₀.rd)
    (hu : Unch base [(0, size)] s₀.mem s.mem) :
    TblMem s T c.combWords ∧ ∀ i < c.combWords.length, ∀ b < 8,
      size ≤ ofs base (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) := by
  have hf := hp.fit
  have hout : ∀ i < c.combWords.length, ∀ b < 8,
      size ≤ ofs base (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) := fun i hi b hb => by
    have hc : (⟨T, 8 * c.combWords.length⟩ : Region).Contains
        (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) 1 := by
      rw [Offset.add_add]; exact Offset.contains_base T (by omega_arith) (by omega_arith)
    have := hp.sc _ hc
    simp only [Region.Contains] at this
    unfold ofs; omega_arith
  refine ⟨⟨⟨_, List.mem_append_left _ (hrd ▸ hp.rd), by simp [Region.Contains]⟩, fun i hi => ?_⟩, hout⟩
  rw [← hp.held i hi]
  refine Mem.readW_congr fun b hb => (hu _ fun w hw => ?_)
  rw [List.mem_singleton.mp hw]
  exact Or.inr (by have := hout i hi b (by omega_arith); dsimp only; omega_arith)

/-- The cleared word of the table of bits is apart from the slots. -/
theorem apart_zw {i : Nat} (hi : i < 45) :
    ∀ w ∈ [(bitsAt c.n 0 + 64 * c.n, 8 * c.combCfg.zw)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  have : 8 * c.combCfg.zw ≤ 8 := by
    show 8 * ((7 * ((64 * c.n + 6) / 7) - 64 * c.n + 7) / 8) ≤ 8; omega_arith
  rcases sl_bits0 c hi (L := 64 * c.n + 8 * c.combCfg.zw) (by omega_arith) with h | h
  · exact Or.inr (by dsimp only; omega_arith)
  · exact Or.inl (by dsimp only; omega_arith)

theorem fixedOk_tcombW : FixedOk c (tcombW c.combCfg) := by
  rw [tcombW_eq]
  refine FixedOk.append (fixedOk_slW (by decide)) fun w hw => ?_
  rw [List.mem_singleton.mp hw]
  exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_bits c (i := 12) (by decide) 0 _))

/-- The flag word apart from what the comb writes. -/
theorem flag_unch_tcomb {base : Addr} {m m' : Mem} (hu : Unch base (tcombW c.combCfg) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 64) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  rw [tcombW_eq] at hu
  refine hu.word (fun w hw => ?_) (by omega_arith)
  rcases apart_append (apart_slW (c := c) (i := FLAG) (by decide)) (apart_zw (c := c) (i := FLAG)
    (by decide)) w hw with h | h
  · exact Or.inl (by omega_arith)
  · exact Or.inr h

/-- A slot apart from what the comb writes. -/
theorem sv_unch_tcomb {base : Addr} {m m' : Mem} (hu : Unch base (tcombW c.combCfg) m m')
    (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 64) {i : Nat} (hi : i < 45)
    (hl : i ∉ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP]) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n := by
  rw [tcombW_eq] at hu
  exact sv_unch hu h7 hn hi (apart_append (apart_slW hl) (apart_zw hi))

theorem combClob_regs : ∀ n < 10, Reg.x0 ∉ combClob n ∧ Reg.x20 ∉ combClob n := by
  unfold combClob maskRegs clob acc; decide

theorem x0_not_combClob {n : Nat} (hn : n < 10) : Reg.x0 ∉ combClob n := (combClob_regs n hn).1

theorem x20_not_combClob {n : Nat} (hn : n < 10) : Reg.x20 ∉ combClob n := (combClob_regs n hn).2

theorem tcombClob_regs : ∀ n < 10, Reg.x0 ∉ tcombClob n ∧ Reg.x20 ∉ tcombClob n := by
  unfold tcombClob entryRegs selRegs combClob maskRegs clob acc; decide

theorem x0_not_tcombClob {n : Nat} (hn : n < 10) : Reg.x0 ∉ tcombClob n := (tcombClob_regs n hn).1

theorem x20_not_tcombClob {n : Nat} (hn : n < 10) : Reg.x20 ∉ tcombClob n := (tcombClob_regs n hn).2

end VG.Proof.Ecdsa.AArch64
