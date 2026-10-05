import VerifiedGarbage.Proof.Weierstrass.AArch64.InvBatch
import VerifiedGarbage.Proof.Weierstrass.AArch64.Pow
import VerifiedGarbage.Proof.Weierstrass.InvToM

/-!
# Inversion by divsteps on AArch64: the whole inversion

`InvCfg.inv P` leaves `[acc]` reading (in Montgomery form) as `[base]^(m - 2)`
for a prime `m` (`invPow_ok`, as `chainPow_ok` for a chain of `m - 2`), given
the arithmetic of the last step (`InvToM`, whose proof needs Mathlib's
algebra, from the curve's variant): the
start holds `(d, f, g, a, b) = (1, m, x, 0, 1)` (`init_ok`), each of the `B`
batches takes it to the next `Divstep.invRun` (`batch_ok`), and the end
multiplies `a` by `C` or `m - C` by the sign of `f = ±1` (`finish_ok`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- The registers the inversion writes, within a power's. -/
theorem invClob_sub {n : Nat} (h4 : 4 ≤ n) (h7 : n < 10) :
    ∀ r ∈ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x16, .x17, .x19],
      r ∈ powClob n := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  all_goals decide

/-- `[dst] = [src]` (`n` words) with a zero word on top. -/
theorem copyTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (h12 : s.gpr .x12 = 0)
    {dst src n : Nat} (hs8 : src % 8 = 0) (hd8 : dst % 8 = 0) (hsrc : src + 8 * n ≤ size)
    (hdst : dst + 8 * (n + 1) ≤ size) (hsep : dst + 8 * (n + 1) ≤ src ∨ src + 8 * n ≤ dst) :
    WP isa (.block (copyW dst src n ++ [st .x12 (dst + 8 * n)])) s fun t =>
      wordsVal t.mem base dst (n + 1) = wordsVal s.mem base src n ∧ KeepRegs [.x2] s t ∧
      Outside base dst (8 * (n + 1)) s.mem t.mem := by
  have hn := hs.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (copyW_ok hs hs8 hd8 n (by omega) (by omega) (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  refine WP.mono (st_ok (hs.of_keepRegs k₁ (by decide)) (d := dst + 8 * n) (by omega) (by omega) .x12)
    fun t et => ?_
  have mt : t.mem = s₁.mem.writeW (off base (dst + 8 * n)) (s₁.gpr .x12) := by rw [et]
  have Ot := writeW_outside s₁.mem base (d := dst + 8 * n) (s₁.gpr .x12) (by omega)
  refine ⟨?_, k₁.trans (KeepRegs.of_st et), fun x hx => by rw [mt, Ot x (by omega), O₁ x (by omega)]⟩
  rw [wordsVal_succ_top, mt, Ot.wordsVal (by omega) (by omega), word_writeW_self, e₁, k₁.gpr _ (by decide), h12]
  rfl

/-- `[a] = 0`, `[b] = 1` (`n ≥ 1` words each, `b` after `a`). -/
theorem zeroOne_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (h12 : s.gpr .x12 = 0)
    (h11 : s.gpr .x11 = 1) {a b n : Nat} (hn1 : 1 ≤ n) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hab : a + 8 * n ≤ b)
    (hb : b + 8 * n ≤ size) :
    WP isa (.block (zerosW a n ++ zerosW b n ++ [st .x11 b])) s fun t =>
      wordsVal t.mem base a n = 0 ∧ wordsVal t.mem base b n = 1 ∧ KeepRegs [] s t ∧
      Outside base a (b + 8 * n - a) s.mem t.mem := by
  have hn := hs.nowrap
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zerosW_ok hs h12 ha8 n (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.mono (zerosW_ok hs₁ (by rw [k₁.gpr _ (by decide), h12]) hb8 n hb) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  refine WP.mono (st_ok (hs₁.of_keepRegs k₂ (by decide)) (d := b) (by omega) hb8 .x11) fun t et => ?_
  have mt : t.mem = s₂.mem.writeW (off base b) (s₂.gpr .x11) := by rw [et]
  have Ot := writeW_outside s₂.mem base (d := b) (s₂.gpr .x11) (by omega)
  refine ⟨?_, ?_, (k₁.trans k₂).trans (KeepRegs.of_st et), fun x hx => by
    rw [mt, Ot x (by omega), O₂ x (by omega), O₁ x (by omega)]⟩
  · rw [mt, Ot.wordsVal (by omega) (by omega), O₂.wordsVal (by omega) (by omega), e₁]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have e₂' := e₂
    rw [wordsVal] at e₂'
    have h0 : wordsVal s₂.mem base (b + 8) k = 0 := by
      rcases Nat.eq_zero_or_pos (wordsVal s₂.mem base (b + 8) k) with h | h
      · exact h
      · have := Nat.mul_le_mul_left (2 ^ 64) h; omega
    rw [wordsVal, mt, word_writeW_self, Ot.wordsVal (by omega) (by omega), h0, k₂.gpr _ (by decide),
      k₁.gpr _ (by decide), h11]
    rfl

/-- The start: `x11 = 1`, `x12 = 0`, `d = 1`, the counter, and `(f, g, a, b) = (m, x, 0, 1)`. -/
theorem init_ok {P : InvCfg} {base : Addr} {size m : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkA P.M size m s.mem base) (hB : P.B < 2 ^ 16) :
    WP isa (.block P.init) s fun t =>
      IInv P base ⟨1, m, wordsVal s.mem base P.base P.M.n, 0, 1⟩ t ∧ t.gpr .x19 = BitVec.ofNat 64 P.B ∧
      KeepRegs [.x1, .x2, .x11, .x12, .x19] s t ∧ Unch base (batchW P) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; have htbl8 := hL.tbl8; have hbase := hL.base; have hb8 := hL.base8
  have hbt := hL.base_tbl; have hmt := hL.mo_tbl; have hmo := hM.mo; have hmo8 := hL.mo8
  simp only [InvCfg.init, List.append_assoc]
  rw [show ([.movz .x .x11 1 0, .movz .x .x12 0 0, .movz .x .x1 1 0, .movz .x .x19 (BitVec.ofNat 16 P.B) 0] :
      List Instr) ++ _ = [.movz .x .x11 1 0] ++ ([.movz .x .x12 0 0] ++ ([.movz .x .x1 1 0] ++
      ([.movz .x .x19 (BitVec.ofNat 16 P.B) 0] ++ _))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (movzI_ok s .x11 1) fun s₁ ⟨c₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movzI_ok s₁ .x12 0) fun s₂ ⟨c₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movzI_ok s₂ .x1 1) fun s₃ ⟨c₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setCounter_ok s₃ hB) fun s₄ ⟨c₄, k₄⟩ => ?_
  have hs₄ : Scr s₄ base size :=
    (((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)).of_keeps k₃ (by decide)).of_keeps k₄ (by decide)
  have m₄ : s₄.mem = s.mem := by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem]
  have z₄ : s₄.gpr .x12 = 0 := by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), c₂]; rfl
  have o₄ : s₄.gpr .x11 = 1 := by
    rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), c₁]; rfl
  have K₄ : KeepRegs [.x1, .x2, .x11, .x12, .x19] s s₄ :=
    (((((Keeps.regs k₁).mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
      ((Keeps.regs k₃).mono (by decide))).trans ((Keeps.regs k₄).mono (by decide)))
  -- `f = m`, `g = x`.
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (copyTop_ok hs₄ z₄ (dst := P.sF) (src := P.M.mo) (n := P.M.n) hmo8
    (by omega_using [eF, htbl8]) hmo (by omega_using [eF, htbl, n4]) (by omega_using [eF, hmt, n4]))
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (copyTop_ok hs₅ (by rw [k₅.gpr _ (by decide), z₄]) (dst := P.sG) (src := P.base) (n := P.M.n) hb8
    (by omega_using [eG, htbl8]) hbase (by omega_using [eG, htbl, n4]) (by omega_using [eG, hbt, n4]))
    fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  -- `a = 0`, `b = 1`.
  rw [← List.append_assoc]
  refine WP.mono (zeroOne_ok hs₆ (by rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), z₄])
    (by rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), o₄]) (a := P.sA) (b := P.sB) (n := P.M.n)
    (by omega_using [n4]) (by omega_using [eA, htbl8]) (by omega_using [eB, htbl8]) (by omega_using [eA, eB])
    (by omega_using [eB, htbl, n4])) fun t ⟨eA₇, eB₇, k₇, O₇⟩ => ?_
  have g₇ : ∀ r, r ∉ [Reg.x2] → t.gpr r = s₄.gpr r := fun r hr => by
    rw [k₇.gpr _ (by simp), k₆.gpr _ hr, k₅.gpr _ hr]
  have rF : wordsVal t.mem base P.sF (P.M.n + 1) = m := by
    rw [O₇.wordsVal (by omega_using [eF, eA]) (by omega_using [eF, htbl, n4, hn]),
      O₆.wordsVal (by omega_using [eF, eG, eL]) (by omega_using [eF, htbl, n4, hn]), e₅,
      m₄, hM.val]
  have rG : wordsVal t.mem base P.sG (P.M.n + 1) = wordsVal s.mem base P.base P.M.n := by
    rw [O₇.wordsVal (by omega_using [eG, eA]) (by omega_using [eG, htbl, n4, hn]), e₆,
      O₅.wordsVal (by omega_using [hbt, eF, n4]) (by omega_using [hbase, hn]), m₄]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [g₇ _ (by decide), k₄.gpr _ (by decide), c₃]
    show (1 : BitVec 16).setWidth 64 = BitVec.ofInt 64 1
    decide
  · rw [eL, rF]
  · rw [eL, rG]
  · rw [eA₇]; rfl
  · rw [eB₇]; rfl
  · rw [g₇ _ (by decide), c₄]
  · exact K₄.trans ((k₅.trans (k₆.trans (k₇.mono (by decide)))).mono (by decide))
  · rw [← m₄]
    refine (((O₅.unch.trans O₆.unch).trans O₇.unch).outside fun w hw => ?_).unch
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> dsimp only <;> omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4]

/-- The batches, counted down in `x19`, from `invRun 0` to `invRun B`. -/
theorem loop_ok {P : InvCfg} {base : Addr} {size m : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkA P.M size m s.mem base) {X : Nat} (hX : X < m) (hm2 : m % 2 = 1) (hm1 : 1 < m)
    (hB1 : 1 ≤ P.B) (hB : P.B < 2 ^ 16)
    (hI : IInv P base (Divstep.invRun 59 m P.M.minv.toNat X 0) s) (h19 : s.gpr .x19 = BitVec.ofNat 64 P.B) :
    WP isa (.loop P.batch (.nonzero .x .x19)) s fun t =>
      IInv P base (Divstep.invRun 59 m P.M.minv.toNat X P.B) t ∧
      KeepRegs [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x16, .x17, .x19] s t ∧
      Unch base (batchW P) s.mem t.mem := by
  have hn := hs.nowrap
  have hmt := hL.mo_tbl; have hmo := hM.mo; have n4 := hL.n4
  have hmi : ((m : Int) * (P.M.minv.toNat : Int) + 1) % 2 ^ 64 = 0 := by exact_mod_cast hM.inv
  refine countLoop_ok (n := P.B) (by omega)
    (Inv := fun j t => IInv P base (Divstep.invRun 59 m P.M.minv.toNat X (P.B - j)) t ∧
      t.gpr .x19 = BitVec.ofNat 64 j ∧ Scr t base size ∧ ModOkA P.M size m t.mem base ∧
      KeepRegs [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x16, .x17, .x19] s t ∧
      Unch base (batchW P) s.mem t.mem)
    (fun j t hj1 hjB ⟨It, xt, St, Mt, Kt, Ut⟩ => ?_) (fun t ⟨It, _, _, _, Kt, Ut⟩ => ⟨by simpa using It, Kt, Ut⟩)
    hB1 ⟨by rw [Nat.sub_self]; exact hI, h19, hs, hM, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _⟩
  obtain ⟨bd, bf1, bf, bg, ba0, ba1, bb0, bb1⟩ := Divstep.invRun_bounds (N := 59) (by decide) (p := m)
    (m := P.M.minv.toNat) (x := X) (by exact_mod_cast hm2) (by exact_mod_cast hm1) hmi (by omega)
    (by exact_mod_cast hX) (P.B - j)
  refine WP.mono (batch_ok hL St Mt It (by
      have : (59 * (P.B - j) : Nat) ≤ 59 * 2 ^ 16 := Nat.mul_le_mul_left _ (by omega)
      have h2 : ((59 * (P.B - j) : Nat) : Int) ≤ 59 * 2 ^ 16 := by exact_mod_cast this
      omega) bf1 bf bg (by rw [abs_of_nonneg ba0]; exact ba1.le) (by rw [abs_of_nonneg bb0]; exact bb1.le)
    hj1 (by omega) xt) fun u ⟨Iu, xu, Ku, Uu⟩ => ⟨⟨?_, xu, ?_, ?_, Kt.trans Ku, (Ut.trans Uu).mono ?_⟩, xu⟩
  · rw [show P.B - (j - 1) = P.B - j + 1 by omega]; exact Iu
  · exact St.of_keepRegs Ku (by decide)
  · refine ⟨Mt.n0, Mt.n10, Mt.mo, Mt.tmp, Mt.sep, ?_, Mt.inv, Mt.red⟩
    rw [Uu.wordsVal (fun w hw => by
      simp only [batchW, List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw; dsimp only; omega_using [hmt, n4]) (by omega_using [hmo, hn])]
    exact Mt.val
  · intro w hw; simp only [batchW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at hw ⊢
    exact hw

/-- `c ^ ((c' ^ c) & m)` selects `c'` under a mask. -/
theorem sel_eq {c c' m : BitVec 64} (hm : IsMask m) :
    c ^^^ ((c' ^^^ c) &&& m) = if m = BitVec.allOnes 64 then c' else c := by
  rcases hm with rfl | rfl
  · simp only [show (0 : BitVec 64) ≠ BitVec.allOnes 64 by decide, ↓reduceIte]; simp
  · simp only [BitVec.and_allOnes, ↓reduceIte]
    rw [← BitVec.xor_assoc, BitVec.xor_comm c c', BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The selection's three instructions: `x2 = x9 ? x3 : x2`. -/
theorem selIns_ok (s : State) (hm : IsMask (s.gpr .x9)) :
    WP isa (.block [.logic .eor .x .x3 .x3 .x2, .logic .and .x .x3 .x3 .x9, .logic .eor .x .x2 .x2 .x3]) s fun t =>
      t.gpr .x2 = (if s.gpr .x9 = BitVec.allOnes 64 then s.gpr .x3 else s.gpr .x2) ∧ Keeps [.x2, .x3] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write, BitVec.setWidth_eq,
    reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
  refine ⟨sel_eq hm, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ↓reduceIte]

/-- Word `i` of a constant: bits `64 i …`. -/
theorem const_word (V i : Nat) : (BitVec.ofNat 64 (V >>> (64 * i))).toNat = V / 2 ^ (64 * i) % 2 ^ 64 := by
  rw [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]

/-- Words `0 … j - 1` of the constant `C` or `Cn`, by the mask in `x9`. -/
theorem selRows_ok {P : InvCfg} {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hm : IsMask (s.gpr .x9)) (hC8 : P.sC % 8 = 0) :
    ∀ j, P.sC + 8 * j ≤ size → WP isa (.block ((List.range j).flatMap fun i =>
      const64 .x2 (BitVec.ofNat 64 (P.C >>> (64 * i))) ++ const64 .x3 (BitVec.ofNat 64 (P.Cn >>> (64 * i))) ++
      ([.logic .eor .x .x3 .x3 .x2, .logic .and .x .x3 .x3 .x9, .logic .eor .x .x2 .x2 .x3, st .x2 (P.sC + 8 * i)] :
        List Instr)))
      s fun t =>
        wordsVal t.mem base P.sC j = (if s.gpr .x9 = BitVec.allOnes 64 then P.Cn else P.C) % 2 ^ (64 * j) ∧
        KeepRegs [.x2, .x3] s t ∧ Outside base P.sC (8 * j) s.mem t.mem
  | 0, _ => WP.block_nil ⟨by simp only [wordsVal, Nat.mul_zero, Nat.pow_zero, Nat.mod_one],
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | j + 1, hj => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (selRows_ok hs hm hC8 j (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have x9₁ : s₁.gpr .x9 = s.gpr .x9 := k₁.gpr _ (by decide)
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (const64_ok s₁ .x2 _) fun s₂ ⟨c₂, k₂⟩ => ?_
    refine WP.mono (const64_ok s₂ .x3 _) fun s₃ ⟨c₃, k₃⟩ => ?_
    rw [show ([.logic .eor .x .x3 .x3 .x2, .logic .and .x .x3 .x3 .x9, .logic .eor .x .x2 .x2 .x3,
        st .x2 (P.sC + 8 * j)] : List Instr) = [.logic .eor .x .x3 .x3 .x2, .logic .and .x .x3 .x3 .x9,
        .logic .eor .x .x2 .x2 .x3] ++ [st .x2 (P.sC + 8 * j)] from rfl, WP.block_append_iff]
    have x9₃ : s₃.gpr .x9 = s.gpr .x9 := by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), x9₁]
    refine WP.mono (selIns_ok s₃ (by rw [x9₃]; exact hm)) fun s₄ ⟨c₄, k₄⟩ => ?_
    have hs₄ : Scr s₄ base size := ((hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)).of_keeps k₄ (by decide)
    refine WP.mono (st_ok hs₄ (d := P.sC + 8 * j) (by omega) (by omega) .x2) fun t et => ?_
    have mt : t.mem = s₄.mem.writeW (off base (P.sC + 8 * j)) (s₄.gpr .x2) := by rw [et]
    have Ot := writeW_outside s₄.mem base (d := P.sC + 8 * j) (s₄.gpr .x2) (by omega)
    have m₄ : s₄.mem = s₁.mem := by rw [k₄.mem, k₃.mem, k₂.mem]
    refine ⟨?_, k₁.trans (((((Keeps.regs k₂).mono (by decide)).trans ((Keeps.regs k₃).mono (by decide))).trans
      ((Keeps.regs k₄).mono (by decide))).trans (KeepRegs.of_st et)), fun x hx => by
        rw [mt, Ot x (by omega), m₄, O₁ x (by omega)]⟩
    rw [wordsVal_succ_top, mt, word_writeW_self, Ot.wordsVal (by omega) (by omega), m₄, e₁, c₄, x9₃,
      k₃.gpr .x2 (by decide), c₂, c₃, pow64_succ, Nat.mul_comm (2 ^ 64), Nat.mod_mul]
    split <;> rw [const_word]

/-- A number's low word, modulo `2^64`. -/
theorem low_word (m : Mem) (base : Addr) (d L : Nat) (hL : 1 ≤ L) :
    ((word m base d).toNat : Int) % 2 ^ 64 = (wordsVal m base d L : Int) % 2 ^ 64 := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  rw [wordsVal]; push_cast; rw [Int.add_mul_emod_self_left]

/-- The end: `[C] = C` or `Cn` by the sign of `f` (`±1`), and `acc = a [C] / R`. -/
theorem finish_ok {P : InvCfg} {base : Addr} {size m : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkA P.M size m s.mem base) {I : Divstep.IState} (hI : IInv P base I s) (hC : P.C < m)
    (hCn : P.Cn < m) :
    WP isa (.block P.finish) s fun t =>
      ∃ Cs, (I.f = 1 → Cs = P.C) ∧ (I.f = -1 → Cs = P.Cn) ∧
        wordsVal t.mem base P.acc P.M.n < m ∧
        wordsVal t.mem base P.acc P.M.n * 2 ^ (64 * P.M.n) % m = wordsVal s.mem base P.sA P.M.n * Cs % m ∧
        KeepRegs (powClob P.M.n) s t ∧ Unch base (invW P) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT⟩ := slots P
  have n4 := hL.n4; have n7 := hL.n10; have htbl := hL.tbl; have htbl8 := hL.tbl8; have hmt := hL.mo_tbl
  have hmo := hM.mo; have hacc := hL.acc; have hat := hL.acc_tbl; have htt := hL.tbl_tmp
  rw [InvCfg.finish, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, ← List.singleton_append,
    WP.block_append_iff]
  refine WP.mono (movzI_ok s .x12 0) fun s₁ ⟨c₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (ld_ok hs₁ (d := P.sF) (by omega_using [eF, htbl, n4]) (by omega_using [eF, htbl8]) .x3)
    fun s₂ ⟨c₂, k₂, _⟩ => ?_
  refine WP.mono (sgnMask_ok s₂ (by rw [k₂.gpr _ (by decide), c₁]; rfl)) fun s₃ ⟨g₃, mk₃, k₃, _⟩ => ?_
  have hs₃ := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  have hC8 : P.sC % 8 = 0 := by simp only [InvCfg.sC]; omega_using [eNF, htbl8]
  have hCl : P.sC + 8 * P.M.n ≤ P.tbl + 9 * (8 * P.M.n) := by simp only [InvCfg.sC]; omega_using [eNF, n4]
  refine WP.mono (selRows_ok hs₃ mk₃ hC8 P.M.n (by omega)) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have m₃ : s₃.mem = s.mem := by rw [k₃.mem, k₂.mem, k₁.mem]
  have hCt : P.tbl ≤ P.sC := by simp only [InvCfg.sC]; omega_using [eNF]
  have M₄ : ModOkA P.M size m s₄.mem base := ⟨hM.n0, hM.n10, hM.mo, hM.tmp, hM.sep,
    by rw [O₄.wordsVal (by omega) (by omega), m₃]; exact hM.val, hM.inv, hM.red⟩
  have hmP : m < 2 ^ (64 * P.M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  have hCs : (if s₃.gpr .x9 = BitVec.allOnes 64 then P.Cn else P.C) < m := by split; exacts [hCn, hC]
  have e₄' : wordsVal s₄.mem base P.sC P.M.n = if s₃.gpr .x9 = BitVec.allOnes 64 then P.Cn else P.C := by
    rw [e₄, Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (mul_ok hs₄ M₄ hL.mod (o := P.acc) (a := P.sA) (b := P.sC) hacc
    (by omega_using [eA, htbl, n4]) (by omega) hL.acc8 (by omega_using [eA, htbl8]) hC8 (by rw [e₄']; exact hCs))
    fun t ⟨Kt, lt, ev⟩ =>
      ⟨if s₃.gpr .x9 = BitVec.allOnes 64 then P.Cn else P.C, ?_, ?_, lt, ?_, ?_, ?_⟩
  -- The sign of `f`, from its low word.
  · intro hf
    have hw : ((s₂.gpr .x3).toNat : Int) % 2 ^ 64 = 1 := by
      have hdvd : ((2 : Int) ^ 64) ∣ ((2 ^ (64 * P.L) : Nat) : Int) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_dvd_pow 2 (by omega)
      rw [c₂, k₁.mem, low_word _ _ _ P.L (by omega), ← Int.emod_emod_of_dvd _ hdvd, hI.f,
        Int.emod_emod_of_dvd _ hdvd, hf]; rfl
    have h1 : (s₂.gpr .x3).toNat = 1 := by have := (s₂.gpr .x3).isLt; omega
    have h0 : s₃.gpr .x9 ≠ BitVec.allOnes 64 := fun h => by
      rw [h, BitVec.toNat_allOnes, sgnW, h1] at g₃; simp at g₃
    simp only [h0, ↓reduceIte]
  · intro hf
    have hw : ((s₂.gpr .x3).toNat : Int) % 2 ^ 64 = 2 ^ 64 - 1 := by
      have hdvd : ((2 : Int) ^ 64) ∣ ((2 ^ (64 * P.L) : Nat) : Int) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_dvd_pow 2 (by omega)
      rw [c₂, k₁.mem, low_word _ _ _ P.L (by omega), ← Int.emod_emod_of_dvd _ hdvd, hI.f,
        Int.emod_emod_of_dvd _ hdvd, hf]; rfl
    have h1 : (s₂.gpr .x3).toNat = 2 ^ 64 - 1 := by have := (s₂.gpr .x3).isLt; omega
    have h0 : s₃.gpr .x9 = BitVec.allOnes 64 := BitVec.eq_of_toNat_eq (by
      rw [g₃, sgnW, h1, BitVec.toNat_allOnes]; rfl)
    simp only [h0, ↓reduceIte]
  · rw [ev, e₄', O₄.wordsVal (by simp only [InvCfg.sC]; omega_using [eA, eNF, eB]) (by omega), m₃]
  · refine ⟨fun r hr => ?_, Kt.rd.trans (k₄.rd.trans (k₃.rd.trans (k₂.rd.trans k₁.rd))),
      Kt.wr.trans (k₄.wr.trans (k₃.wr.trans (k₂.wr.trans k₁.wr))),
      Kt.sp.trans (k₄.sp.trans (k₃.sp.trans (k₂.sp.trans k₁.sp)))⟩
    have h7 : r ∉ clob P.M.n := fun h => hr (List.mem_cons_of_mem _ h)
    have hsub : ∀ q, q ∈ [Reg.x2, .x3, .x9, .x12] → q ∈ powClob P.M.n := fun q h =>
      invClob_sub n4 n7 q (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl <;> decide)
    rw [Kt.gpr r h7,
      k₄.gpr r (fun h => hr (hsub r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide))),
      k₃.gpr r (fun h => hr (hsub r (by rw [List.mem_singleton] at h; subst h; decide))),
      k₂.gpr r (fun h => hr (hsub r (by rw [List.mem_singleton] at h; subst h; decide))),
      k₁.gpr r (fun h => hr (hsub r (by rw [List.mem_singleton] at h; subst h; decide)))]
  · intro x hx
    have h1 := hx _ (List.mem_cons_self ..)
    have h2 := hx (P.tbl, 9 * (8 * P.M.n)) (by simp [invW])
    have h3 := hx (P.M.tmp, 8 * P.M.n) (by simp [invW])
    dsimp only at h1 h2 h3
    rw [Kt.mem x h1 h3, O₄ x (by omega), m₃]

/-- `[acc] = [base]^(m - 2)` in Montgomery form, for a prime `m > 2`. -/
theorem invPow_ok (hI : InvToM) {P : InvCfg} {base : Addr} {size m : Nat} [NeZero m] (hpr : m.Prime)
    (hL : InvLay P size)
    (hm2 : 2 < m) (hR : UnitMod m (2 ^ (64 * P.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkA P.M size m s.mem base) (hX : wordsVal s.mem base P.base P.M.n < m) (hC : InvOk P m) :
    WP isa (InvCfg.inv P) s fun s' => KeepRegs (powClob P.M.n) s s' ∧ Unch base (invW P) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) =
        toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ (m - 2) := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT⟩ := slots P
  have n4 := hL.n4; have n7 := hL.n10; have htbl := hL.tbl; have hmt := hL.mo_tbl; have hmo := hM.mo
  have hbt := hL.base_tbl; have hbase := hL.base
  have hm2' : m % 2 = 1 := (hpr.eq_one_or_self_of_dvd 2 |>.mt (by omega) |> fun h => by
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact absurd (hpr.eq_one_or_self_of_dvd 2 ⟨k, by omega⟩) (by omega)
    · omega)
  have hCm : P.C < m := by rw [hC.C]; exact Nat.mod_lt _ (by omega)
  have hCnm : P.Cn < m := by rw [hC.Cn]; have := hC.Cpos; omega
  -- The mo slot and the input, through writes to the table.
  have modU : ∀ {mem' : Mem}, Unch base (batchW P) s.mem mem' → ModOkA P.M size m mem' base := fun U =>
    ⟨hM.n0, hM.n10, hM.mo, hM.tmp, hM.sep, by
      rw [U.wordsVal (fun w hw => by
        simp only [batchW, List.mem_cons, List.not_mem_nil, or_false] at hw
        subst hw; dsimp only; omega_using [hmt, n4]) (by omega_using [hmo, hn])]
      exact hM.val, hM.inv, hM.red⟩
  rw [InvCfg.inv]
  refine WP.seq (WP.mono (init_ok hL hs hM hC.B16) fun s₁ ⟨I₁, x₁, K₁, U₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs K₁ (by decide)
  refine WP.seq (WP.mono (loop_ok hL hs₁ (modU U₁) hX hm2' (by omega) hC.B1 hC.B16 I₁ x₁)
    fun s₂ ⟨I₂, K₂, U₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs K₂ (by decide)
  have U₁₂ : Unch base (batchW P) s.mem s₂.mem := (U₁.trans U₂).mono fun w hw => by
    simp only [batchW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at hw ⊢; exact hw
  refine WP.mono (finish_ok hL hs₂ (modU U₁₂) I₂ hCm hCnm) fun t ⟨Cs, hf1, hfm1, lt, ev, K₃, U₃⟩ =>
    ⟨?_, ?_, lt, ?_⟩
  · have hsub := invClob_sub n4 n7
    exact (((K₁.mono fun r h => hsub r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with h | h | h | h | h <;> simp [h])).trans (K₂.mono hsub)).trans K₃)
  · intro x hx
    rw [U₃ x hx, U₁₂ x fun w hw => by
      simp only [batchW, List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw
      have := hx (P.tbl, 9 * (8 * P.M.n)) (by simp [invW])
      dsimp only at this ⊢; omega_using [this, n4]]
  -- The arithmetic.
  set X := wordsVal s.mem base P.base P.M.n with hXd
  set I := Divstep.invRun 59 m P.M.minv.toNat X P.B with hId
  have hmi : ((m : Int) * (P.M.minv.toNat : Int) + 1) % 2 ^ 64 = 0 := by exact_mod_cast hM.inv
  have ha : (wordsVal s₂.mem base P.sA P.M.n : Int) = I.a := I₂.a
  -- The divsteps end.
  have done : ∀ x : Int, 0 ≤ x → x < m → (Divstep.divsteps (59 * P.B) (1, m, x)).2.2 = 0 ∧
      (Divstep.divsteps (59 * P.B) (1, m, x)).2.1.natAbs = Int.gcd m x := fun x h0 h1 => by
    have hodd : (m : Int) % 2 = 1 := by exact_mod_cast hm2'
    have hmP := hM.val ▸ wordsVal_lt s.mem base P.M.mo P.M.n
    have hfn : (m : Int) < 2 ^ (64 * P.M.n) := by exact_mod_cast hmP
    exact Divstep.divsteps_words hodd h0 h1.le hfn hC.bound
  -- `x ≠ 0`: `f = ±1` and `x f a 2^(5 B) ≡ 1`.
  have spec : X ≠ 0 → (I.f = 1 ∨ I.f = -1) ∧ (X : Int) * (I.f * I.a) * 2 ^ ((64 - 59) * P.B) ≡ 1 [ZMOD m] :=
    fun hX0 => Divstep.invRun_spec (N := 59) (B := P.B) (by decide) (by exact_mod_cast hm2') (by exact_mod_cast hpr.one_lt) hmi
      (done X (by omega) (by exact_mod_cast hX)) (by
        rw [Int.gcd_natCast_natCast]
        rcases hpr.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_left m X) with h | h
        · exact h
        · have hd := Nat.gcd_dvd_right m X
          rw [h] at hd
          have := Nat.le_of_dvd (by omega) hd
          omega)
  refine hI (K := 2 ^ (5 * P.B)) (f := I.f) (a := wordsVal s₂.mem base P.sA P.M.n) (Cs := Cs) hpr hm2 hR hX
    ?_ ?_ ?_ ev
  · intro hX0
    have h := (Divstep.invRun_zero (N := 59) (p := m) (m := P.M.minv.toNat) (by omega) P.B).2
    have hIa : I.a = 0 := by rw [hId, hX0, Nat.cast_zero]; exact h
    have : (wordsVal s₂.mem base P.sA P.M.n : Int) = 0 := by rw [ha, hIa]
    exact_mod_cast this
  · intro hX0
    have h := (spec hX0).2
    rw [ha, show (64 - 59) * P.B = 5 * P.B by omega] at *
    push_cast
    exact h
  · intro hX0
    rcases (spec hX0).1 with h | h
    · rw [hf1 h, hC.C, h]; push_cast; rw [Int.emod_emod_of_dvd _ (dvd_refl _)]; ring_nf
    · rw [hfm1 h, hC.Cn, h, Nat.cast_sub hCm.le]
      have hc : (P.C : Int) ≡ ((2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3 : Nat) : Int) [ZMOD m] := by
        rw [hC.C]; push_cast; exact Int.emod_emod_of_dvd _ (dvd_refl _)
      have hm0 : (m : Int) ≡ 0 [ZMOD m] := Int.emod_self.trans (Int.zero_emod _).symm
      have := hm0.sub hc
      push_cast at this ⊢
      rw [show (-1 : Int) * (2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3) =
        0 - 2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3 by ring]
      exact this

/-- A prime modulus's inversion is sound. -/
theorem invSound_of_prime (hI : InvToM) {m : Nat} [NeZero m] (hp : m.Prime) : InvSound m :=
  fun hL hm2 hR _ hs hM hX hC => invPow_ok hI hp hL hm2 hR hs hM hX hC

end VG.Proof.Weierstrass.AArch64
