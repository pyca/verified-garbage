import VerifiedGarbage.Impl.Weierstrass.X86_64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.Booth

/-!
# The comb with Booth's digits on x86-64: digits and masks

Booth's digit `j = rbx` from the table of bits: window `j` by Horner's rule
as before (`hornerBits_ok`), plus the bit below it (`c_j`) for `j ≥ 1`, and
the magnitude from the window's top bit (`bmagTail_ok`), together `bdigit_ok`;
the sign's mask (`bsignMask_ok`); the mask of a nonzero number (`nzMask_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

private theorem bmag_fact : ∀ w < 9, ∀ m < 2 ^ w + 1, ∀ s < 2,
    (BitVec.ofNat 64 m ^^^ ((0 : BitVec 64) - BitVec.ofNat 64 s)) - ((0 : BitVec 64) - BitVec.ofNat 64 s) +
      (((0 : BitVec 64) - BitVec.ofNat 64 s) &&& BitVec.ofNat 64 (2 ^ w)) =
    BitVec.ofNat 64 (if s = 1 then 2 ^ w - m else m) := by
  decide +kernel

/-- The magnitude from `m = W + c` in `rax` and the window's top bit `s` at
`rdi + rcx + bits + w - 1`: `s ? 2^w - m : m` into `rax` and `r8`, through `rdx`. -/
theorem bmagTail_ok (K : TCombCfg) {s : State} {base : Addr} {i m sb : Nat} (hw : K.w < 9)
    (hm2 : m < 2 ^ K.w + 1) (hs2 : sb < 2) (hb : s.gpr .rdi = base)
    (hc : s.gpr .rcx = BitVec.ofNat 64 i) (hx : s.gpr .rax = BitVec.ofNat 64 m)
    (hr : InRegions (s.rd ++ s.wr) (off base (K.bits + K.w - 1 + i)) 1)
    (hm : s.mem (off base (K.bits + K.w - 1 + i)) = BitVec.ofNat 8 sb) :
    WP isa (.block [.movzx8 .rdx (winByte (K.bits + K.w - 1)), .mov32 .r8 (.imm 0), .alu .sub .r8 (.reg .rdx),
    .alu .xor .rax (.reg .r8), .alu .sub .rax (.reg .r8),
    .alu .and .r8 (.imm (BitVec.ofNat 32 (2 ^ K.w))), .alu .add .rax (.reg .r8), .mov .r8 (.reg .rax)]) s
      fun t => t.gpr .rax = BitVec.ofNat 64 (if sb = 1 then 2 ^ K.w - m else m) ∧
        t.gpr .r8 = BitVec.ofNat 64 (if sb = 1 then 2 ^ K.w - m else m) ∧ Keeps [.rax, .rdx, .r8] s t := by
  have hea : s.ea (winByte (K.bits + K.w - 1)) = off base (K.bits + K.w - 1 + i) := ea_winByte hb hc _
  have hW : 2 ^ K.w < 2 ^ 31 := Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide)
    (show K.w ≤ 8 by omega)) (by decide)
  have e0 : (0 : BitVec 32).setWidth 64 = 0 := rfl
  have es : BitVec.setWidth 64 (BitVec.ofNat 8 sb) = BitVec.ofNat 64 sb := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : sb < 2 ^ 8), Nat.mod_eq_of_lt (by omega : sb < 2 ^ 64)]
  apply WP.of_runBlock
  set_option linter.unusedSimpArgs false in
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.load8, hea, hr,
    hm, ite_true, Option.map_some, Option.bind_some, State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left', hx, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, e0, es,
    imm32_sext hW]
  rw [bmag_fact K.w hw m hm2 sb hs2]
  refine ⟨rfl, rfl, fun r hr' => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr'.1, hr'.2.1, hr'.2.2, ite_false]

theorem bcar_testBit {w k j : Nat} (hj : 1 ≤ j) : bcar w k j = (k.testBit (w * j - 1)).toNat := by
  simp only [bcar, show j ≠ 0 by omega, ↓reduceIte, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ (w * j - 1)) with h | h <;> simp [h]

theorem bcar_succ_testBit {w : Nat} (hw : 1 ≤ w) (k j : Nat) :
    bcar w k (j + 1) = (k.testBit (w * j + (w - 1))).toNat := by
  rw [bcar_testBit (by omega), show w * (j + 1) - 1 = w * j + (w - 1) by rw [Nat.mul_succ]; omega]

theorem byte_testBit (b : Bool) : (if b then (1 : BitVec 8) else 0) = BitVec.ofNat 8 b.toNat := by
  cases b <;> rfl

/-- Booth's digit's magnitude into `rax` and `r8`, for `rbx = j`, from the
table of bits at `K.bits`: with `c` (the bit below the window) for `j ≥ 1`,
without for `j = 0`. -/
theorem bdigit_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {k j N : Nat} (hw1 : 1 ≤ K.w) (hw : K.w < 9) (hj : K.w * j + K.w ≤ N) (hN : K.bits + N ≤ size)
    (hb1 : 1 ≤ K.bits) (hx : s.gpr .rbx = BitVec.ofNat 64 j)
    (hbits : ∀ t < N, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0) {c : Bool}
    (hc : (c = true ∧ 1 ≤ j) ∨ (c = false ∧ j = 0)) :
    WP isa (.block (K.bdigit c)) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (bmag K.w k j) ∧ t.gpr .r8 = BitVec.ofNat 64 (bmag K.w k j) ∧
        Keeps [.rax, .rcx, .rdx, .r8] s t := by
  have hn := hs.nowrap
  have hj32 : j < 2 ^ 64 := by
    have : j ≤ K.w * j := Nat.le_mul_of_pos_left _ (by omega)
    omega
  rw [TCombCfg.bdigit, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (winIndex_ok s (by omega) hj32 hx) fun a ⟨a1, ka⟩ => ?_
  have hda : a.gpr .rdi = base := (ka.1 .rdi (by decide)).trans hs.rdi
  have hreg : ∀ t < N, InRegions (a.rd ++ a.wr) (off base (K.bits + t)) 1 := fun t ht =>
    ⟨_, List.mem_append_right _ (ka.2.2.2 ▸ hs.wr), hs.contains (by omega) (by decide)⟩
  rw [WP.block_append_iff]
  have hv : ∀ i, (fun t => (k.testBit (K.w * j + (t - K.bits))).toNat) i ≤ 1 := fun _ => Bool.toNat_le _
  refine WP.mono (hornerBits_ok hv K.w K.bits (s := a) (by omega) fun i hi => ?_)
    fun b ⟨b2, kb⟩ => ?_
  · have he : a.ea (winByte (K.bits + i)) = off base (K.bits + (K.w * j + i)) := by
      rw [ea_winByte hda a1]
      exact congrArg (off base) (by omega)
    refine ⟨by rw [he]; exact hreg _ (by omega), ?_⟩
    rw [he, ka.2.1, hbits _ (by omega), show K.bits + i - K.bits = i by omega]
    cases k.testBit (K.w * j + i) <;> rfl
  have hW : hornerVal (fun t => (k.testBit (K.w * j + (t - K.bits))).toNat) K.bits K.w = combWin K.w k j := by
    have := hornerVal_eq k K.w j K.w (Nat.le_refl _)
    rw [Nat.sub_self, Nat.add_zero] at this
    rw [combWin, ← this]
    exact hornerVal_congr fun i _ => by simp only [show K.bits + i - K.bits = i by omega]
  rw [hW] at b2
  have hdb : b.gpr .rdi = base := (kb.1 .rdi (by decide)).trans hda
  have hcb : b.gpr .rcx = BitVec.ofNat 64 (K.w * j) := (kb.1 .rcx (by decide)).trans a1
  have hlt := combWin_lt K.w k j
  have hcar := bcar_le K.w k j
  -- `rax = W + c`.
  obtain ⟨b', hb'⟩ : ∃ q : State → Prop, q = fun t => t.gpr .rax =
      BitVec.ofNat 64 (combWin K.w k j + bcar K.w k j) ∧ Keeps [.rax, .rdx] b t := ⟨_, rfl⟩
  have hmid : WP isa (.block (if c then [.movzx8 .rdx (winByte (K.bits - 1)), .alu .add .rax (.reg .rdx)]
      else [])) b b' := by
    subst hb'
    rcases hc with ⟨rfl, hj1⟩ | ⟨rfl, rfl⟩
    · have hwj : 1 ≤ K.w * j := Nat.mul_le_mul hw1 hj1
      have hea : b.ea (winByte (K.bits - 1)) = off base (K.bits + (K.w * j - 1)) := by
        rw [ea_winByte hdb hcb]; exact congrArg (off base) (by omega)
      have hm : b.mem (off base (K.bits + (K.w * j - 1))) = BitVec.ofNat 8 (bcar K.w k j) := by
        rw [kb.2.1, ka.2.1, hbits _ (by omega), bcar_testBit hj1, byte_testBit]
      have hr := hreg (K.w * j - 1) (by omega)
      rw [← kb.2.2.1, ← kb.2.2.2] at hr
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load8,
        hea, hr, hm, ite_true, Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
        reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left', b2]
      refine ⟨?_, fun r hr' => ?_, rfl, rfl, rfl⟩
      · apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
        have : combWin K.w k j < 2 ^ 9 := Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))
        rw [Nat.mod_eq_of_lt (by omega : bcar K.w k j < 2 ^ 8), Nat.mod_eq_of_lt (by omega : bcar K.w k j < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : combWin K.w k j < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : combWin K.w k j + bcar K.w k j < 2 ^ 64)]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr'.1, hr'.2, ite_false]
    · have h0 : bcar K.w k 0 = 0 := rfl
      rw [h0, Nat.add_zero]
      exact WP.block_nil ⟨b2, fun _ _ => rfl, rfl, rfl, rfl⟩
  rw [WP.block_append_iff]
  refine WP.mono hmid fun t₁ h₁ => ?_
  rw [hb'] at h₁
  obtain ⟨m₁, k₁⟩ := h₁
  have hd₁ : t₁.gpr .rdi = base := (k₁.1 .rdi (by decide)).trans hdb
  have hc₁ : t₁.gpr .rcx = BitVec.ofNat 64 (K.w * j) := (k₁.1 .rcx (by decide)).trans hcb
  have hea : off base (K.bits + K.w - 1 + K.w * j) = off base (K.bits + (K.w * j + (K.w - 1))) :=
    congrArg (off base) (by omega)
  have hr := hreg (K.w * j + (K.w - 1)) (by omega)
  rw [← kb.2.2.1, ← kb.2.2.2, ← k₁.2.2.1, ← k₁.2.2.2, ← hea] at hr
  have hm : t₁.mem (off base (K.bits + K.w - 1 + K.w * j)) = BitVec.ofNat 8 (bcar K.w k (j + 1)) := by
    rw [hea, k₁.2.1, kb.2.1, ka.2.1, hbits _ (by omega), bcar_succ_testBit hw1, byte_testBit]
  have hmle : combWin K.w k j + bcar K.w k j < 2 ^ K.w + 1 := by
    rcases bdig_cases hw1 k j with ⟨-, h, -⟩ | ⟨h0, -⟩
    · omega
    · rw [bcar_succ hw1] at h0
      have := (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).mp h0
      have := two_pow_pred hw1
      omega
  refine WP.mono (bmagTail_ok K hw hmle (Nat.lt_succ_of_le (bcar_le _ _ _)) hd₁ hc₁ m₁ hr hm)
    fun t ⟨t1, t2, kt⟩ => ?_
  rw [← bmag_eq hw1] at t1 t2
  exact ⟨t1, t2, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans
    ((k₁.mono (by decide)).trans (kt.mono (by decide)))⟩

/-! ## Whether a number is zero -/

/-- `f 0 ||| … ||| f (m - 1)`. -/
def orAll (f : Nat → BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | m + 1 => orAll f m ||| f m

theorem orAll_eq_zero (f : Nat → BitVec 64) : ∀ m, orAll f m = 0 ↔ ∀ i < m, f i = 0
  | 0 => by simp [orAll]
  | m + 1 => by
    rw [orAll]
    have ih := orAll_eq_zero f m
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h
      have h1 := ih.mp h1
      intro i hi
      rcases Nat.lt_or_ge i m with h | h
      · exact h1 i h
      · obtain rfl : i = m := by omega
        exact h2
    · intro h
      exact BitVec.or_eq_zero_iff.mpr ⟨ih.mpr fun i hi => h i (by omega), h m (by omega)⟩

theorem wordsVal_eq_zero_iff (mem : Mem) (base : Addr) (d : Nat) :
    ∀ k, wordsVal mem base d k = 0 ↔ ∀ i < k, word mem base (d + 8 * i) = 0
  | 0 => by simp [wordsVal]
  | k + 1 => by
    rw [wordsVal_succ_top]
    have ih := wordsVal_eq_zero_iff mem base d k
    have hp := Nat.two_pow_pos (64 * k)
    have hw : word mem base (d + 8 * k) = 0 ↔ (word mem base (d + 8 * k)).toNat = 0 :=
      ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
    constructor
    · intro h i hi
      have h0 : 2 ^ (64 * k) * (word mem base (d + 8 * k)).toNat = 0 := by omega
      rcases Nat.lt_or_ge i k with hik | hik
      · exact ih.mp (by omega) i hik
      · obtain rfl : i = k := by omega
        rcases Nat.mul_eq_zero.mp h0 with h1 | h1
        · omega
        · exact hw.mpr h1
    · intro h
      have h1 : wordsVal mem base d k = 0 := ih.mpr fun i hi => h i (by omega)
      rw [h1, hw.mp (h k (by omega))]
      simp

/-- `rax |= [z + 8 (i + 1)]` for `i < m`, from `rax = [z]`. -/
theorem orChain_ok {base : Addr} {size z : Nat} : ∀ m, ∀ (s : State), Scr s base size → z + 8 * (m + 1) ≤ size →
    s.gpr .rax = orAll (fun i => word s.mem base (z + 8 * i)) 1 →
    WP isa (.block ((List.range m).map fun i => .alu .or .rax (.mem (sc (z + 8 * (i + 1)))))) s fun t =>
      t.gpr .rax = orAll (fun i => word s.mem base (z + 8 * i)) (m + 1) ∧ Keeps [.rax] s t
  | 0, s, _, _, hr => WP.block_nil ⟨hr, fun _ _ => rfl, rfl, rfl, rfl⟩
  | m + 1, s, hs, hz, hr => by
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (orChain_ok m s hs (by omega) hr) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by decide)
    apply WP.of_runBlock
    simp only [List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      Option.bind_some, load_sc hs₁ (d := z + 8 * (m + 1)) (by omega), RegUpd.gpr_setReg,
      RegUpd.gpr_arithFlags, ite_true, Option.some.injEq, exists_eq_left', e₁, k₁.2.1]
    refine ⟨rfl, fun r hr' => ?_, k₁.2.1, k₁.2.2.1, k₁.2.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr', ite_false]
    exact k₁.1 r (by simp [hr'])

/-- `rcx` all ones if the `n ≥ 1` words at `z` are not all zero, through
`rax`. -/
theorem nzMask_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n z : Nat} (hn1 : 1 ≤ n)
    (hz : z + 8 * n ≤ size) :
    WP isa (.block (nzMask n z)) s fun t =>
      t.gpr .rcx = bmask (decide (wordsVal s.mem base z n ≠ 0)) ∧ Keeps [.rax, .rcx] s t := by
  have hnw := hs.nowrap
  rw [nzMask, WP.block_append_iff]
  refine WP.mono (show WP isa (.block (.mov .rax (.mem (sc z)) :: (List.range (n - 1)).map
      fun i => .alu .or .rax (.mem (sc (z + 8 * (i + 1)))))) s (fun s₂ =>
      s₂.gpr .rax = orAll (fun i => word s.mem base (z + 8 * i)) n ∧ Keeps [.rax] s s₂) by
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mov .rax (.mem (sc z))]) s (fun s₁ =>
        s₁.gpr .rax = orAll (fun i => word s.mem base (z + 8 * i)) 1 ∧ Keeps [.rax] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
        load_sc hs (d := z) (by omega), RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨by simp [orAll], fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by decide)
    refine WP.mono (orChain_ok (n - 1) s₁ hs₁ (by omega) (by rw [k₁.2.1]; exact e₁)) fun s₂ ⟨e₂, k₂⟩ => ?_
    rw [k₁.2.1, show n - 1 + 1 = n by omega] at e₂
    exact ⟨e₂, k₁.trans k₂⟩) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hz' : (orAll (fun i => word s.mem base (z + 8 * i)) n = 0) ↔ wordsVal s.mem base z n = 0 := by
    rw [orAll_eq_zero, wordsVal_eq_zero_iff]
  apply WP.of_runBlock
  set_option linter.unusedSimpArgs false in
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.setReg32,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    RegUpd.cf_setReg, reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left', e₂,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags]
  refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have e0 : (0 : BitVec 32).setWidth 64 = 0 := rfl
    rw [e0]
    by_cases h0 : wordsVal s.mem base z n = 0
    · have h1 := hz'.mpr h0
      rw [h1]; simp [h0]; rfl
    · have h1 : orAll (fun i => word s.mem base (z + 8 * i)) n ≠ 0 := fun h => h0 (hz'.mp h)
      have : 0 < (orAll (fun i => word s.mem base (z + 8 * i)) n).toNat := by
        refine Nat.pos_of_ne_zero fun h => h1 (BitVec.eq_of_toNat_eq h)
      simp [h0, this]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
    exact k₂.1 r (by simp [hr.1])
  · exact k₂.2.1
  · exact k₂.2.2.1
  · exact k₂.2.2.2

/-! ## The sign, and `Y = 1` for `O` -/

/-- `rcx` all ones if Booth's digit `rbx = j` is negative (or a negative
zero): if its window's top bit is set. -/
theorem bsignMask_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {k j N : Nat} (hw1 : 1 ≤ K.w) (hw : K.w < 2 ^ 31) (hj : K.w * j + K.w ≤ N) (hN : K.bits + N ≤ size)
    (hx : s.gpr .rbx = BitVec.ofNat 64 j)
    (hbits : ∀ t < N, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block K.bsignMask) s fun t =>
      t.gpr .rcx = bmask (decide (bcar K.w k (j + 1) = 1)) ∧ Keeps [.rax, .rcx, .rdx] s t := by
  have hn := hs.nowrap
  have hj64 : j < 2 ^ 64 := by
    have : j ≤ K.w * j := Nat.le_mul_of_pos_left _ (by omega)
    omega
  rw [TCombCfg.bsignMask, WP.block_append_iff]
  refine WP.mono (winIndex_ok s hw hj64 hx) fun a ⟨a1, ka⟩ => ?_
  have hea : a.ea (winByte (K.bits + K.w - 1)) = off base (K.bits + (K.w * j + (K.w - 1))) := by
    rw [ea_winByte ((ka.1 .rdi (by decide)).trans hs.rdi) a1]
    exact congrArg (off base) (by omega)
  have hr : InRegions (a.rd ++ a.wr) (off base (K.bits + (K.w * j + (K.w - 1)))) 1 :=
    ⟨_, List.mem_append_right _ (ka.2.2.2 ▸ hs.wr), hs.contains (by omega) (by decide)⟩
  have hm : a.mem (off base (K.bits + (K.w * j + (K.w - 1)))) = BitVec.ofNat 8 (bcar K.w k (j + 1)) := by
    rw [ka.2.1, hbits _ (by omega), bcar_succ_testBit hw1, byte_testBit]
  have hb := bcar_le K.w k (j + 1)
  apply WP.of_runBlock
  set_option linter.unusedSimpArgs false in
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.load8, hea,
    hr, hm, ite_true, Option.map_some, Option.bind_some, State.setReg32, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left',
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags]
  refine ⟨?_, fun r hr' => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
  · rcases (by omega : bcar K.w k (j + 1) = 0 ∨ bcar K.w k (j + 1) = 1) with h | h <;> rw [h] <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr'.1, hr'.2.1, ite_false]
    exact ka.1 r (by simp [hr'.1, hr'.2.1, hr'.2.2])

/-- `Y = R` (`one`) where `Z = 0`, in place: `Y`'s value, and nothing but `Y`
changes. -/
theorem outFix_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hn1 : 1 ≤ K.M.n) (hone : K.one < 2 ^ (64 * K.M.n)) (hy : K.A.y + 8 * K.M.n ≤ size)
    (hz : K.A.z + 8 * K.M.n ≤ size) (hzero : K.zero + 8 * K.M.n ≤ size)
    (hy0 : K.A.y + 8 * K.M.n ≤ K.zero ∨ K.zero + 8 * K.M.n ≤ K.A.y)
    (h0 : wordsVal s.mem base K.zero K.M.n = 0) :
    WP isa (.block K.outFix) s fun t =>
      wordsVal t.mem base K.A.y K.M.n =
        (if wordsVal s.mem base K.A.z K.M.n = 0 then K.one else wordsVal s.mem base K.A.y K.M.n) ∧
      KeepRegs [.rax, .rcx, .rdx] s t ∧ Outside base K.A.y (8 * K.M.n) s.mem t.mem := by
  have hnw := hs.nowrap
  unfold TCombCfg.outFix
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (nzMask_ok hs hn1 hz) fun s₁ ⟨c₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok (decide (wordsVal s.mem base K.A.z K.M.n ≠ 0)) K.M.n hs₁ c₁ (o := K.A.y)
    (a := K.zero) (b := K.A.y) hy hzero hy (by omega) (Or.inl (Nat.le_refl _))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (notMask_ok s₂ (b := decide (wordsVal s.mem base K.A.z K.M.n ≠ 0))
    (by rw [k₂.gpr _ (by decide), c₁])) fun s₃ ⟨c₃, k₃, _⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (orSteps_ok K.M.n s₃ hs₃ c₃ hy) fun t ⟨e₄, k₄, O₄, _⟩ => ⟨?_, ?_, ?_⟩
  · rw [k₁.2.1] at e₂
    by_cases hz0 : wordsVal s.mem base K.A.z K.M.n = 0
    · simp only [hz0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
        Bool.not_false] at e₂ e₄ ⊢
      rw [h0] at e₂
      have hw0 := (wordsVal_eq_zero_iff _ _ _ _).mp e₂
      refine wordsVal_wordOf hone fun i hi => ?_
      rw [e₄ i hi, k₃.2.1, hw0 i hi, bv_and_true, bv_or_zero]
    · simp only [hz0, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, Bool.not_true] at e₂ e₄ ⊢
      rw [← e₂, ← k₃.2.1]
      exact wordsVal_congr₂ _ _ _ fun i hi => by rw [e₄ i hi, bv_and_or_false]
  · exact ((Keeps.regs k₁).mono (by decide)).trans ((k₂.mono (by decide)).trans
      (((Keeps.regs k₃).mono (by decide)).trans (k₄.mono (by decide))))
  · intro x hx
    rw [O₄ x hx, k₃.2.1, O₂ x hx, k₁.2.1]

end VG.Proof.Weierstrass.X86_64
