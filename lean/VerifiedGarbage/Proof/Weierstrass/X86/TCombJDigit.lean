import VerifiedGarbage.Impl.Weierstrass.X86.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.Booth

/-!
# The comb with Booth's digits on x86 (32-bit): digits and masks

Booth's digit `j = esi` from the table of bits: window `j` by Horner's rule
as before (`hornerBits_ok`), plus the bit below it (`c_j`) for `j ≥ 1`, and
the magnitude from the window's top bit (`bmagTail_ok`), together `bdigit_ok`;
and the sign's mask (`bsignMask_ok`).
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

private theorem bmag_fact : ∀ w < 9, ∀ m < 2 ^ w + 1, ∀ s < 2,
    (BitVec.ofNat 32 m ^^^ ((0 : BitVec 32) - BitVec.ofNat 32 s)) - ((0 : BitVec 32) - BitVec.ofNat 32 s) +
      (((0 : BitVec 32) - BitVec.ofNat 32 s) &&& BitVec.ofNat 32 (2 ^ w)) =
    BitVec.ofNat 32 (if s = 1 then 2 ^ w - m else m) := by
  decide +kernel

/-- The magnitude from `m = W + c` in `eax` and the window's top bit `s` at
`edi + ecx + bits + w - 1`: `s ? 2^w - m : m` into `eax` and `ebx`, through `edx`. -/
theorem bmagTail_ok (K : TCombCfg) {s : State} {base : Addr} {i m sb : Nat} (hw : K.w < 9)
    (hm2 : m < 2 ^ K.w + 1) (hs2 : sb < 2) {size : Nat} (hs : Scr s base size)
    (hd : K.bits + K.w - 1 + i < size)
    (hc : s.gpr .ecx = s.gpr .edi + BitVec.ofNat 32 i) (hx : s.gpr .eax = BitVec.ofNat 32 m)
    (hr : InRegions (s.rd ++ s.wr) (off base (K.bits + K.w - 1 + i)) 1)
    (hm : s.mem (off base (K.bits + K.w - 1 + i)) = BitVec.ofNat 8 sb) :
    WP isa (.block [.movzx8 .edx (winByte (K.bits + K.w - 1)), .mov .ebx (.imm 0), .alu .sub .ebx (.reg .edx),
    .alu .xor .eax (.reg .ebx), .alu .sub .eax (.reg .ebx),
    .alu .and .ebx (.imm (BitVec.ofNat 32 (2 ^ K.w))), .alu .add .eax (.reg .ebx), .mov .ebx (.reg .eax)]) s
      fun t => t.gpr .eax = BitVec.ofNat 32 (if sb = 1 then 2 ^ K.w - m else m) ∧
        t.gpr .ebx = BitVec.ofNat 32 (if sb = 1 then 2 ^ K.w - m else m) ∧ CKeeps [.eax, .edx, .ebx] s t := by
  have hea : s.ea (winByte (K.bits + K.w - 1)) = off base (K.bits + K.w - 1 + i) := ea_winByte hs hc hd
  have es : BitVec.setWidth 32 (BitVec.ofNat 8 sb) = BitVec.ofNat 32 sb := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : sb < 2 ^ 8), Nat.mod_eq_of_lt (by omega : sb < 2 ^ 32)]
  apply WP.of_runBlock
  set_option linter.unusedSimpArgs false in
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load8, hea, hr,
    hm, ite_true, Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left', hx, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, es]
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

/-- Booth's digit's magnitude into `eax` and `ebx`, for `esi = j`, from the
table of bits at `K.bits`: with `c` (the bit below the window) for `j ≥ 1`,
without for `j = 0`. -/
theorem bdigit_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {k j N : Nat} (hw1 : 1 ≤ K.w) (hw : K.w < 9) (hj : K.w * j + K.w ≤ N) (hN : K.bits + N ≤ size)
    (hb1 : 1 ≤ K.bits) (hx : s.gpr .esi = BitVec.ofNat 32 j)
    (hbits : ∀ t < N, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0) {c : Bool}
    (hc : (c = true ∧ 1 ≤ j) ∨ (c = false ∧ j = 0)) :
    WP isa (.block (K.bdigit c)) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (bmag K.w k j) ∧ t.gpr .ebx = BitVec.ofNat 32 (bmag K.w k j) ∧
        CKeeps [.eax, .ecx, .edx, .ebx] s t := by
  have hn := hs.nowrap
  have hj32 : j < 2 ^ 32 := by
    have : j ≤ K.w * j := Nat.le_mul_of_pos_left _ (by omega)
    omega
  rw [TCombCfg.bdigit, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (winIndex_ok s (by omega) hj32 hx) fun a ⟨a1, ka⟩ => ?_
  have hsa := hs.of_keeps ka.keeps (by decide)
  have hca : a.gpr .ecx = a.gpr .edi + BitVec.ofNat 32 (K.w * j) := by
    rw [ka.1 .edi (by decide)]; exact a1
  have hreg : ∀ t < N, InRegions (a.rd ++ a.wr) (off base (K.bits + t)) 1 := fun t ht =>
    ⟨_, List.mem_append_right _ (ka.2.2.2 ▸ hs.wr), Scr.contains hs.nowrap (by omega)⟩
  rw [WP.block_append_iff]
  have hv : ∀ i, (fun t => (k.testBit (K.w * j + (t - K.bits))).toNat) i ≤ 1 := fun _ => Bool.toNat_le _
  refine WP.mono (hornerBits_ok hv K.w K.bits (s := a) (by omega) fun i hi => ?_)
    fun b ⟨b2, kb⟩ => ?_
  · have he : a.ea (winByte (K.bits + i)) = off base (K.bits + (K.w * j + i)) := by
      rw [ea_winByte hsa hca (by omega)]
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
  have hsb := hsa.of_keeps kb.keeps (by decide)
  have hcb : b.gpr .ecx = b.gpr .edi + BitVec.ofNat 32 (K.w * j) := by
    rw [kb.1 .ecx (by decide), kb.1 .edi (by decide)]; exact hca
  have hlt := combWin_lt K.w k j
  have hcar := bcar_le K.w k j
  -- `eax = W + c`.
  obtain ⟨b', hb'⟩ : ∃ q : State → Prop, q = fun t => t.gpr .eax =
      BitVec.ofNat 32 (combWin K.w k j + bcar K.w k j) ∧ CKeeps [.eax, .edx] b t := ⟨_, rfl⟩
  have hmid : WP isa (.block (if c then [.movzx8 .edx (winByte (K.bits - 1)), .alu .add .eax (.reg .edx)]
      else [])) b b' := by
    subst hb'
    rcases hc with ⟨rfl, hj1⟩ | ⟨rfl, rfl⟩
    · have hwj : 1 ≤ K.w * j := Nat.mul_le_mul hw1 hj1
      have hea : b.ea (winByte (K.bits - 1)) = off base (K.bits + (K.w * j - 1)) := by
        rw [ea_winByte hsb hcb (by omega)]; exact congrArg (off base) (by omega)
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
        rw [Nat.mod_eq_of_lt (by omega : bcar K.w k j < 2 ^ 8), Nat.mod_eq_of_lt (by omega : bcar K.w k j < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : combWin K.w k j < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : combWin K.w k j + bcar K.w k j < 2 ^ 32)]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr'.1, hr'.2, ite_false]
    · have h0 : bcar K.w k 0 = 0 := rfl
      rw [h0, Nat.add_zero]
      exact WP.block_nil ⟨b2, fun _ _ => rfl, rfl, rfl, rfl⟩
  rw [WP.block_append_iff]
  refine WP.mono hmid fun t₁ h₁ => ?_
  rw [hb'] at h₁
  obtain ⟨m₁, k₁⟩ := h₁
  have hs₁ := hsb.of_keeps k₁.keeps (by decide)
  have hc₁ : t₁.gpr .ecx = t₁.gpr .edi + BitVec.ofNat 32 (K.w * j) := by
    rw [k₁.1 .ecx (by decide), k₁.1 .edi (by decide)]; exact hcb
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
  refine WP.mono (bmagTail_ok K hw hmle (Nat.lt_succ_of_le (bcar_le _ _ _)) hs₁ (by omega) hc₁ m₁ hr hm)
    fun t ⟨t1, t2, kt⟩ => ?_
  rw [← bmag_eq hw1] at t1 t2
  exact ⟨t1, t2, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans
    ((k₁.mono (by decide)).trans (kt.mono (by decide)))⟩

/-- `ecx` all ones if Booth's digit `esi = j` is negative (or a negative
zero): if its window's top bit is set. -/
theorem bsignMask_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {k j N : Nat} (hw1 : 1 ≤ K.w) (hw : K.w < 2 ^ 31) (hj : K.w * j + K.w ≤ N) (hN : K.bits + N ≤ size)
    (hx : s.gpr .esi = BitVec.ofNat 32 j)
    (hbits : ∀ t < N, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block K.bsignMask) s fun t =>
      t.gpr .ecx = bmask (decide (bcar K.w k (j + 1) = 1)) ∧ CKeeps [.eax, .ecx, .edx] s t := by
  have hn := hs.nowrap
  have hj32 : j < 2 ^ 32 := by
    have : j ≤ K.w * j := Nat.le_mul_of_pos_left _ (by omega)
    omega
  rw [TCombCfg.bsignMask, WP.block_append_iff]
  refine WP.mono (winIndex_ok s (by omega) hj32 hx) fun a ⟨a1, ka⟩ => ?_
  have hea : a.ea (winByte (K.bits + K.w - 1)) = off base (K.bits + (K.w * j + (K.w - 1))) := by
    rw [ea_winByte (hs.of_keeps ka.keeps (by decide)) (by rw [ka.1 .edi (by decide)]; exact a1) (by omega)]
    exact congrArg (off base) (by omega)
  have hr : InRegions (a.rd ++ a.wr) (off base (K.bits + (K.w * j + (K.w - 1)))) 1 :=
    ⟨_, List.mem_append_right _ (ka.2.2.2 ▸ hs.wr), Scr.contains hs.nowrap (by omega)⟩
  have hm : a.mem (off base (K.bits + (K.w * j + (K.w - 1)))) = BitVec.ofNat 8 (bcar K.w k (j + 1)) := by
    rw [ka.2.1, hbits _ (by omega), bcar_succ_testBit hw1, byte_testBit]
  have hb := bcar_le K.w k (j + 1)
  apply WP.of_runBlock
  set_option linter.unusedSimpArgs false in
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load8, hea,
    hr, hm, ite_true, Option.map_some, Option.bind_some, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left',
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags]
  refine ⟨?_, fun r hr' => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
  · rcases (by omega : bcar K.w k (j + 1) = 0 ∨ bcar K.w k (j + 1) = 1) with h | h <;> rw [h] <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr'.1, hr'.2.1, ite_false]
    exact ka.1 r (by simp [hr'.1, hr'.2.1, hr'.2.2])

end VG.Proof.Weierstrass.X86
