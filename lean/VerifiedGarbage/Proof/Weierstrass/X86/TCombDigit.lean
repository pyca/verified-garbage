import VerifiedGarbage.Impl.Weierstrass.X86.TComb
import VerifiedGarbage.Proof.Weierstrass.CombDigitW
import VerifiedGarbage.Proof.Weierstrass.X86.Bits
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd

/-!
# The comb from tables in memory on x86 (32-bit): digits

Iteration `j` reads window `j` (of `w` bits) of the scalar from its table of
bits: `ecx = w j` (`winIndex_ok`), Horner's rule adds its bits
(`hornerBits_ok`), and `|k_j - H|` is its magnitude (`magnitudeH_ok`);
`digit_ok` is all three. The sign of the digit is the complement of the
window's top bit (`signMask_ok`), and the selection's masks compare the
magnitude with each index (`eqMask_ok`).
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

/-- Digit blocks preserve memory as well as registers outside their clobbers. -/
def CKeeps (rs : List Reg) (s t : State) : Prop :=
  (∀ r, r ∉ rs → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem CKeeps.keeps {rs : List Reg} {s t : State} (h : CKeeps rs s t) :
    VG.Proof.Mont.X86.Keeps rs s t := ⟨h.1, h.2.2⟩

theorem CKeeps.mono {rs rs' : List Reg} {s t : State} (h : CKeeps rs s t)
    (hs : ∀ r ∈ rs, r ∈ rs') : CKeeps rs' s t :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem CKeeps.trans {rs : List Reg} {s t u : State} (h : CKeeps rs s t) (k : CKeeps rs t u) :
    CKeeps rs s u := ⟨fun r hr => (k.1 r hr).trans (h.1 r hr), k.2.1.trans h.2.1,
      k.2.2.1.trans h.2.2.1, k.2.2.2.trans h.2.2.2⟩

/-- Runs a block by symbolic execution, reading registers through the writes. -/
syntax "crun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| crun) => `(tactic| crun [])
  | `(tactic| crun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
        execShift, execMul, State.load8, State.ea, winByte, Option.bind_some,
        Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
        RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_arithFlags,
        RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setFlags,
        RegUpd.rd_setFlags, RegUpd.wr_setFlags, ite_true, ite_false, reduceCtorEq, Nat.le_refl,
        true_and, and_true, and_self, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte, Option.some.injEq,
        exists_eq_left', $ls,*]))

/-- All ones if `b`, else zero. -/
abbrev bmask (b : Bool) : BitVec 32 := if b then BitVec.allOnes 32 else 0

/-- The window index added to the scratch pointer. -/
theorem winIndex_ok (s : State) {w j : Nat} (hw : w < 2 ^ 32) (hj : j < 2 ^ 32)
    (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block (winIndex w)) s fun t =>
      t.gpr .ecx = s.gpr .edi + BitVec.ofNat 32 (w * j) ∧ CKeeps [.eax, .ecx, .edx] s t := by
  crun [winIndex, hb]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hj]
    rw [Nat.mul_comm, BitVec.add_comm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
      hr.1, hr.2.1, hr.2.2, ite_false]

/-- The byte address is within the non-wrapping scratch region. -/
theorem ea_winByte {s : State} {base : Addr} {size i d : Nat} (hs : Scr s base size)
    (hc : s.gpr .ecx = s.gpr .edi + BitVec.ofNat 32 i) (hd : d + i < size) :
    s.ea (winByte d) = off base (d + i) := by
  change ((s.gpr .ecx + BitVec.ofNat 32 d).setWidth 64) = _
  rw [hc, Offset.add_add, Nat.add_comm i d]
  exact hs.ea hd

/-- `eax = Σ_{i<k} b_i 2^i` for the bytes `b_i` (0 or 1) at `edi + ecx + d + i`. -/
theorem hornerBits_ok {v : Nat → Nat} (hv : ∀ i, v i ≤ 1) :
    ∀ (k d : Nat) {s : State}, k < 32 →
      (∀ i < k, InRegions (s.rd ++ s.wr) (s.ea (winByte (d + i))) 1 ∧
        s.mem (s.ea (winByte (d + i))) = BitVec.ofNat 8 (v (d + i))) →
      WP isa (.block (hornerBits d k)) s fun t =>
        t.gpr .eax = BitVec.ofNat 32 (hornerVal v d k) ∧ CKeeps [.eax, .edx] s t
  | 0, d, s, _, _ => by
    apply WP.of_runBlock
    simp only [hornerBits, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      Option.map_some, RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
    refine ⟨by rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact RegUpd.gpr_setReg_of_ne s _ hr.1
  | k + 1, d, s, hk, hb => by
    rw [hornerBits, WP.block_append_iff]
    refine WP.mono (hornerBits_ok hv k (d + 1) (by omega) fun i hi => by
      rw [show d + 1 + i = d + (i + 1) by omega]; exact hb (i + 1) (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
    obtain ⟨hr, hm⟩ := hb 0 (by omega)
    rw [Nat.add_zero] at hr hm
    have hcx : s₁.gpr .ecx = s.gpr .ecx := k₁.1 .ecx (by decide)
    simp only [State.ea, winByte] at hr hm
    have hlt := hornerVal_lt hv (d + 1) k
    have hk2 : 2 ^ k < 2 ^ 31 := Nat.pow_lt_pow_right (by decide) (by omega)
    crun [hcx, k₁.2.1, k₁.2.2.1, k₁.2.2.2, hr, hm, e₁]
    refine ⟨?_, ⟨fun r hr' => ?_, k₁.2.1, k₁.2.2.1, k₁.2.2.2⟩⟩
    · apply BitVec.eq_of_toNat_eq
      have := hv d
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, hornerVal]
      rw [Nat.mod_eq_of_lt (by omega : v d % 2 ^ 8 < 2 ^ 32), Nat.mod_eq_of_lt (by omega : v d < 2 ^ 8),
        Nat.mod_eq_of_lt (by omega : hornerVal v (d + 1) k < 2 ^ 32)]
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr'.1, hr'.2, ite_false]
      exact k₁.1 r (by simpa using hr')

private theorem magH_fact : ∀ w < 9, ∀ v < 2 ^ w,
    (BitVec.ofNat 32 v - BitVec.ofNat 32 (2 ^ (w - 1)) ^^^
        ((0 : BitVec 32) - (BitVec.ofNat 32 v - BitVec.ofNat 32 (2 ^ (w - 1))) >>> 31)) -
      ((0 : BitVec 32) - (BitVec.ofNat 32 v - BitVec.ofNat 32 (2 ^ (w - 1))) >>> 31) =
      BitVec.ofNat 32 (magH (2 ^ (w - 1)) v) := by
  decide +kernel

/-- `eax = ebx = |v - H|` from the window `v` in `eax`, for `H = 2^(w-1)`,
`w ≤ 8`, through `edx`. -/
theorem magnitudeH_ok (s : State) {w v : Nat} (hw : w < 9) (hv : v < 2 ^ w)
    (hx : s.gpr .eax = BitVec.ofNat 32 v) :
    WP isa (.block (magnitudeH (2 ^ (w - 1)))) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (magH (2 ^ (w - 1)) v) ∧
      t.gpr .ebx = BitVec.ofNat 32 (magH (2 ^ (w - 1)) v) ∧ CKeeps [.eax, .edx, .ebx] s t := by
  crun [magnitudeH, hx]
  rw [magH_fact w hw v hv]
  refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2,
    ite_false]

/-- The digit's magnitude into `eax` and `ebx`: `|k_j - H|` of window `j` of
`k`, for `esi = j`, from its table of bits at `K.bits`. -/
theorem digit_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {k j N : Nat} (hw1 : 1 ≤ K.w) (hw : K.w < 9) (hj : K.w * j + K.w ≤ N) (hN : K.bits + N ≤ size)
    (hx : s.gpr .esi = BitVec.ofNat 32 j)
    (hbits : ∀ t < N, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block K.digit) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (magH K.H (combWin K.w k j)) ∧
      t.gpr .ebx = BitVec.ofNat 32 (magH K.H (combWin K.w k j)) ∧ CKeeps [.eax, .ecx, .edx, .ebx] s t := by
  have hn := hs.nowrap
  have hj32 : j < 2 ^ 32 := by
    have : j ≤ K.w * j := Nat.le_mul_of_pos_left _ (by omega)
    omega
  rw [TCombCfg.digit, List.append_assoc, WP.block_append_iff]
  refine WP.mono (winIndex_ok s (by omega) hj32 hx) fun a ⟨a1, ka⟩ => ?_
  rw [WP.block_append_iff]
  have hv : ∀ i, (fun t => (k.testBit (K.w * j + (t - K.bits))).toNat) i ≤ 1 := fun _ => Bool.toNat_le _
  refine WP.mono (hornerBits_ok hv K.w K.bits (s := a) (by omega) fun i hi => ?_)
    fun b ⟨b2, kb⟩ => ?_
  · have he : a.ea (winByte (K.bits + i)) = off base (K.bits + (K.w * j + i)) := by
      rw [ea_winByte (hs.of_keeps ka.keeps (by decide)) (by rw [ka.1 .edi (by decide)]; exact a1) (by omega)]
      exact congrArg (off base) (by omega)
    refine ⟨by rw [he]; exact ⟨_, List.mem_append_right _ (ka.2.2.2 ▸ hs.wr), Scr.contains hs.nowrap (by omega)⟩, ?_⟩
    rw [he, ka.2.1, hbits _ (by omega), show K.bits + i - K.bits = i by omega]
    cases k.testBit (K.w * j + i) <;> rfl
  · have hw' : hornerVal (fun t => (k.testBit (K.w * j + (t - K.bits))).toNat) K.bits K.w = combWin K.w k j := by
      have := hornerVal_eq k K.w j K.w (Nat.le_refl _)
      rw [Nat.sub_self, Nat.add_zero] at this
      rw [combWin, ← this]
      exact hornerVal_congr fun i _ => by simp only [show K.bits + i - K.bits = i by omega]
    have hlt := combWin_lt K.w k j
    refine WP.mono (magnitudeH_ok b hw hlt (by rw [b2, hw'])) fun t ⟨t1, t2, kt⟩ =>
      ⟨t1, t2, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kt.mono (by decide))⟩

/-- `ecx` all ones if `ebx = v`, else zero. -/
theorem eqMask_ok (s : State) {v a : Nat} (hv : v < 2 ^ 31) (ha : a < 2 ^ 31)
    (h8 : s.gpr .ebx = BitVec.ofNat 32 a) :
    WP isa (.block (eqMask v)) s fun t => t.gpr .ecx = bmask (decide (a = v)) ∧ CKeeps [.ecx] s t ∧
      t.xmm = s.xmm := by
  crun [eqMask, h8, RegUpd.xmm_setReg, RegUpd.xmm_arithFlags]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h1 : (1 : BitVec 32).toNat = 1 := by decide
    have hx : decide ((BitVec.ofNat 32 v ^^^ BitVec.ofNat 32 a).toNat < 1) = decide (a = v) := by
      refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
      · have e0 : BitVec.ofNat 32 v ^^^ BitVec.ofNat 32 a = 0 :=
          BitVec.eq_of_toNat_eq ((Nat.lt_one_iff.mp h).trans rfl)
        have e := BitVec.xor_eq_zero_iff.mp e0
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at this
        omega
      · subst h; rw [BitVec.xor_self, BitVec.toNat_zero]; decide
    rw [BitVec.sub_self, h1, hx]
    cases decide (a = v) <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `ecx` all ones if digit `esi = j` is negative: if the top bit of its
window is clear. -/
theorem signMask_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {k j N : Nat} (hw1 : 1 ≤ K.w) (hw : K.w < 2 ^ 31) (hj : K.w * j + K.w ≤ N) (hN : K.bits + N ≤ size)
    (hx : s.gpr .esi = BitVec.ofNat 32 j)
    (hbits : ∀ t < N, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block K.signMask) s fun t =>
      t.gpr .ecx = bmask (decide (combWin K.w k j < 2 ^ (K.w - 1))) ∧ CKeeps [.eax, .ecx, .edx] s t := by
  have hn := hs.nowrap
  have hj64 : j < 2 ^ 32 := by
    have : j ≤ K.w * j := Nat.le_mul_of_pos_left _ (by omega)
    omega
  rw [TCombCfg.signMask, WP.block_append_iff]
  refine WP.mono (winIndex_ok s (by omega) hj64 hx) fun a ⟨a1, ka⟩ => ?_
  have hea : a.ea (winByte (K.bits + K.w - 1)) = off base (K.bits + (K.w * j + (K.w - 1))) := by
    rw [ea_winByte (hs.of_keeps ka.keeps (by decide)) (by rw [ka.1 .edi (by decide)]; exact a1) (by omega)]
    exact congrArg (off base) (by omega)
  have hr : InRegions (a.rd ++ a.wr) (off base (K.bits + (K.w * j + (K.w - 1)))) 1 :=
    ⟨_, List.mem_append_right _ (ka.2.2.2 ▸ hs.wr), Scr.contains hs.nowrap (by omega)⟩
  have hm : a.mem (off base (K.bits + (K.w * j + (K.w - 1)))) =
      if decide (2 ^ (K.w - 1) ≤ combWin K.w k j) then 1 else 0 := by
    rw [ka.2.1, hbits _ (by omega), testBit_top k K.w j hw1]
  apply WP.of_runBlock
  set_option linter.unusedSimpArgs false in
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load8, hea, hr,
    hm, ite_true, Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr' => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
  · by_cases h : 2 ^ (K.w - 1) ≤ combWin K.w k j
    · rw [decide_eq_true h, decide_eq_false (show ¬ combWin K.w k j < 2 ^ (K.w - 1) by omega)]
      decide
    · rw [decide_eq_false h, decide_eq_true (show combWin K.w k j < 2 ^ (K.w - 1) by omega)]
      decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr'.1, hr'.2.1, ite_false]
    exact ka.1 r (by simp [hr'.1, hr'.2.1, hr'.2.2])

end VG.Proof.Weierstrass.X86
