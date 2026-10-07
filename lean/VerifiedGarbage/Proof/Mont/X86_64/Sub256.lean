import VerifiedGarbage.Proof.Mont.X86_64.OpsReg

/-!
# P-256 field subtraction on x86-64

The modulus limbs are all ones, `2³² - 1`, zero and `2⁶⁴ - 2³² + 1`.
Construct their borrow masks in registers, then add them directly to the
four-limb difference. The inputs may alias the output. No temporary memory
is written; the existing field-operation frame is preserved.
-/

namespace VG.Proof.Mont.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono add_carry adc_carry)

/-- Form the masked P-256 modulus from the subtraction borrow. -/
theorem p256SubMask_ok (s : State) (c : Bool) (hx : s.gpr .rax = if c then -1 else 0) :
    WP isa (.block p256SubMask) s fun s' =>
      (s'.gpr .rax).toNat + 2 ^ 64 * (s'.gpr .rcx).toNat +
        2 ^ 192 * (s'.gpr .rdx).toNat =
          (if c then 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff else 0) ∧
      Keeps [.rcx, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [p256SubMask, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, readSrc32, State.setReg32, Option.bind_some, Option.map_some, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [hx]
    cases c <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
      hr.1, hr.2, ite_false]

/-- The four-word carry chain adds the masked modulus. -/
theorem p256SubAdd_ok (s : State) :
    WP isa (.block p256SubAdd) s fun s' => ∃ c, s'.cf = some c ∧
      regsVal s' (low 4) + 2 ^ 256 * c.toNat = regsVal s (low 4) +
        ((s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rcx).toNat + 2 ^ 192 * (s.gpr .rdx).toNat) ∧
      Keeps (low 4) s s' := by
  apply WP.of_runBlock
  simp only [p256SubAdd, low, acc, List.take, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, Option.bind_some, Option.map_some, regsVal, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, reduceCtorEq, ↓reduceIte,
    BitVec.ofNat_eq_ofNat, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e1 := add_carry (s.gpr .r8) (s.gpr .rax)
    have e2 := adc_carry (s.gpr .r9) (s.gpr .rcx)
      (decide (2 ^ 64 ≤ (s.gpr .r8).toNat + (s.gpr .rax).toNat))
    generalize decide (2 ^ 64 ≤ (s.gpr .r8).toNat + (s.gpr .rax).toNat) = c₁ at e1 e2 ⊢
    have e3 := adc_carry (s.gpr .r10) (BitVec.signExtend 64 (0#32))
      (decide (2 ^ 64 ≤ (s.gpr .r9).toNat + (s.gpr .rcx).toNat + c₁.toNat))
    generalize decide (2 ^ 64 ≤ (s.gpr .r9).toNat + (s.gpr .rcx).toNat + c₁.toNat) = c₂ at e2 e3 ⊢
    have e4 := adc_carry (s.gpr .r11) (s.gpr .rdx)
      (decide (2 ^ 64 ≤ (s.gpr .r10).toNat + (BitVec.signExtend 64 (0#32)).toNat + c₂.toNat))
    generalize decide (2 ^ 64 ≤ (s.gpr .r10).toNat + (BitVec.signExtend 64 (0#32)).toNat + c₂.toNat) = c₃ at e3 e4 ⊢
    have hz : (BitVec.signExtend 64 (0#32)).toNat = 0 := rfl
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- Subtraction specialized to the four limbs of P-256's field modulus. -/
theorem sub256_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hn4 : M.n = 4) (hm : m = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
    {o a b : Nat} (ho : o + 8 * M.n ≤ size) (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (sub256 o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m := by
  simp only [hn4] at ho ha hb hA hB ⊢
  have hf : Fresh (low 4) := (fresh_top_low (n := 4) (by decide)).tail
  have hl : (low 4).length = 4 := rfl
  have hsub : ∀ r ∈ low 4, r ∈ clob M.n := by rw [hn4]; decide
  rw [sub256, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok (low 4) hs (a := a) (by simpa only [hl] using ha) hf)
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (chainSub_ok hs₁ (t := .r8) (ts := [.r9, .r10, .r11]) (b := b) hb hf)
    fun s₂ ⟨c, c₂, e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sbbMask_ok s₂ c₂) fun s₃ ⟨x₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (p256SubMask_ok s₃ c x₃) fun s₄ ⟨e₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (p256SubAdd_ok s₄) fun s₅ ⟨c', _, e₅, k₅⟩ => ?_
  have hs₅ := ((hs₂.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)).of_keeps k₅ (by decide)
  refine WP.mono (stores_ok (low 4) hs₅ (o := o) (by simpa only [hl] using ho) hf.1)
    fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  rw [hl] at e₁ e₆ O₆
  change regsVal s₂ (low 4) + wordsVal s₁.mem base b 4 =
    regsVal s₁ (low 4) + 2 ^ 256 * c.toNat at e₂
  have hR₄ : regsVal s₄ (low 4) = regsVal s₂ (low 4) := by
    apply regsVal_congr
    intro r hr
    rw [k₄.1 r (by revert r; decide), k₃.1 r (by revert r; decide)]
  rw [hR₄, e₄, ← hm] at e₅
  rw [e₁, k₁.2.1] at e₂
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx _ => ?_⟩, ?_⟩
  · have hr' : r ∉ low 4 := fun h => hr (hsub r h)
    have h4 : r ∉ [.rcx, .rdx] := by
      intro h; apply hr; rw [hn4]
      exact (by decide : ∀ r : Reg, r ∈ [.rcx, .rdx] → r ∈ clob 4) r h
    have h3 : r ∉ [.rax] := by
      intro h; apply hr; rw [hn4]
      exact (by decide : ∀ r : Reg, r ∈ [.rax] → r ∈ clob 4) r h
    rw [k₆.gpr r (by simp), k₅.1 r hr', k₄.1 r h4, k₃.1 r h3, k₂.1 r hr', k₁.1 r hr']
  · rw [k₆.rd, k₅.2.2.1, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
  · rw [k₆.wr, k₅.2.2.2, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  · rw [O₆ x (by simpa only [hn4] using hx), k₅.2.1, k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
  · rw [e₆]
    have hR₂ := regsVal_lt s₂ (low 4)
    have hR₅ := regsVal_lt s₅ (low 4)
    rw [hl] at hR₂ hR₅
    have hmX : m < 2 ^ 256 := by rw [hm]; decide
    cases c <;> cases c' <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero,
      Nat.mul_one, Nat.add_zero, Bool.false_eq_true, ite_false, ite_true] at e₂ e₅
    · rw [show wordsVal s.mem base a 4 + m - wordsVal s.mem base b 4 =
        (wordsVal s.mem base a 4 - wordsVal s.mem base b 4) + m by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
      omega
    · omega
    · omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega

/-- The friendly reduction's words determine P-256's field modulus. -/
theorem p256_of_red {M : Mod} {m : Nat} (hred : M.red = .friendly p256Ws) (h : M.ok m = true) :
    M.n = 4 ∧ m = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff := by
  have h' := Mod.ok_red h
  rw [hred] at h'
  simp only [Red.ok, Bool.and_eq_true, beq_iff_eq] at h'
  obtain ⟨⟨⟨hn, hm⟩, hw⟩, -⟩ := h'
  have h1 : (m + 1) % 2 ^ 64 = 0 := by omega
  have hw' : mwVal p256Ws = 0xffffffff0000000100000000000000000000000100000000 := by rfl
  have h2 := Nat.div_add_mod (m + 1) (2 ^ 64)
  rw [← hw, hw', h1, Nat.add_zero] at h2
  refine ⟨by rw [← hn]; rfl, ?_⟩
  omega
end VG.Proof.Mont.X86_64
