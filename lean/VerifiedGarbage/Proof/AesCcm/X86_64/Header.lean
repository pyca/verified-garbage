import VerifiedGarbage.Proof.AesCcm.X86_64.Absorb

/-!
# AES-CCM on x86-64: the encoding of the length of the associated data

Untrusted: everything here is checked by Lean. `header` zeroes `B` and
writes the encoding of the length `a > 0` (A.2.2) at its start: `[a]₁₆`,
`0xff ‖ 0xfe ‖ [a]₃₂` or `0xff ‖ 0xff ‖ [a]₆₄`, by byte-swapping and
shifting `a` (`header_ok`); its length is in `rbx`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr minLen)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)

/-- A right shift by whole bytes drops the low bytes. -/
theorem le8_ushiftRight (x : BitVec 64) {k : Nat} (hk : k ≤ 8) :
    le8 (x >>> (8 * k)) = (le8 x).drop k ++ Spec.Ccm.zeros k := by
  have hl : ((le8 x).drop k).length = 8 - k := by rw [List.length_drop, Proof.Cmac.length_le8]
  have hlen : (le8 (x >>> (8 * k))).length = ((le8 x).drop k ++ Spec.Ccm.zeros k).length := by
    rw [Proof.Cmac.length_le8, List.length_append, hl, Spec.Ccm.zeros, List.length_replicate]
    omega_arith
  apply List.ext_getElem hlen
  intro i h₁ h₂
  have hi : i < 8 := by rwa [Proof.Cmac.length_le8] at h₁
  by_cases h : i < 8 - k
  · rw [List.getElem_append_left (by rw [hl]; exact h), List.getElem_drop]
    simp only [le8, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      ← Nat.pow_add]
    rw [show 8 * k + 8 * i = 8 * (k + i) by omega_arith]
  · rw [List.getElem_append_right (by rw [hl]; omega_arith)]
    simp only [Spec.Ccm.zeros, List.getElem_replicate, le8, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      ← Nat.pow_add, BitVec.toNat_ofNat]
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega_arith)))]
    rfl

theorem le8_ffff : le8 (BitVec.ofNat 64 0xffff) = [0xff, 0xff] ++ Spec.Ccm.zeros 6 := by decide
theorem le8_feff : le8 (BitVec.ofNat 64 0xfeff) = [0xff, 0xfe] ++ Spec.Ccm.zeros 6 := by decide

theorem encodeLen_lo {a : Nat} (h : a < 2 ^ 16 - 2 ^ 8) : Spec.Ccm.encodeLen a = Spec.Ccm.be 2 a := by
  simp [Spec.Ccm.encodeLen, h]

theorem encodeLen_mid {a : Nat} (h₁ : ¬ a < 2 ^ 16 - 2 ^ 8) (h₂ : a < 2 ^ 32) :
    Spec.Ccm.encodeLen a = [0xff, 0xfe] ++ Spec.Ccm.be 4 a := by
  simp [Spec.Ccm.encodeLen, h₁, h₂]

theorem encodeLen_hi {a : Nat} (h₁ : ¬ a < 2 ^ 16 - 2 ^ 8) (h₂ : ¬ a < 2 ^ 32) :
    Spec.Ccm.encodeLen a = [0xff, 0xff] ++ Spec.Ccm.be 8 a := by
  simp [Spec.Ccm.encodeLen, h₁, h₂]

theorem minLen_ok (s : State) {o n : Nat} (hbx : s.gpr .rbx = BitVec.ofNat 64 o)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 n) (ho : o ≤ 16) (hn : n < 2 ^ 64) :
    WP isa minLen s fun s' => s'.gpr .rcx = BitVec.ofNat 64 (min (16 - o) n) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, h₁⟩ : ∃ s₁, runBlock isa [.mov32 .rcx (imm 16), .alu .sub .rcx (.reg .rbx),
      .alu .cmp .rbp (.reg .rcx)] s = some s₁ ∧
      s₁.gpr .rcx = BitVec.ofNat 64 (16 - o) ∧ s₁.cf = some (decide (n < 16 - o)) ∧
      (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hbx, ofNat_sub ho (by decide)]
    · simp only [cf_arithFlags, hbp, hbx, setWidth_imm, ofNat_sub ho (by decide),
        toNat_ofNat_of_lt hn, toNat_ofNat_of_lt (show 16 - o < 2 ^ 64 by omega_arith),
        show (16 : Nat) % 2 ^ 32 = 16 from rfl, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
    all_goals rfl
  obtain ⟨hcx, hcf, hg, hm, hrd, hwr⟩ := h₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n < 16 - o)) (eval_b hcf) (fun ht => ?_) (fun hf => ?_)
  · have h := of_decide_eq_true ht
    refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hg .rbp (by decide), hbp, Nat.min_eq_right (Nat.le_of_lt h)]
    · intro r hr; simp [gpr_setReg, hr, hg r hr]
    all_goals first | exact hm | exact hrd | exact hwr
  · have h := of_decide_eq_false hf
    refine WP.of_runBlock ⟨s₁, rfl, ?_, hg, hm, hrd, hwr⟩
    rw [hcx, Nat.min_eq_left (by omega_arith)]

/-- `B` zeroed, then the encoding of the length `a` of the associated data
(`rbp`) at its start, and its length in `rbx`. -/
theorem header_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {a : Nat} (ha0 : 0 < a)
    (ha : a < 2 ^ 64) (hbp : s.gpr .rbp = BitVec.ofNat 64 a) :
    WP isa header s fun s' => Env K W SP s' ∧ s'.gpr .rbx = BitVec.ofNat 64 (Proof.AesCcm.hdrLen a) ∧
      (∀ r ∈ [Reg.rbp, .r12, .r14], s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 32) 16 =
        Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - Proof.AesCcm.hdrLen a) := by
  have h15 := E.r15
  have w₁ := E.perm.wW (show 32 + 8 ≤ 2560 by decide)
  have w₂ := E.perm.wW (show 40 + 8 ≤ 2560 by decide)
  have w₃ := E.perm.wW (show 34 + 8 ≤ 2560 by decide)
  have e40 : W + BitVec.ofNat 64 40 = W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have e34 : W + BitVec.ofNat 64 34 = W + BitVec.ofNat 64 32 + BitVec.ofNat 64 2 := by rw [add_ofNat_assoc]
  have cB : ∀ d k, 32 ≤ d → d + k ≤ 48 → (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains W h₁ (by omega_arith) (by decide)
  -- `B` zeroed; CF for `a < 2¹⁶ − 2⁸`.
  obtain ⟨s₁, run₁, hm₁, hcf₁, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      (zero16 bO ++ [.mov32 .rax (imm 0xff00), .alu .cmp .rbp (.reg .rax)]) s = some s₁ ∧
      s₁.mem = (s.mem.writeW (W + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 40)
        (0 : BitVec 64) ∧ s₁.cf = some (decide (a < 2 ^ 16 - 2 ^ 8)) ∧
      (∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [zero16, h15, w₁, w₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags]; rfl
    · simp only [cf_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbp, toNat_ofNat_of_lt ha,
        BitVec.toNat_ofNat]
    · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
    all_goals rfl
  have hz : bytesAt s₁.mem (W + BitVec.ofNat 64 32) 16 = Spec.Ccm.zeros 16 := by
    rw [hm₁, e40, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
  have fz : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₁.mem := by
    rw [hm₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64) (cB 32 8 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64) (cB 40 8 (by decide) (by decide))
  have E₁ : Env K W SP s₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hrd₁ hwr₁
  have hbp₁ : s₁.gpr .rbp = BitVec.ofNat 64 a := by rw [hg₁ _ (by decide), hbp]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have ha64 := toNat_ofNat_of_lt ha
  refine WP.ite (decide (a < 2 ^ 16 - 2 ^ 8)) (eval_b hcf₁) (fun ht => ?_) (fun hf => ?_)
  · -- `[a]₁₆`.
    have h₁ := of_decide_eq_true ht
    have w₁' := E₁.perm.wW (show 32 + 8 ≤ 2560 by decide)
    refine WP.of_runBlock ⟨_, by crun [E₁.r15, w₁'], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact E₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg, gpr_setFlags]) rfl rfl
    · simp [gpr_setReg, Proof.AesCcm.hdrLen, h₁]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg, gpr_setFlags, hg₁ _ (by decide : Reg.r12 ≠ .rax),
        hg₁ _ (by decide : Reg.r14 ≠ .rax), hg₁ _ (by decide : Reg.rbp ≠ .rax)]
    · exact hrd₁
    · exact hwr₁
    · simp only [mem_setReg]
      exact fz.writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))
    · simp only [mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbp₁]
      rw [bytesAt_writeW64_base _ _ _ (by decide) (by decide), hz,
        show (48 : Nat) = 8 * 6 from rfl, le8_ushiftRight _ (by decide), le8_bswap64_ofNat ha,
        be_split (q := 2) (by decide) (by omega_arith), encodeLen_lo h₁, show Proof.AesCcm.hdrLen a = 2 by
          simp [Proof.AesCcm.hdrLen, h₁]]
      simp [Spec.Ccm.zeros, List.drop_append_of_le_length, Proof.AesCcm.length_be]
  · have h₁ := of_decide_eq_false hf
    obtain ⟨s₂, run₂, hcf₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        [.movImm64 .rax 0x100000000, .alu .cmp .rbp (.reg .rax)] s₁ = some s₂ ∧
        s₂.cf = some (decide (a < 2 ^ 32)) ∧ (∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧
        s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
      refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_⟩
      · simp only [cf_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbp₁, ha64]; rfl
      · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
      all_goals rfl
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have E₂ : Env K W SP s₂ := E₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂
    have hbp₂ : s₂.gpr .rbp = BitVec.ofNat 64 a := by rw [hg₂ _ (by decide), hbp₁]
    refine WP.ite (decide (a < 2 ^ 32)) (eval_b hcf₂) (fun ht => ?_) (fun hf => ?_)
    · -- `0xff ‖ 0xfe ‖ [a]₃₂`.
      have h₂ := of_decide_eq_true ht
      have w₁' := E₂.perm.wW (show 32 + 8 ≤ 2560 by decide)
      refine WP.of_runBlock ⟨_, by crun [E₂.r15, w₁'], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact E₂.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags, gpr_setFlags]) rfl rfl
      · simp [gpr_setReg, gpr_arithFlags, Proof.AesCcm.hdrLen, h₁, h₂]
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hg₂ _ (by decide : Reg.r12 ≠ .rax),
          hg₂ _ (by decide : Reg.r14 ≠ .rax), hg₂ _ (by decide : Reg.rbp ≠ .rax),
          hg₁ _ (by decide : Reg.r12 ≠ .rax), hg₁ _ (by decide : Reg.r14 ≠ .rax), hg₁ _ (by decide : Reg.rbp ≠ .rax)]
      · simp only [rd_setReg, rd_arithFlags]; rw [hrd₂, hrd₁]
      · simp only [wr_setReg, wr_arithFlags]; rw [hwr₂, hwr₁]
      · simp only [mem_setReg, mem_arithFlags, hm₂]
        exact fz.writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))
      · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbp₂, hm₂]
        rw [bytesAt_writeW64_base _ _ _ (by decide) (by decide), hz,
          show (65279#64 : BitVec 64) = BitVec.ofNat 64 0xfeff from rfl, le8_or,
          show bswap64 (BitVec.ofNat 64 a) >>> 16 = bswap64 (BitVec.ofNat 64 a) >>> (8 * 2) from rfl,
          le8_ushiftRight _ (by decide), le8_bswap64_ofNat ha, be_split (q := 4) (by decide) (by omega_arith),
          encodeLen_mid h₁ h₂, le8_feff, show Proof.AesCcm.hdrLen a = 6 by simp [Proof.AesCcm.hdrLen, h₁, h₂]]
        have hl4 := Proof.AesCcm.length_be 4 a
        rcases hb : Spec.Ccm.be 4 a with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
          rw [hb] at hl4 <;> simp at hl4
        simp [Spec.Ccm.zeros, List.replicate]

    · -- `0xff ‖ 0xff ‖ [a]₆₄`.
      have h₂ := of_decide_eq_false hf
      have w₁' := E₂.perm.wW (show 32 + 8 ≤ 2560 by decide)
      have w₃' := E₂.perm.wW (show 34 + 8 ≤ 2560 by decide)
      refine WP.of_runBlock ⟨_, by crun [E₂.r15, w₁', w₃'], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact E₂.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl
      · simp [gpr_setReg, Proof.AesCcm.hdrLen, h₁, h₂]
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg, hg₂ _ (by decide : Reg.r12 ≠ .rax),
          hg₂ _ (by decide : Reg.r14 ≠ .rax), hg₂ _ (by decide : Reg.rbp ≠ .rax),
          hg₁ _ (by decide : Reg.r12 ≠ .rax), hg₁ _ (by decide : Reg.r14 ≠ .rax), hg₁ _ (by decide : Reg.rbp ≠ .rax)]
      · simp only [rd_setReg]; rw [hrd₂, hrd₁]
      · simp only [wr_setReg]; rw [hwr₂, hwr₁]
      · simp only [mem_setReg, hm₂]
        exact (fz.writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))).writeW
          (List.mem_singleton_self _) _ (cB 34 8 (by decide) (by decide))
      · simp only [mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbp₂, hm₂]
        rw [e34, bytesAt_writeW64_at _ _ _ (by decide) (by decide), bytesAt_writeW64_base _ _ _ (by decide)
          (by decide), hz, show (65535#64 : BitVec 64) = BitVec.ofNat 64 0xffff from rfl, le8_ffff,
          le8_bswap64_ofNat ha, encodeLen_hi h₁ h₂, show Proof.AesCcm.hdrLen a = 10 by
            simp [Proof.AesCcm.hdrLen, h₁, h₂]]
        simp [Spec.Ccm.zeros, List.replicate]

end VG.Proof.AesCcm.X86_64
