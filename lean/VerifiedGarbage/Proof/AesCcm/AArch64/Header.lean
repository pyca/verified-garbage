import VerifiedGarbage.Proof.AesCcm.AArch64.Absorb

/-!
# AES-CCM on AArch64: the first block of the associated data

Untrusted: everything here is checked by Lean. `header` zeroes `B` and
writes the encoding of the length `a > 0` (A.2.2) at its start: `[a]₁₆`,
`0xff ‖ 0xfe ‖ [a]₃₂` or `0xff ‖ 0xff ‖ [a]₆₄`, by byte-reversing and
shifting `a` (`header_ok`); its length is in `x25`. `aadHead y` copies the
first `min (a, 16 − h)` bytes after it and chains the block (`aadHead_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)
open VG.Impl.AesGcm.AArch64 (mov ptr imm copyLoop minK)
open VG.Proof.AesGcm.AArch64 (LoopPre copyLoop_ok minK_ok loopRegs minRegs Others add_ofNat_assoc eval_zero
  ofNat_sub lsr_ofNat toNat_ofNat_of_lt ofNat_add_ofNat)
open VG.Proof.AesCcm (hdrLen headLen length_bytesAt bytesAt_writeW64_at bytesAt_writeW64_base
  bytesAt_writeBytes_at bytesAt_prefix enc_lo enc_mid enc_hi)

/-- The sign of a difference of two numbers below `2⁶³`: whether the first
is the smaller. -/
theorem sign63 {x k : Nat} (hx : x < 2 ^ 63) (hk : k < 2 ^ 63) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 k) >>> 63 = BitVec.ofNat 64 (if x < k then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, toNat_ofNat_of_lt (by omega), toNat_ofNat_of_lt (by omega),
    Nat.shiftRight_eq_div_pow]
  split
  · rw [toNat_ofNat_of_lt (by decide)]; omega
  · rw [toNat_ofNat_of_lt (by decide)]; omega

theorem movz_lit (k : Nat) (hk : k < 2 ^ 16) :
    BitVec.setWidth 64 (BitVec.ofNat 16 k) <<< (16 * 0) = BitVec.ofNat 64 k :=
  Proof.AesGcm.AArch64.movz_ofNat hk

/-- `B` zeroed, then the encoding of the length `a` of the associated data
(`x24`) at its start, and its length in `x25`. -/
theorem header_ok {c : Cx} {s : State} (E : Env c s) {a : Nat} (ha0 : 0 < a) (ha : a < 2 ^ 64)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 a) :
    WP isa header s fun s' => Env c s' ∧ s'.gpr .x25 = BitVec.ofNat 64 (hdrLen a) ∧
      Others [.x9, .x10, .x25] s s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a) := by
  have w₁ := E.perm.wW (show 32 + 8 ≤ 2560 by decide)
  have w₂ := E.perm.wW (show 40 + 8 ≤ 2560 by decide)
  have w₃ := E.perm.wW (show 34 + 8 ≤ 2560 by decide)
  have e40 : c.W + BitVec.ofNat 64 40 = c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have e34 : c.W + BitVec.ofNat 64 34 = c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 2 := by rw [add_ofNat_assoc]
  have cB : ∀ d k, 32 ≤ d → d + k ≤ 48 →
      (⟨c.W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains c.W h₁ (by omega) (by decide)
  -- `B` zeroed; `a >> 32`.
  obtain ⟨s₁, run₁, hm₁, x9₁, hg₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa (zero16 bO ++ [.lsr .x .x9 .x24 32]) s =
      some s₁ ∧
      s₁.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 40)
        (0 : BitVec 64) ∧ s₁.gpr .x9 = BitVec.ofNat 64 (a / 2 ^ 32) ∧
      Others [.x9] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by carun [E.x19, w₁, w₂], ?_⟩
    refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, h24, lsr_ofNat a 32 ha]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  have hz : bytesAt s₁.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.zeros 16 := by
    rw [hm₁, e40, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
  have fz : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₁.mem := by
    rw [hm₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64) (cB 32 8 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64) (cB 40 8 (by decide) (by decide))
  have E₁ : Env c s₁ := E.others hg₁ (by decide) sp₁ rd₁ wr₁
  have h24₁ : s₁.gpr .x24 = BitVec.ofNat 64 a := by rw [hg₁ _ (by decide), h24]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (a / 2 ^ 32 = 0)) (eval_zero x9₁ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h₂ : a < 2 ^ 32 := by have := of_decide_eq_true ht; omega
    obtain ⟨s₂, run₂, x9₂, hg₂, hm₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
        [.lsr .x .x9 .x24 8, .subImm .x .x9 .x9 255, .lsr .x .x9 .x9 63] s₁ = some s₂ ∧
        s₂.gpr .x9 = BitVec.ofNat 64 (if a / 256 < 255 then 1 else 0) ∧ Others [.x9] s₁ s₂ ∧
        s₂.mem = s₁.mem ∧ s₂.sp = s₁.sp ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
      refine ⟨_, by carun [], ?_⟩
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
      · simp only [gpr_write, BitVec.setWidth_eq, ite_true, h24₁, lsr_ofNat a 8 ha]
        exact sign63 (by omega) (by decide)
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [gpr_write, hr]
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have E₂ : Env c s₂ := E₁.others hg₂ (by decide) sp₂ rd₂ wr₂
    have h24₂ : s₂.gpr .x24 = BitVec.ofNat 64 a := by rw [hg₂ _ (by decide), h24₁]
    have w₁' := E₂.perm.wW (show 32 + 8 ≤ 2560 by decide)
    refine WP.ite (decide ((if a / 256 < 255 then 1 else 0) = 0)) (eval_zero x9₂ (by split <;> decide))
      (fun ht => ?_) (fun hf => ?_)
    · -- `0xff ‖ 0xfe ‖ [a]₃₂`.
      have h₁ : ¬ a < 2 ^ 16 - 2 ^ 8 := by
        have := of_decide_eq_true ht; split at this <;> simp_all <;> omega
      have kf : (BitVec.setWidth 64 (0xfeff : BitVec 16) <<< 0 : BitVec 64) = BitVec.ofNat 64 0xfeff := by decide
      obtain ⟨s₃, run₃, hm₃, x25₃, hg₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa
          [.rev .x9 .x24, .lsr .x .x9 .x9 16, .movz .x .x10 0xfeff 0, .logic .orr .x .x9 .x9 .x10,
            .str .x .x9 .x19 bO, imm .x25 6] s₂ = some s₃ ∧
          s₃.mem = s₂.mem.writeW (c.W + BitVec.ofNat 64 32)
            (byteRev64 (BitVec.ofNat 64 a) >>> 16 ||| BitVec.ofNat 64 0xfeff) ∧
          s₃.gpr .x25 = BitVec.ofNat 64 6 ∧ Others [.x9, .x10, .x25] s₂ s₃ ∧
          s₃.sp = s₂.sp ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
        refine ⟨_, by carun [E₂.x19, w₁', kf], ?_⟩
        refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
        · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, h24₂]; rfl
        · simp [gpr_write]
        · intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp [gpr_write, hr]
      refine WP.of_runBlock ⟨s₃, run₃, E₂.others hg₃ (by decide) sp₃ rd₃ wr₃,
        by rw [x25₃, Proof.AesCcm.hdrLen_mid h₁ h₂], fun r hr => ?_, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁],
        ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [hg₃ r (by simp [hr.1, hr.2.1, hr.2.2]), hg₂ r (by simp [hr.1]), hg₁ r (by simp [hr.1])]
      · rw [hm₃, hm₂]
        exact fz.writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))
      · rw [hm₃, bytesAt_writeW64_base _ _ _ (by decide) (by decide), hm₂, hz]
        exact enc_mid h₁ h₂ _ rfl
    · -- `[a]₁₆`.
      have h₁ : a < 2 ^ 16 - 2 ^ 8 := by
        have := of_decide_eq_false hf; split at this <;> simp_all <;> omega
      obtain ⟨s₃, run₃, hm₃, x25₃, hg₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa
          [.rev .x9 .x24, .lsr .x .x9 .x9 48, .str .x .x9 .x19 bO, imm .x25 2] s₂ = some s₃ ∧
          s₃.mem = s₂.mem.writeW (c.W + BitVec.ofNat 64 32) (byteRev64 (BitVec.ofNat 64 a) >>> 48) ∧
          s₃.gpr .x25 = BitVec.ofNat 64 2 ∧ Others [.x9, .x10, .x25] s₂ s₃ ∧
          s₃.sp = s₂.sp ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
        refine ⟨_, by carun [E₂.x19, w₁'], ?_⟩
        refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
        · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, h24₂]; rfl
        · simp [gpr_write]
        · intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp [gpr_write, hr]
      refine WP.of_runBlock ⟨s₃, run₃, E₂.others hg₃ (by decide) sp₃ rd₃ wr₃,
        by rw [x25₃, Proof.AesCcm.hdrLen_lo h₁], fun r hr => ?_, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁],
        ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [hg₃ r (by simp [hr.1, hr.2.1, hr.2.2]), hg₂ r (by simp [hr.1]), hg₁ r (by simp [hr.1])]
      · rw [hm₃, hm₂]
        exact fz.writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))
      · rw [hm₃, bytesAt_writeW64_base _ _ _ (by decide) (by decide), hm₂, hz]
        exact enc_lo h₁ _ rfl
  · -- `0xff ‖ 0xff ‖ [a]₆₄`.
    have h₂ : ¬ a < 2 ^ 32 := by have := of_decide_eq_false hf; omega
    have h₁ : ¬ a < 2 ^ 16 - 2 ^ 8 := by omega
    have w₁' := E₁.perm.wW (show 32 + 8 ≤ 2560 by decide)
    have w₃' := E₁.perm.wW (show 34 + 8 ≤ 2560 by decide)
    have kf : (BitVec.setWidth 64 (0xffff : BitVec 16) <<< 0 : BitVec 64) = BitVec.ofNat 64 0xffff := by decide
    obtain ⟨s₃, run₃, hm₃, x25₃, hg₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa
        [.movz .x .x9 0xffff 0, .str .x .x9 .x19 bO, .rev .x9 .x24, ptr .x10 .x19 (bO + 2),
          .str .x .x9 .x10 0, imm .x25 10] s₁ = some s₃ ∧
        s₃.mem = (s₁.mem.writeW (c.W + BitVec.ofNat 64 32) (BitVec.ofNat 64 0xffff)).writeW
          (c.W + BitVec.ofNat 64 34) (byteRev64 (BitVec.ofNat 64 a)) ∧
        s₃.gpr .x25 = BitVec.ofNat 64 10 ∧ Others [.x9, .x10, .x25] s₁ s₃ ∧
        s₃.sp = s₁.sp ∧ s₃.rd = s₁.rd ∧ s₃.wr = s₁.wr := by
      refine ⟨_, by carun [E₁.x19, w₁', w₃', kf], ?_⟩
      refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
      · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, h24₁]; rfl
      · simp [gpr_write]
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [gpr_write, hr]
    refine WP.of_runBlock ⟨s₃, run₃, E₁.others hg₃ (by decide) sp₃ rd₃ wr₃,
      by rw [x25₃, Proof.AesCcm.hdrLen_hi h₁ h₂], fun r hr => ?_, by rw [rd₃, rd₁], by rw [wr₃, wr₁], ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [hg₃ r (by simp [hr.1, hr.2.1, hr.2.2]), hg₁ r (by simp [hr.1])]
    · rw [hm₃]
      exact (fz.writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (cB 34 8 (by decide) (by decide))
    · rw [hm₃, e34, bytesAt_writeW64_at _ _ _ (by decide) (by decide),
        bytesAt_writeW64_base _ _ _ (by decide) (by decide), hz]
      exact enc_hi h₁ h₂ ha

end VG.Proof.AesCcm.AArch64
