import VerifiedGarbage.Proof.AesCcm.Arm.Absorb

/-!
# AES-CCM on ARMv7: the encoding of the length of the associated data

Untrusted: everything here is checked by Lean. `header` zeroes `B` and
writes the encoding of the length `0 < a < 2³²` (A.2.2) at its start:
`[a]₁₆` or `0xff ‖ 0xfe ‖ [a]₃₂`, from the byte-reversed `a` shifted
(`header_ok`); its length is in `r6`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)
open VG.Impl.AesGcm.Arm (imm addI zero16)
open VG.Proof.AesGcm.Arm (bytesAt_frame runBlock_app_of toNat32 eval_eq' Keeps z_subFlags gpr_subFlags
  c_subFlags adc_c gpr_store mem_store)
open VG.Proof.AesCcm (hdrLen bytesAt_writeW32_at bytesAt_writeW32_base be_split length_be)

theorem encodeLen_lo {a : Nat} (h : a < 2 ^ 16 - 2 ^ 8) : Spec.Ccm.encodeLen a = Spec.Ccm.be 2 a := by
  simp [Spec.Ccm.encodeLen, h]

theorem encodeLen_mid {a : Nat} (h₁ : ¬ a < 2 ^ 16 - 2 ^ 8) (h₂ : a < 2 ^ 32) :
    Spec.Ccm.encodeLen a = [0xff, 0xfe] ++ Spec.Ccm.be 4 a := by
  simp [Spec.Ccm.encodeLen, h₁, h₂]

theorem le4_feff : le4 (BitVec.ofNat 32 0xfeff) = [0xff, 0xfe, 0, 0] := by decide

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : Lay k w sp)
include L

/-- `B` zeroed, then the encoding of the length `a` of the associated data
(`r5`) at its start, and its length in `r6`. -/
theorem header_ok {s : State} (he : Env k w sp R q1 s) {a : Nat} (ha0 : 0 < a) (ha : a < 2 ^ 32)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 a) :
    WP isa header s fun s' => Env k w sp R q1 s' ∧ s'.gpr .r6 = BitVec.ofNat 32 (hdrLen a) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      (s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp) ∧ Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 32) 16 =
        Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a) := by
  obtain ⟨s₁, run₁, hm₁, g₁, rd₁, wr₁, sp₁, -⟩ := zero16_ok L he (d := bO) (by decide) (by decide)
  simp only [bO] at hm₁
  have h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 a := by rw [g₁ _ (by decide), h5]
  obtain ⟨s₂, run₂, hz₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [.mov .r0 (imm 0xff00), .cmp .r5 (.reg .r0),
      .mov .r12 (imm 0), .adc .r12 .r12 (imm 0), .cmp .r12 (imm 0)] s₁ = some s₂ ∧
      s₂.z = !decide (65280 ≤ a) ∧ (∀ r, r ≠ .r0 → r ≠ .r12 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp only [z_subFlags, c_subFlags, gpr_setReg, gpr_subFlags, z_setReg, c_setReg, ite_true, ite_false,
        reduceCtorEq, h5₁, toNat32 ha, imm, show (BitVec.ofNat 32 65280).toNat = 65280 from rfl]
      cases decide (65280 ≤ a) <;> rfl
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have hz : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 32) 16 = Spec.Ccm.zeros 16 := by
    rw [k₂.mem, hm₁]; exact store4_zero_bytes' _ _
  have fz : Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s₂.mem := by
    rw [k₂.mem, hm₁]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have he₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rw [g₂ _ (by decide) (by decide), g₁ _ (by decide)])
    (k₂.sp.trans sp₁) (k₂.rd.trans rd₁) (k₂.wr.trans wr₁)
  have h5₂ : s₂.gpr .r5 = BitVec.ofNat 32 a := by rw [g₂ _ (by decide) (by decide), h5₁]
  have h11 := he₂.r11
  have e32 := L.wA (d := 32) (by decide)
  have e36 := L.wA (d := 36) (by decide)
  have w₀ := he₂.perm.wW (show 32 + 4 ≤ 2560 by decide)
  have w₁ := he₂.perm.wW (show 36 + 4 ≤ 2560 by decide)
  have cB : ∀ d n, 32 ≤ d → d + n ≤ 48 →
      (⟨State.addr w + BitVec.ofNat 64 32, 16⟩ : Region).Contains (State.addr w + BitVec.ofNat 64 d) n :=
    fun d n h₁ h₂ => Offset.contains _ h₁ (by omega_arith) (by decide)
  have kg : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → s₂.gpr r = s.gpr r := fun r a b c d e => by
    rw [g₂ r a e, g₁ r a]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [show zero16 bO ++ [.mov .r0 (imm 0xff00), .cmp .r5 (.reg .r0), .mov .r12 (imm 0),
      .adc .r12 .r12 (imm 0), .cmp .r12 (imm 0)] = zero16 bO ++ ([.mov .r0 (imm 0xff00), .cmp .r5 (.reg .r0),
      .mov .r12 (imm 0), .adc .r12 .r12 (imm 0), .cmp .r12 (imm 0)] : List Instr) from rfl]
    exact runBlock_app_of run₁ run₂, ?_⟩)
  have hrev := le4_rev_ofNat ha
  refine WP.ite (!decide (65280 ≤ a)) (eval_eq' hz₂) (fun ht => ?_) (fun hf => ?_)
  · -- `[a]₁₆`.
    have h₁ : a < 2 ^ 16 - 2 ^ 8 := by simp at ht; omega_arith
    refine WP.of_runBlock ⟨_, by simp only [bO]; arun [h11, e32, w₀], ?_⟩
    refine ⟨he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, ?_, ?_,
      ⟨k₂.rd.trans rd₁, k₂.wr.trans wr₁, k₂.sp.trans sp₁⟩, ?_, ?_⟩
    · simp [gpr_setReg, hdrLen, h₁]
    · intro r a b c d e; simp only [gpr_store, gpr_setReg, a, d, ite_false]; exact kg r a b c d e
    · simp only [mem_store, mem_setReg]
      exact fz.writeW (List.mem_singleton_self _) _ (cB 32 4 (by decide) (by decide))
    · simp only [mem_store, gpr_store, mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, h5₂]
      rw [bytesAt_writeW32_base _ _ _ (by decide) (by decide), hz, le4_shr16, hrev,
        be_split (q := 2) (by decide) (by omega_arith), encodeLen_lo h₁, show hdrLen a = 2 by simp [hdrLen, h₁]]
      simp [Spec.Ccm.zeros, List.drop_append_of_le_length, length_be]
  · -- `0xff ‖ 0xfe ‖ [a]₃₂`.
    have h₁ : ¬ a < 2 ^ 16 - 2 ^ 8 := by simp at hf; omega_arith
    refine WP.of_runBlock ⟨_, by simp only [bO]; arun [h11, e32, e36, w₀, w₁], ?_⟩
    refine ⟨he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, ?_, ?_,
      ⟨k₂.rd.trans rd₁, k₂.wr.trans wr₁, k₂.sp.trans sp₁⟩, ?_, ?_⟩
    · simp [gpr_setReg, hdrLen, h₁, ha]
    · intro r a b c d e; simp only [gpr_store, gpr_setReg, a, b, c, d, ite_false]; exact kg r a b c d e
    · simp only [mem_store, mem_setReg]
      exact (fz.writeW (List.mem_singleton_self _) _ (cB 32 4 (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (cB 36 4 (by decide) (by decide))
    · simp only [mem_store, gpr_store, mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, h5₂]
      rw [show State.addr w + BitVec.ofNat 64 36 = State.addr w + BitVec.ofNat 64 32 + BitVec.ofNat 64 4 by
          rw [Offset.add_add],
        bytesAt_writeW32_at _ _ _ (by decide) (by decide), bytesAt_writeW32_base _ _ _ (by decide) (by decide), hz,
        Proof.AesCcm.le4_or, le4_shl16, le4_shr16, hrev, encodeLen_mid h₁ ha,
        show hdrLen a = 6 by simp [hdrLen, h₁, ha]]
      have hl4 := length_be 4 a
      have hfe : le4 (BitVec.ofNat 32 0xfeff) = [0xff, 0xfe, 0, 0] := le4_feff
      rcases hb : Spec.Ccm.be 4 a with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
        rw [hb] at hl4 <;> simp at hl4
      simp [Spec.Ccm.zeros, List.replicate, hfe]

end

end VG.Proof.AesCcm.Arm
