module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageStore
public import VerifiedGarbage.Proof.MillerRabin.X86.OperandFrame
public import VerifiedGarbage.Impl.MillerRabin.X86.Round

/-! # Shift the exponent word and advance the public window count -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Mont.X86 VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem window_advance {σ s : State} {base : Addr} {bytes w k : Nat} {v : BitVec 32}
    (h : Stage base bytes w σ s) (hf : arrAt w 28 ≤ bytes) (hk : 0 < k ∧ k < 2 ^ 32)
    (word : s.gpr .eax = v) (count : s.mem.readW (off base sK) 32 = BitVec.ofNat 32 k) :
    WP isa (.block winAdvance) s fun t =>
      Stage base bytes w σ t ∧ w32 t.mem base sV = (v <<< 4).toNat ∧
      w32 t.mem base sK = k - 1 ∧ t.zf = some (decide ((k - 1) % 8 = 0)) ∧
      Frame [⟨off base sV, 4⟩, ⟨off base sK, 4⟩] s.mem t.mem := by
  simp only [winAdvance, List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append]
  refine wp_addS rfl fun s₁ U₁ _ => wp_addS rfl fun s₂ U₂ _ =>
    wp_addS rfl fun s₃ U₃ _ => wp_addS rfl fun s₄ U₄ _ => ?_
  have h₄ := (((h.of_registers U₁.keeps U₁.mem).of_registers U₂.keeps U₂.mem).of_registers
    U₃.keeps U₃.mem).of_registers U₄.keeps U₄.mem
  have m₄ : s₄.mem = s.mem := by rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  have shifted : s₄.gpr .eax = v <<< 4 := by
    rw [U₄.gpr, U₃.gpr, U₂.gpr, U₁.gpr, word]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega
  refine h₄.store_header hf (by decide) fun s₅ h₅ m₅ _ _ => ?_
  have m₅' : s₅.mem = s.mem.writeW (off base sV) (v <<< 4) := by rw [m₅, shifted, m₄]
  have vFrame : Frame [⟨off base sV, 4⟩] s.mem s₅.mem := by
    rw [m₅']; exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  have hdrFit : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right _ _) hf
  have count₅ : s₅.mem.readW (off base sK) 32 = BitVec.ofNat 32 k :=
    (workspace_frame_word h.context.ws.nowrap (Nat.le_trans (by decide : sK + 4 ≤ 256) hdrFit)
      (Nat.le_trans (by decide : sV + 4 ≤ 256) hdrFit) (by decide) vFrame).trans count
  refine wp_movS (by rw [h₅.read_header hf (by decide), count₅]) fun s₆ U₆ _ =>
    wp_subS rfl fun s₇ U₇ _ => ?_
  have h₇ := (h₅.of_registers U₆.keeps U₆.mem).of_registers U₇.keeps U₇.mem
  refine h₇.store_header hf (by decide) fun s₈ h₈ m₈ K₈ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₉ U₉ => wp_cmpS rfl fun t Ut zt => WP.block_nil ?_
  have ht := (h₈.of_registers U₉.keeps U₉.mem).of_registers
    (rs := []) ⟨fun r _ => congrFun Ut.gpr r, Ut.rd, Ut.wr⟩ Ut.mem
  have dec : s₇.gpr .eax = BitVec.ofNat 32 (k - 1) := by
    rw [U₇.gpr, U₆.gpr]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    change (2 ^ 32 - 1 + k % 2 ^ 32) % 2 ^ 32 = (k - 1) % 2 ^ 32
    omega
  have memory : t.mem = (s.mem.writeW (off base sV) (v <<< 4)).writeW (off base sK)
      (BitVec.ofNat 32 (k - 1)) := by rw [Ut.mem, U₉.mem, m₈, dec, U₇.mem, U₆.mem, m₅']
  have nw256 : base.toNat + 256 ≤ 2 ^ 32 := Nat.le_trans (Nat.add_le_add_left hdrFit _) h.context.ws.nowrap
  refine ⟨ht, ?_, ?_, ?_, ?_⟩
  · rw [memory, w32_write_ne nw256 (by decide : sK + 4 ≤ 256) (by decide : sV + 4 ≤ 256)
      (by decide), w32_write_self]
  · rw [memory, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [zt, U₉.gpr, K₈.1 .eax (by decide), dec]
    simp only [↓reduceIte]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    rw [show (BitVec.ofNat 32 (k - 1) &&& 7) - 0 = BitVec.ofNat 32 (k - 1) &&& 7 from BitVec.sub_zero _,
      ← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat]
    change ((k - 1) % 2 ^ 32 &&& (2 ^ 3 - 1)) = 0 ↔ (k - 1) % 8 = 0
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega : k - 1 < 2 ^ 32)]
  · rw [memory]
    exact ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW
      (by simp) _ (Region.contains_self _ _)

end VG.Proof.MillerRabin.X86
