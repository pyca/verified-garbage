module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageStore
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.Mont.X86.Rt.Step
import VerifiedGarbage.Proof.Framework.Offset

/-! # Advance the append pointer and count down a power-table iteration -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86 VG.Impl.Mont.X86 VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem table_end {σ s : State} {base : Addr} {bytes w j k : Nat}
    (h : Stage base bytes w σ s) (hf : arrAt w 28 ≤ bytes)
    (hk : 0 < k ∧ k < 2 ^ 32)
    (dest : s.gpr .ebx = ptr32 base (arrAt w j) + BitVec.ofNat 32 (8 * w))
    (count : s.mem.readW (off base sK) 32 = BitVec.ofNat 32 k) :
    WP isa (.block tabEnd) s fun t =>
      Stage base bytes w σ t ∧ w32 t.mem base sK = k - 1 ∧
      t.zf = some (decide (k = 1)) ∧
      t.mem.readW (off (byteAddr (σ.gpr .esp)) tableCursor) 32 = ptr32 base (arrAt w (j + 1)) ∧
      Frame [⟨off (byteAddr (σ.gpr .esp)) tableCursor, 4⟩, ⟨off base sK, 4⟩] s.mem t.mem := by
  have fit : sK + 4 ≤ bytes := Nat.le_trans (by decide : 240 ≤ 256) (Nat.le_trans (Nat.le_add_right _ _) hf)
  have next : ptr32 base (arrAt w j) + BitVec.ofNat 32 (8 * w) + 16 =
      ptr32 base (arrAt w (j + 1)) := by
    unfold ptr32
    change (BitVec.ofNat 32 (base.toNat + arrAt w j) + BitVec.ofNat 32 (8 * w)) + BitVec.ofNat 32 16 = _
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 1
    simp only [arrAt, Nat.add_mul, Nat.one_mul]
    omega
  unfold tabEnd
  refine wp_addS rfl fun s₁ U₁ _ => ?_
  have h₁ := h.of_registers U₁.keeps U₁.mem
  refine h₁.store_cursor fun s₂ h₂ m₂ K₂ _ => ?_
  have cursorValue : s₁.gpr .ebx = ptr32 base (arrAt w (j + 1)) := by rw [U₁.gpr, dest]; exact next
  have m₂' : s₂.mem = s.mem.writeW (off (byteAddr (σ.gpr .esp)) tableCursor)
      (ptr32 base (arrAt w (j + 1))) := by rw [m₂, h₁.stack, cursorValue, U₁.mem]
  have Fc : Frame [⟨off (byteAddr (s.gpr .esp)) tableCursor, 4⟩] s.mem s₂.mem := by
    rw [m₂', h.stack]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  have count₂ : s₂.mem.readW (off base sK) 32 = BitVec.ofNat 32 k :=
    (h.context.stack_frame_readW (by decide) Fc fit).trans count
  refine wp_movS (by rw [readSrc_sc h₂.context.ws fit, count₂]) fun s₃ U₃ _ => ?_
  have h₃ := h₂.of_registers U₃.keeps U₃.mem
  refine wp_subZ rfl fun s₄ U₄ z₄ => ?_
  have h₄ := h₃.of_registers U₄.keeps U₄.mem
  refine h₄.store_header hf (by decide) fun t ht mt _ zt => WP.block_nil ?_
  have dec : s₃.gpr .eax - 1 = BitVec.ofNat 32 (k - 1) := by
    rw [U₃.gpr]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    change (2 ^ 32 - 1 + k % 2 ^ 32) % 2 ^ 32 = (k - 1) % 2 ^ 32
    omega
  have mt' : t.mem = (s.mem.writeW (off (byteAddr (σ.gpr .esp)) tableCursor)
      (ptr32 base (arrAt w (j + 1)))).writeW (off base sK) (BitVec.ofNat 32 (k - 1)) := by
    rw [mt, U₄.gpr, dec, U₄.mem, U₃.mem, m₂']
  have apart : Region.Disjoint ⟨off (byteAddr (σ.gpr .esp)) tableCursor, 4⟩ ⟨off base sK, 4⟩ := by
    simpa only [h.stack] using
      (h.context.apart.symm.sub_left (Offset.sub_base _ (by decide : tableCursor + 4 ≤ VG.Impl.MillerRabin.X86.frameBytes))).sub_right
        (Offset.sub_base _ fit)
  refine ⟨ht, ?_, ?_, ?_, ?_⟩
  · rw [mt', w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [zt, z₄, dec]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
    change (k - 1) % 2 ^ 32 = 0 ↔ k = 1
    omega
  · rw [mt', Mem.readW_writeW_sep (apart.sep (Region.contains_self _ _) (Region.contains_self _ _))
      (by decide), Mem.readW_writeW_self32]
  · rw [mt']
    exact ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW
      (by simp) _ (Region.contains_self _ _)

end VG.Proof.MillerRabin.X86
