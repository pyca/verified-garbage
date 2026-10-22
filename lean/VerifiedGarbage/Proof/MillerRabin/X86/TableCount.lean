module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageStore
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
import VerifiedGarbage.Proof.Framework.Offset

/-! # Initialize the public append cursor and table-loop count -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Mont.X86 VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem table_count {σ s : State} {base : Addr} {bytes w : Nat}
    (h : Stage base bytes w σ s) (hu : w ≤ 128) (hf : arrAt w 28 ≤ bytes)
    (initial : σ.mem.readW (off base 48) 32 = BitVec.ofNat 32 w) :
    WP isa (.block (arrayPointer .eax 13 .edx ++ [.store (sp tableCursor) .eax,
      .mov .eax (.imm 14), .store (sc sK) .eax])) s fun t =>
      Stage base bytes w σ t ∧ w32 t.mem base sK = 14 ∧
      t.mem.readW (off (byteAddr (σ.gpr .esp)) tableCursor) 32 = ptr32 base (arrAt w 13) ∧
      Frame [⟨off (byteAddr (σ.gpr .esp)) tableCursor, 4⟩, ⟨off base sK, 4⟩] s.mem t.mem := by
  have h52 : 52 ≤ bytes := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at hf; omega
  refine arrayPointer_ok (by decide) (by decide) (by decide)
    (by rw [readSrc_sc h.context.ws h52, h.width hf initial]) hu h.context.ws.edi_toNat
    fun s₁ K₁ m₁ p₁ => ?_
  have h₁ := h.of_registers K₁ m₁
  refine h₁.store_cursor fun s₂ h₂ m₂ K₂ _ => ?_
  refine wp_movS rfl fun s₃ U₃ _ => ?_
  have h₃ := h₂.of_registers U₃.keeps U₃.mem
  refine h₃.store_header hf (by decide) fun t ht mt _ _ => WP.block_nil ?_
  have value : s₁.gpr .eax = ptr32 base (arrAt w 13) := ptrAt_eq p₁
  have mem : t.mem = (s.mem.writeW (off (byteAddr (σ.gpr .esp)) tableCursor)
      (ptr32 base (arrAt w 13))).writeW (off base sK) (BitVec.ofNat 32 14) := by
    rw [mt, U₃.gpr, U₃.mem, m₂, h₁.stack, value, m₁]
    rfl
  have apart : Region.Disjoint ⟨off (byteAddr (σ.gpr .esp)) tableCursor, 4⟩ ⟨off base sK, 4⟩ := by
    have bound : sK + 4 ≤ bytes := by
      change 240 ≤ bytes
      exact Nat.le_trans (by decide : 240 ≤ 256) (Nat.le_trans (Nat.le_add_right _ _) hf)
    simpa only [h.stack] using
      (h.context.apart.symm.sub_left (Offset.sub_base _ (by decide : tableCursor + 4 ≤ VG.Impl.MillerRabin.X86.frameBytes))).sub_right
        (Offset.sub_base _ bound)
  refine ⟨ht, ?_, ?_, ?_⟩
  · rw [mem, w32_write_self]
    decide
  · rw [mem, Mem.readW_writeW_sep (apart.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide), Mem.readW_writeW_self32]
  · rw [mem]
    exact ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW
      (by simp) _ (Region.contains_self _ _)

end VG.Proof.MillerRabin.X86
