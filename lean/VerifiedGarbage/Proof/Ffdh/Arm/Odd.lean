module

public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.PdParity
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! Parity comes from the operand's least significant byte. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_ldrb wp_dp op2_imm dpVal)

theorem odd_ok (s : State) {base : BitVec 32} {len w a : Nat}
    (h : ArithmeticReady base len w s) (ha : a < 8) :
    WP isa (VG.Impl.Ffdh.Arm.odd a) s fun t => ArithmeticReady base len w t ∧
      t.gpr .r11 = BitVec.ofNat 32 (numAt s.mem (State.addr base) w a % 2) ∧
      t.mem = s.mem ∧ Rest [.r4, .r11] s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have bound := array_end_le (w := w) ha
  have size : 64 + 8 * a + 4 ≤ 8 * len := by
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits
    omega
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  have ptrAddr : State.addr (base + BitVec.ofNat 32 (arrAt w a)) = off (State.addr base) (arrAt w a) :=
    VG.Arm.addr_add (by have := h.workspace.nowrap; omega)
  unfold VG.Impl.Ffdh.Arm.odd
  refine wp_ldr (a := off (State.addr base) (64 + 8 * a)) (by omega)
    (by rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega))
    (h.workspace.read size) fun u loaded => ?_
  have ptrU : u.gpr .r4 = base + BitVec.ofNat 32 (arrAt w a) := loaded.gpr.trans (header.array a ha)
  have read : InRegions (u.rd ++ u.wr) (off (State.addr base) (arrAt w a)) 1 := by
    rw [loaded.rd, loaded.wr]
    refine ⟨⟨State.addr base, 8 * len⟩, List.mem_append_right _ h.workspace.writable, ?_⟩
    exact Offset.contains_base _ (by omega) (by have := h.workspace.nowrap; omega)
  refine wp_ldrb (a := off (State.addr base) (arrAt w a)) (by decide)
    (by rw [ptrU, BitVec.add_zero, ptrAddr]) read fun v byte => ?_
  refine wp_dp (op2_imm (by decide : encodable (1 : BitVec 32) = true)) fun t masked => WP.block_nil ?_
  have rest : Rest [.r4, .r11] s t := (loaded.rest (by simp)).trans ((byte.rest (by simp)).trans (masked.rest (by simp)))
  have mem : t.mem = s.mem := masked.mem.trans (byte.mem.trans loaded.mem)
  refine ⟨h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr), ?_, mem, rest⟩
  rw [masked.gpr, dpVal, byte.gpr, loaded.mem]
  exact numAt_parity_word s.mem (State.addr base) (by omega)

end VG.Proof.Ffdh.Arm
