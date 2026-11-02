module

import VerifiedGarbage.Proof.Ffdh.Arm.Odd
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.Ffdh.Arm.Checks
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

/-! Reading an operand's parity uses a public array pointer and fixed byte offset. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (wp_ldr)

theorem odd_ct {base : BitVec 32} {len w a : Nat} (ha : a < 8) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.odd a) (fun _ _ => True) := by
  have load : RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (.block [.ldr .r4 .r0 (64 + 8 * a)]) (fun _ _ => True) := by
    have trace : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0)
        (.block [.ldr .r4 .r0 (64 + 8 * a)]) (fun _ _ => True) := by
      have casesA : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by omega
      rcases casesA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)
    exact trace.mono (fun _ _ h => h.1.ptr.trans h.2.1.ptr.symm) (fun _ _ h => h)
  have wp (s : State) (h : ArithmeticReady base len w s) :
      WP isa (.block [.ldr .r4 .r0 (64 + 8 * a)]) s
        (fun t => t.gpr .r4 = base + BitVec.ofNat 32 (arrAt w a)) := by
    have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
    have size : 64 + 8 * a + 4 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
    have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    refine wp_ldr (by omega) (a := off (State.addr base) (64 + 8 * a))
      (by rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega))
      (h.workspace.read size) fun t loaded => WP.block_nil ?_
    exact loaded.gpr.trans (header.array a ha)
  have tail : RelCT isa (fun s t => s.gpr .r4 = base + BitVec.ofNat 32 (arrAt w a) ∧
      t.gpr .r4 = base + BitVec.ofNat 32 (arrAt w a) ∧ s.sp = t.sp)
      (.block [.ldrb .r11 .r4 0, .dp .and .r11 .r11 (.imm 1)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r4]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.trans h.2.1.symm
  exact RelCT.block_append (relCT_chain load wp wp tail)

end VG.Proof.Ffdh.Arm
