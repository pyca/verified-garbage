module

import VerifiedGarbage.Proof.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Impl.Ffdh.Arm.Checks
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

/-! Array 7's pointer is public even when its low word is secret. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (wp_ldr)

theorem setLowBit_ct {base : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (.block VG.Impl.Ffdh.Arm.setLowBit) (fun _ _ => True) := by
  have load : RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (.block [.ldr .r4 .r0 120]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.1.ptr.trans h.2.1.ptr.symm)
  have wp (s : State) (h : ArithmeticReady base len w s) :
      WP isa (.block [.ldr .r4 .r0 120]) s fun t => t.gpr .r4 = base + BitVec.ofNat 32 (arrAt w 7) := by
    have fit : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
    have size : 124 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fit; omega
    have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    refine wp_ldr (by decide) (a := off (State.addr base) 120)
      (by rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega))
      (h.workspace.read (by omega)) fun t loaded => WP.block_nil ?_
    exact loaded.gpr.trans (header.array 7 (by decide))
  have body : RelCT isa (fun s t => s.gpr .r4 = base + BitVec.ofNat 32 (arrAt w 7) ∧
      t.gpr .r4 = base + BitVec.ofNat 32 (arrAt w 7) ∧ s.sp = t.sp)
      (.block [.ldr .r3 .r4 0, .dp .orr .r3 .r3 (.imm 1), .str .r3 .r4 0]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r4]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.1.trans h.2.1.symm)
  exact RelCT.block_append (relCT_chain load wp wp body)

end VG.Proof.Ffdh.Arm
