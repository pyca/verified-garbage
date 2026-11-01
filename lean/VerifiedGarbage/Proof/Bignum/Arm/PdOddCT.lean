module
public import VerifiedGarbage.Impl.Bignum.Arm.PdChecks
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT

import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.PdChecks
meta import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Bignum.Words
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Parity testing and flag combination access only public addresses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (wp_ldr)

theorem pdOdd_ct {base : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => LayoutFrameReady base len w s ∧ LayoutFrameReady base len w t ∧ s.sp = t.sp)
      pdOdd (fun _ _ => True) := by
  let P := fun s t => LayoutFrameReady base len w s ∧ LayoutFrameReady base len w t ∧ s.sp = t.sp
  let Q := fun s : State => s.gpr .r1 = base + BitVec.ofNat 32 (arrAt w 0)
  have pointer : RelCT isa P (.block [.ldr .r1 .r0 64]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.1.ptr.symm
  have wpPointer (s : State) (h : LayoutFrameReady base len w s) :
      WP isa (.block [.ldr .r1 .r0 64]) s Q := by
    have fits := h.layout.2.2.1
    have size : 68 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
    have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    refine wp_ldr (a := off (State.addr base) 64) (by decide)
      (by rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega))
      (h.workspace.read size) fun t moved => WP.block_nil ?_
    exact moved.gpr.trans (header.array 0 (by decide))
  have loaded := (relCT_keep_sp pointer (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wpPointer s h.1, wpPointer t h.2.1⟩)
  have byte : RelCT isa (fun s t => s.sp = t.sp ∧ Q s ∧ Q t) (.block [.ldrb .r1 .r1 0])
      (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp ?_ (fun _ _ h => h.1)
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r1]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.trans h.2.2.symm
  have read := loaded.seq (byte.seq (loadStack_ct .r11 48))
  have finish : RelCT isa (fun _ _ => True) (.block pdOddFinish) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact (read.seq (finish.mono (fun _ _ _ => trivial) (fun _ _ h => h))).mono
    (fun _ _ h => h) (fun _ _ h => h)

end VG.Proof.Bignum.Arm
