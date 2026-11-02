module

import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
public import VerifiedGarbage.Proof.Bignum.Arm.MontBodyCT
public import VerifiedGarbage.Impl.Bignum.Arm.MontFn
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.MontBodyCT
meta import VerifiedGarbage.Impl.Bignum.Arm.MontFn
meta import VerifiedGarbage.Proof.Rsa.MontContract
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The callable body reveals only the workspace, indices, and RSA word count -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand)

structure FnBodyReady (base : BitVec 32) (len w o a b : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  layout : Layout s.mem (State.addr base) len
  width : wOf s.mem (State.addr base) = w
  ptr : s.gpr .r0 = base
  outIndex : s.gpr .r2 = BitVec.ofNat 32 o
  aIndex : s.gpr .r3 = BitVec.ofNat 32 a
  bIndex : s.gpr .r12 = BitVec.ofNat 32 b
  inverse : ((word s.mem (State.addr base) (arrAt w 0)).toNat *
    (wordAt s.mem (State.addr base) Proof.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0
  operand : numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0

theorem bases_ready {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (s : State) (h : FnBodyReady base len w o a b s) :
    WP isa (.block MontFn.bases) s
      (InitReady base (8 * len) (arrAt w o) (arrAt w 3) (arrAt w a) (arrAt w b) (arrAt w 0) (arrAt w 2) (2 * w)) := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  obtain ⟨ctx, _⟩ := layout_context h.workspace hw fits ho ha hb
  have bound : 128 ≤ 8 * len := by
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits
    omega
  refine WP.mono (bases_ok s h.workspace bound header ho.1 ha.1 hb.1 h.ptr h.outIndex h.aIndex h.bIndex) ?_
  rintro t ⟨regs, mem, keep⟩
  refine ⟨ctx.congr keep.wr, ⟨_, regs, ?_⟩, ?_⟩
  · rw [mem]; exact native_inverse s.mem (State.addr base) (by omega) h.inverse
  · rw [mem, ← numAt_native, ← numAt_native]; exact h.operand

theorem montFnBody_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => FnBodyReady base len w o a b s ∧ FnBodyReady base len w o a b t)
      MontFn.body (fun _ _ => True) := by
  have ct : RelCT isa (fun s t => FnBodyReady base len w o a b s ∧ FnBodyReady base len w o a b t)
      (.block MontFn.bases) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r2, .r3, .r12]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.1.ptr.trans h.2.ptr.symm
    · exact h.1.outIndex.trans h.2.outIndex.symm
    · exact h.1.aIndex.trans h.2.aIndex.symm
    · exact h.1.bIndex.trans h.2.bIndex.symm
  exact (pair_posts ct (bases_ready ho ha hb)).seq (montBody_ct fit)

end VG.Proof.Bignum.Arm
