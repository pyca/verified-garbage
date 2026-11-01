module

public import VerifiedGarbage.Impl.Bignum.Arm.DoubleFnBody
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleCT
public import VerifiedGarbage.Proof.Bignum.Arm.MontFnBodyCT
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.DoubleFnBody
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleCT
meta import VerifiedGarbage.Proof.Bignum.Arm.MontFnBodyCT
meta import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Modular doubling through the header has the same public inputs as Montgomery multiplication -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand)

def DoubleFnReady (base : BitVec 32) (len w o a b : Nat) (s : State) : Prop :=
  FnBodyReady base len w o a b s ∧ w32 s.mem (State.addr base) (arrAt w a) = 2

theorem doubleBases_ready {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (s : State) (ready : DoubleFnReady base len w o a b s) :
    WP isa (.block MontFn.bases) s
      (DoubleInitReady base (8 * len) (arrAt w o) (arrAt w 3) (arrAt w a) (arrAt w b) (arrAt w 0) (arrAt w 2) (2 * w)) := by
  have h := ready.1
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
  refine ⟨⟨ctx.congr keep.wr, ⟨_, regs, ?_⟩, ?_⟩, ?_⟩
  · rw [mem]; exact native_inverse s.mem (State.addr base) (by omega) h.inverse
  · rw [mem, ← numAt_native, ← numAt_native]; exact h.operand
  · rw [mem]; exact ready.2

theorem doubleFnBody_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) (fit : arrAt w 3 + 32 ≤ 8 * len) (hn : 0 < 2 * w) :
    RelCT isa (fun s t => DoubleFnReady base len w o a b s ∧ DoubleFnReady base len w o a b t)
      doubleFnBody (fun _ _ => True) := by
  have ct : RelCT isa (fun s t => DoubleFnReady base len w o a b s ∧ DoubleFnReady base len w o a b t)
      (.block MontFn.bases) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r2, .r3, .r12]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.1.1.ptr.trans h.2.1.ptr.symm
    · exact h.1.1.outIndex.trans h.2.1.outIndex.symm
    · exact h.1.1.aIndex.trans h.2.1.aIndex.symm
    · exact h.1.1.bIndex.trans h.2.1.bIndex.symm
  exact (pair_posts ct (doubleBases_ready ho ha hb)).seq (doubleBody_ct fit hn)

end VG.Proof.Bignum.Arm
