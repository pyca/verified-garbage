module
public import VerifiedGarbage.Impl.Bignum.Arm.SetSmallFn
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.SetSmallCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.SetSmallFn
meta import VerifiedGarbage.Proof.Bignum.Arm.Workspace
meta import VerifiedGarbage.Proof.Rsa.MontContract
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SetSmallCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SetSmallArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Workspace-array initialization has no dependence on the stored value -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt wOf Layout)

structure SmallFnReady (base : BitVec 32) (len w o : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  layout : Layout s.mem (State.addr base) len
  width : wOf s.mem (State.addr base) = w
  ptr : s.gpr .r0 = base
  index : s.gpr .r2 = BitVec.ofNat 32 o

theorem setSmallFnBody_ct {base : BitVec 32} {len w o : Nat} (ho : o < 8) :
    RelCT isa (fun s t => SmallFnReady base len w o s ∧ SmallFnReady base len w o t)
      setSmallFnBody (fun _ _ => True) := by
  let P := SmallFnReady base len w o
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 (arrAt w o) ∧
    s.gpr .r4 = base + BitVec.ofNat 32 (arrAt w o) ∧ s.gpr .lr = BitVec.ofNat 32 (2 * w)
  have ct : RelCT isa (fun s t => P s ∧ P t) (.block setSmallArgs) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r2]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.ptr.trans h.2.ptr.symm
    · exact h.1.index.trans h.2.index.symm
  have wp (s : State) (h : P s) : WP isa (.block setSmallArgs) s Q := by
    have fits := h.layout.2.2.1
    have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
    have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    exact WP.mono (setSmallArgs_ok s h.workspace size header ho h.ptr h.index)
      (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
  refine (pair_posts ct wp).seq ?_
  intro s t tr1 tr2 u v h e1 e2
  exact ⟨setSmall_ct s t tr1 tr2 u v trivial trivial
    ⟨h.1.1.trans h.2.1.symm, h.1.2.1.trans h.2.2.1.symm, h.1.2.2.trans h.2.2.2.symm⟩ e1 e2, trivial⟩

theorem setSmallFn_ct {base : BitVec 32} {len w o : Nat} (ho : o < 8) :
    RelCT isa (fun s t => SmallFnReady base len w o s ∧ SmallFnReady base len w o t ∧ s.sp = t.sp)
      setSmallFn (fun _ _ => True) := by
  have body := relCT_keep_sp
    ((setSmallFnBody_ct (base := base) (len := len) (w := w) ho).mono
      (P' := fun (s t : State) => SmallFnReady base len w o s ∧ SmallFnReady base len w o t ∧ s.sp = t.sp)
      (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)
  exact (body.seq (loadStack_ct .r0 0)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
