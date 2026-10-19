module
public import VerifiedGarbage.Proof.Framework.RelCT
public import Batteries.Logic
public import VerifiedGarbage.Impl.Bignum.Arm.CrtProduct
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtProduct
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtCopyChildPointer
import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Bignum.Arm.Shift
import VerifiedGarbage.Proof.Bignum.Arm.ShiftArgs
import VerifiedGarbage.Proof.Bignum.Arm.ShiftCT
import VerifiedGarbage.Proof.Bignum.Arm.ShiftStep
import VerifiedGarbage.Proof.Bignum.Arm.WideMath
import VerifiedGarbage.Proof.Bignum.Arm.WideValue
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-! # Product-header copies use only public workspace addresses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (wp_ldr)

theorem crt_copyChildPointer_ct {base child : BitVec 32} {size src dst : Nat} {slot : Nat}
    (fit : src + 4 ≤ size) (hs : src < 4096) :
    let P := fun s : State => Workspace s base size ∧ s.gpr .r0 = base ∧
      s.mem.readW (off (State.addr base) src) 32 = child
    RelCT isa (fun s t => P s ∧ P t) (.block (copyChildPointer src dst slot)) (fun _ _ => True) := by
  dsimp only
  let P := fun s : State => Workspace s base size ∧ s.gpr .r0 = base ∧
    s.mem.readW (off (State.addr base) src) 32 = child
  let Q := fun s : State => s.gpr .r0 = base ∧ s.gpr .r1 = child
  have head : RelCT isa (fun s t => P s ∧ P t) (.block [.ldr .r1 .r0 src]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.2.1.trans h.2.2.1.symm
  have wp (s : State) (h : P s) : WP isa (.block [.ldr .r1 .r0 src]) s Q := by
    refine wp_ldr (a := off (State.addr base) src) hs
      (by rw [h.2.1]; exact addr_add (by have := h.1.nowrap; omega)) (h.1.read fit) fun t j => WP.block_nil ?_
    exact ⟨(j.other .r0 (by decide)).trans h.2.1, j.gpr.trans h.2.2⟩
  have tail : RelCT isa (fun s t => Q s ∧ Q t) (.block [.ldr .r1 .r1 slot, .str .r1 .r0 dst]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0, .r1])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.trans h.2.2.symm
  exact RelCT.block_append (M := isa) (l₁ := [.ldr .r1 .r0 src]) (l₂ := [.ldr .r1 .r1 slot, .str .r1 .r0 dst]) ((pair_posts head wp).seq tail)

theorem crt_copyHeaderPointer_ct (src dst : Nat) :
    RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block (copyHeaderPointer src dst)) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (hc := .block []) (by
    rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
    rfl)
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h

theorem crt_productCount_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block productCount) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h

end VG.Proof.Bignum.Arm
