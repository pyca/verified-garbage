module
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.SelectArray
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Rsa.MontContract

import VerifiedGarbage.Proof.Bignum.Arm.SelectCT
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Workspace selection reveals only the public word count and addresses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

structure SelectArrayReady (base : BitVec 32) (len w : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  layout : Proof.Rsa.Mont.Layout s.mem (State.addr base) len
  width : Proof.Rsa.Mont.wOf s.mem (State.addr base) = w
  ptr : s.gpr .r0 = base

theorem selectArray_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8) :
    RelCT isa (fun s t => SelectArrayReady base len w s ∧ SelectArrayReady base len w t ∧ s.sp = t.sp)
      (selectArray o a b) (fun _ _ => True) := by
  let P := SelectArrayReady base len w
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 (arrAt w o) ∧
    s.gpr .r10 = base + BitVec.ofNat 32 (arrAt w a) ∧
    s.gpr .r12 = base + BitVec.ofNat 32 (arrAt w b) ∧ s.gpr .lr = BitVec.ofNat 32 (2 * w)
  have args : RelCT isa (fun s t => P s ∧ P t) (.block (selectArrayArgs o a b)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block (selectArrayArgs o a b)) s Q := by
    have fits := h.layout.2.2.1
    have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
    have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    exact WP.mono (selectArrayArgs_ok s ho ha hb h.workspace size header h.ptr)
      (fun _ j => ⟨j.1, j.2.1, j.2.2.1, j.2.2.2.1⟩)
  have sub : RelCT isa (fun s t => Q s ∧ Q t) selectRow (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨selectRow_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.1.trans h.2.1.symm, h.1.2.1.trans h.2.2.1.symm,
        h.1.2.2.1.trans h.2.2.2.1.symm, h.1.2.2.2.trans h.2.2.2.2.symm⟩ e1 e2, trivial⟩
  have body := relCT_keep_sp (((pair_posts args wp).seq sub).mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)
  exact ((body.seq (loadStack_ct .r0 0)).assoc).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
