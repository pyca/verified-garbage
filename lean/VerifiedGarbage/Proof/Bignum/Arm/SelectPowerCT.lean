module

public import VerifiedGarbage.Proof.Bignum.Arm.SelectPower
public import VerifiedGarbage.Proof.Bignum.Arm.SelectCT
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
meta import VerifiedGarbage.Impl.Bignum.Arm.SelectPower
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Private-power selection reveals only the public word count and addresses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt)

theorem selectPower_ct {base : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      selectPower (fun _ _ => True) := by
  let P := ArithmeticReady base len w
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 (arrAt w 6) ∧
    s.gpr .r10 = base + BitVec.ofNat 32 (arrAt w 6) ∧
    s.gpr .r12 = base + BitVec.ofNat 32 (arrAt w 1) ∧ s.gpr .lr = BitVec.ofNat 32 (2 * w)
  have args : RelCT isa (fun s t => P s ∧ P t) (.block selectPowerArgs) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block selectPowerArgs) s Q := by
    have fits := h.layout.2.2.1
    have size : 128 ≤ 8 * len := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fits; omega
    have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    exact WP.mono (selectPowerArgs_ok s h.workspace size header h.ptr)
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
