module
public import VerifiedGarbage.Impl.Bignum.Arm.ArrayCompare
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT

import VerifiedGarbage.Proof.Bignum.Arm.SubRowCT
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Impl.Bignum.Arm.ArrayCompare
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompareArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # RSA input range checking reveals only the public word count and addresses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem arrayCompare_ct {base : BitVec 32} {len w a b : Nat} (ha : a < 8) (hb : b < 8) :
    RelCT isa (fun s t => LayoutFrameReady base len w s ∧ LayoutFrameReady base len w t ∧ s.sp = t.sp)
      (arrayCompare a b) (fun _ _ => True) := by
  let P := LayoutFrameReady base len w
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 (arrAt w 3) ∧
    s.gpr .r10 = base + BitVec.ofNat 32 (arrAt w a) ∧
    s.gpr .r12 = base + BitVec.ofNat 32 (arrAt w b) ∧ s.gpr .lr = BitVec.ofNat 32 (2 * w)
  have args : RelCT isa (fun s t => P s ∧ P t) (.block (arrayCompareArgs a b)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (hc := .block []) _ (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs _)]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block (arrayCompareArgs a b)) s Q := by
    have fits := h.layout.2.2.1
    have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
    have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    exact WP.mono (arrayCompareArgs_ok s h.workspace size ha hb header h.ptr)
      (fun _ j => ⟨j.1, j.2.1, j.2.2.1, j.2.2.2.1⟩)
  have sub : RelCT isa (fun s t => Q s ∧ Q t) subRow (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨subRow_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.1.trans h.2.1.symm, h.1.2.1.trans h.2.2.1.symm,
        h.1.2.2.1.trans h.2.2.2.1.symm, h.1.2.2.2.trans h.2.2.2.2.symm⟩ e1 e2, trivial⟩
  have body := relCT_keep_sp (((pair_posts args wp).seq sub).mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)
  exact ((body.seq (loadStack_ct .r0 0)).assoc).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
