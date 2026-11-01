module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Bignum.Arm.ClearOperandBuffer
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.ZeroCT
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.Bignum.Arm.ClearOperandBufferArgs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PlainSimp
/-! # Clearing an extended result array leaks only its public layout -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/ClearOperandBufferCT.lean`, which only this module imported.
section

/-! # Clearing an extended operand buffer reveals only its public pointer and width -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

structure ClearOperandBufferInput (base dst : BitVec 32) (size slot w : Nat) (s : State) : Prop where
  workspace : Workspace s base size
  ptr : s.gpr .r0 = base
  count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w
  link : s.mem.readW (off (State.addr base) slot) 32 = dst

theorem clearOperandBuffer_ct {base dst : BitVec 32} {size slot w : Nat}
    (fit : 52 ≤ size) (slotFit : slot + 4 ≤ size) (hs : slot < 4096) :
    RelCT isa (fun s t => ClearOperandBufferInput base dst size slot w s ∧ ClearOperandBufferInput base dst size slot w t ∧ s.sp = t.sp)
      (clearOperandBuffer slot) (fun _ _ => True) := by
  let P := ClearOperandBufferInput base dst size slot w
  let Q := fun s : State => s.gpr .r0 = dst ∧ s.gpr .lr = BitVec.ofNat 32 (2 * w + 2)
  have args : RelCT isa (fun s t => P s ∧ P t) (.block (clearOperandBufferArgs slot)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block (clearOperandBufferArgs slot)) s Q :=
    WP.mono (clearOperandBufferArgs_ok s h.workspace fit slotFit hs h.ptr h.count h.link) (fun _ j => ⟨j.1, j.2.1⟩)
  have clear : RelCT isa (fun s t => Q s ∧ Q t) zero (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨zero_ct s t tr1 tr2 u v trivial trivial ⟨h.1.1.trans h.2.1.symm, h.1.2.trans h.2.2.symm⟩ e1 e2, trivial⟩
  have body := relCT_keep_sp (((pair_posts args wp).seq clear).mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ _ => trivial)) (fun _ _ h => h.2.2)
  exact ((body.seq (loadStack_ct .r0 0)).assoc).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem clearArrayWide_ct {base : BitVec 32} {len w o : Nat} (ho : o < 8) (fit : 128 ≤ 8 * len) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (clearOperandBuffer (64 + 8 * o)) (fun _ _ => True) := by
  have input (s : State) (h : ArithmeticReady base len w s) :
      ClearOperandBufferInput base (base + BitVec.ofNat 32 (arrAt w o)) (8 * len) (64 + 8 * o) w s := by
    have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    exact ⟨h.workspace, h.ptr, header.count, header.array o ho⟩
  exact (clearOperandBuffer_ct (base := base) (dst := base + BitVec.ofNat 32 (arrAt w o))
    (size := 8 * len) (slot := 64 + 8 * o) (w := w) (by omega) (by omega) (by omega)).mono
    (fun s t h => ⟨input s h.1, input t h.2.1, h.2.2⟩) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
