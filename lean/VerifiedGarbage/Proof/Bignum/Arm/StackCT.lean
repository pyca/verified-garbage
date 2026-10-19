module

import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Impl.Bignum.Arm.MontFn
public import Batteries.Logic
public import VerifiedGarbage.Proof.Framework.RelCT

/-! # Stack loads have public addresses even when the saved registers are secret -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem loadStack_ct (r : Reg) (d : Nat) :
    RelCT isa (fun s t => s.sp = t.sp) (.block [.ldrSp r d]) (fun s t => s.sp = t.sp) := by
  intro s t tr1 tr2 u v h e1 e2
  rw [Exec.block_iff] at e1 e2
  simp only [execBlock] at e1 e2
  split at e1
  · cases e1
  · rename_i a ha
    split at e2
    · cases e2
    · rename_i b hb
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.append_nil] at e1 e2
      obtain ⟨rfl, rfl⟩ := e1
      obtain ⟨rfl, rfl⟩ := e2
      exact ⟨by simp only [addrs, h], (exec_sp ha).trans (h.trans (exec_sp hb).symm)⟩

theorem stackLoads_ct (slots : List (Reg × Nat)) :
    RelCT isa (fun s t => s.sp = t.sp) (.block (slots.map fun p => Instr.ldrSp p.1 p.2))
      (fun s t => s.sp = t.sp) := by
  induction slots with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons p rest ih => exact RelCT.block_append ((loadStack_ct p.1 p.2).seq ih)

theorem montRestore_ct : RelCT isa (fun s t => s.sp = t.sp) (.block MontFn.restore)
    (fun s t => s.sp = t.sp) :=
  stackLoads_ct [(.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16), (.r9, 20), (.r10, 24), (.r11, 28), (.lr, 32)]

theorem relCT_keep_sp {P : State → State → Prop} {code : Prog isa}
    (ct : RelCT isa P code (fun _ _ => True)) (sp : ∀ s t, P s t → s.sp = t.sp) :
    RelCT isa P code (fun s t => s.sp = t.sp) := by
  intro s t tr1 tr2 u v h e1 e2
  exact ⟨(ct s t tr1 tr2 u v h e1 e2).1,
    (Exec.rdwr e1).2.2.trans ((sp s t h).trans (Exec.rdwr e2).2.2.symm)⟩

end VG.Proof.Bignum.Arm
