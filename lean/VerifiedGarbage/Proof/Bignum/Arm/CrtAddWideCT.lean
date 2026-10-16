module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtAddWide
public import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
public import VerifiedGarbage.Proof.Bignum.Arm.StageCT
public import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtAddWide
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The final CRT addition keeps both addends secret -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_addWide_ct {base : BitVec 32} {size o b w : Nat} :
    RelCT isa (fun s t => CrtAddWideInput base size o b w s ∧
      CrtAddWideInput base size o b w t ∧ s.sp = t.sp) addWide (fun _ _ => True) := by
  let P := CrtAddWideInput base size o b w
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 o ∧
    s.gpr .r12 = base + BitVec.ofNat 32 b ∧ s.gpr .lr = BitVec.ofNat 32 (4 * w)
  have args : RelCT isa (fun s t => P s ∧ P t) addWideArgs (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa addWideArgs s Q :=
    WP.mono (crt_addWideArgs_ok s h.workspace h.fit h.ptr h.count h.output h.input)
      (fun _ j => ⟨j.1, j.2.1, j.2.2.1⟩)
  have row : RelCT isa (fun s t => Q s ∧ Q t) rowFull (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨rowFull_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.1.trans h.2.1.symm, h.1.2.1.trans h.2.2.1.symm,
        h.1.2.2.trans h.2.2.2.symm⟩ e1 e2, trivial⟩
  have body := relCT_keep_sp (((pair_posts args wp).seq row).mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ _ => trivial)) (fun _ _ h => h.2.2)
  exact ((body.seq (loadStack_ct .r0 0)).assoc).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
