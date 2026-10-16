module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtCompareProduct
public import VerifiedGarbage.Proof.Bignum.Arm.EqualBuffersCT
public import VerifiedGarbage.Proof.Bignum.Arm.StageCT
public import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtCompareProduct
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # CRT factor validation does not reveal the factors or product -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_compareProduct_ct {base : BitVec 32} {size o a b w : Nat} :
    RelCT isa (fun s t => CrtCompareInput base size o a b w s ∧
      CrtCompareInput base size o a b w t ∧ s.sp = t.sp) compareProduct (fun _ _ => True) := by
  let P := CrtCompareInput base size o a b w
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 o ∧
    s.gpr .r10 = base + BitVec.ofNat 32 a ∧ s.gpr .r12 = base + BitVec.ofNat 32 b ∧
    s.gpr .lr = BitVec.ofNat 32 (4 * w + 2)
  have args : RelCT isa (fun s t => P s ∧ P t) compareArgs (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa compareArgs s Q :=
    WP.mono (crt_compareArgs_ok s h.workspace h.fit h.ptr h.count h.output h.first h.second)
      (fun _ j => ⟨j.1, j.2.1, j.2.2.1, j.2.2.2.1⟩)
  have compare : RelCT isa (fun s t => Q s ∧ Q t) equalBuffers (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨equalBuffers_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.1.trans h.2.1.symm, h.1.2.1.trans h.2.2.1.symm,
        h.1.2.2.1.trans h.2.2.2.1.symm, h.1.2.2.2.trans h.2.2.2.2.symm⟩ e1 e2, trivial⟩
  have body := relCT_keep_sp (((pair_posts args wp).seq compare).mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ _ => trivial)) (fun _ _ h => h.2.2)
  exact ((body.seq (loadStack_ct .r0 0)).assoc).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
