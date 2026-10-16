module

public import VerifiedGarbage.Proof.Bignum.Arm.PdEntryReady
public import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
public import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Bignum.Arm.PdFn
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The checked public RSA entry uses only stack-relative addresses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem pdEntry_ct : RelCT isa (fun s t => s.sp = t.sp) (.block PdFn.entry) (fun s t => s.sp = t.sp) := by
  let P := fun (s t : State) => s.sp = t.sp ∧ s.gpr .r12 = t.gpr .r12
  have addr : RelCT isa (fun s t => s.sp = t.sp) (.block [.addSp .r12 0]) P := by
    apply single_ct (fun _ _ _ => rfl)
    intro s t u v h e1 e2
    simp only [exec, Nat.reduceLT, ite_true, BitVec.add_zero, Option.some.injEq] at e1 e2
    subst u; subst v
    exact ⟨h, by simpa only [State.setReg, ite_true] using h⟩
  have store : RelCT isa P (.block [.str .r0 .r12 4]) P := by
    apply single_ct (fun s t h => by simp only [addrs, h.2])
    intro s t u v h e1 e2
    simp only [exec, Nat.reduceLT, ite_true, State.store32] at e1 e2
    split at e1
    · split at e2
      · simp only [Option.some.injEq] at e1 e2
        subst u; subst v; exact h
      · cases e2
    · cases e1
  have load : RelCT isa P (.block [.ldrSp .r0 72]) P := by
    apply single_ct (fun s t h => by simp only [addrs, h.1])
    intro s t u v h e1 e2
    simp only [exec, Nat.reduceLT, ite_true, State.load32] at e1 e2
    split at e1
    · split at e2
      · simp only [Option.map_some, Option.some.injEq] at e1 e2
        subst u; subst v
        exact ⟨h.1, by simpa only [State.setReg, reduceCtorEq, ite_false] using h.2⟩
      · cases e2
    · cases e1
  have tail : RelCT isa P (.block [.str .r0 .r12 0, .str .r1 .r12 12])
      (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp (sp := fun _ _ h => h.1)
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r12]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2
  unfold PdFn.entry PublicFn.entry
  simp only [List.cons_append, List.nil_append]
  exact RelCT.block_append (addr.seq (RelCT.block_append (store.seq (RelCT.block_append (load.seq tail)))))

end VG.Proof.Bignum.Arm
