module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCallSquareU
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallArithmetic
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Bignum.Arm.MontCallSquareUArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.MontCallCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareUmaalCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The replacement diagonal retains the same public square dispatch. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt Operand)

theorem montCallSquareUArithmetic_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => CallBodyReady base len w o a b s ∧
      CallBodyReady base len w o a b t ∧ s.sp = t.sp)
      MontCallSquareU.arithmetic (fun _ _ => True) := by
  let P := fun s t : State => CallBodyReady base len w o a b s ∧
    CallBodyReady base len w o a b t ∧ s.sp = t.sp
  have cmp : RelCT isa P (.block [.cmp .r3 (.reg .r12)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have ready := cmp.wpDep (fun s t h => ⟨callCompare_ready s h.1, callCompare_ready t h.2.1⟩)
  unfold MontCallSquareU.arithmetic MontCallWith.dispatch
  refine ready.seq (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    obtain ⟨_, s0, t0, _, hs, ht⟩ := h
    simp only [eval, hs.2.1, ht.2.1]
  · intro s t tr1 tr2 u v h e1 e2
    obtain ⟨⟨_, s0, t0, hp, hs, ht⟩, branch⟩ := h
    have bits : BitVec.ofNat 32 a = BitVec.ofNat 32 b := by
      have sub : BitVec.ofNat 32 a - BitVec.ofNat 32 b = 0 := by
        simpa only [eval, hs.2.1, Option.some.injEq, beq_iff_eq] using branch
      calc
        BitVec.ofNat 32 a = (BitVec.ofNat 32 a - BitVec.ofNat 32 b) + BitVec.ofNat 32 b := (BitVec.sub_add_cancel _ _).symm
        _ = BitVec.ofNat 32 b := by rw [sub]; exact BitVec.zero_add _
    have aw : a < 2 ^ 32 := by have := ha.1; omega
    have bw : b < 2 ^ 32 := by have := hb.1; omega
    have indices : a = b := by
      have natEq := congrArg BitVec.toNat bits
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt aw, Nat.mod_eq_of_lt bw] using natEq
    subst b
    exact squareBodyU_ct ho ha _ _ _ _ _ _
      ⟨hs.2.2.trans (hp.2.2.trans ht.2.2.symm),
        ⟨hs.1.input, hs.1.stackRead, hs.1.stackSep, hs.1.saved⟩,
        ⟨ht.1.input, ht.1.stackRead, ht.1.stackSep, ht.1.saved⟩⟩ e1 e2
  · intro s t tr1 tr2 u v h e1 e2
    obtain ⟨⟨_, s0, t0, _, hs, ht⟩, _⟩ := h
    exact montFnBody_ct ho ha hb fit _ _ _ _ _ _ ⟨hs.1.input, ht.1.input⟩ e1 e2

end VG.Proof.Bignum.Arm
