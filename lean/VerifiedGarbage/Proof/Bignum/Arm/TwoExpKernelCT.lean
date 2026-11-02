module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpKernel
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnRestore
import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Bignum.Arm.MontOp
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! The linear doubling candidate has a trace independent of the secret
power, exponent prefix, and modulus. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem twice_ct {base : BitVec 32} {len w M1 M2 E1 E2 : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (hn : 0 < 2 * w) :
    RelCT isa (fun s t => Power base len w M1 E1 s ∧ Power base len w M2 E2 t ∧ s.sp = t.sp)
      twice (fun _ _ => True) := by
  let P := fun (s t : State) => Power base len w M1 E1 s ∧ Power base len w M2 E2 t ∧ s.sp = t.sp
  have args : RelCT isa P (.block (montOpArgs 1 5 6)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have ready := (relCT_keep_sp args (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨twiceArgs_ready s h.1, twiceArgs_ready t h.2.1⟩)
  have body := (doubleFnRestore_ct (base := base) (len := len) (w := w)
    (o := 1) (a := 5) (b := 6)
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) fit hn).mono
      (P' := fun (s t : State) => s.sp = t.sp ∧ DoubleFnReady base len w 1 5 6 s ∧ DoubleFnReady base len w 1 5 6 t)
      (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)
  exact (ready.seq body).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem timing_of_square {base : BitVec 32} {len w : Nat}
    {P : State → Prop} {regions : List Region} (K : Kernel base len w P regions)
    (twice_code : K.twice = twice)
    (fit : arrAt w 3 + 32 ≤ 8 * len) (hn : 0 < 2 * w)
    (square_ct : RelCT isa (fun s t => Ready base len w P s ∧ Ready base len w P t ∧ s.sp = t.sp)
      K.square (fun _ _ => True)) : Timing K where
  square := square_ct
  twice := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨⟨M1, E1, p1, _⟩, ⟨M2, E2, p2, _⟩, sp⟩ := h
    rw [twice_code] at e1 e2
    exact twice_ct fit hn s t tr1 tr2 u v ⟨p1, p2, sp⟩ e1 e2

end VG.Proof.Bignum.Arm.TwoExp
