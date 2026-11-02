module

public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBitCT
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBit
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBitCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBit
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Advancing exponent-loop controls has no secret-dependent address -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

variable {ok : Prop}
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem expRound_ct {base : BitVec 32} {len w M1 M2 x1 x2 E V : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (hv : V < 2 ^ 32) :
    RelCT isa (fun s t => ExpBitInput ok base len w M1 x1 E V s ∧
      ExpBitInput ok base len w M2 x2 E V t ∧ s.sp = t.sp) expBitRound (fun _ _ => True) := by
  have wp (s : State) {M x : Nat} (h : ExpBitInput ok base len w M x E V s) :
      WP isa expBit s (ExpState ok base len w M x (2 * E + V / 128 % 2)) :=
    WP.mono (expBit_ok s h.power hv h.byte) (fun _ h => h.1)
  have bit := (expBit_ct (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2) fit hv).wp (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  have controls : RelCT isa
      (fun s t => True ∧ ExpState ok base len w M1 x1 (2 * E + V / 128 % 2) s ∧
        ExpState ok base len w M2 x2 (2 * E + V / 128 % 2) t)
      (.seq (.block expShift) (.block expDecrement)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.ready.ptr.trans h.2.2.ready.ptr.symm
  exact bit.seq controls

end VG.Proof.Bignum.Arm.ConditionalExp
