module

public import VerifiedGarbage.Proof.Bignum.Arm.ExpBitCT
public import VerifiedGarbage.Proof.Bignum.Arm.SecretExpBitCT
public import VerifiedGarbage.Proof.Bignum.Arm.SecretExpRound
meta import VerifiedGarbage.Impl.Bignum.Arm.Exp
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Advancing exponent-loop controls has no secret-dependent address -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt)

theorem secretExpRound_ct {base : BitVec 32} {len w M1 M2 x1 x2 E1 E2 V1 V2 : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (hv1 : V1 < 2 ^ 32) (hv2 : V2 < 2 ^ 32) :
    RelCT isa (fun s t => ExpBitInput base len w M1 x1 E1 V1 s ∧
      ExpBitInput base len w M2 x2 E2 V2 t ∧ s.sp = t.sp) secretExpRound (fun _ _ => True) := by
  have wp (s : State) {M x E V : Nat} (hv : V < 2 ^ 32) (h : ExpBitInput base len w M x E V s) :
      WP isa secretExpBit s (ExpState base len w M x (2 * E + V / 128 % 2)) :=
    WP.mono (secretExpBit_ok s h.power hv h.byte) (fun _ h => h.1)
  have bit := ((secretExpBit_ct (base := base) (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2)
    (E1 := E1) (E2 := E2) fit).mono
    (P' := fun (s t : State) => ExpBitInput base len w M1 x1 E1 V1 s ∧
      ExpBitInput base len w M2 x2 E2 V2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.power, h.2.1.power, h.2.2⟩) (fun _ _ h => h)).wp
    (fun s t h => ⟨wp s hv1 h.1, wp t hv2 h.2.1⟩)
  have controls : RelCT isa
      (fun s t => True ∧ ExpState base len w M1 x1 (2 * E1 + V1 / 128 % 2) s ∧
        ExpState base len w M2 x2 (2 * E2 + V2 / 128 % 2) t)
      (.seq (.block expShift) (.block expDecrement)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.ready.ptr.trans h.2.2.ready.ptr.symm
  exact bit.seq controls

end VG.Proof.Bignum.Arm
