module

public import VerifiedGarbage.Proof.Bignum.Arm.ExpByteHeadCT
public import VerifiedGarbage.Proof.Bignum.Arm.SecretExpBitsCT
public import VerifiedGarbage.Proof.Bignum.Arm.ExpByteCT
meta import VerifiedGarbage.Impl.Bignum.Arm.Exp
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Processing a private exponent byte reveals only its address -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt)

theorem secretExpByte_ct {base ep : BitVec 32} {len w M1 M2 x1 x2 E1 E2 : Nat} {b1 b2 : Byte}
    (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => ExpByteInput base ep len w M1 x1 E1 b1 s ∧
      ExpByteInput base ep len w M2 x2 E2 b2 t ∧ s.sp = t.sp)
      (.seq expByteHead (.seq secretExpBits (.block expByteNext))) (fun _ _ => True) := by
  let P := fun (s t : State) => ExpByteInput base ep len w M1 x1 E1 b1 s ∧
    ExpByteInput base ep len w M2 x2 E2 b2 t ∧ s.sp = t.sp
  have wpHead (s : State) {M x E : Nat} {b : Byte} (h : ExpByteInput base ep len w M x E b s) :
      WP isa expByteHead s (ExpBitState base len w M x E b.toNat 0) := by
    have head := expByteHead_ok s h.power h.pointer h.read
    rw [h.byte] at head
    exact WP.mono head (fun _ h => h.1)
  have head := (relCT_keep_sp (expByteHead_ct.mono (P' := P)
    (fun _ _ h => ⟨⟨h.1.power.ready, h.1.pointer⟩, ⟨h.2.1.power.ready, h.2.1.pointer⟩⟩)
    (fun _ _ h => h)) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wpHead s h.1, wpHead t h.2.1⟩)
  have wpBits (s : State) {M x E : Nat} {b : Byte} (h : ExpBitState base len w M x E b.toNat 0 s) :
      WP isa secretExpBits s (ExpState base len w M x (256 * E + b.toNat)) :=
    WP.mono (secretExpBits_ok s h b.isLt) (fun _ h => h.1)
  have bits := ((secretExpBits_ct (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2) (E1 := E1) (E2 := E2) fit b1.isLt b2.isLt).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ ExpBitState base len w M1 x1 E1 b1.toNat 0 s ∧
      ExpBitState base len w M2 x2 E2 b2.toNat 0 t)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)).wp
    (fun s t h => ⟨wpBits s h.2.1, wpBits t h.2.2⟩)
  have next : RelCT isa (fun s t => True ∧ ExpState base len w M1 x1 (256 * E1 + b1.toNat) s ∧
      ExpState base len w M2 x2 (256 * E2 + b2.toNat) t) (.block expByteNext) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.ready.ptr.trans h.2.2.ready.ptr.symm
  exact head.seq (bits.seq next)

end VG.Proof.Bignum.Arm
