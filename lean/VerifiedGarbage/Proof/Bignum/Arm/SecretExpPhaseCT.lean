module

public import VerifiedGarbage.Proof.Bignum.Arm.ExpPhaseInput
public import VerifiedGarbage.Proof.Bignum.Arm.ExpInitCT
public import VerifiedGarbage.Proof.Bignum.Arm.SecretExpBytesCT
public import VerifiedGarbage.Proof.Bignum.Arm.SecretExpPhase
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Complete private RSA exponentiation hides the exponent, input, and modulus values -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt)

theorem secretExpPhase_ct {base ep : BitVec 32} {len w M1 M2 x1 x2 : Nat} {eb1 eb2 : List Byte}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (positive : 0 < eb1.length) (length : eb1.length = eb2.length) :
    RelCT isa (fun s t => ExpPhaseInput base ep len w M1 x1 eb1 s ∧
      ExpPhaseInput base ep len w M2 x2 eb2 t ∧ s.sp = t.sp) secretExpPhase (fun _ _ => True) := by
  let P := fun (s t : State) => ExpPhaseInput base ep len w M1 x1 eb1 s ∧
    ExpPhaseInput base ep len w M2 x2 eb2 t ∧ s.sp = t.sp
  have wpInit (s : State) {M x : Nat} {eb : List Byte} (h : ExpPhaseInput base ep len w M x eb s) :
      WP isa expInit s (ExpByteState base ep len w M x eb 0) :=
    WP.mono (expPhase_init_ready s h) (fun _ h => h.1)
  have init := (relCT_keep_sp ((expInit_ct fit).mono (P' := P)
    (fun _ _ h => ⟨⟨h.1.ready, by rw [h.1.modulus]; exact h.1.r2bound⟩,
      ⟨h.2.1.ready, by rw [h.2.1.modulus]; exact h.2.1.r2bound⟩, h.2.2⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wpInit s h.1, wpInit t h.2.1⟩)
  have wpBytes (s : State) {M x : Nat} {eb : List Byte} (positive : 0 < eb.length)
      (h : ExpByteState base ep len w M x eb 0 s) :
      WP isa secretExpBytes s (ExpState base len w M x (Spec.Rsa.os2ip eb)) :=
    WP.mono (secretExpBytes_ok s h.power positive h.countFit h.sourceFit h.read h.separate h.bytes
      (by simpa only [BitVec.add_zero] using h.pointer) h.count) (fun _ h => h.1)
  have bytes := (relCT_keep_sp ((secretExpBytes_ct (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2) fit positive length).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ ExpByteState base ep len w M1 x1 eb1 0 s ∧
      ExpByteState base ep len w M2 x2 eb2 0 t)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)) (fun _ _ h => h.1)).wp
    (fun s t h => ⟨wpBytes s positive h.2.1, wpBytes t (by omega) h.2.2⟩)
  have finish : RelCT isa (fun (s t : State) => s.sp = t.sp ∧
      ExpState base len w M1 x1 (Spec.Rsa.os2ip eb1) s ∧
      ExpState base len w M2 x2 (Spec.Rsa.os2ip eb2) t) (montOp 6 6 7) (fun _ _ => True) := by
    apply (montOp_ct (base := base) (o := 6) (a := 6) (b := 7)
      (by simp [Spec.Rsa.Mont.Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])
      (by simp [Spec.Rsa.Mont.Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])
      (by simp [Spec.Rsa.Mont.Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) fit).mono
      (fun _ _ h => ⟨⟨h.2.1.ready, by rw [h.2.1.one]; exact h.2.1.ready.modulus⟩,
        ⟨h.2.2.ready, by rw [h.2.2.one]; exact h.2.2.ready.modulus⟩, h.1⟩) (fun _ _ h => h)
  exact init.seq (bytes.seq finish)

end VG.Proof.Bignum.Arm
