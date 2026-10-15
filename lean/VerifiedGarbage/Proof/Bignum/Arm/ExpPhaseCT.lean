module

public import VerifiedGarbage.Proof.Bignum.Arm.ExpPhaseInput
public import VerifiedGarbage.Proof.Bignum.Arm.ExpInitCT
public import VerifiedGarbage.Proof.Bignum.Arm.ExpBytesCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Complete RSA exponentiation reveals no input-dependent trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt)

theorem expPhase_ct {base ep : BitVec 32} {len w M1 M2 x1 x2 : Nat} {eb : List Byte}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (positive : 0 < eb.length) :
    RelCT isa (fun s t => ExpPhaseInput base ep len w M1 x1 eb s ∧
      ExpPhaseInput base ep len w M2 x2 eb t ∧ s.sp = t.sp) expPhase (fun _ _ => True) := by
  let P := fun (s t : State) => ExpPhaseInput base ep len w M1 x1 eb s ∧
    ExpPhaseInput base ep len w M2 x2 eb t ∧ s.sp = t.sp
  have wpInit (s : State) {M x : Nat} (h : ExpPhaseInput base ep len w M x eb s) :
      WP isa expInit s (ExpByteState base ep len w M x eb 0) :=
    WP.mono (expPhase_init_ready s h) (fun _ h => h.1)
  have init := (relCT_keep_sp ((expInit_ct fit).mono (P' := P)
    (fun _ _ h => ⟨⟨h.1.ready, by rw [h.1.modulus]; exact h.1.r2bound⟩,
      ⟨h.2.1.ready, by rw [h.2.1.modulus]; exact h.2.1.r2bound⟩, h.2.2⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wpInit s h.1, wpInit t h.2.1⟩)
  have wpBytes (s : State) {M x : Nat} (h : ExpByteState base ep len w M x eb 0 s) :
      WP isa expBytes s (ExpState base len w M x (Spec.Rsa.os2ip eb)) :=
    WP.mono (expPhase_bytes_ready s h positive) (fun _ h => h.1)
  have bytes := (relCT_keep_sp ((expBytes_ct (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2) fit positive).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ ExpByteState base ep len w M1 x1 eb 0 s ∧
      ExpByteState base ep len w M2 x2 eb 0 t)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)) (fun _ _ h => h.1)).wp
    (fun s t h => ⟨wpBytes s h.2.1, wpBytes t h.2.2⟩)
  have finish := (exp_finish_ct (base := base) (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2)
    (E := Spec.Rsa.os2ip eb) fit).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ ExpState base len w M1 x1 (Spec.Rsa.os2ip eb) s ∧
      ExpState base len w M2 x2 (Spec.Rsa.os2ip eb) t)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)
  exact init.seq (bytes.seq finish)

end VG.Proof.Bignum.Arm
