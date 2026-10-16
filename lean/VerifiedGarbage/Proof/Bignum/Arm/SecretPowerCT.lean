module

public import VerifiedGarbage.Proof.Bignum.Arm.SecretPower
public import VerifiedGarbage.Proof.Bignum.Arm.ExpControlsCT
public import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandCT
public import VerifiedGarbage.Proof.Bignum.Arm.SecretExpPhaseCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Ciphertext import and secret modular exponentiation have public-only traces -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt)

theorem secretPower_ct {base xp ep : BitVec 32} {len w k eLen M1 M2 : Nat} {xb1 xb2 eb1 eb2 : List Byte}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (positive : 0 < eb1.length) (length : eb1.length = eb2.length) :
    RelCT isa (fun s t => SecretPowerInput base xp ep len w k eLen M1 xb1 eb1 s ∧
      SecretPowerInput base xp ep len w k eLen M2 xb2 eb2 t ∧ s.sp = t.sp) secretPower (fun _ _ => True) := by
  let P := fun (s t : State) => SecretPowerInput base xp ep len w k eLen M1 xb1 eb1 s ∧
    SecretPowerInput base xp ep len w k eLen M2 xb2 eb2 t ∧ s.sp = t.sp
  let Q := fun (M : Nat) (xb eb : List Byte) (s : State) =>
    SecretPowerInput base xp ep len w k eLen M xb eb s ∧
    s.mem.readW (off (State.addr base) 128) 32 = ep ∧
    s.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 eLen
  have controls : RelCT isa P (.block expControls) (fun _ _ => True) :=
    expControls_ct.mono (fun _ _ h => h.1.ready.ptr.trans h.2.1.ready.ptr.symm) (fun _ _ _ => trivial)
  have controlsWP (s : State) {M : Nat} {xb eb : List Byte}
      (h : SecretPowerInput base xp ep len w k eLen M xb eb s) : WP isa (.block expControls) s (Q M xb eb) :=
    (secretPower_controls_ready s h).mono (fun _ j => ⟨j.1, j.2.1, j.2.2.1⟩)
  have first := (relCT_keep_sp controls (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨controlsWP s h.1, controlsWP t h.2.1⟩)
  have load : RelCT isa (fun (s t : State) => s.sp = t.sp ∧ Q M1 xb1 eb1 s ∧ Q M2 xb2 eb2 t)
      (importOperand 1) (fun _ _ => True) :=
    (importOperand_ct (base := base) (src := xp) (len := len) (w := w) (k := k) (by decide : 1 < 8)).mono
      (fun _ _ h => ⟨h.2.1.1.ready, h.2.2.1.ready, h.2.1.1.source, h.2.2.1.source,
        h.2.1.1.count, h.2.2.1.count, h.1⟩) (fun _ _ _ => trivial)
  have importWP (s : State) {M : Nat} {xb eb : List Byte} (h : Q M xb eb s) :
      WP isa (importOperand 1) s (ExpPhaseInput base ep len w M (Spec.Rsa.os2ip xb) eb) :=
    (secretPower_import_ready s h.1 h.2.1 h.2.2).mono (fun _ j => j.1)
  have second := (relCT_keep_sp load (fun _ _ h => h.1)).wp
    (fun s t h => ⟨importWP s h.2.1, importWP t h.2.2⟩)
  exact first.seq (second.seq ((secretExpPhase_ct fit positive length).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial)))

end VG.Proof.Bignum.Arm
