module

public import VerifiedGarbage.Proof.Bignum.Arm.R2Kernel
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! Public setup keeps the imported modulus public when selecting an R-squared kernel. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)

def PublicR2Timing (code : Prog isa) : Prop := ∀ {base : BitVec 32} {len w M : Nat},
  128 * w < 2 ^ 32 → RelCT isa (fun s t =>
    (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = M) ∧
    (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w 0 = M) ∧ s.sp = t.sp)
    code (fun _ _ => True)

theorem precomputePublic_ct (kernel : R2Kernel) (timing : PublicR2Timing kernel.code)
    {base src : BitVec 32} {len w k : Nat} {nb : List Byte} (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t =>
      (PrecomputeInput base src len w k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) ∧
      (PrecomputeInput base src len w k t ∧ Spec.Rsa.bytesAt t.mem (State.addr src) k = nb) ∧ s.sp = t.sp)
      (precomputeWith kernel.code) (fun _ _ => True) := by
  let N := Spec.Rsa.os2ip nb
  let P := fun s : State => PrecomputeInput base src len w k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb
  let Q := fun s : State => PrecomputeModulus base len w s ∧ numAt s.mem (State.addr base) w 0 = N
  let R := fun s : State => ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = N
  have imported := (relCT_keep_sp ((importModulus_ct (base := base) (src := src) (len := len) (w := w) (k := k)).mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)).wp
    (fun s t h =>
      ⟨WP.mono (importModulus_ready_value s h.1.1) (fun u j => (⟨j.1, by rw [j.2, h.1.2]⟩ : Q u)),
       WP.mono (importModulus_ready_value t h.2.1.1) (fun u j => (⟨j.1, by rw [j.2, h.2.1.2]⟩ : Q u))⟩)
  have inverse := (relCT_keep_sp ((precomputeInverse_ct (base := base) (len := len) (w := w)).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ Q s ∧ Q t)
    (fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩) (fun _ _ h => h)) (fun _ _ h => h.1)).wp
    (fun s t h =>
      ⟨WP.mono (precomputeInverse_ready_value s h.2.1.1) (fun u j => (⟨j.1, j.2.trans h.2.1.2⟩ : R u)),
       WP.mono (precomputeInverse_ready_value t h.2.2.1) (fun u j => (⟨j.1, j.2.trans h.2.2.2⟩ : R u))⟩)
  have tail := inverse.seq ((timing (M := N) countFits).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))
  exact imported.seq tail

end VG.Proof.Bignum.Arm
