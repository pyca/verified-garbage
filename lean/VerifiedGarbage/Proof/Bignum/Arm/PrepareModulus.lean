module

public import VerifiedGarbage.Impl.Bignum.Arm.PrivPreFn
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopState
import VerifiedGarbage.Proof.Bignum.Arm.R2Public
import VerifiedGarbage.Proof.Bignum.Arm.R2PublicCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.RelCT

/-! # `R² mod n` for the private precomputation's public modulus

`prepareModulus`, in the main workspace holding the valid modulus `n`: its
inverse, then `R² mod n` as the public precomputation computes it
(`r2Public`), whose one branch tests `n`, which both runs share. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.PrivPreFn
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem prepareModulus_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : PrecomputeModulus base len w s) (countFits : 128 * w < 2 ^ 32) :
    WP isa prepareModulus s fun t =>
      DoubleLoopReady base len w 0 t ∧ numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [prepareModulus, WP.seq_iff]
  refine WP.mono (precomputeInverse_ok s h.workspace h.layout h.width h.ptr h.odd h.large h.stackRead h.stackSep
    h.saved) ?_
  rintro v ⟨ready, modV, frameV, restV⟩
  refine WP.mono (r2Public_ok v ready countFits) ?_
  rintro t ⟨done, value, modT, frameT, restT⟩
  rw [modV] at value
  exact ⟨done, modT.trans modV, value, frameV.trans frameT, restV.trans restT⟩

theorem prepareModulus_ct {base : BitVec 32} {len w M : Nat} (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t =>
      (PrecomputeModulus base len w s ∧ numAt s.mem (State.addr base) w 0 = M) ∧
      (PrecomputeModulus base len w t ∧ numAt t.mem (State.addr base) w 0 = M) ∧ s.sp = t.sp)
      prepareModulus (fun _ _ => True) := by
  have inverse := (relCT_keep_sp ((precomputeInverse_ct (base := base) (len := len) (w := w)).mono
    (P' := fun (s t : State) =>
      (PrecomputeModulus base len w s ∧ numAt s.mem (State.addr base) w 0 = M) ∧
      (PrecomputeModulus base len w t ∧ numAt t.mem (State.addr base) w 0 = M) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1, h.2.1.1⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)).wp
    (F₁ := fun (u : State) => ArithmeticReady base len w u ∧ numAt u.mem (State.addr base) w 0 = M)
    (F₂ := fun (u : State) => ArithmeticReady base len w u ∧ numAt u.mem (State.addr base) w 0 = M)
    (fun s t h => ⟨WP.mono (precomputeInverse_ready_value s h.1.1) fun _ j => ⟨j.1, j.2.trans h.1.2⟩,
      WP.mono (precomputeInverse_ready_value t h.2.1.1) fun _ j => ⟨j.1, j.2.trans h.2.1.2⟩⟩)
  rw [prepareModulus]
  exact (inverse.mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)).seq (r2Public_ct countFits)

end VG.Proof.Bignum.Arm
