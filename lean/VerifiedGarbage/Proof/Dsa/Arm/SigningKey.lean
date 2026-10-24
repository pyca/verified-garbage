module

public import VerifiedGarbage.Proof.Dsa.Arm.PublicKey
import VerifiedGarbage.Proof.Framework.Omega

/-! # Signing reuses the private/public consistency equation

The generator's subgroup equation and g^x = y imply y's subgroup equation,
even for composite domain integers. The signer therefore needs one public
subgroup exponentiation; verification still checks both independently.
-/

@[expose] public section
namespace VG.Proof.Dsa.Arm
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32 mask32_and)

def signingPublicChecks (P Q G Y : Nat) : Prop :=
  ((1 < G ∧ G < P) ∧ (1 < Y ∧ Y < P)) ∧ (P - 1) % Q = 0 ∧ G ^ Q % P = 1

instance (P Q G Y : Nat) : Decidable (signingPublicChecks P Q G Y) := by
  unfold signingPublicChecks
  infer_instance

theorem public_subgroup_of_consistency {P Q G Y X : Nat} (hp : 1 < P)
    (hg : G ^ Q % P = 1) (he : G ^ X % P = Y) : Y ^ Q % P = 1 := by
  rw [← he, ← Nat.pow_mod, ← Nat.pow_mul, Nat.mul_comm X Q, Nat.pow_mul, Nat.pow_mod, hg]
  simp [Nat.mod_eq_of_lt hp]

theorem signingPublicChecks_consistent {P Q G Y X : Nat} {A : Prop} (hp : 1 < P) :
    (signingPublicChecks P Q G Y ∧ A ∧ G ^ X % P = Y) ↔
      (publicChecks P Q G Y ∧ A ∧ G ^ X % P = Y) := by
  constructor
  · rintro ⟨⟨hr, hd, hg⟩, ha, he⟩
    exact ⟨⟨hr, hd, hg, public_subgroup_of_consistency hp hg he⟩, ha, he⟩
  · rintro ⟨⟨hr, hd, hg, _⟩, ha, he⟩
    exact ⟨⟨hr, hd, hg⟩, ha, he⟩

theorem signingSubgroup_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (hP : 1 < P) (hPo : P % 2 = 1) :
    WP isa (Validate.signingSubgroup pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (G ^ Q % P = 1) ∧
      KeepsLocals base s t scalars.1 scalars.2 ∧ Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := S.lens
  have big := S.big
  have Plt := operand_lt_of Ip
  have ho : 4960 ≤ Impl.Dsa.Layout.t ∧ Impl.Dsa.Layout.t + pLen ≤ 15712 := by
    simp only [Impl.Dsa.Layout.t]; omega
  have ht : Impl.Dsa.Layout.t + pLen < size := by omega
  unfold Validate.signingSubgroup
  refine WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.t) S.ws (by omega) S.wp q4 qp qw Ip.toReady
    Ig.toReady Iq.toReady Ip.value hP hPo ho.1 (by omega) (by decide)) fun v₁ ⟨B₁, St₁⟩ => ?_)
  rw [Ig.value, Iq.value] at B₁
  have S₁ := S.stage St₁
  refine WP.mono (isOne_ok S₁.ws (by omega) S.wp (localReady S₁.ws ho.1 ht (by decide)))
    fun v₂ ⟨F₂, St₂⟩ => ⟨?_, ?_, ?_⟩
  · rw [local_operand S₁.ws (by omega), localVal_of_bytes B₁ (Nat.lt_trans (Nat.mod_lt _ (by omega)) Plt)] at F₂
    rw [F₂, St₁.maskW (by decide)]
  · exact (St₁.keepsScalars (by omega) (by simp only [Impl.Dsa.Layout.t]; omega)).trans
      (St₂.keepsScalars (by decide) (by decide))
  · exact (St₁.run (.inr ho)).trans (St₂.run (.inl ⟨rfl, rfl⟩))

theorem signingKey_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (Validate.signingKey pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (signingPublicChecks P Q G Y) ∧
      localVal base t Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 ∧ Run base s t := by
  have big := S.big
  have fits := S.fits
  unfold Validate.signingKey
  refine WP.seq (WP.mono (domain_ok S Ip Iq Ig Iy hP hPo hQ hQo) fun u ⟨Fu, Lu, Ru⟩ =>
    WP.mono (signingSubgroup_ok (S.run Ru) (Ip.run Ru (by omega) fits) (Iq.run Ru (by omega) fits)
      (Ig.run Ru (by omega) fits) hP hPo) fun t ⟨Ft, Kt, Rt⟩ => ?_)
  have L : localVal base t Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 := by
    rw [Kt _ _ (by decide) (by simp only [Impl.Dsa.Layout.qMinusTwo, Impl.Dsa.Layout.t]; have := S.q32; omega)]
    exact Lu
  refine ⟨?_, L, Ru.toRun.trans Rt⟩
  rw [Ft, Fu, BitVec.and_assoc, mask32_and]
  exact congrArg _ (mask32_iff (by simp only [signingPublicChecks, and_assoc]))

end VG.Proof.Dsa.Arm
