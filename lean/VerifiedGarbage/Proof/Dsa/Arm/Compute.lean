module

import VerifiedGarbage.Proof.Dsa.Arm.SigningKey
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCall
public import VerifiedGarbage.Impl.Dsa.Arm.SignVerify
public import VerifiedGarbage.Proof.Dsa.Arm.PublicKey
public import VerifiedGarbage.Proof.Dsa.Arm.Sign
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Dsa.Arm.Verify`, which only this module used -/

section

/-!
# DSA on 32-bit ARM: the verification's arithmetic

`verify_ok`: `((g^u₁ mod p)(y^u₂ mod p) mod p) mod q` for
`w = s^(q-2) mod q`, `u₁ = (z mod q) w mod q` and `u₂ = r w mod q`, from
`q - 2` stored by the domain's check.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm

/-- The value the verification compares with `r`. -/
abbrev verifyValue (P Q G Y R S D : Nat) : Nat :=
  (G ^ (D % Q * (S ^ (Q - 2) % Q) % Q) % P * (Y ^ (R * (S ^ (Q - 2) % Q) % Q) % P) % P) % Q

theorem verify_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y R S D c : Nat}
    (Sc : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (Ir : Input s base size (.input .signature) qLen R) (Is : Input s base size .signatureS qLen S)
    (Id : Input s base size (.input .digest) c D) (hc : countValue base s Core.digestPrefix = c)
    (hq2 : localVal base s Impl.Dsa.Layout.qMinusTwo qLen = Q - 2)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (Core.verify pLen qLen) s fun t =>
      localVal base t Impl.Dsa.Layout.u qLen = verifyValue P Q G Y R S D ∧
      maskW base t = maskW base s ∧ Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := Sc.lens
  have big := Sc.big
  have fits := Sc.fits
  obtain Plt := operand_lt_of Ip
  obtain Qlt := operand_lt_of Iq
  have Lt : Impl.Dsa.Layout.t = 14944 := rfl
  have Lt2 : Impl.Dsa.Layout.t2 = 15328 := rfl
  have Li : Impl.Dsa.Layout.inverse = 14784 := rfl
  have Lu : Impl.Dsa.Layout.u = 14816 := rfl
  have Lv : Impl.Dsa.Layout.v = 14848 := rfl
  have Lz : Impl.Dsa.Layout.z = 14880 := rfl
  have L2 : Impl.Dsa.Layout.qMinusTwo = 14912 := rfl
  obtain qlt : ∀ x, x % Q < 256 ^ qLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Qlt
  obtain plt : ∀ x, x % P < 256 ^ pLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Plt
  simp only [Core.verify, Core.verifyScalars, Core.verifyPowers, Core.sequence, List.foldr]
  -- `w = s^(q-2) mod q`
  refine WP.seq (WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.inverse) Sc.ws (by omega_arith) Sc.wq q4
    (Nat.le_refl _) qw Iq.toReady Is.toReady (localReady (o := Impl.Dsa.Layout.qMinusTwo) Sc.ws (by omega_arith)
    (by omega_arith) (by omega_arith)) Iq.value (by omega_arith) hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₁ ⟨B₁, St₁⟩ => ?_))
  rw [Is.value, local_operand Sc.ws (by omega_arith), hq2] at B₁
  obtain S₁ := Sc.stage St₁
  obtain n₁ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₁ base size p len v :=
    fun I => I.next Sc St₁ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain W₁ : localVal base v₁ Impl.Dsa.Layout.inverse qLen = S ^ (Q - 2) % Q := localVal_of_bytes B₁ (qlt _)
  -- `z = digest mod q`
  obtain C₁ : countValue base v₁ Core.digestPrefix = c := by rw [countValue_stage St₁ (by omega_arith), hc]
  obtain Id₁ := n₁ Id
  rw [← C₁] at Id₁
  refine WP.seq (WP.mono (reduce_ok (output := Impl.Dsa.Layout.z) S₁.ws (by omega_arith) Sc.wq (n₁ Iq).toReady
    (by simp only [CountOk, Core.digestPrefix]; decide) Id₁.toReady (n₁ Iq).value hQ hQo (by omega_arith) (by omega_arith)
    (by omega_arith)) fun v₂ ⟨B₂, St₂⟩ => ?_)
  rw [Id₁.value] at B₂
  obtain S₂ := S₁.stage St₂
  obtain n₂ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₂ base size p len v :=
    fun I => (n₁ I).next S₁ St₂ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain Z₂ : localVal base v₂ Impl.Dsa.Layout.z qLen = D % Q := localVal_of_bytes B₂ (qlt _)
  obtain W₂ : localVal base v₂ Impl.Dsa.Layout.inverse qLen = S ^ (Q - 2) % Q := by
    rw [St₂.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), W₁]
  -- `u₁ = z w mod q`
  refine WP.seq (WP.mono (productMod_ok (output := Impl.Dsa.Layout.u) S₂.ws (by omega_arith) Sc.wq (n₂ Iq).toReady
    (localReady (o := Impl.Dsa.Layout.z) S₂.ws (by omega_arith) (by omega_arith) (by omega_arith))
    (localReady (o := Impl.Dsa.Layout.inverse) S₂.ws (by omega_arith) (by omega_arith) (by omega_arith)) (n₂ Iq).value (by omega_arith) hQo
    (by omega_arith) (by omega_arith) (by omega_arith)) fun v₃ ⟨B₃, St₃⟩ => ?_)
  rw [local_operand S₂.ws (by omega_arith), local_operand S₂.ws (by omega_arith), Z₂, W₂] at B₃
  obtain S₃ := S₂.stage St₃
  obtain n₃ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₃ base size p len v :=
    fun I => (n₂ I).next S₂ St₃ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain U₃ : localVal base v₃ Impl.Dsa.Layout.u qLen = D % Q * (S ^ (Q - 2) % Q) % Q := localVal_of_bytes B₃ (qlt _)
  obtain W₃ : localVal base v₃ Impl.Dsa.Layout.inverse qLen = S ^ (Q - 2) % Q := by
    rw [St₃.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), W₂]
  -- `u₂ = r w mod q`
  refine WP.seq (WP.mono (productMod_ok (output := Impl.Dsa.Layout.v) S₃.ws (by omega_arith) Sc.wq (n₃ Iq).toReady
    (n₃ Ir).toReady (localReady (o := Impl.Dsa.Layout.inverse) S₃.ws (by omega_arith) (by omega_arith) (by omega_arith))
    (n₃ Iq).value (by omega_arith) hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₄ ⟨B₄, St₄⟩ => ?_)
  rw [(n₃ Ir).value, local_operand S₃.ws (by omega_arith), W₃] at B₄
  obtain S₄ := S₃.stage St₄
  obtain n₄ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₄ base size p len v :=
    fun I => (n₃ I).next S₃ St₄ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain V₄ : localVal base v₄ Impl.Dsa.Layout.v qLen = R * (S ^ (Q - 2) % Q) % Q := localVal_of_bytes B₄ (qlt _)
  obtain U₄ : localVal base v₄ Impl.Dsa.Layout.u qLen = D % Q * (S ^ (Q - 2) % Q) % Q := by
    rw [St₄.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), U₃]
  refine WP.block_nil ?_
  -- `g^u₁ mod p`
  refine WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.t) S₄.ws (by omega_arith) Sc.wp q4 qp qw (n₄ Ip).toReady
    (n₄ Ig).toReady (localReady (o := Impl.Dsa.Layout.u) S₄.ws (by omega_arith) (by omega_arith) (by omega_arith)) (n₄ Ip).value
    hP hPo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₅ ⟨B₅, St₅⟩ => ?_)
  rw [(n₄ Ig).value, local_operand S₄.ws (by omega_arith), U₄] at B₅
  obtain S₅ := S₄.stage St₅
  obtain n₅ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₅ base size p len v :=
    fun I => (n₄ I).next S₄ St₅ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain T₅ : localVal base v₅ Impl.Dsa.Layout.t pLen = G ^ (D % Q * (S ^ (Q - 2) % Q) % Q) % P :=
    localVal_of_bytes B₅ (plt _)
  obtain V₅ : localVal base v₅ Impl.Dsa.Layout.v qLen = R * (S ^ (Q - 2) % Q) % Q := by
    rw [St₅.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), V₄]
  -- `y^u₂ mod p`
  refine WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.t2) S₅.ws (by omega_arith) Sc.wp q4 qp qw (n₅ Ip).toReady
    (n₅ Iy).toReady (localReady (o := Impl.Dsa.Layout.v) S₅.ws (by omega_arith) (by omega_arith) (by omega_arith)) (n₅ Ip).value
    hP hPo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₆ ⟨B₆, St₆⟩ => ?_)
  rw [(n₅ Iy).value, local_operand S₅.ws (by omega_arith), V₅] at B₆
  obtain S₆ := S₅.stage St₆
  obtain n₆ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₆ base size p len v :=
    fun I => (n₅ I).next S₅ St₆ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain T₆ : localVal base v₆ Impl.Dsa.Layout.t pLen = G ^ (D % Q * (S ^ (Q - 2) % Q) % Q) % P := by
    rw [St₆.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), T₅]
  obtain T2₆ : localVal base v₆ Impl.Dsa.Layout.t2 pLen = Y ^ (R * (S ^ (Q - 2) % Q) % Q) % P :=
    localVal_of_bytes B₆ (plt _)
  -- their product mod p
  refine WP.seq (WP.mono (productMod_ok (output := Impl.Dsa.Layout.t) S₆.ws (by omega_arith) Sc.wp (n₆ Ip).toReady
    (localReady (o := Impl.Dsa.Layout.t) S₆.ws (by omega_arith) (by omega_arith) (by omega_arith))
    (localReady (o := Impl.Dsa.Layout.t2) S₆.ws (by omega_arith) (by omega_arith) (by omega_arith)) (n₆ Ip).value hP hPo
    (by omega_arith) (by omega_arith) (by omega_arith)) fun v₇ ⟨B₇, St₇⟩ => ?_)
  rw [local_operand S₆.ws (by omega_arith), local_operand S₆.ws (by omega_arith), T₆, T2₆] at B₇
  obtain S₇ := S₆.stage St₇
  obtain n₇ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₇ base size p len v :=
    fun I => (n₆ I).next S₆ St₇ (.inr ⟨by omega_arith, by omega_arith⟩)
  obtain T₇ := localVal_of_bytes B₇ (plt _)
  -- mod q
  refine WP.seq (WP.mono (reduce_ok (output := Impl.Dsa.Layout.u) S₇.ws (by omega_arith) Sc.wq (n₇ Iq).toReady
    (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega_arith)
    (localReady S₇.ws (by omega_arith) (by simp only [countValue]; omega_arith) (by omega_arith))
    (n₇ Iq).value hQ hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₈ ⟨B₈, St₈⟩ => WP.block_nil ⟨?_, ?_, ?_⟩)
  · rw [countValue, local_operand S₇.ws (by omega_arith), T₇] at B₈
    exact localVal_of_bytes B₈ (qlt _)
  · rw [St₈.maskW (by omega_arith), St₇.maskW (by omega_arith), St₆.maskW (by omega_arith), St₅.maskW (by omega_arith),
      St₄.maskW (by omega_arith), St₃.maskW (by omega_arith), St₂.maskW (by omega_arith), St₁.maskW (by omega_arith)]
  · exact (((((((St₁.run (.inr ⟨by omega_arith, by omega_arith⟩)).trans (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans
      (St₃.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans (St₄.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans
      (St₅.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans (St₆.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans
      (St₇.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans (St₈.run (.inr ⟨by omega_arith, by omega_arith⟩))

end VG.Proof.Dsa.Arm

end

end


/-!
# DSA on 32-bit ARM: the computations of signing and verifying

`signCompute_ok`: the flag `&=` every check of a signature (the domain,
the keys, the nonce, and nonzero r and s), with r and s computed;
`verifyCompute_ok`: the flag `&=` every check of a verification, the last
the comparison of the computed value with r.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32 mask32_and)

theorem countValue_run {base : Addr} {s t : State} (Rn : Run base s t) :
    countValue base t Core.digestPrefix = countValue base s Core.digestPrefix :=
  countValue_keep Rn.mem (by decide) (by simp only [CountOk, Core.digestPrefix]; decide)

/-- Every check of a signature. -/
abbrev signChecks (P Q G Y X K D : Nat) : Prop :=
  publicChecks P Q G Y ∧ ((0 < X ∧ X < Q) ∧ (0 < K ∧ K < Q)) ∧ G ^ X % P = Y ∧
    rValue P Q G K ≠ 0 ∧ sValue P Q G X K D ≠ 0

theorem signCompute_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y X K D c : Nat}
    (Sc : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (Ix : Input s base size (.input .x) qLen X) (Ik : Input s base size (.input .nonce) qLen K)
    (Id : Input s base size (.input .digest) c D) (hc : countValue base s Core.digestPrefix = c)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (SignVerify.signCompute pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (signChecks P Q G Y X K D) ∧
      localVal base t Impl.Dsa.Layout.r qLen = rValue P Q G K ∧
      localVal base t Impl.Dsa.Layout.s qLen = sValue P Q G X K D ∧ Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := Sc.lens
  have big := Sc.big
  have fits := Sc.fits
  obtain Qlt := operand_lt_of Iq
  obtain qlt : ∀ x, x % Q < 256 ^ qLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Qlt
  have Lr : Impl.Dsa.Layout.r = 14720 := rfl
  have Ls : Impl.Dsa.Layout.s = 14752 := rfl
  simp only [SignVerify.signCompute, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (signingKey_ok Sc Ip Iq Ig Iy hP hPo hQ hQo) fun u₁ ⟨F₁, L₁, Rn₁⟩ => ?_)
  obtain r₁ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input u₁ base size p len v :=
    fun I => I.run Rn₁ (by omega_arith) fits
  refine WP.seq (WP.mono (privateKey_ok (Sc.run Rn₁) (r₁ Ip) (r₁ Iq) (r₁ Ig) (r₁ Iy) (r₁ Ix) (r₁ Ik) hP hPo)
    fun u₂ ⟨F₂, K₂, Rn₂⟩ => ?_)
  obtain r₂ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input u₂ base size p len v :=
    fun I => (r₁ I).run Rn₂ (by omega_arith) fits
  obtain L₂ : localVal base u₂ Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 := by
    rw [K₂ _ _ (by decide) (by simp only [Impl.Dsa.Layout.qMinusTwo, Impl.Dsa.Layout.t]; omega_arith), L₁]
  refine WP.seq (WP.mono (sign_ok (Sc.run (Rn₁.trans Rn₂)) (r₂ Ip) (r₂ Iq) (r₂ Ig) (r₂ Ix) (r₂ Ik) (r₂ Id)
    (by rw [countValue_run Rn₂, countValue_run Rn₁, hc]) L₂ hP hPo hQ hQo) fun u₃ ⟨R₃, S₃, M₃, Rn₃⟩ => ?_)
  obtain Sc₃ := Sc.run ((Rn₁.trans Rn₂).trans Rn₃)
  refine WP.seq (WP.seq (WP.mono (zero_ok Sc₃.ws (by omega_arith) Sc.wq
    (localReady (o := Impl.Dsa.Layout.r) (len := qLen) Sc₃.ws (by omega_arith) (by omega_arith) (by omega_arith)) true)
    fun u₄ ⟨F₄, St₄⟩ => WP.mono (zero_ok (St₄.ws Sc₃.ws) (by omega_arith) Sc.wq
      (localReady (o := Impl.Dsa.Layout.s) (len := qLen) (St₄.ws Sc₃.ws) (by omega_arith) (by omega_arith) (by omega_arith)) true)
    fun u₅ ⟨F₅, St₅⟩ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩))
  · rw [local_operand Sc₃.ws (by omega_arith), R₃] at F₄
    rw [local_operand (St₄.ws Sc₃.ws) (by omega_arith), St₄.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      S₃] at F₅
    rw [F₅, F₄, M₃, F₂, F₁, BitVec.and_assoc, BitVec.and_assoc, BitVec.and_assoc, mask32_and, mask32_and,
      mask32_and]
    apply congrArg _ (mask32_iff ?_)
    obtain H := signingPublicChecks_consistent (P := P) (Q := Q) (G := G) (Y := Y) (X := X)
      (A := ((0 < X ∧ X < Q) ∧ (0 < K ∧ K < Q))) hP
    obtain H' := and_congr H (Iff.rfl :
      (rValue P Q G K ≠ 0 ∧ sValue P Q G X K D ≠ 0) ↔
        (rValue P Q G K ≠ 0 ∧ sValue P Q G X K D ≠ 0))
    simpa only [↓reduceIte, signChecks, and_assoc] using H'
  · rw [St₅.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      St₄.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), R₃]
  · rw [St₅.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      St₄.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), S₃]
  · exact (((Rn₁.trans Rn₂).trans Rn₃).trans (St₄.run (.inl ⟨rfl, rfl⟩))).trans (St₅.run (.inl ⟨rfl, rfl⟩))

/-- Every check of a verification. -/
abbrev verifyChecks (P Q G Y R S D : Nat) : Prop :=
  publicChecks P Q G Y ∧ (0 < R ∧ R < Q) ∧ (0 < S ∧ S < Q) ∧ verifyValue P Q G Y R S D = R

/-- The checks of a verification after the public key's: the signature's
ranges, and the comparison of the computed value with r, given q − 2. -/
theorem verifyTail_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y R S D c : Nat}
    (Sc : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (Ir : Input s base size (.input .signature) qLen R) (Is : Input s base size .signatureS qLen S)
    (Id : Input s base size (.input .digest) c D) (hc : countValue base s Core.digestPrefix = c)
    (L : localVal base s Impl.Dsa.Layout.qMinusTwo qLen = Q - 2)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (Core.sequence [
      .seq (Validate.range qLen .q (.input .signature)) (Validate.range qLen .q .signatureS),
      Core.verify pLen qLen,
      Validate.equalValues qLen (.local Impl.Dsa.Layout.u) (.input .signature)]) s fun t =>
      maskW base t = maskW base s &&& mask32 ((0 < R ∧ R < Q) ∧ (0 < S ∧ S < Q) ∧ verifyValue P Q G Y R S D = R) ∧
        Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := Sc.lens
  have big := Sc.big
  have fits := Sc.fits
  have Lu : Impl.Dsa.Layout.u = 14816 := rfl
  have L2 : Impl.Dsa.Layout.qMinusTwo = 14912 := rfl
  simp only [Core.sequence, List.foldr]
  refine WP.seq (WP.seq (WP.mono (range_ok Sc.ws (by omega_arith) Sc.wq Iq.toReady Ir.toReady false)
    fun u₂ ⟨F₂, St₂⟩ => WP.mono (range_ok (St₂.ws Sc.ws) (by omega_arith) Sc.wq
      (Iq.next Sc St₂ (.inl ⟨rfl, rfl⟩)).toReady (Is.next Sc St₂ (.inl ⟨rfl, rfl⟩)).toReady false)
    fun u₃ ⟨F₃, St₃⟩ => ?_))
  rw [Iq.value, Ir.value] at F₂
  rw [(Iq.next Sc St₂ (.inl ⟨rfl, rfl⟩)).value, (Is.next Sc St₂ (.inl ⟨rfl, rfl⟩)).value] at F₃
  obtain Sc₃ := (Sc.stage St₂).stage St₃
  obtain r₃ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input u₃ base size p len v :=
    fun I => (I.next Sc St₂ (.inl ⟨rfl, rfl⟩)).next (Sc.stage St₂) St₃ (.inl ⟨rfl, rfl⟩)
  obtain L₃ : localVal base u₃ Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 := by
    rw [St₃.localVal_eq (by decide) (by omega_arith) (by omega_arith) (by omega_arith),
      St₂.localVal_eq (by decide) (by omega_arith) (by omega_arith) (by omega_arith), L]
  obtain C₃ : countValue base u₃ Core.digestPrefix = c := by
    rw [countValue_stage St₃ (by omega_arith), countValue_stage St₂ (by omega_arith), hc]
  refine WP.seq (WP.mono (verify_ok Sc₃ (r₃ Ip) (r₃ Iq) (r₃ Ig) (r₃ Iy) (r₃ Ir) (r₃ Is) (r₃ Id) C₃ L₃ hP hPo hQ hQo)
    fun u₄ ⟨V₄, M₄, Rn₄⟩ => ?_)
  obtain Sc₄ := Sc₃.run Rn₄
  refine WP.seq (WP.mono (equalValues_ok Sc₄.ws (by omega_arith) Sc.wq
    (localReady (o := Impl.Dsa.Layout.u) Sc₄.ws (by omega_arith) (by omega_arith) (by omega_arith)) ((r₃ Ir).run Rn₄ (by omega_arith) fits).toReady)
    fun u₅ ⟨F₅, St₅⟩ => WP.block_nil ⟨?_, ?_⟩)
  · rw [local_operand Sc₄.ws (by omega_arith), V₄, ((r₃ Ir).run Rn₄ (by omega_arith) fits).value] at F₅
    rw [F₅, M₄, F₃, F₂, BitVec.and_assoc, BitVec.and_assoc, mask32_and, mask32_and]
    exact congrArg _ (mask32_iff (by simp only [Bool.false_eq_true, ↓reduceIte]))
  · exact (((St₂.run (.inl ⟨rfl, rfl⟩)).trans (St₃.run (.inl ⟨rfl, rfl⟩))).trans Rn₄).trans
      (St₅.run (.inl ⟨rfl, rfl⟩))

end VG.Proof.Dsa.Arm
