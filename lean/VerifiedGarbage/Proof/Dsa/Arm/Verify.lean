module
public import VerifiedGarbage.Proof.Dsa.Arm.PublicKey

import VerifiedGarbage.Proof.Dsa.Arm.Sign
import VerifiedGarbage.Proof.Framework.Omega

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
  have Plt := operand_lt_of Ip
  have Qlt := operand_lt_of Iq
  have Lt : Impl.Dsa.Layout.t = 14944 := rfl
  have Lt2 : Impl.Dsa.Layout.t2 = 15328 := rfl
  have Li : Impl.Dsa.Layout.inverse = 14784 := rfl
  have Lu : Impl.Dsa.Layout.u = 14816 := rfl
  have Lv : Impl.Dsa.Layout.v = 14848 := rfl
  have Lz : Impl.Dsa.Layout.z = 14880 := rfl
  have L2 : Impl.Dsa.Layout.qMinusTwo = 14912 := rfl
  have qlt : ∀ x, x % Q < 256 ^ qLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Qlt
  have plt : ∀ x, x % P < 256 ^ pLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Plt
  simp only [Core.verify, Core.verifyScalars, Core.verifyPowers, Core.sequence, List.foldr]
  -- `w = s^(q-2) mod q`
  refine WP.seq (WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.inverse) Sc.ws (by omega_arith) Sc.wq q4
    (Nat.le_refl _) qw Iq.toReady Is.toReady (localReady (o := Impl.Dsa.Layout.qMinusTwo) Sc.ws (by omega_arith)
    (by omega_arith) (by omega_arith)) Iq.value (by omega_arith) hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₁ ⟨B₁, St₁⟩ => ?_))
  rw [Is.value, local_operand Sc.ws (by omega_arith), hq2] at B₁
  have S₁ := Sc.stage St₁
  have n₁ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₁ base size p len v :=
    fun I => I.next Sc St₁ (.inr ⟨by omega_arith, by omega_arith⟩)
  have W₁ : localVal base v₁ Impl.Dsa.Layout.inverse qLen = S ^ (Q - 2) % Q := localVal_of_bytes B₁ (qlt _)
  -- `z = digest mod q`
  have C₁ : countValue base v₁ Core.digestPrefix = c := by rw [countValue_stage St₁ (by omega_arith), hc]
  have Id₁ := n₁ Id
  rw [← C₁] at Id₁
  refine WP.seq (WP.mono (reduce_ok (output := Impl.Dsa.Layout.z) S₁.ws (by omega_arith) Sc.wq (n₁ Iq).toReady
    (by simp only [CountOk, Core.digestPrefix]; decide) Id₁.toReady (n₁ Iq).value hQ hQo (by omega_arith) (by omega_arith)
    (by omega_arith)) fun v₂ ⟨B₂, St₂⟩ => ?_)
  rw [Id₁.value] at B₂
  have S₂ := S₁.stage St₂
  have n₂ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₂ base size p len v :=
    fun I => (n₁ I).next S₁ St₂ (.inr ⟨by omega_arith, by omega_arith⟩)
  have Z₂ : localVal base v₂ Impl.Dsa.Layout.z qLen = D % Q := localVal_of_bytes B₂ (qlt _)
  have W₂ : localVal base v₂ Impl.Dsa.Layout.inverse qLen = S ^ (Q - 2) % Q := by
    rw [St₂.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), W₁]
  -- `u₁ = z w mod q`
  refine WP.seq (WP.mono (productMod_ok (output := Impl.Dsa.Layout.u) S₂.ws (by omega_arith) Sc.wq (n₂ Iq).toReady
    (localReady (o := Impl.Dsa.Layout.z) S₂.ws (by omega_arith) (by omega_arith) (by omega_arith))
    (localReady (o := Impl.Dsa.Layout.inverse) S₂.ws (by omega_arith) (by omega_arith) (by omega_arith)) (n₂ Iq).value (by omega_arith) hQo
    (by omega_arith) (by omega_arith) (by omega_arith)) fun v₃ ⟨B₃, St₃⟩ => ?_)
  rw [local_operand S₂.ws (by omega_arith), local_operand S₂.ws (by omega_arith), Z₂, W₂] at B₃
  have S₃ := S₂.stage St₃
  have n₃ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₃ base size p len v :=
    fun I => (n₂ I).next S₂ St₃ (.inr ⟨by omega_arith, by omega_arith⟩)
  have U₃ : localVal base v₃ Impl.Dsa.Layout.u qLen = D % Q * (S ^ (Q - 2) % Q) % Q := localVal_of_bytes B₃ (qlt _)
  have W₃ : localVal base v₃ Impl.Dsa.Layout.inverse qLen = S ^ (Q - 2) % Q := by
    rw [St₃.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), W₂]
  -- `u₂ = r w mod q`
  refine WP.seq (WP.mono (productMod_ok (output := Impl.Dsa.Layout.v) S₃.ws (by omega_arith) Sc.wq (n₃ Iq).toReady
    (n₃ Ir).toReady (localReady (o := Impl.Dsa.Layout.inverse) S₃.ws (by omega_arith) (by omega_arith) (by omega_arith))
    (n₃ Iq).value (by omega_arith) hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₄ ⟨B₄, St₄⟩ => ?_)
  rw [(n₃ Ir).value, local_operand S₃.ws (by omega_arith), W₃] at B₄
  have S₄ := S₃.stage St₄
  have n₄ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₄ base size p len v :=
    fun I => (n₃ I).next S₃ St₄ (.inr ⟨by omega_arith, by omega_arith⟩)
  have V₄ : localVal base v₄ Impl.Dsa.Layout.v qLen = R * (S ^ (Q - 2) % Q) % Q := localVal_of_bytes B₄ (qlt _)
  have U₄ : localVal base v₄ Impl.Dsa.Layout.u qLen = D % Q * (S ^ (Q - 2) % Q) % Q := by
    rw [St₄.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), U₃]
  refine WP.block_nil ?_
  -- `g^u₁ mod p`
  refine WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.t) S₄.ws (by omega_arith) Sc.wp q4 qp qw (n₄ Ip).toReady
    (n₄ Ig).toReady (localReady (o := Impl.Dsa.Layout.u) S₄.ws (by omega_arith) (by omega_arith) (by omega_arith)) (n₄ Ip).value
    hP hPo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₅ ⟨B₅, St₅⟩ => ?_)
  rw [(n₄ Ig).value, local_operand S₄.ws (by omega_arith), U₄] at B₅
  have S₅ := S₄.stage St₅
  have n₅ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₅ base size p len v :=
    fun I => (n₄ I).next S₄ St₅ (.inr ⟨by omega_arith, by omega_arith⟩)
  have T₅ : localVal base v₅ Impl.Dsa.Layout.t pLen = G ^ (D % Q * (S ^ (Q - 2) % Q) % Q) % P :=
    localVal_of_bytes B₅ (plt _)
  have V₅ : localVal base v₅ Impl.Dsa.Layout.v qLen = R * (S ^ (Q - 2) % Q) % Q := by
    rw [St₅.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), V₄]
  -- `y^u₂ mod p`
  refine WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.t2) S₅.ws (by omega_arith) Sc.wp q4 qp qw (n₅ Ip).toReady
    (n₅ Iy).toReady (localReady (o := Impl.Dsa.Layout.v) S₅.ws (by omega_arith) (by omega_arith) (by omega_arith)) (n₅ Ip).value
    hP hPo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₆ ⟨B₆, St₆⟩ => ?_)
  rw [(n₅ Iy).value, local_operand S₅.ws (by omega_arith), V₅] at B₆
  have S₆ := S₅.stage St₆
  have n₆ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₆ base size p len v :=
    fun I => (n₅ I).next S₅ St₆ (.inr ⟨by omega_arith, by omega_arith⟩)
  have T₆ : localVal base v₆ Impl.Dsa.Layout.t pLen = G ^ (D % Q * (S ^ (Q - 2) % Q) % Q) % P := by
    rw [St₆.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), T₅]
  have T2₆ : localVal base v₆ Impl.Dsa.Layout.t2 pLen = Y ^ (R * (S ^ (Q - 2) % Q) % Q) % P :=
    localVal_of_bytes B₆ (plt _)
  -- their product mod p
  refine WP.seq (WP.mono (productMod_ok (output := Impl.Dsa.Layout.t) S₆.ws (by omega_arith) Sc.wp (n₆ Ip).toReady
    (localReady (o := Impl.Dsa.Layout.t) S₆.ws (by omega_arith) (by omega_arith) (by omega_arith))
    (localReady (o := Impl.Dsa.Layout.t2) S₆.ws (by omega_arith) (by omega_arith) (by omega_arith)) (n₆ Ip).value hP hPo
    (by omega_arith) (by omega_arith) (by omega_arith)) fun v₇ ⟨B₇, St₇⟩ => ?_)
  rw [local_operand S₆.ws (by omega_arith), local_operand S₆.ws (by omega_arith), T₆, T2₆] at B₇
  have S₇ := S₆.stage St₇
  have n₇ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₇ base size p len v :=
    fun I => (n₆ I).next S₆ St₇ (.inr ⟨by omega_arith, by omega_arith⟩)
  have T₇ := localVal_of_bytes B₇ (plt _)
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
