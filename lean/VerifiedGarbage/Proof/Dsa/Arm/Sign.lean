module

public import VerifiedGarbage.Proof.Dsa.Arm.PublicKey
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA on 32-bit ARM: the signature's arithmetic

`sign_ok`: `r = (g^k mod p) mod q` and
`s = k^(q-2) ((z mod q + x r mod q) mod q) mod q` for the value `z` of the
digest's saved prefix, from `q - 2` stored by the domain's check.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32 mask32_and)

theorem countValue_stage {base : Addr} {s t : State} {o l : Nat} (St : Stage base s t o l) (ho : 116 ≤ o) :
    countValue base t Core.digestPrefix = countValue base s Core.digestPrefix :=
  countValue_keep St.mem (fun r hr => by
    simp only [arithRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega) (by simp only [CountOk, Core.digestPrefix]; decide)

/-- The value of the first scalar. -/
abbrev rValue (P Q G K : Nat) : Nat := G ^ K % P % Q

/-- The value of the second. -/
abbrev sValue (P Q G X K D : Nat) : Nat := K ^ (Q - 2) % Q * ((D % Q + X * rValue P Q G K % Q) % Q) % Q

theorem sign_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G X K D c : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Ix : Input s base size (.input .x) qLen X)
    (Ik : Input s base size (.input .nonce) qLen K) (Id : Input s base size (.input .digest) c D)
    (hc : countValue base s Core.digestPrefix = c)
    (hq2 : localVal base s Impl.Dsa.Layout.qMinusTwo qLen = Q - 2)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (Core.sign pLen qLen) s fun t =>
      localVal base t Impl.Dsa.Layout.r qLen = rValue P Q G K ∧
      localVal base t Impl.Dsa.Layout.s qLen = sValue P Q G X K D ∧
      maskW base t = maskW base s ∧ Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := S.lens
  have big := S.big
  have fits := S.fits
  have Plt := operand_lt_of Ip
  have Qlt := operand_lt_of Iq
  have Lt : Impl.Dsa.Layout.t = 14944 := rfl
  have Lr : Impl.Dsa.Layout.r = 14720 := rfl
  have Ls : Impl.Dsa.Layout.s = 14752 := rfl
  have Li : Impl.Dsa.Layout.inverse = 14784 := rfl
  have Lu : Impl.Dsa.Layout.u = 14816 := rfl
  have Lv : Impl.Dsa.Layout.v = 14848 := rfl
  have Lz : Impl.Dsa.Layout.z = 14880 := rfl
  have L2 : Impl.Dsa.Layout.qMinusTwo = 14912 := rfl
  have qlt : ∀ x, x % Q < 256 ^ qLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Qlt
  simp only [Core.sign, Core.signStart, Core.signFinish, Core.sequence, List.foldr]
  -- `t = g^k mod p`
  refine WP.seq (WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.t) S.ws (by omega_arith) S.wp q4 qp qw Ip.toReady
    Ig.toReady Ik.toReady Ip.value hP hPo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₁ ⟨B₁, St₁⟩ => ?_))
  rw [Ig.value, Ik.value] at B₁
  have S₁ := S.stage St₁
  have n₁ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₁ base size p len v :=
    fun I => I.next S St₁ (.inr ⟨by omega_arith, by omega_arith⟩)
  have T₁ : localVal base v₁ Impl.Dsa.Layout.t pLen = G ^ K % P :=
    localVal_of_bytes B₁ (Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Plt)
  -- `r = t mod q`
  refine WP.seq (WP.mono (reduce_ok (output := Impl.Dsa.Layout.r) S₁.ws (by omega_arith) S.wq (n₁ Iq).toReady
    (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega_arith)
    (localReady (o := Impl.Dsa.Layout.t) S₁.ws (by omega_arith) (by simp only [countValue]; omega_arith) (by omega_arith))
    (n₁ Iq).value hQ hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₂ ⟨B₂, St₂⟩ => ?_)
  rw [countValue, local_operand S₁.ws (by omega_arith), T₁] at B₂
  have S₂ := S₁.stage St₂
  have n₂ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₂ base size p len v :=
    fun I => (n₁ I).next S₁ St₂ (.inr ⟨by omega_arith, by omega_arith⟩)
  have R₂ : localVal base v₂ Impl.Dsa.Layout.r qLen = rValue P Q G K := localVal_of_bytes B₂ (qlt _)
  have M₂ : localVal base v₂ Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 := by
    rw [St₂.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      St₁.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), hq2]
  -- `k^(q-2) mod q`
  refine WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.inverse) S₂.ws (by omega_arith) S.wq q4 (Nat.le_refl _) qw
    (n₂ Iq).toReady (n₂ Ik).toReady (localReady (o := Impl.Dsa.Layout.qMinusTwo) S₂.ws (by omega_arith) (by omega_arith) (by omega_arith)) (n₂ Iq).value
    (by omega_arith) hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₃ ⟨B₃, St₃⟩ => ?_)
  rw [(n₂ Ik).value, local_operand S₂.ws (by omega_arith), M₂] at B₃
  have S₃ := S₂.stage St₃
  have n₃ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₃ base size p len v :=
    fun I => (n₂ I).next S₂ St₃ (.inr ⟨by omega_arith, by omega_arith⟩)
  have I₃ : localVal base v₃ Impl.Dsa.Layout.inverse qLen = K ^ (Q - 2) % Q := localVal_of_bytes B₃ (qlt _)
  have R₃ : localVal base v₃ Impl.Dsa.Layout.r qLen = rValue P Q G K := by
    rw [St₃.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), R₂]
  -- `u = x r mod q`
  refine WP.block_nil ?_
  refine WP.seq (WP.mono (productMod_ok (output := Impl.Dsa.Layout.u) S₃.ws (by omega_arith) S.wq (n₃ Iq).toReady
    (n₃ Ix).toReady (localReady (o := Impl.Dsa.Layout.r) S₃.ws (by omega_arith) (by omega_arith) (by omega_arith)) (n₃ Iq).value (by omega_arith) hQo
    (by omega_arith) (by omega_arith) (by omega_arith)) fun v₄ ⟨B₄, St₄⟩ => ?_)
  rw [(n₃ Ix).value, local_operand S₃.ws (by omega_arith), R₃] at B₄
  have S₄ := S₃.stage St₄
  have n₄ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₄ base size p len v :=
    fun I => (n₃ I).next S₃ St₄ (.inr ⟨by omega_arith, by omega_arith⟩)
  have U₄ : localVal base v₄ Impl.Dsa.Layout.u qLen = X * rValue P Q G K % Q := localVal_of_bytes B₄ (qlt _)
  -- `z = digest mod q`
  have C₃ : countValue base v₄ Core.digestPrefix = c := by
    rw [countValue_stage St₄ (by omega_arith), countValue_stage St₃ (by omega_arith), countValue_stage St₂ (by omega_arith),
      countValue_stage St₁ (by omega_arith), hc]
  have Id₄ := n₄ Id
  rw [← C₃] at Id₄
  refine WP.seq (WP.mono (reduce_ok (output := Impl.Dsa.Layout.z) S₄.ws (by omega_arith) S.wq (n₄ Iq).toReady
    (by simp only [CountOk, Core.digestPrefix]; decide) Id₄.toReady (n₄ Iq).value hQ hQo (by omega_arith) (by omega_arith) (by omega_arith))
    fun v₅ ⟨B₅, St₅⟩ => ?_)
  rw [Id₄.value] at B₅
  have S₅ := S₄.stage St₅
  have n₅ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₅ base size p len v :=
    fun I => (n₄ I).next S₄ St₅ (.inr ⟨by omega_arith, by omega_arith⟩)
  have Z₅ : localVal base v₅ Impl.Dsa.Layout.z qLen = D % Q := localVal_of_bytes B₅ (qlt _)
  have U₅ : localVal base v₅ Impl.Dsa.Layout.u qLen = X * rValue P Q G K % Q := by
    rw [St₅.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), U₄]
  -- `v = z + u mod q`
  refine WP.seq (WP.mono (sum_ok (output := Impl.Dsa.Layout.v) S₅.ws (by omega_arith) S.wq (n₅ Iq).toReady
    (localReady (o := Impl.Dsa.Layout.z) S₅.ws (by omega_arith) (by omega_arith) (by omega_arith)) (localReady (o := Impl.Dsa.Layout.u) S₅.ws (by omega_arith) (by omega_arith) (by omega_arith))
    (n₅ Iq).value (by omega_arith) hQo (by rw [local_operand S₅.ws (by omega_arith), Z₅]; exact Nat.mod_lt _ (by omega_arith))
    (by rw [local_operand S₅.ws (by omega_arith), U₅]; exact Nat.mod_lt _ (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith))
    fun v₆ ⟨B₆, St₆⟩ => ?_)
  rw [local_operand S₅.ws (by omega_arith), local_operand S₅.ws (by omega_arith), Z₅, U₅] at B₆
  have S₆ := S₅.stage St₆
  have n₆ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₆ base size p len v :=
    fun I => (n₅ I).next S₅ St₆ (.inr ⟨by omega_arith, by omega_arith⟩)
  have V₆ : localVal base v₆ Impl.Dsa.Layout.v qLen = (D % Q + X * rValue P Q G K % Q) % Q :=
    localVal_of_bytes B₆ (qlt _)
  have I₆ : localVal base v₆ Impl.Dsa.Layout.inverse qLen = K ^ (Q - 2) % Q := by
    rw [St₆.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), St₅.localVal_eq (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith), St₄.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), I₃]
  -- `s = k^(q-2) v mod q`
  refine WP.seq (WP.mono (productMod_ok (output := Impl.Dsa.Layout.s) S₆.ws (by omega_arith) S.wq (n₆ Iq).toReady
    (localReady (o := Impl.Dsa.Layout.inverse) S₆.ws (by omega_arith) (by omega_arith) (by omega_arith)) (localReady (o := Impl.Dsa.Layout.v) S₆.ws (by omega_arith) (by omega_arith) (by omega_arith))
    (n₆ Iq).value (by omega_arith) hQo (by omega_arith) (by omega_arith) (by omega_arith)) fun v₇ ⟨B₇, St₇⟩ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩)
  · rw [St₇.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), St₆.localVal_eq (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith), St₅.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      St₄.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      St₃.localVal_eq (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), R₂]
  · rw [local_operand S₆.ws (by omega_arith), local_operand S₆.ws (by omega_arith), I₆, V₆] at B₇
    exact localVal_of_bytes B₇ (qlt _)
  · rw [St₇.maskW (by omega_arith), St₆.maskW (by omega_arith), St₅.maskW (by omega_arith), St₄.maskW (by omega_arith),
      St₃.maskW (by omega_arith), St₂.maskW (by omega_arith), St₁.maskW (by omega_arith)]
  · exact ((((((St₁.run (.inr ⟨by omega_arith, by omega_arith⟩)).trans (St₂.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans
      (St₃.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans (St₄.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans
      (St₅.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans (St₆.run (.inr ⟨by omega_arith, by omega_arith⟩))).trans
      (St₇.run (.inr ⟨by omega_arith, by omega_arith⟩))

end VG.Proof.Dsa.Arm
