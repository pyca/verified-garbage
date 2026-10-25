module

public import VerifiedGarbage.Proof.Dsa.Arm.PublicKey
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Encoding

/-!
# DSA domain checks and key derivation on 32-bit ARM: the computations

`domain_gen_ok`: the flag `&=` g's range and `q ∣ p - 1`; `subgroup_gen_ok`:
`g^q = 1 mod p`; `parameters_ok`: both. `deriveCompute_ok`: the flag `&=`
those, x's range and y's, with y = g^x mod p stored at `t2`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32 mask32_and)

/-- The checks of a domain beyond its shape. -/
abbrev domainChecks (P Q G : Nat) : Prop := ((1 < G ∧ G < P) ∧ (P - 1) % Q = 0) ∧ G ^ Q % P = 1

/-- The checks of a derivation beyond the domain's shape. -/
abbrev deriveChecks (P Q G X : Nat) : Prop :=
  domainChecks P Q G ∧ (0 < X ∧ X < Q) ∧ (1 < G ^ X % P ∧ G ^ X % P < P)

theorem domain_gen_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (Generate.domain pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 ((1 < G ∧ G < P) ∧ (P - 1) % Q = 0) ∧ Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := S.lens
  have big := S.big
  have fits := S.fits
  have Qlt := operand_lt_of Iq
  simp only [Generate.domain, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (range_ok S.ws (by omega_arith) S.wp Ip.toReady Ig.toReady true) fun v₁ ⟨F₁, St₁⟩ => ?_)
  have S₁ := S.stage St₁
  have Ip₁ := Ip.next S St₁ (.inl ⟨rfl, rfl⟩)
  have Iq₁ := Iq.next S St₁ (.inl ⟨rfl, rfl⟩)
  rw [Ip.value, Ig.value] at F₁
  -- `p - 1`
  refine WP.seq (WP.mono (minus_ok (output := Impl.Dsa.Layout.t) S₁.ws (by omega_arith) S.wp Ip₁.toReady Ip₁.value hP hPo
    (by omega_arith) (by decide) (by decide) (by simp only [Impl.Dsa.Layout.t]; omega_arith) (by decide))
    fun v₃ ⟨B₃, St₃⟩ => ?_)
  have S₃ := S₁.stage St₃
  have ho₃ : 4960 ≤ Impl.Dsa.Layout.t ∧ Impl.Dsa.Layout.t + pLen ≤ 15712 := by
    simp only [Impl.Dsa.Layout.t]; omega_arith
  have Iq₃ := Iq₁.next S₁ St₃ (.inr ho₃)
  have L₃ : localVal base v₃ Impl.Dsa.Layout.t pLen = P - 1 := localVal_of_bytes B₃ (by
    have := operand_lt_of Ip; omega_arith)
  -- `(p - 1) mod q`
  refine WP.seq (WP.mono (reduce_ok (output := Impl.Dsa.Layout.u) S₃.ws (by omega_arith) S.wq Iq₃.toReady
    (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega_arith)
    (localReady S₃.ws (by decide) (by simp only [countValue, Impl.Dsa.Layout.t]; omega_arith) (by decide))
    Iq₃.value hQ hQo (by decide) (by simp only [Impl.Dsa.Layout.u]; omega_arith) (by decide)) fun v₄ ⟨B₄, St₄⟩ => ?_)
  rw [countValue, local_operand S₃.ws (by simp only [Impl.Dsa.Layout.t]; omega_arith), L₃] at B₄
  have S₄ := S₃.stage St₄
  have ho₄ : 4960 ≤ Impl.Dsa.Layout.u ∧ Impl.Dsa.Layout.u + qLen ≤ 15712 := by
    simp only [Impl.Dsa.Layout.u]; omega_arith
  have L₄ : localVal base v₄ Impl.Dsa.Layout.u qLen = (P - 1) % Q :=
    localVal_of_bytes B₄ (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega_arith)) (Nat.le_of_lt Qlt))
  -- `q ∣ p - 1`
  refine WP.seq (WP.mono (zero_ok S₄.ws (by omega_arith) S.wq
    (localReady (len := qLen) S₄.ws (by decide) (by simp only [Impl.Dsa.Layout.u]; omega_arith) (by decide)) false)
    fun v₅ ⟨F₅, St₅⟩ => WP.block_nil ⟨?_, ?_⟩)
  · rw [local_operand S₄.ws (by simp only [Impl.Dsa.Layout.u]; omega_arith), L₄] at F₅
    rw [F₅, St₄.maskW (by decide), St₃.maskW (by decide), F₁, BitVec.and_assoc, mask32_and]
    exact congrArg _ (mask32_iff (by simp only [↓reduceIte, Bool.false_eq_true] <;> omega_arith))
  · exact (((St₁.run (.inl ⟨rfl, rfl⟩)).trans (St₃.run (.inr ho₃))).trans (St₄.run (.inr ho₄))).trans
      (St₅.run (.inl ⟨rfl, rfl⟩))

theorem subgroup_gen_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (hP : 1 < P) (hPo : P % 2 = 1) :
    WP isa (Generate.subgroup pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (G ^ Q % P = 1) ∧ Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := S.lens
  have big := S.big
  have Plt := operand_lt_of Ip
  have ho : 4960 ≤ Impl.Dsa.Layout.t ∧ Impl.Dsa.Layout.t + pLen ≤ 15712 := by
    simp only [Impl.Dsa.Layout.t]; omega_arith
  have ht : Impl.Dsa.Layout.t + pLen < size := by omega_arith
  unfold Generate.subgroup
  refine WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.t) S.ws (by omega_arith) S.wp q4 qp qw Ip.toReady
    Ig.toReady Iq.toReady Ip.value hP hPo ho.1 (by omega_arith) (by decide)) fun v₁ ⟨B₁, St₁⟩ => ?_)
  rw [Ig.value, Iq.value] at B₁
  have S₁ := S.stage St₁
  refine WP.mono (isOne_ok S₁.ws (by omega_arith) S.wp (localReady S₁.ws ho.1 ht (by decide)))
    fun v₂ ⟨F₂, St₂⟩ => ⟨?_, (St₁.run (.inr ho)).trans (St₂.run (.inl ⟨rfl, rfl⟩))⟩
  rw [local_operand S₁.ws (by omega_arith), localVal_of_bytes B₁ (Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Plt)] at F₂
  rw [F₂, St₁.maskW (by decide)]

theorem parameters_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (Generate.parameters pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (domainChecks P Q G) ∧ Run base s t := by
  have big := S.big
  have fits := S.fits
  unfold Generate.parameters
  refine WP.seq (WP.mono (domain_gen_ok S Ip Iq Ig hP hPo hQ hQo) fun u ⟨Fu, Ru⟩ =>
    WP.mono (subgroup_gen_ok (S.run Ru) (Ip.run Ru (by omega_arith) fits) (Iq.run Ru (by omega_arith) fits)
      (Ig.run Ru (by omega_arith) fits) hP hPo) fun t ⟨Ft, Rt⟩ => ⟨?_, Ru.trans Rt⟩)
  rw [Ft, Fu, BitVec.and_assoc, mask32_and]

theorem deriveCompute_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G X : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Ix : Input s base size (.input .nonce) qLen X)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (Generate.deriveCompute pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (deriveChecks P Q G X) ∧
      Spec.Rsa.bytesAt t.mem (off base Impl.Dsa.Layout.t2) pLen = Spec.Dsa.encodeBE pLen (G ^ X % P) ∧
      Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := S.lens
  have big := S.big
  have fits := S.fits
  have Plt := operand_lt_of Ip
  have ho : 4960 ≤ Impl.Dsa.Layout.t2 ∧ Impl.Dsa.Layout.t2 + pLen ≤ 15712 := by
    simp only [Impl.Dsa.Layout.t2]; omega_arith
  have ht : Impl.Dsa.Layout.t2 + pLen < size := by omega_arith
  simp only [Generate.deriveCompute, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (parameters_ok S Ip Iq Ig hP hPo hQ hQo) fun v₁ ⟨F₁, R₁⟩ => ?_)
  have S₁ := S.run R₁
  have nx : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₁ base size p len v :=
    fun I => I.run R₁ (by omega_arith) fits
  -- `0 < x < q`
  refine WP.seq (WP.mono (range_ok S₁.ws (by omega_arith) S.wq (nx Iq).toReady (nx Ix).toReady false)
    fun v₂ ⟨F₂, St₂⟩ => ?_)
  rw [(nx Iq).value, (nx Ix).value] at F₂
  have S₂ := S₁.stage St₂
  have nx₂ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₂ base size p len v :=
    fun I => (nx I).next S₁ St₂ (.inl ⟨rfl, rfl⟩)
  -- `y = g^x mod p`
  refine WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.t2) S₂.ws (by omega_arith) S.wp q4 qp qw (nx₂ Ip).toReady
    (nx₂ Ig).toReady (nx₂ Ix).toReady (nx₂ Ip).value hP hPo ho.1 (by omega_arith) (by decide)) fun v₃ ⟨B₃, St₃⟩ => ?_)
  rw [(nx₂ Ig).value, (nx₂ Ix).value] at B₃
  have S₃ := S₂.stage St₃
  have Ip₃ := (nx₂ Ip).next S₂ St₃ (.inr ho)
  -- `1 < y < p`
  refine WP.seq (WP.mono (range_ok S₃.ws (by omega_arith) S.wp Ip₃.toReady (localReady S₃.ws ho.1 ht (by decide)) true)
    fun v₄ ⟨F₄, St₄⟩ => WP.block_nil ⟨?_, ?_, ?_⟩)
  · rw [local_operand S₃.ws (by omega_arith), localVal_of_bytes B₃ (Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Plt),
      Ip₃.value] at F₄
    rw [F₄, St₃.maskW (by decide), F₂, F₁, BitVec.and_assoc, BitVec.and_assoc, mask32_and, mask32_and]
    exact congrArg _ (mask32_iff (by simp only [Bool.false_eq_true, ↓reduceIte, deriveChecks] <;> omega_arith))
  · have K : localVal base v₄ Impl.Dsa.Layout.t2 pLen = G ^ X % P :=
      (St₄.localVal_eq (by decide) (by omega_arith) (by decide) (.inr (by simp only [Impl.Dsa.Layout.t2]; omega_arith))).trans
        (localVal_of_bytes B₃ (Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Plt))
    have L : (Spec.Rsa.bytesAt v₄.mem (off base Impl.Dsa.Layout.t2) pLen).length = pLen := by
      simp [Spec.Rsa.bytesAt]
    have e := VG.Proof.Dsa.encodeBE_decodeBE (Spec.Rsa.bytesAt v₄.mem (off base Impl.Dsa.Layout.t2) pLen)
    rw [L] at e
    rw [← K]
    exact e.symm
  · exact ((R₁.trans (St₂.run (.inl ⟨rfl, rfl⟩))).trans (St₃.run (.inr ho))).trans (St₄.run (.inl ⟨rfl, rfl⟩))

end VG.Proof.Dsa.Arm
