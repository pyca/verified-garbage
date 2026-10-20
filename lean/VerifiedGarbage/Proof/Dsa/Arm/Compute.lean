module

import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCall
public import VerifiedGarbage.Impl.Dsa.Arm.SignVerify
public import VerifiedGarbage.Proof.Dsa.Arm.Verify
public import VerifiedGarbage.Proof.Dsa.Arm.Sign
import VerifiedGarbage.Proof.Framework.Omega

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
  have Qlt := operand_lt_of Iq
  have qlt : ∀ x, x % Q < 256 ^ qLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega)) Qlt
  have Lr : Impl.Dsa.Layout.r = 14720 := rfl
  have Ls : Impl.Dsa.Layout.s = 14752 := rfl
  simp only [SignVerify.signCompute, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (PublicValidation.call_ok Sc Ip Iq Ig Iy hP hPo hQ hQo) fun u₁ ⟨F₁, L₁, Rn₁⟩ => ?_)
  have r₁ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input u₁ base size p len v :=
    fun I => I.run Rn₁ (by omega) fits
  refine WP.seq (WP.mono (privateKey_ok (Sc.run Rn₁) (r₁ Ip) (r₁ Iq) (r₁ Ig) (r₁ Iy) (r₁ Ix) (r₁ Ik) hP hPo)
    fun u₂ ⟨F₂, K₂, Rn₂⟩ => ?_)
  have r₂ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input u₂ base size p len v :=
    fun I => (r₁ I).run Rn₂ (by omega) fits
  have L₂ : localVal base u₂ Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 := by
    rw [K₂ _ _ (by decide) (by simp only [Impl.Dsa.Layout.qMinusTwo, Impl.Dsa.Layout.t]; omega), L₁]
  refine WP.seq (WP.mono (sign_ok (Sc.run (Rn₁.trans Rn₂)) (r₂ Ip) (r₂ Iq) (r₂ Ig) (r₂ Ix) (r₂ Ik) (r₂ Id)
    (by rw [countValue_run Rn₂, countValue_run Rn₁, hc]) L₂ hP hPo hQ hQo) fun u₃ ⟨R₃, S₃, M₃, Rn₃⟩ => ?_)
  have Sc₃ := Sc.run ((Rn₁.trans Rn₂).trans Rn₃)
  refine WP.seq (WP.seq (WP.mono (zero_ok Sc₃.ws (by omega) Sc.wq
    (localReady (o := Impl.Dsa.Layout.r) (len := qLen) Sc₃.ws (by omega) (by omega) (by omega)) true)
    fun u₄ ⟨F₄, St₄⟩ => WP.mono (zero_ok (St₄.ws Sc₃.ws) (by omega) Sc.wq
      (localReady (o := Impl.Dsa.Layout.s) (len := qLen) (St₄.ws Sc₃.ws) (by omega) (by omega) (by omega)) true)
    fun u₅ ⟨F₅, St₅⟩ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩))
  · rw [local_operand Sc₃.ws (by omega), R₃] at F₄
    rw [local_operand (St₄.ws Sc₃.ws) (by omega), St₄.localVal_eq (by omega) (by omega) (by omega) (by omega),
      S₃] at F₅
    rw [F₅, F₄, M₃, F₂, F₁, BitVec.and_assoc, BitVec.and_assoc, BitVec.and_assoc, mask32_and, mask32_and,
      mask32_and]
    exact congrArg _ (mask32_iff (by simp only [↓reduceIte, signChecks, and_assoc]))
  · rw [St₅.localVal_eq (by omega) (by omega) (by omega) (by omega),
      St₄.localVal_eq (by omega) (by omega) (by omega) (by omega), R₃]
  · rw [St₅.localVal_eq (by omega) (by omega) (by omega) (by omega),
      St₄.localVal_eq (by omega) (by omega) (by omega) (by omega), S₃]
  · exact (((Rn₁.trans Rn₂).trans Rn₃).trans (St₄.run (.inl ⟨rfl, rfl⟩))).trans (St₅.run (.inl ⟨rfl, rfl⟩))

/-- Every check of a verification. -/
abbrev verifyChecks (P Q G Y R S D : Nat) : Prop :=
  publicChecks P Q G Y ∧ (0 < R ∧ R < Q) ∧ (0 < S ∧ S < Q) ∧ verifyValue P Q G Y R S D = R

theorem verifyCompute_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y R S D c : Nat}
    (Sc : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (Ir : Input s base size (.input .signature) qLen R) (Is : Input s base size .signatureS qLen S)
    (Id : Input s base size (.input .digest) c D) (hc : countValue base s Core.digestPrefix = c)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (SignVerify.verifyCompute pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (verifyChecks P Q G Y R S D) ∧ Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := Sc.lens
  have big := Sc.big
  have fits := Sc.fits
  have Lu : Impl.Dsa.Layout.u = 14816 := rfl
  have L2 : Impl.Dsa.Layout.qMinusTwo = 14912 := rfl
  simp only [SignVerify.verifyCompute, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (PublicValidation.call_ok Sc Ip Iq Ig Iy hP hPo hQ hQo) fun u₁ ⟨F₁, L₁, Rn₁⟩ => ?_)
  have r₁ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input u₁ base size p len v :=
    fun I => I.run Rn₁ (by omega) fits
  have Sc₁ := Sc.run Rn₁
  refine WP.seq (WP.seq (WP.mono (range_ok Sc₁.ws (by omega) Sc.wq (r₁ Iq).toReady (r₁ Ir).toReady false)
    fun u₂ ⟨F₂, St₂⟩ => WP.mono (range_ok (St₂.ws Sc₁.ws) (by omega) Sc.wq
      ((r₁ Iq).next Sc₁ St₂ (.inl ⟨rfl, rfl⟩)).toReady ((r₁ Is).next Sc₁ St₂ (.inl ⟨rfl, rfl⟩)).toReady false)
    fun u₃ ⟨F₃, St₃⟩ => ?_))
  rw [(r₁ Iq).value, (r₁ Ir).value] at F₂
  rw [((r₁ Iq).next Sc₁ St₂ (.inl ⟨rfl, rfl⟩)).value, ((r₁ Is).next Sc₁ St₂ (.inl ⟨rfl, rfl⟩)).value] at F₃
  have Sc₃ := (Sc₁.stage St₂).stage St₃
  have r₃ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input u₃ base size p len v :=
    fun I => ((r₁ I).next Sc₁ St₂ (.inl ⟨rfl, rfl⟩)).next (Sc₁.stage St₂) St₃ (.inl ⟨rfl, rfl⟩)
  have L₃ : localVal base u₃ Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 := by
    rw [St₃.localVal_eq (by decide) (by omega) (by omega) (by omega),
      St₂.localVal_eq (by decide) (by omega) (by omega) (by omega), L₁]
  have C₃ : countValue base u₃ Core.digestPrefix = c := by
    rw [countValue_stage St₃ (by omega), countValue_stage St₂ (by omega), countValue_run Rn₁, hc]
  refine WP.seq (WP.mono (verify_ok Sc₃ (r₃ Ip) (r₃ Iq) (r₃ Ig) (r₃ Iy) (r₃ Ir) (r₃ Is) (r₃ Id) C₃ L₃ hP hPo hQ hQo)
    fun u₄ ⟨V₄, M₄, Rn₄⟩ => ?_)
  have Sc₄ := Sc₃.run Rn₄
  refine WP.seq (WP.mono (equalValues_ok Sc₄.ws (by omega) Sc.wq
    (localReady (o := Impl.Dsa.Layout.u) Sc₄.ws (by omega) (by omega) (by omega)) ((r₃ Ir).run Rn₄ (by omega) fits).toReady)
    fun u₅ ⟨F₅, St₅⟩ => WP.block_nil ⟨?_, ?_⟩)
  · rw [local_operand Sc₄.ws (by omega), V₄, ((r₃ Ir).run Rn₄ (by omega) fits).value] at F₅
    rw [F₅, M₄, F₃, F₂, F₁, BitVec.and_assoc, BitVec.and_assoc, BitVec.and_assoc, mask32_and, mask32_and,
      mask32_and]
    exact congrArg _ (mask32_iff (by simp only [Bool.false_eq_true, ↓reduceIte, verifyChecks]))
  · exact ((((Rn₁.trans (St₂.run (.inl ⟨rfl, rfl⟩))).trans (St₃.run (.inl ⟨rfl, rfl⟩))).trans Rn₄)).trans
      (St₅.run (.inl ⟨rfl, rfl⟩))

end VG.Proof.Dsa.Arm
