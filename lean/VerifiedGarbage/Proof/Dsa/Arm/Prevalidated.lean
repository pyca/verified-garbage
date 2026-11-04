module

public import VerifiedGarbage.Impl.Dsa.Arm.Prevalidated
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.Proof.Dsa.Arm.Contract
public import VerifiedGarbage.Proof.Dsa.Arm.Env
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateEntry
public import VerifiedGarbage.Proof.Dsa.Arm.Compute
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
import VerifiedGarbage.Proof.Dsa.Arm.VerifyCorrect
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCall
import VerifiedGarbage.Proof.Dsa.Arm.Body
import VerifiedGarbage.Proof.Dsa.Arm.Shape
import VerifiedGarbage.Proof.Dsa.Arm.Install
import VerifiedGarbage.Proof.Dsa.Validation
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA public-key validation and prevalidated verification on 32-bit ARM: correctness

The contracts the proofs are written against: `validateArm`, the domain
check's (`checkArm`) with a whole public key, whose result is
`Spec.Dsa.validatePublicKeyBytes`; and `prevArm`, verification's
(`verifyArm`) for a key whose exact bytes validate.

`validate_correct`: `vg_dsa_validate_public_key` returns whether the key
validates. `prevalidated_correct`: `vg_dsa_verify_prevalidated` returns
`Spec.Dsa.verifyBytes`, since rebuilding q − 2 in place of the checks of the
domain and public value leaves out only checks that the precondition makes
hold. Both restore the registers the ABI preserves.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32 mask32_and)
open VG.Proof.X25519.Arm (Rest eval_eq wp_mov op2_imm)

/-! ## The contracts -/

/-- What `vg_dsa_validate_public_key` needs: `(key = r0, key_len = r1,
p_len = r2, q_len = r3, scratch = [sp], scratch_len = [sp + 4])`. -/
def validatePre (s : State) : Prop :=
  let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
  let scratch : Region := ⟨State.addr (arg s 0), (arg s 1).toNat * 8⟩
  let args : Region := ⟨State.addr s.sp, 8⟩
  s.sp.toNat + 8 ≤ 2 ^ 32 ∧ s.rd = [key, args] ∧ s.wr = [scratch] ∧
    key.Disjoint scratch ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (arg s 0).toNat + (arg s 1).toNat * 8 ≤ 2 ^ 32 ∧
    Spec.Dsa.lengthsValid (s.gpr .r2).toNat (s.gpr .r3).toNat ∧
    (s.gpr .r1).toNat = 3 * (s.gpr .r2).toNat + (s.gpr .r3).toNat ∧
    Spec.Dsa.scratchWords (s.gpr .r2).toNat ≤ (arg s 1).toNat

/-- The bytes of the key. -/
abbrev validateKey (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat

/-- The result of the validation in a state. -/
abbrev validateRes (s : State) : Bool :=
  Spec.Dsa.validatePublicKeyBytes (s.gpr .r2).toNat (s.gpr .r3).toNat (validateKey s)

/-- What validation may leak: the key. -/
abbrev validateLeak (s : State) : List Nat :=
  Spec.Dsa.publicBytesLeak (s.gpr .r2).toNat (s.gpr .r3).toNat (validateKey s)

def validateArm : Contract isa where
  pre := validatePre
  post s s' := (BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0)).toNat = if validateRes s then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ validateLeak s₁ = validateLeak s₂ ∧
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 2, arg s₁ i = arg s₂ i

/-- What `vg_dsa_verify_prevalidated` needs: `verifyPre`, and a key whose
exact bytes validate. -/
def prevPre (s : State) : Prop :=
  verifyPre s ∧ Spec.Dsa.validatePublicKeyBytes (s.gpr .r2).toNat (s.gpr .r3).toNat
    (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) = true

def prevArm : Contract isa where
  pre := prevPre
  post := verifyArm.post
  pub := verifyArm.pub

/-! ## Validation -/

/-- The key's components, at a state with the environment of validation. -/
theorem validateIn {s t : State} {base : Addr} {size : Nat} (h : validatePre s) (hb : State.addr (arg s 0) = base)
    (hsz : (arg s 1).toNat * 8 = size) (E : Env s base size (checkFields s) t) :
    Input t base size (.input .p) (s.gpr .r2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat)) ∧
      Input t base size (.input .q) (s.gpr .r3).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat)
          (s.gpr .r3).toNat)) ∧
      Input t base size (.input .g) (s.gpr .r2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 ((s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat)) ∧
      Input t base size (.input .y) (s.gpr .r2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 (2 * (s.gpr .r2).toNat + (s.gpr .r3).toNat))
          (s.gpr .r2).toNat)) := by
  subst hb hsz
  obtain ⟨_, hrd, _, dKS, _, fK, _, hv, hr1, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hz : 4960 ≤ (arg s 1).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  have kr : (⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have ip := input_of E (p := .input .p) (by decide : Impl.Dsa.Layout.Field.p ≠ .mask) (o := 0)
    (len := (s.gpr .r2).toNat)
    (by rw [BitVec.add_zero]; exact E.field (d := 64) (v := s.gpr .r0) (by simp)) kr fK (by omega_arith) (.inr rfl) dKS hz
  rw [BitVec.add_zero] at ip
  have cg := fun {a : Nat} {xs : List (BitVec 32)} (h : (xs.map BitVec.toNat).sum = a) =>
    (sum_ofNat (s.gpr .r0) xs).trans (congrArg (fun n => s.gpr .r0 + BitVec.ofNat 32 n) h)
  refine ⟨ip, input_of E (p := .input .q) (by decide : Impl.Dsa.Layout.Field.q ≠ .mask) ?_ kr fK (by omega_arith)
      (.inl (by omega_arith)) dKS hz,
    input_of E (p := .input .g) (by decide : Impl.Dsa.Layout.Field.g ≠ .mask) ?_ kr fK (by omega_arith)
      (.inl (by omega_arith)) dKS hz,
    input_of E (p := .input .y) (by decide : Impl.Dsa.Layout.Field.y ≠ .mask) ?_ kr fK (by omega_arith)
      (.inl (by omega_arith)) dKS hz⟩
  · exact (E.field (d := 68) (v := s.gpr .r0 + s.gpr .r2) (by simp)).trans
      (cg (xs := [s.gpr .r2]) (by simp))
  · exact (E.field (d := 72) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3) (by simp)).trans
      (cg (xs := [s.gpr .r2, s.gpr .r3]) (by simp))
  · exact (E.field (d := 76) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2) (by simp)).trans
      (cg (xs := [s.gpr .r2, s.gpr .r3, s.gpr .r2]) (by simp; omega_arith))

/-- Validation, by the checks the code makes. -/
theorem validateRes_eq {s : State} (h : validatePre s) :
    validateRes s = decide (shapeValid
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat))
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat)
          (s.gpr .r3).toNat)) ∧
      publicChecks
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat))
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat)
          (s.gpr .r3).toNat))
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 ((s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat))
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 (2 * (s.gpr .r2).toNat + (s.gpr .r3).toNat))
          (s.gpr .r2).toNat))) :=
  VG.Proof.Dsa.validatePublicKeyBytes_eq h.2.2.2.2.2.2.2.1
    (by simp only [validateKey, Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact h.2.2.2.2.2.2.2.2.1)
    (verifyKey _ _ (by have := h.2.2.2.2.2.2.2.2.1; omega_arith))

theorem validate_correct {s : State} (h : validatePre s) :
    WP isa Prevalidated.validate s fun t => abiPreserved s t ∧ validateArm.post s t := by
  obtain ⟨hsp, hrd, hwr, _, _, _, hsb, hv, _, hsw⟩ := id h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 128 * (s.gpr .r2).toNat ≤ (arg s 1).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  have spec := validateRes_eq h
  simp only [Prevalidated.validate, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (checkEntry_of hsp (by rw [hrd]; simp) hwr hsb hv hsw) fun u I => ?_)
  have E₀ := Env.of_installed I (by omega_arith)
  have fok := checkFields_ok s
  refine WP.seq (genDispatch_ok Prevalidated.validateSized _ E₀.ws (by omega_arith) (genWidths_mem hv) (by decide)
    (by rw [E₀.field (d := 100) (v := s.gpr .r2) (by simp)]) (by rw [E₀.field (d := 104) (v := s.gpr .r3) (by simp)])
    fun t₁ R₁ M₁ => ?_)
  have E₁ := E₀.of_mem R₁ (by decide) M₁
  have hz : 4960 ≤ (arg s 1).toNat * 8 := by omega_arith
  obtain ⟨Ip₁, Iq₁, -, -⟩ := validateIn h rfl rfl E₁
  unfold Prevalidated.validateSized
  refine WP.seq (WP.mono (check_ok E₁.ws hz wp wq Ip₁.toReady Iq₁.toReady Ip₁.value Iq₁.value)
    fun t₂ ⟨Z, M, _, R₂, O₂⟩ => ?_)
  have E₂ := E₁.keep fok R₂ (by decide) O₂ (fun r hr => by
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith)
  refine WP.ite t₂.z (eval_eq _) (fun ht => ?_) (fun hf => ?_)
  · -- A rejected shape.
    have nv := of_decide_eq_true (Z ▸ ht)
    refine wp_mov (op2_imm (by decide)) fun t₃ v₃ => WP.block_nil ?_
    refine finish_ok (E₂.ws.of_upd v₃ (by decide)) (by omega_arith) (fun i hi => by rw [v₃.mem]; exact E₂.saved i hi)
      (v₃.sp.trans E₂.sp) fun u A r0 _ => ⟨A, ?_⟩
    have : validateRes s = false := by
      rw [spec]
      exact decide_eq_false fun hc => nv hc.1
    show (BitVec.setWidth 32 (u.gpr .r1 ++ u.gpr .r0)).toNat = if validateRes s = true then 1 else 0
    rw [this, BitVec.setWidth_append_eq_right, r0, v₃.gpr]
    rfl
  · have valid : shapeValid _ _ := Classical.not_not.mp (of_decide_eq_false (Z ▸ hf))
    obtain ⟨Ip, Iq, Ig, Iy⟩ := validateIn h rfl rfl E₂
    obtain ⟨hP, hPo, hQ, hQo⟩ := shape_bounds valid
    have hm : maskW (State.addr (arg s 0)) t₂ = BitVec.allOnes 32 := by
      rw [M]; unfold mask32; split
      · rfl
      · contradiction
    refine WP.seq (WP.mono (PublicValidation.call_ok ⟨E₂.ws, by omega_arith, wp, wq, qp, q32⟩ Ip Iq Ig Iy hP hPo hQ hQo)
      fun t₃ ⟨F₃, _, Rn₃⟩ => ?_)
    have E₃ := E₂.keep fok Rn₃.rest (by decide) Rn₃.mem (fun r hr => by
      simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> omega_arith)
    rw [hm, BitVec.allOnes_and] at F₃
    refine WP.mono (result_ok E₃.ws (by omega_arith) _ F₃) fun t₄ ⟨r0₄, R₄, M₄⟩ => ?_
    refine finish_ok (E₃.ws.of_rest R₄ (by decide)) (by omega_arith) (fun i hi => by rw [M₄]; exact E₃.saved i hi)
      (R₄.sp.trans E₃.sp) fun u A r0 _ => ⟨A, ?_⟩
    show (BitVec.setWidth 32 (u.gpr .r1 ++ u.gpr .r0)).toNat = if validateRes s = true then 1 else 0
    rw [status_toNat (r0.trans r0₄), spec]
    simp only [decide_eq_true_eq, valid, true_and]

/-! ## Prevalidated verification -/

/-- The prevalidated verifier's body: q − 2, the checks of the signature,
and the result, for a key whose public checks hold. -/
theorem prevBody_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y R S D c : Nat}
    (Sc : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (Ir : Input s base size (.input .signature) qLen R) (Is : Input s base size .signatureS qLen S)
    (Id : Input s base size (.input .digest) c D) (hc : countValue base s Core.digestPrefix = c)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1)
    (hm : maskW base s = BitVec.allOnes 32) (pub : publicChecks P Q G Y) :
    WP isa (Prevalidated.body pLen qLen) s fun t =>
      t.gpr .r0 = (if verifyChecks P Q G Y R S D then 1 else 0) ∧ Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := Sc.lens
  have big := Sc.big
  have fits := Sc.fits
  have Qlt := operand_lt_of Iq
  have L2 : Impl.Dsa.Layout.qMinusTwo = 14912 := rfl
  have ho : 4960 ≤ Impl.Dsa.Layout.qMinusTwo ∧ Impl.Dsa.Layout.qMinusTwo + qLen ≤ 15712 := by omega
  unfold Prevalidated.body Prevalidated.compute Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.seq (WP.mono (minus_ok (output := Impl.Dsa.Layout.qMinusTwo) Sc.ws (by omega) Sc.wq Iq.toReady
    Iq.value (by omega) hQo (by omega) (by decide) (by decide) (by omega) (by decide)) fun u₁ ⟨B₁, St₁⟩ => ?_))
  have r₁ : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input u₁ base size p len v :=
    fun I => I.next Sc St₁ (.inr ho)
  have Sc₁ := Sc.stage St₁
  refine WP.mono (verifyTail_ok Sc₁ (r₁ Ip) (r₁ Iq) (r₁ Ig) (r₁ Iy) (r₁ Ir) (r₁ Is) (r₁ Id)
    ((countValue_stage St₁ (by omega)).trans hc) (localVal_of_bytes B₁ (by omega)) hP hPo hQ hQo)
    fun u ⟨F, Rn⟩ => ?_
  have hm' : maskW base u = mask32 (verifyChecks P Q G Y R S D) := by
    rw [F, St₁.maskW (by omega), hm, BitVec.allOnes_and]
    exact mask32_iff ⟨fun h => ⟨pub, h⟩, fun h => h.2⟩
  exact WP.mono (result_ok (Rn.ws Sc₁.ws) (by omega) _ hm') fun t ⟨r0, Rt, Mt⟩ =>
    ⟨r0, ((St₁.run (.inr ho)).trans Rn).trans ⟨Rt.mono (by decide), fun x _ => by rw [Mt]⟩⟩

/-- The checks that the key's validation makes hold. -/
theorem prevPre_checks {s : State} (h : prevPre s) :
    shapeValid (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat))
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat)
          (s.gpr .r3).toNat)) ∧
      publicChecks
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat))
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat)
          (s.gpr .r3).toNat))
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 ((s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat))
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 (2 * (s.gpr .r2).toNat + (s.gpr .r3).toNat))
          (s.gpr .r2).toNat)) := by
  have hr1 := h.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have keyLen : (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat).length =
      3 * (s.gpr .r2).toNat + (s.gpr .r3).toNat := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hr1
  exact of_decide_eq_true ((VG.Proof.Dsa.validatePublicKeyBytes_eq h.1.2.2.2.2.2.2.2.2.2.2.2.1 keyLen
    (verifyKey _ _ (by omega_arith))).symm.trans h.2)

theorem prevalidated_correct {s : State} (h : prevPre s) :
    WP isa Prevalidated.verify s fun t => abiPreserved s t ∧ verifyArm.post s t := by
  have checks := prevPre_checks h
  obtain ⟨h, -⟩ := h
  obtain ⟨hsp, hrd, hwr, dKS, dSS, dDS, _, fK, fS, fD, fW, hv, hr1, hs1, hsw⟩ := id h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 128 * (s.gpr .r2).toNat ≤ (arg s 5).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  have keyLen : (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat).length =
      3 * (s.gpr .r2).toNat + (s.gpr .r3).toNat := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hr1
  simp only [Prevalidated.verify, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (verifyEntry_ok h) fun u I => ?_)
  have E₀ := Env.of_installed I (by omega_arith)
  have fok := verifyFields_ok s
  refine WP.seq (genDispatch_ok Prevalidated.sized _ E₀.ws (by omega_arith) (genWidths_mem hv) (by decide)
    (by rw [E₀.field (d := 100) (v := s.gpr .r2) (by simp)]) (by rw [E₀.field (d := 104) (v := s.gpr .r3) (by simp)])
    fun t₁ R₁ M₁ => ?_)
  have E₁ := E₀.of_mem R₁ (by decide) M₁
  have hz : 4960 ≤ (arg s 5).toNat * 8 := by omega_arith
  obtain ⟨Ip₁, Iq₁, -, -⟩ := verifyKeyIn h rfl rfl E₁
  unfold Prevalidated.sized
  refine WP.seq (WP.mono (check_ok E₁.ws hz wp wq Ip₁.toReady Iq₁.toReady Ip₁.value Iq₁.value)
    fun t₂ ⟨Z, M, D₂, R₂, O₂⟩ => ?_)
  have E₂ := E₁.keep fok R₂ (by decide) O₂ (fun r hr => by
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith)
  refine WP.ite t₂.z (eval_eq _) (fun ht => ?_) (fun hf => ?_)
  · -- Unreachable for a validated key, but the code rejects the shape as the verifier does.
    have nv := of_decide_eq_true (Z ▸ ht)
    have rej : verifyRes s = false :=
      VG.Proof.Dsa.verifyBytes_invalid_shape (by rw [verifyKey _ _ (by omega_arith)]; exact nv)
    simp only [Entry.failure, Bool.false_eq_true, ↓reduceIte]
    refine wp_mov (op2_imm (by decide)) fun t₃ v₃ => WP.block_nil ?_
    refine finish_ok (E₂.ws.of_upd v₃ (by decide)) (by omega_arith) (fun i hi => by rw [v₃.mem]; exact E₂.saved i hi)
      (v₃.sp.trans E₂.sp) fun u A r0 M => ⟨A, ?_⟩
    show (BitVec.setWidth 32 (u.gpr .r1 ++ u.gpr .r0)).toNat = _
    rw [BitVec.setWidth_append_eq_right, r0, v₃.gpr, rej]
    rfl
  · have valid : shapeValid _ _ := Classical.not_not.mp (of_decide_eq_false (Z ▸ hf))
    have hm : maskW (State.addr (arg s 4)) t₂ = BitVec.allOnes 32 := by
      rw [M]; unfold mask32; split
      · rfl
      · contradiction
    obtain ⟨Ip, Iq, Ig, Iy⟩ := verifyKeyIn h rfl rfl E₂
    have Ir := verifySigIn h rfl rfl E₂
    have Is := verifySigSIn h rfl rfl E₂
    have Id := verifyDigestIn h rfl rfl E₂ (Nat.min_le_left (arg s 3).toNat (qWidth (Spec.Dsa.decodeBE
      (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat) (s.gpr .r3).toNat))))
    have hc : countValue (State.addr (arg s 4)) t₂ Core.digestPrefix = min (arg s 3).toNat (qWidth
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat) (s.gpr .r3).toNat))) := by
      refine D₂.trans ?_
      rw [E₁.field (d := 108) (v := arg s 3) (by simp)]
    rw [VG.Proof.Dsa.bytesAt_prefix, qWidth_of_shape valid] at Id
    rw [qWidth_of_shape valid] at hc
    obtain ⟨hP, hPo, hQ, hQo⟩ := shape_bounds valid
    refine WP.mono (prevBody_ok ⟨E₂.ws, by omega_arith, wp, wq, qp, q32⟩ Ip Iq Ig Iy Ir Is Id hc hP hPo hQ hQo hm
      checks.2) fun t₃ ⟨Z₃, Rn₃⟩ => ?_
    have E₃ := E₂.keep fok Rn₃.rest (by decide) Rn₃.mem (fun r hr => by
      simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> omega_arith)
    have e := verifyBytes_eq s.mem (State.addr (arg s 0))
        (Spec.Rsa.bytesAt s.mem (State.addr (arg s 2)) (arg s 3).toNat) hv valid keyLen (verifyKey _ _ (by omega_arith))
    rw [← hs1] at e
    refine finish_ok E₃.ws (by omega_arith) E₃.saved E₃.sp fun u A r0 M => ⟨A, ?_⟩
    show (BitVec.setWidth 32 (u.gpr .r1 ++ u.gpr .r0)).toNat = _
    rw [BitVec.setWidth_append_eq_right, r0, Z₃, show verifyRes s = _ from e]
    split <;> simp_all

end VG.Proof.Dsa.Arm
