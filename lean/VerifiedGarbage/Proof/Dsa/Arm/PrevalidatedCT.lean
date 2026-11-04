module

public import VerifiedGarbage.Proof.Dsa.Arm.Prevalidated
public import VerifiedGarbage.Proof.Dsa.Arm.KeyTrace
import VerifiedGarbage.Proof.Dsa.Arm.GenerateTrace
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
import VerifiedGarbage.Proof.Dsa.Arm.VerifyCorrect
import VerifiedGarbage.Proof.Dsa.Arm.VerifyCT
import VerifiedGarbage.Proof.Dsa.Arm.BodyTrace
import VerifiedGarbage.Proof.Dsa.Arm.ValidateTrace
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCall
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Dsa.Arm.ShapeTrace
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.OutputBytes

-- separate module: the constant-time proofs cost more than their imports, and the
-- satisfiability witnesses of `PrevalidatedVerified.lean` should not re-check them.

/-!
# DSA public-key validation and prevalidated verification on 32-bit ARM: constant time

Validation's inputs are all public: as the domain check's
(`GenerateCheckCT.lean`), two runs with the same arguments and key compute on
the same values, through the same pointers. The prevalidated verifier leaks
what the verifier does (`VerifyCT.lean`): the key and the result.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest eval_eq)
open VG.Proof.Ecdsa.Arm (mask32)

/-! ## Validation -/

/-- The key's operands. -/
def validateIns (pLen qLen : Nat) : List (Pointer × Nat) :=
  [(.input .p, pLen), (.input .q, qLen), (.input .g, pLen), (.input .y, pLen)]

/-- Their values. -/
def validateVal (s : State) : Pointer → Nat
  | .input .p => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat)
  | .input .q => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat)
      (s.gpr .r3).toNat)
  | .input .g => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (State.addr (s.gpr .r0) + BitVec.ofNat 64 ((s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat)
  | .input .y => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (State.addr (s.gpr .r0) + BitVec.ofNat 64 (2 * (s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat)
  | _ => 0

theorem validateCtx {s t : State} {base : Addr} {size : Nat} (h : validatePre s)
    (hb : State.addr (arg s 0) = base) (hsz : (arg s 1).toNat * 8 = size)
    (E : Env s base size (checkFields s) t) :
    Ctx base size (s.gpr .r2).toNat (s.gpr .r3).toNat (((s.gpr .r2).toNat + 7) / 8) (((s.gpr .r3).toNat + 7) / 8)
      (validateIns (s.gpr .r2).toNat (s.gpr .r3).toNat) (validateVal s) t := by
  have hv := h.2.2.2.2.2.2.2.1
  have hsw := h.2.2.2.2.2.2.2.2.2
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have big : 15712 < size := by rw [← hsz]; unfold Spec.Dsa.scratchWords at hsw; omega
  obtain ⟨Ip, Iq, Ig, Iy⟩ := validateIn h hb hsz E
  refine ⟨⟨E.ws, big, wp, wq, qp, q32⟩, fun i hi => ?_⟩
  simp only [validateIns, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact Ip
  · exact Iq
  · exact Ig
  · exact Iy

theorem validatePtrs {s t : State} {base : Addr} {size pLen qLen : Nat} (E : Env s base size (checkFields s) t) :
    ∀ i ∈ validateIns pLen qLen, pointerValue base t i.1 =
      match i.1 with
      | .input .p => s.gpr .r0
      | .input .q => s.gpr .r0 + s.gpr .r2
      | .input .g => s.gpr .r0 + s.gpr .r2 + s.gpr .r3
      | _ => s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2 := by
  intro i hi
  simp only [validateIns, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact E.field (d := 64) (v := s.gpr .r0) (by simp)
  · exact E.field (d := 68) (v := s.gpr .r0 + s.gpr .r2) (by simp)
  · exact E.field (d := 72) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3) (by simp)
  · exact E.field (d := 76) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2) (by simp)

/-- The key's bytes at an offset, the same in two runs that leak the same. -/
theorem validate_bytes {s₁ s₂ : State} (h₁ : validatePre s₁) (hl : validateLeak s₁ = validateLeak s₂)
    (hr0 : s₁.gpr .r0 = s₂.gpr .r0) (hr1 : s₁.gpr .r1 = s₂.gpr .r1) (hr2 : s₁.gpr .r2 = s₂.gpr .r2)
    (hr3 : s₁.gpr .r3 = s₂.gpr .r3) {o l : Nat} (hol : o + l ≤ (s₁.gpr .r1).toNat) :
    Spec.Rsa.bytesAt s₁.mem (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 o) l =
      Spec.Rsa.bytesAt s₂.mem (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 o) l := by
  have r1 := h₁.2.2.2.2.2.2.2.2.1
  simp only [validateLeak, validateKey, Spec.Dsa.publicBytesLeak] at hl
  rw [← hr0, ← hr1, ← hr2, ← hr3] at hl
  have E := List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h) |>.mp hl
  rw [← VG.Proof.Dsa.bytesAt_prefix, ← VG.Proof.Dsa.bytesAt_prefix,
    show min (s₁.gpr .r1).toNat (3 * (s₁.gpr .r2).toNat + (s₁.gpr .r3).toNat) = (s₁.gpr .r1).toNat by omega] at E
  rw [← VG.Proof.Dsa.bytesAt_slice _ _ hol, ← VG.Proof.Dsa.bytesAt_slice _ _ hol, E]

theorem validate_constantTime : ConstantTime isa validateArm.pre validateArm.pub Prevalidated.validate := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ pub => ?_
  obtain ⟨hsp, hl, hr0, hr1, hr2, hr3, ha⟩ := pub
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  obtain ⟨sp₁, rd₁, wr₁, _, dSA₁, _, sb₁, hv, hpl, hsw⟩ := id h₁
  obtain ⟨sp₂, rd₂, wr₂, _, dSA₂, _, sb₂, hv₂, _, hsw₂⟩ := id h₂
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 128 * (s₁.gpr .r2).toNat ≤ (arg s₁ 1).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  have hb₂ : State.addr (arg s₂ 0) = State.addr (arg s₁ 0) := by rw [a0]
  have hz₂ : (arg s₂ 1).toNat * 8 = (arg s₁ 1).toNat * 8 := by rw [a1]
  simp only [Prevalidated.validate, Core.sequence, List.foldr]
  refine SameTrace.seq (SameTrace.of_relCT (entry_relCT 8 _ rfl) (agree_args (n := 2) hsp (by omega) ha
      (fun r hr => by
        rw [wr₁] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact dSA₁.symm)
      (fun r hr => by
        rw [wr₂] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact dSA₂.symm)))
    (WP.mono (checkEntry_of sp₁ (by rw [rd₁]; simp) wr₁ sb₁ hv hsw) fun u I => Env.of_installed I (by omega))
    (WP.mono (checkEntry_of sp₂ (by rw [rd₂]; simp) wr₂ sb₂ hv₂ hsw₂) fun u I => by
      have E := Env.of_installed I (by rw [hz₂]; omega)
      rwa [hb₂, hz₂] at E)
    fun u₁ u₂ E₁ E₂ => ?_
  refine genDispatch_trace Prevalidated.validateSized _ E₁.ws E₂.ws (by omega) (by omega) (genWidths_mem hv)
    (by decide) (by rw [E₁.field (d := 100) (v := s₁.gpr .r2) (by simp)])
    (by rw [E₁.field (d := 104) (v := s₁.gpr .r3) (by simp)])
    (by rw [E₂.field (d := 100) (v := s₂.gpr .r2) (by simp), hr2])
    (by rw [E₂.field (d := 104) (v := s₂.gpr .r3) (by simp), hr3])
    fun t₁ t₂ R₁ M₁ R₂ M₂ => ?_
  have F₁ := E₁.of_mem R₁ (by decide) M₁
  have F₂ := E₂.of_mem R₂ (by decide) M₂
  have hz : 4960 ≤ (arg s₁ 1).toNat * 8 := by omega
  have C₁ := validateCtx h₁ rfl rfl F₁
  have C₂ := validateCtx h₂ hb₂ hz₂ F₂
  rw [← hr2, ← hr3] at C₂
  have pe : ∀ {u₁ u₂ : State} (G₁ : Env s₁ (State.addr (arg s₁ 0)) ((arg s₁ 1).toNat * 8) (checkFields s₁) u₁)
      (G₂ : Env s₂ (State.addr (arg s₁ 0)) ((arg s₁ 1).toNat * 8) (checkFields s₂) u₂),
      ∀ i ∈ validateIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat, PtrEq (State.addr (arg s₁ 0)) u₁ u₂ i.1 := by
    intro u₁ u₂ G₁ G₂ i hi
    unfold PtrEq
    rw [validatePtrs G₁ i hi, validatePtrs (pLen := (s₁.gpr .r2).toNat) (qLen := (s₁.gpr .r3).toNat) G₂ i hi,
      hr0, hr2, hr3]
  -- Both runs see the same key.
  have key := fun {o l : Nat} (h : o + l ≤ (s₁.gpr .r1).toNat) =>
    validate_bytes h₁ hl hr0 hr1 hr2 hr3 (o := o) (l := l) h
  have Vp : validateVal s₂ (.input .p) = validateVal s₁ (.input .p) := by
    have k := key (o := 0) (l := (s₁.gpr .r2).toNat) (by omega)
    rw [BitVec.add_zero] at k
    simp only [validateVal]; rw [← hr0, ← hr2, k]
  have Vq : validateVal s₂ (.input .q) = validateVal s₁ (.input .q) := by
    simp only [validateVal]; rw [← hr0, ← hr2, ← hr3, key (by omega)]
  have mp : (.input .p, (s₁.gpr .r2).toNat) ∈ validateIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat := by
    simp [validateIns]
  have mq : (.input .q, (s₁.gpr .r3).toNat) ∈ validateIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat := by
    simp [validateIns]
  have mg : (.input .g, (s₁.gpr .r2).toNat) ∈ validateIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat := by
    simp [validateIns]
  have my : (.input .y, (s₁.gpr .r2).toNat) ∈ validateIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat := by
    simp [validateIns]
  have Pe : operand (State.addr (arg s₁ 0)) t₁ (.input .p) (s₁.gpr .r2).toNat =
      operand (State.addr (arg s₁ 0)) t₂ (.input .p) (s₁.gpr .r2).toNat := by
    rw [(C₁.inp mp).value, (C₂.inp mp).value, Vp]
  have Qe : operand (State.addr (arg s₁ 0)) t₁ (.input .q) (s₁.gpr .r3).toNat =
      operand (State.addr (arg s₁ 0)) t₂ (.input .q) (s₁.gpr .r3).toNat := by
    rw [(C₁.inp mq).value, (C₂.inp mq).value, Vq]
  unfold Prevalidated.validateSized
  refine SameTrace.assoc_left (SameTrace.seq (check_trace F₁.ws F₂.ws hz hz wp wq (C₁.inp mp).toReady
      (C₂.inp mp).toReady (C₁.inp mq).toReady (C₂.inp mq).toReady (pe F₁ F₂ _ mp) (pe F₁ F₂ _ mq))
    (check_ok F₁.ws hz wp wq (C₁.inp mp).toReady (C₁.inp mq).toReady rfl rfl)
    (check_ok F₂.ws hz wp wq (C₂.inp mp).toReady (C₂.inp mq).toReady rfl rfl)
    fun v₁ v₂ ⟨Z₁, K₁, _, S₁, O₁⟩ ⟨Z₂, K₂, _, S₂, O₂⟩ => ?_)
  have kee : ∀ r ∈ shapeRanges, r.1 + r.2 ≤ (arg s₁ 1).toNat * 8 ∧
      (r.1 + r.2 ≤ 64 ∨ 164 ≤ r.1 ∨ (112 ≤ r.1 ∧ r.1 + r.2 ≤ 128)) := fun r hr => by
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega
  have G₁ := F₁.keep (checkFields_ok s₁) S₁ (by decide) O₁ kee
  have G₂ := F₂.keep (checkFields_ok s₂) S₂ (by decide) O₂ kee
  refine SameTrace.seq_ite (by rw [eval_eq, eval_eq, Z₁, Z₂, Pe, Qe]) (fun _ => ?_) (fun hf => ?_)
  · exact SameTrace.of_relCT (RelCT.seq (block_relCT_T0 _ rfl) (RelCT.seq (block_relCT_T0 _ rfl)
      (RelCT.block_nil (Q := fun _ _ => True) fun _ _ _ => trivial))) (agree0 G₁.ws G₂.ws)
  · have valid : shapeValid (operand (State.addr (arg s₁ 0)) t₁ (.input .p) (s₁.gpr .r2).toNat)
        (operand (State.addr (arg s₁ 0)) t₁ (.input .q) (s₁.gpr .r3).toNat) := by
      rw [eval_eq, Z₁] at hf
      exact Classical.not_not.mp (of_decide_eq_false (Option.some.inj hf))
    rw [(C₁.inp mp).value, (C₁.inp mq).value] at valid
    have B₁ := shape_bounds valid
    have Dm₁ : DomainOk (validateVal s₁ (.input .p)) (validateVal s₁ (.input .q)) :=
      ⟨B₁.1, B₁.2.1, B₁.2.2.1, B₁.2.2.2⟩
    have Dm₂ : DomainOk (validateVal s₂ (.input .p)) (validateVal s₂ (.input .q)) := by rw [Vp, Vq]; exact Dm₁
    have D₁ := validateCtx h₁ rfl rfl G₁
    have D₂ := validateCtx h₂ hb₂ hz₂ G₂
    rw [← hr2, ← hr3] at D₂
    have X : Pair (State.addr (arg s₁ 0)) ((arg s₁ 1).toNat * 8) ((arg s₁ 1).toNat * 8) (s₁.gpr .r2).toNat
        (s₁.gpr .r3).toNat (((s₁.gpr .r2).toNat + 7) / 8) (((s₁.gpr .r3).toNat + 7) / 8)
        (validateIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat) (validateVal s₁) (validateVal s₂) v₁ v₂ :=
      ⟨D₁, D₂, pe G₁ G₂⟩
    exact SameTrace.assoc_left (SameTrace.seq (PublicValidation.call_trace X mp mq mg my Dm₁ Dm₂)
      (PublicValidation.call_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) (X.C₁.inp my)
        Dm₁.hP Dm₁.hPo Dm₁.hQ Dm₁.hQo)
      (PublicValidation.call_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) (X.C₂.inp my)
        Dm₂.hP Dm₂.hPo Dm₂.hQ Dm₂.hQo)
      fun w₁ w₂ ⟨_, _, Rn₁⟩ ⟨_, _, Rn₂⟩ => SameTrace.of_relCT (RelCT.seq result_relCT
        (RelCT.seq (block_relCT_T0 _ rfl) (RelCT.block_nil (Q := fun _ _ => True) fun _ _ _ => trivial)))
        (agree0 (G₁.ws.of_rest Rn₁.rest (by decide)) (G₂.ws.of_rest Rn₂.rest (by decide))))

/-! ## Prevalidated verification -/

theorem prevBody_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ c : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (my : (.input .y, pLen) ∈ ins) (mr : (.input .signature, qLen) ∈ ins) (ms : (.signatureS, qLen) ∈ ins)
    (md : (.input .digest, c) ∈ ins)
    (hc₁ : countValue base s₁ Core.digestPrefix = c) (hc₂ : countValue base s₂ Core.digestPrefix = c)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Prevalidated.body pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have L2 : Impl.Dsa.Layout.qMinusTwo = 14912 := rfl
  have ho : 4960 ≤ Impl.Dsa.Layout.qMinusTwo ∧ Impl.Dsa.Layout.qMinusTwo + qLen ≤ 15712 := by omega
  have Q₁ := operand_lt_of (X.C₁.inp mq)
  have Q₂ := operand_lt_of (X.C₂.inp mq)
  have hQ₁ := D₁.hQ
  have hQ₂ := D₂.hQ
  unfold Prevalidated.body Prevalidated.compute Core.sequence
  dsimp only [List.foldr]
  refine SameTrace.assoc_left (SameTrace.seq (minus_trace (amount := 2) (output := Impl.Dsa.Layout.qMinusTwo)
      (X.C₁.opPre mq X.C₁.S.wq (by omega) D₁.hQo) (X.C₂.opPre mq X.C₁.S.wq (by omega) D₂.hQo) (X.E _ mq))
    (minus_ok (output := Impl.Dsa.Layout.qMinusTwo) X.C₁.S.ws (by omega) X.C₁.S.wq (X.C₁.inp mq).toReady
      (X.C₁.inp mq).value (by omega) D₁.hQo (by omega) (by decide) (by decide) (by omega) (by decide))
    (minus_ok (output := Impl.Dsa.Layout.qMinusTwo) X.C₂.S.ws (by omega) X.C₁.S.wq (X.C₂.inp mq).toReady
      (X.C₂.inp mq).value (by omega) D₂.hQo (by omega) (by decide) (by decide) (by omega) (by decide))
    fun u₁ u₂ ⟨B₁, St₁⟩ ⟨B₂, St₂⟩ => ?_)
  have X₁ := X.run (St₁.run (.inr ho)) (St₂.run (.inr ho))
  exact SameTrace.seq (verifyTail_trace X₁ mp mq mg my mr ms md
      ((countValue_stage St₁ (by omega)).trans hc₁) ((countValue_stage St₂ (by omega)).trans hc₂)
      (localVal_of_bytes B₁ (by omega)) (localVal_of_bytes B₂ (by omega)) D₁ D₂)
    (verifyTail_ok X₁.C₁.S (X₁.C₁.inp mp) (X₁.C₁.inp mq) (X₁.C₁.inp mg) (X₁.C₁.inp my) (X₁.C₁.inp mr)
      (X₁.C₁.inp ms) (X₁.C₁.inp md) ((countValue_stage St₁ (by omega)).trans hc₁) (localVal_of_bytes B₁ (by omega))
      D₁.hP D₁.hPo D₁.hQ D₁.hQo)
    (verifyTail_ok X₁.C₂.S (X₁.C₂.inp mp) (X₁.C₂.inp mq) (X₁.C₂.inp mg) (X₁.C₂.inp my) (X₁.C₂.inp mr)
      (X₁.C₂.inp ms) (X₁.C₂.inp md) ((countValue_stage St₂ (by omega)).trans hc₂) (localVal_of_bytes B₂ (by omega))
      D₂.hP D₂.hPo D₂.hQ D₂.hQo)
    fun _ _ ⟨_, A₁⟩ ⟨_, A₂⟩ => SameTrace.of_relCT result_relCT (agree0 (A₁.ws X₁.C₁.S.ws) (A₂.ws X₁.C₂.S.ws))

theorem prevalidated_constantTime : ConstantTime isa prevArm.pre prevArm.pub Prevalidated.verify := by
  refine SameTrace.constantTime fun s₁ s₂ h₁' h₂' pub => ?_
  have pc₁ := (prevPre_checks h₁').2
  have pc₂ := (prevPre_checks h₂').2
  have h₁ := h₁'.1
  have h₂ := h₂'.1
  obtain ⟨hsp, hl, hr0, hr1, hr2, hr3, ha⟩ := pub
  have a0 := ha 0 (by decide)
  have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide)
  have a4 := ha 4 (by decide)
  have a5 := ha 5 (by decide)
  obtain ⟨sp₁, _, wr₁, _, _, _, dSA₁, _, _, _, fW₁, hv, r1₁, _, hsw⟩ := id h₁
  obtain ⟨_, _, wr₂, _, _, _, dSA₂, _, _, _, _, _, _, _, _⟩ := id h₂
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 128 * (s₁.gpr .r2).toNat ≤ (arg s₁ 5).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  have hb₂ : State.addr (arg s₂ 4) = State.addr (arg s₁ 4) := by rw [a4]
  have hz₂ : (arg s₂ 5).toNat * 8 = (arg s₁ 5).toNat * 8 := by rw [a5]
  simp only [Prevalidated.verify, Core.sequence, List.foldr]
  refine SameTrace.seq (SameTrace.of_relCT (entry_relCT 24 _ rfl) (agree_args (n := 6) hsp (by omega_arith) ha
      (fun r hr => by
        rw [wr₁] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact dSA₁.symm)
      (fun r hr => by
        rw [wr₂] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact dSA₂.symm)))
    (WP.mono (verifyEntry_ok h₁) fun u I => Env.of_installed I (by omega_arith))
    (WP.mono (verifyEntry_ok h₂) fun u I => by
      have E := Env.of_installed I (by rw [hz₂]; omega_arith)
      rwa [hb₂, hz₂] at E)
    fun u₁ u₂ E₁ E₂ => ?_
  refine genDispatch_trace Prevalidated.sized _ E₁.ws E₂.ws (by omega_arith) (by omega_arith) (genWidths_mem hv)
    (by decide) (by rw [E₁.field (d := 100) (v := s₁.gpr .r2) (by simp)])
    (by rw [E₁.field (d := 104) (v := s₁.gpr .r3) (by simp)])
    (by rw [E₂.field (d := 100) (v := s₂.gpr .r2) (by simp), hr2])
    (by rw [E₂.field (d := 104) (v := s₂.gpr .r3) (by simp), hr3])
    fun t₁ t₂ R₁ M₁ R₂ M₂ => ?_
  have F₁ := E₁.of_mem R₁ (by decide) M₁
  have F₂ := E₂.of_mem R₂ (by decide) M₂
  have hz : 4960 ≤ (arg s₁ 5).toNat * 8 := by omega_arith
  obtain ⟨Ip₁, Iq₁, -, -⟩ := verifyKeyIn h₁ rfl rfl F₁
  obtain ⟨Ip₂, Iq₂, -, -⟩ := verifyKeyIn h₂ hb₂ hz₂ F₂
  have Rp₂ : Ready t₂ (State.addr (arg s₁ 4)) (.input .p) (s₁.gpr .r2).toNat := by rw [hr2]; exact Ip₂.toReady
  have Rq₂ : Ready t₂ (State.addr (arg s₁ 4)) (.input .q) (s₁.gpr .r3).toNat := by rw [hr3]; exact Iq₂.toReady
  have pe : ∀ {u₁ u₂ : State} (G₁ : Env s₁ (State.addr (arg s₁ 4)) ((arg s₁ 5).toNat * 8) (verifyFields s₁) u₁)
      (G₂ : Env s₂ (State.addr (arg s₁ 4)) ((arg s₁ 5).toNat * 8) (verifyFields s₂) u₂) {c : Nat},
      ∀ i ∈ verifyIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat c, PtrEq (State.addr (arg s₁ 4)) u₁ u₂ i.1 := by
    intro u₁ u₂ G₁ G₂ c i hi
    unfold PtrEq
    rw [verifyPtrs G₁ i hi, verifyPtrs (pLen := (s₁.gpr .r2).toNat) (qLen := (s₁.gpr .r3).toNat) (c := c) G₂ i hi]
    simp only [verifyIns, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [verifyPtr, hr0, hr2, hr3, a0, a2]
  have key := fun {o l : Nat} (h : o + l ≤ 3 * (s₁.gpr .r2).toNat + (s₁.gpr .r3).toNat) =>
    verify_keyBytes h₁ hl hr0 hr1 hr2 hr3 (o := o) (l := l) h
  have kp := key (o := 0) (l := (s₁.gpr .r2).toNat) (by omega_arith)
  have kq := key (o := (s₁.gpr .r2).toNat) (l := (s₁.gpr .r3).toNat) (by omega_arith)
  rw [BitVec.add_zero] at kp
  have Pe : operand (State.addr (arg s₁ 4)) t₁ (.input .p) (s₁.gpr .r2).toNat =
      operand (State.addr (arg s₁ 4)) t₂ (.input .p) (s₁.gpr .r2).toNat := by
    have P₂ := Ip₂.value
    rw [← hr0, ← hr2] at P₂
    rw [Ip₁.value, P₂, kp]
  have Qe : operand (State.addr (arg s₁ 4)) t₁ (.input .q) (s₁.gpr .r3).toNat =
      operand (State.addr (arg s₁ 4)) t₂ (.input .q) (s₁.gpr .r3).toNat := by
    have Q₂ := Iq₂.value
    rw [← hr0, ← hr2, ← hr3] at Q₂
    rw [Iq₁.value, Q₂, kq]
  unfold Prevalidated.sized
  refine SameTrace.assoc_left (SameTrace.seq (check_trace F₁.ws F₂.ws hz hz wp wq Ip₁.toReady Rp₂ Iq₁.toReady Rq₂
      (pe F₁ F₂ (c := 0) (.input .p, (s₁.gpr .r2).toNat) (by simp [verifyIns]))
      (pe F₁ F₂ (c := 0) (.input .q, (s₁.gpr .r3).toNat) (by simp [verifyIns])))
    (check_ok F₁.ws hz wp wq Ip₁.toReady Iq₁.toReady rfl rfl) (check_ok F₂.ws hz wp wq Rp₂ Rq₂ rfl rfl)
    fun v₁ v₂ ⟨Z₁, K₁, D₁, S₁, O₁⟩ ⟨Z₂, K₂, D₂, S₂, O₂⟩ => ?_)
  have kee : ∀ r ∈ shapeRanges, r.1 + r.2 ≤ (arg s₁ 5).toNat * 8 ∧
      (r.1 + r.2 ≤ 64 ∨ 164 ≤ r.1 ∨ (112 ≤ r.1 ∧ r.1 + r.2 ≤ 128)) := fun r hr => by
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith
  have G₁ := F₁.keep (verifyFields_ok s₁) S₁ (by decide) O₁ kee
  have G₂ := F₂.keep (verifyFields_ok s₂) S₂ (by decide) O₂ kee
  refine SameTrace.seq_ite (by rw [eval_eq, eval_eq, Z₁, Z₂, Pe, Qe]) (fun _ => ?_) (fun hf => ?_)
  · exact failure_trace false G₁.ws G₂.ws (by omega_arith) (by omega_arith) (fun h => nomatch h) (fun h => nomatch h)
  · have valid : shapeValid (operand (State.addr (arg s₁ 4)) t₁ (.input .p) (s₁.gpr .r2).toNat)
        (operand (State.addr (arg s₁ 4)) t₁ (.input .q) (s₁.gpr .r3).toNat) := by
      rw [eval_eq, Z₁] at hf
      exact Classical.not_not.mp (of_decide_eq_false (Option.some.inj hf))
    have valid₂ : shapeValid (operand (State.addr (arg s₁ 4)) t₂ (.input .p) (s₁.gpr .r2).toNat)
        (operand (State.addr (arg s₁ 4)) t₂ (.input .q) (s₁.gpr .r3).toNat) := by rw [← Pe, ← Qe]; exact valid
    have hm₁ : maskW (State.addr (arg s₁ 4)) v₁ = BitVec.allOnes 32 := by rw [K₁]; simp [mask32, valid]
    have hm₂ : maskW (State.addr (arg s₁ 4)) v₂ = BitVec.allOnes 32 := by rw [K₂]; simp [mask32, valid₂]
    have Vp : verifyVal s₂ 0 (.input .p) = verifyVal s₁ 0 (.input .p) := by
      simp only [verifyVal]; rw [← hr0, ← hr2, kp]
    have Vq : verifyVal s₂ 0 (.input .q) = verifyVal s₁ 0 (.input .q) := by
      simp only [verifyVal]; rw [← hr0, ← hr2, ← hr3, kq]
    rw [Ip₁.value, Iq₁.value] at valid
    let c := min (arg s₁ 3).toNat (qWidth (verifyVal s₁ 0 (.input .q)))
    have hc₁ : countValue (State.addr (arg s₁ 4)) v₁ Core.digestPrefix = c := by
      refine D₁.trans ?_
      rw [F₁.field (d := 108) (v := arg s₁ 3) (by simp), Iq₁.value]
      rfl
    have hc₂ : countValue (State.addr (arg s₁ 4)) v₂ Core.digestPrefix = c := by
      refine D₂.trans ?_
      rw [F₂.field (d := 108) (v := arg s₂ 3) (by simp), ← a3, ← Qe, Iq₁.value]
      rfl
    have C₁ := verifyCtx h₁ rfl rfl G₁ rfl rfl (Nat.min_le_left _ _ : c ≤ (arg s₁ 3).toNat)
    have C₂ := verifyCtx h₂ hb₂ hz₂ G₂ (by rw [hr2] : (s₂.gpr .r2).toNat = (s₁.gpr .r2).toNat)
      (by rw [hr3] : (s₂.gpr .r3).toNat = (s₁.gpr .r3).toNat)
      (by rw [← a3]; exact Nat.min_le_left _ _ : c ≤ (arg s₂ 3).toNat)
    have X : Pair (State.addr (arg s₁ 4)) ((arg s₁ 5).toNat * 8) ((arg s₁ 5).toNat * 8) (s₁.gpr .r2).toNat
        (s₁.gpr .r3).toNat (((s₁.gpr .r2).toNat + 7) / 8) (((s₁.gpr .r3).toNat + 7) / 8)
        (verifyIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat c) (verifyVal s₁ c) (verifyVal s₂ c) v₁ v₂ :=
      ⟨C₁, C₂, pe G₁ G₂⟩
    have mp : (.input .p, (s₁.gpr .r2).toNat) ∈ verifyIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat c := by
      simp [verifyIns]
    have mq : (.input .q, (s₁.gpr .r3).toNat) ∈ verifyIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat c := by
      simp [verifyIns]
    have mg : (.input .g, (s₁.gpr .r2).toNat) ∈ verifyIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat c := by
      simp [verifyIns]
    have my : (.input .y, (s₁.gpr .r2).toNat) ∈ verifyIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat c := by
      simp [verifyIns]
    have mr : (.input .signature, (s₁.gpr .r3).toNat) ∈ verifyIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat c := by
      simp [verifyIns]
    have ms : (.signatureS, (s₁.gpr .r3).toNat) ∈ verifyIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat c := by
      simp [verifyIns]
    have md : (.input .digest, c) ∈ verifyIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat c := by simp [verifyIns]
    have B₁ := shape_bounds valid
    have Dm₁ : DomainOk (verifyVal s₁ c (.input .p)) (verifyVal s₁ c (.input .q)) :=
      ⟨B₁.1, B₁.2.1, B₁.2.2.1, B₁.2.2.2⟩
    have Dm₂ : DomainOk (verifyVal s₂ c (.input .p)) (verifyVal s₂ c (.input .q)) := by
      have e₁ : verifyVal s₂ c (.input .p) = verifyVal s₁ c (.input .p) := Vp
      have e₂ : verifyVal s₂ c (.input .q) = verifyVal s₁ c (.input .q) := Vq
      rw [e₁, e₂]; exact Dm₁
    exact SameTrace.seq (prevBody_trace X mp mq mg my mr ms md hc₁ hc₂ Dm₁ Dm₂)
      (prevBody_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) (X.C₁.inp my) (X.C₁.inp mr) (X.C₁.inp ms)
        (X.C₁.inp md) hc₁ Dm₁.hP Dm₁.hPo Dm₁.hQ Dm₁.hQo hm₁ pc₁)
      (prevBody_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) (X.C₂.inp my) (X.C₂.inp mr) (X.C₂.inp ms)
        (X.C₂.inp md) hc₂ Dm₂.hP Dm₂.hPo Dm₂.hQ Dm₂.hQo hm₂ pc₂)
      fun w₁ w₂ ⟨_, Rn₁⟩ ⟨_, Rn₂⟩ => tail_trace (Rn₁.ws G₁.ws) (Rn₂.ws G₂.ws)

end VG.Proof.Dsa.Arm
