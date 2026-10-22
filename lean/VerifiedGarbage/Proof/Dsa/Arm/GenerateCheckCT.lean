module

import VerifiedGarbage.Proof.Dsa.Arm.GenerateTrace
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Dsa.Arm.ShapeTrace
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.PackedBytes
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateEntry
public import VerifiedGarbage.Proof.Dsa.Arm.KeyTrace

/-!
# DSA domain checks on 32-bit ARM: constant time

Every input of `vg_dsa_check_parameters` is public: two runs with the same
arguments and domain bytes compute on the same values, through the same
pointers, so each part leaks the same trace.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest eval_eq)
open VG.Proof.Ecdsa.Arm (mask32)

/-- The domain's operands. -/
def checkIns (pLen qLen : Nat) : List (Pointer × Nat) := [(.input .p, pLen), (.input .q, qLen), (.input .g, pLen)]

/-- Their values. -/
def checkVal (s : State) : Pointer → Nat
  | .input .p => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat)
  | .input .q => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat)
      (s.gpr .r3).toNat)
  | .input .g => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (State.addr (s.gpr .r0) + BitVec.ofNat 64 ((s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat)
  | _ => 0

theorem checkCtx {s t : State} {base : Addr} {size : Nat} (h : checkPre s)
    (hb : State.addr (arg s 0) = base) (hsz : (arg s 1).toNat * 8 = size)
    (E : Env s base size (checkFields s) t) :
    Ctx base size (s.gpr .r2).toNat (s.gpr .r3).toNat (((s.gpr .r2).toNat + 7) / 8) (((s.gpr .r3).toNat + 7) / 8)
      (checkIns (s.gpr .r2).toNat (s.gpr .r3).toNat) (checkVal s) t := by
  have hv := h.2.2.2.2.2.2.2.1
  have hsw := h.2.2.2.2.2.2.2.2.2
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have big : 15712 < size := by rw [← hsz]; unfold Spec.Dsa.scratchWords at hsw; omega
  obtain ⟨Ip, Iq, Ig⟩ := checkIn h hb hsz E
  refine ⟨⟨E.ws, big, wp, wq, qp, q32⟩, fun i hi => ?_⟩
  simp only [checkIns, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact Ip
  · exact Iq
  · exact Ig

theorem checkPtrs {s t : State} {base : Addr} {size pLen qLen : Nat} (E : Env s base size (checkFields s) t) :
    ∀ i ∈ checkIns pLen qLen, pointerValue base t i.1 =
      match i.1 with
      | .input .p => s.gpr .r0
      | .input .q => s.gpr .r0 + s.gpr .r2
      | _ => s.gpr .r0 + s.gpr .r2 + s.gpr .r3 := by
  intro i hi
  simp only [checkIns, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact E.field (d := 64) (v := s.gpr .r0) (by simp)
  · exact E.field (d := 68) (v := s.gpr .r0 + s.gpr .r2) (by simp)
  · exact E.field (d := 72) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3) (by simp)

/-- The domain's bytes at an offset, the same in two runs that leak the same. -/
theorem check_bytes {s₁ s₂ : State} (hl : (checkParams s₁).map (·.toNat) = (checkParams s₂).map (·.toNat))
    (hr0 : s₁.gpr .r0 = s₂.gpr .r0) (hr1 : s₁.gpr .r1 = s₂.gpr .r1) {o l : Nat}
    (hol : o + l ≤ (s₁.gpr .r1).toNat) :
    Spec.Rsa.bytesAt s₁.mem (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 o) l =
      Spec.Rsa.bytesAt s₂.mem (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 o) l := by
  have E := List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h) |>.mp hl
  simp only [checkParams] at E
  rw [← hr0, ← hr1] at E
  rw [← VG.Proof.Dsa.bytesAt_slice _ _ hol, ← VG.Proof.Dsa.bytesAt_slice _ _ hol, E]

theorem check_constantTime : ConstantTime isa checkArm.pre checkArm.pub Generate.checkParameters := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ pub => ?_
  obtain ⟨hsp, hl, hr0, hr1, hr2, hr3, ha⟩ := pub
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  obtain ⟨sp₁, _, wr₁, _, dSA₁, _, _, hv, hpl, hsw⟩ := id h₁
  obtain ⟨_, _, wr₂, _, dSA₂, _, _, _, _, _⟩ := id h₂
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 128 * (s₁.gpr .r2).toNat ≤ (arg s₁ 1).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  have hb₂ : State.addr (arg s₂ 0) = State.addr (arg s₁ 0) := by rw [a0]
  have hz₂ : (arg s₂ 1).toNat * 8 = (arg s₁ 1).toNat * 8 := by rw [a1]
  simp only [Generate.checkParameters, Core.sequence, List.foldr]
  refine SameTrace.seq (SameTrace.of_relCT (entry_relCT 8 _ rfl) (agree_args (n := 2) hsp (by omega) ha
      (fun r hr => by
        rw [wr₁] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact dSA₁.symm)
      (fun r hr => by
        rw [wr₂] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact dSA₂.symm)))
    (WP.mono (checkEntry_ok h₁) fun u I => Env.of_installed I (by omega))
    (WP.mono (checkEntry_ok h₂) fun u I => by
      have E := Env.of_installed I (by rw [hz₂]; omega)
      rwa [hb₂, hz₂] at E)
    fun u₁ u₂ E₁ E₂ => ?_
  refine genDispatch_trace Generate.checkSized _ E₁.ws E₂.ws (by omega) (by omega) (genWidths_mem hv) (by decide)
    (by rw [E₁.field (d := 100) (v := s₁.gpr .r2) (by simp)]) (by rw [E₁.field (d := 104) (v := s₁.gpr .r3) (by simp)])
    (by rw [E₂.field (d := 100) (v := s₂.gpr .r2) (by simp), hr2])
    (by rw [E₂.field (d := 104) (v := s₂.gpr .r3) (by simp), hr3])
    fun t₁ t₂ R₁ M₁ R₂ M₂ => ?_
  have F₁ := E₁.of_mem R₁ (by decide) M₁
  have F₂ := E₂.of_mem R₂ (by decide) M₂
  have hz : 4960 ≤ (arg s₁ 1).toNat * 8 := by omega
  have C₁ := checkCtx h₁ rfl rfl F₁
  have C₂ := checkCtx h₂ hb₂ hz₂ F₂
  rw [← hr2, ← hr3] at C₂
  have pe : ∀ {u₁ u₂ : State} (G₁ : Env s₁ (State.addr (arg s₁ 0)) ((arg s₁ 1).toNat * 8) (checkFields s₁) u₁)
      (G₂ : Env s₂ (State.addr (arg s₁ 0)) ((arg s₁ 1).toNat * 8) (checkFields s₂) u₂),
      ∀ i ∈ checkIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat, PtrEq (State.addr (arg s₁ 0)) u₁ u₂ i.1 := by
    intro u₁ u₂ G₁ G₂ i hi
    unfold PtrEq
    rw [checkPtrs G₁ i hi, checkPtrs (pLen := (s₁.gpr .r2).toNat) (qLen := (s₁.gpr .r3).toNat) G₂ i hi, hr0, hr2, hr3]
  -- Both runs see the same domain.
  have key := fun {o l : Nat} (h : o + l ≤ (s₁.gpr .r1).toNat) => check_bytes hl hr0 hr1 (o := o) (l := l) h
  have Vp : checkVal s₂ (.input .p) = checkVal s₁ (.input .p) := by
    have k := key (o := 0) (l := (s₁.gpr .r2).toNat) (by omega)
    rw [BitVec.add_zero] at k
    simp only [checkVal]; rw [← hr0, ← hr2, k]
  have Vq : checkVal s₂ (.input .q) = checkVal s₁ (.input .q) := by
    simp only [checkVal]; rw [← hr0, ← hr2, ← hr3, key (by omega)]
  have Vg : checkVal s₂ (.input .g) = checkVal s₁ (.input .g) := by
    simp only [checkVal]; rw [← hr0, ← hr2, ← hr3, key (by omega)]
  have mp : (.input .p, (s₁.gpr .r2).toNat) ∈ checkIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat := by simp [checkIns]
  have mq : (.input .q, (s₁.gpr .r3).toNat) ∈ checkIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat := by simp [checkIns]
  have mg : (.input .g, (s₁.gpr .r2).toNat) ∈ checkIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat := by simp [checkIns]
  have Pe : operand (State.addr (arg s₁ 0)) t₁ (.input .p) (s₁.gpr .r2).toNat =
      operand (State.addr (arg s₁ 0)) t₂ (.input .p) (s₁.gpr .r2).toNat := by
    rw [(C₁.inp mp).value, (C₂.inp mp).value, Vp]
  have Qe : operand (State.addr (arg s₁ 0)) t₁ (.input .q) (s₁.gpr .r3).toNat =
      operand (State.addr (arg s₁ 0)) t₂ (.input .q) (s₁.gpr .r3).toNat := by
    rw [(C₁.inp mq).value, (C₂.inp mq).value, Vq]
  unfold Generate.checkSized
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
    have Dm₁ : DomainOk (checkVal s₁ (.input .p)) (checkVal s₁ (.input .q)) := ⟨B₁.1, B₁.2.1, B₁.2.2.1, B₁.2.2.2⟩
    have Dm₂ : DomainOk (checkVal s₂ (.input .p)) (checkVal s₂ (.input .q)) := by rw [Vp, Vq]; exact Dm₁
    have D₁ := checkCtx h₁ rfl rfl G₁
    have D₂ := checkCtx h₂ hb₂ hz₂ G₂
    rw [← hr2, ← hr3] at D₂
    have X : Pair (State.addr (arg s₁ 0)) ((arg s₁ 1).toNat * 8) ((arg s₁ 1).toNat * 8) (s₁.gpr .r2).toNat
        (s₁.gpr .r3).toNat (((s₁.gpr .r2).toNat + 7) / 8) (((s₁.gpr .r3).toNat + 7) / 8)
        (checkIns (s₁.gpr .r2).toNat (s₁.gpr .r3).toNat) (checkVal s₁) (checkVal s₂) v₁ v₂ :=
      ⟨D₁, D₂, pe G₁ G₂⟩
    exact SameTrace.assoc_left (SameTrace.seq (parameters_trace X mp mq mg Dm₁ Dm₂)
      (parameters_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) Dm₁.hP Dm₁.hPo Dm₁.hQ Dm₁.hQo)
      (parameters_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) Dm₂.hP Dm₂.hPo Dm₂.hQ Dm₂.hQo)
      fun w₁ w₂ ⟨_, Rn₁⟩ ⟨_, Rn₂⟩ => SameTrace.of_relCT (RelCT.seq result_relCT
        (RelCT.seq (block_relCT_T0 _ rfl) (RelCT.block_nil (Q := fun _ _ => True) fun _ _ _ => trivial)))
        (agree0 (G₁.ws.of_rest Rn₁.rest (by decide)) (G₂.ws.of_rest Rn₂.rest (by decide))))

end VG.Proof.Dsa.Arm
