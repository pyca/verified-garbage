module
public import VerifiedGarbage.Proof.Dsa.Arm.KeyTrace
public import VerifiedGarbage.Proof.Dsa.Arm.Env

import VerifiedGarbage.Proof.Dsa.Arm.VerifyCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.OpTrace
import VerifiedGarbage.Proof.Dsa.Arm.ShapeTrace
import VerifiedGarbage.Proof.Dsa.Arm.BodyTrace
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.PackedBytes

/-!
# DSA on 32-bit ARM: verification is constant time

As signing (`SignCT.lean`): two runs whose public data agree
(`verifyArm.pub`: the arguments, the key and the result) leak the same trace.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest eval_eq)
open VG.Proof.Ecdsa.Arm (mask32)

/-- The caller's operands of verification. -/
def verifyIns (pLen qLen c : Nat) : List (Pointer × Nat) :=
  [(.input .p, pLen), (.input .q, qLen), (.input .g, pLen), (.input .y, pLen), (.input .signature, qLen),
    (.signatureS, qLen), (.input .digest, c)]

/-- Their values. -/
def verifyVal (s : State) (c : Nat) : Pointer → Nat
  | .input .p => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat)
  | .input .q => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat)
      (s.gpr .r3).toNat)
  | .input .g => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (State.addr (s.gpr .r0) + BitVec.ofNat 64 ((s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat)
  | .input .y => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (State.addr (s.gpr .r0) + BitVec.ofNat 64 (2 * (s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat)
  | .input .signature => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 0)) (s.gpr .r3).toNat)
  | .signatureS => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 0) + BitVec.ofNat 64 (s.gpr .r3).toNat)
      (s.gpr .r3).toNat)
  | .input .digest => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 2)) c)
  | _ => 0

/-- Their pointers. -/
def verifyPtr (s : State) : Pointer → BitVec 32
  | .input .p => s.gpr .r0
  | .input .q => s.gpr .r0 + s.gpr .r2
  | .input .g => s.gpr .r0 + s.gpr .r2 + s.gpr .r3
  | .input .y => s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2
  | .input .signature => arg s 0
  | .signatureS => arg s 0 + s.gpr .r3
  | .input .digest => arg s 2
  | _ => 0

theorem verifyCtx {s t : State} {base : Addr} {size pLen qLen c : Nat} (h : verifyPre s)
    (hb : State.addr (arg s 4) = base) (hsz : (arg s 5).toNat * 8 = size)
    (E : Env s base size (verifyFields s) t) (hpl : (s.gpr .r2).toNat = pLen) (hql : (s.gpr .r3).toNat = qLen)
    (hc : c ≤ (arg s 3).toNat) :
    Ctx base size pLen qLen ((pLen + 7) / 8) ((qLen + 7) / 8) (verifyIns pLen qLen c) (verifyVal s c) t := by
  have hv := h.2.2.2.2.2.2.2.2.2.2.2.1
  have hsw := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  subst hpl hql
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have big : 15712 < size := by rw [← hsz]; unfold Spec.Dsa.scratchWords at hsw; omega
  obtain ⟨Ip, Iq, Ig, Iy⟩ := verifyKeyIn h hb hsz E
  refine ⟨⟨E.ws, big, wp, wq, qp, q32⟩, fun i hi => ?_⟩
  simp only [verifyIns, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Ip
  · exact Iq
  · exact Ig
  · exact Iy
  · exact verifySigIn h hb hsz E
  · exact verifySigSIn h hb hsz E
  · exact verifyDigestIn h hb hsz E hc

theorem verifyPtrs {s t : State} {base : Addr} {size pLen qLen c : Nat} (E : Env s base size (verifyFields s) t) :
    ∀ i ∈ verifyIns pLen qLen c, pointerValue base t i.1 = verifyPtr s i.1 := by
  intro i hi
  simp only [verifyIns, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact E.field (d := 64) (v := s.gpr .r0) (by simp)
  · exact E.field (d := 68) (v := s.gpr .r0 + s.gpr .r2) (by simp)
  · exact E.field (d := 72) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3) (by simp)
  · exact E.field (d := 76) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2) (by simp)
  · exact E.field (d := 84) (v := arg s 0) (by simp)
  · show hdr base t 84 + hdr base t 104 = _
    rw [E.field (d := 84) (v := arg s 0) (by simp), E.field (d := 104) (v := s.gpr .r3) (by simp)]
    rfl
  · exact E.field (d := 92) (v := arg s 2) (by simp)

/-- The key's bytes, the same in two runs that leak the same. -/
theorem verify_keyBytes {s₁ s₂ : State} (h₁ : verifyPre s₁) (hl : verifyLeak s₁ = verifyLeak s₂)
    (hr0 : s₁.gpr .r0 = s₂.gpr .r0) (hr1 : s₁.gpr .r1 = s₂.gpr .r1) (hr2 : s₁.gpr .r2 = s₂.gpr .r2)
    (hr3 : s₁.gpr .r3 = s₂.gpr .r3) {o l : Nat} (hol : o + l ≤ 3 * (s₁.gpr .r2).toNat + (s₁.gpr .r3).toNat) :
    Spec.Rsa.bytesAt s₁.mem (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 o) l =
      Spec.Rsa.bytesAt s₂.mem (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 o) l := by
  have r1 := h₁.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [verifyLeak, Spec.Dsa.publicBytesLeak] at hl
  rw [← hr0, ← hr1, ← hr2, ← hr3] at hl
  have E := List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h) |>.mp
    (List.append_inj hl (by simp [Spec.Rsa.bytesAt])).1
  rw [← VG.Proof.Dsa.bytesAt_prefix, ← VG.Proof.Dsa.bytesAt_prefix,
    show min (s₁.gpr .r1).toNat (3 * (s₁.gpr .r2).toNat + (s₁.gpr .r3).toNat) =
      3 * (s₁.gpr .r2).toNat + (s₁.gpr .r3).toNat by omega] at E
  rw [← VG.Proof.Dsa.bytesAt_slice _ _ hol, ← VG.Proof.Dsa.bytesAt_slice _ _ hol, E]

theorem verify_constantTime : ConstantTime isa verifyArm.pre verifyArm.pub (Entry.operation false) := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ pub => ?_
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
  have hs16 : 128 * (s₁.gpr .r2).toNat ≤ (arg s₁ 5).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  have hb₂ : State.addr (arg s₂ 4) = State.addr (arg s₁ 4) := by rw [a4]
  have hz₂ : (arg s₂ 5).toNat * 8 = (arg s₁ 5).toNat * 8 := by rw [a5]
  simp only [Entry.operation, Core.sequence, List.foldr, Bool.false_eq_true, ↓reduceIte]
  refine SameTrace.seq (SameTrace.of_relCT (entry_relCT 24 _ rfl) (agree_args (n := 6) hsp (by omega) ha
      (fun r hr => by
        rw [wr₁] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact dSA₁.symm)
      (fun r hr => by
        rw [wr₂] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact dSA₂.symm)))
    (WP.mono (verifyEntry_ok h₁) fun u I => Env.of_installed I (by omega))
    (WP.mono (verifyEntry_ok h₂) fun u I => by
      have E := Env.of_installed I (by rw [hz₂]; omega)
      rwa [hb₂, hz₂] at E)
    fun u₁ u₂ E₁ E₂ => ?_
  refine widthDispatch_trace false _ E₁.ws E₂.ws (by omega) (by omega) (widths_mem hv) (by decide)
    (by rw [E₁.field (d := 100) (v := s₁.gpr .r2) (by simp)]) (by rw [E₁.field (d := 104) (v := s₁.gpr .r3) (by simp)])
    (by rw [E₂.field (d := 100) (v := s₂.gpr .r2) (by simp), hr2])
    (by rw [E₂.field (d := 104) (v := s₂.gpr .r3) (by simp), hr3])
    fun t₁ t₂ R₁ M₁ R₂ M₂ => ?_
  have F₁ := E₁.of_mem R₁ (by decide) M₁
  have F₂ := E₂.of_mem R₂ (by decide) M₂
  have hz : 4960 ≤ (arg s₁ 5).toNat * 8 := by omega
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
  have kp := key (o := 0) (l := (s₁.gpr .r2).toNat) (by omega)
  have kq := key (o := (s₁.gpr .r2).toNat) (l := (s₁.gpr .r3).toNat) (by omega)
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
  unfold Entry.sized
  refine SameTrace.assoc_left (SameTrace.seq (check_trace F₁.ws F₂.ws hz hz wp wq Ip₁.toReady Rp₂ Iq₁.toReady Rq₂
      (pe F₁ F₂ (c := 0) (.input .p, (s₁.gpr .r2).toNat) (by simp [verifyIns]))
      (pe F₁ F₂ (c := 0) (.input .q, (s₁.gpr .r3).toNat) (by simp [verifyIns])))
    (check_ok F₁.ws hz wp wq Ip₁.toReady Iq₁.toReady rfl rfl) (check_ok F₂.ws hz wp wq Rp₂ Rq₂ rfl rfl)
    fun v₁ v₂ ⟨Z₁, K₁, D₁, S₁, O₁⟩ ⟨Z₂, K₂, D₂, S₂, O₂⟩ => ?_)
  have kee : ∀ r ∈ shapeRanges, r.1 + r.2 ≤ (arg s₁ 5).toNat * 8 ∧
      (r.1 + r.2 ≤ 64 ∨ 164 ≤ r.1 ∨ (112 ≤ r.1 ∧ r.1 + r.2 ≤ 128)) := fun r hr => by
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega
  have G₁ := F₁.keep (verifyFields_ok s₁) S₁ (by decide) O₁ kee
  have G₂ := F₂.keep (verifyFields_ok s₂) S₂ (by decide) O₂ kee
  refine SameTrace.seq_ite (by rw [eval_eq, eval_eq, Z₁, Z₂, Pe, Qe]) (fun _ => ?_) (fun hf => ?_)
  · exact failure_trace false G₁.ws G₂.ws (by omega) (by omega) (fun h => nomatch h) (fun h => nomatch h)
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
    exact SameTrace.seq (verifyBody_trace X mp mq mg my mr ms md hc₁ hc₂ Dm₁ Dm₂)
      (verifyBody_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) (X.C₁.inp my) (X.C₁.inp mr) (X.C₁.inp ms)
        (X.C₁.inp md) hc₁ Dm₁.hP Dm₁.hPo Dm₁.hQ Dm₁.hQo hm₁)
      (verifyBody_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) (X.C₂.inp my) (X.C₂.inp mr) (X.C₂.inp ms)
        (X.C₂.inp md) hc₂ Dm₂.hP Dm₂.hPo Dm₂.hQ Dm₂.hQo hm₂)
      fun w₁ w₂ ⟨_, Rn₁⟩ ⟨_, Rn₂⟩ => tail_trace (Rn₁.ws G₁.ws) (Rn₂.ws G₂.ws)

end VG.Proof.Dsa.Arm
