module
public import VerifiedGarbage.Proof.Dsa.Arm.Env
public import VerifiedGarbage.Proof.Dsa.Arm.KeyTrace

import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Dsa.Arm.BodyTrace
import VerifiedGarbage.Proof.Dsa.Arm.ShapeTrace
import VerifiedGarbage.Proof.Dsa.Arm.OpTrace
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.PackedBytes

/-!
# DSA on 32-bit ARM: signing is constant time

Two runs whose public data agree (`signArm.pub`: the arguments, the key's
public bytes and whether signing succeeds) leak the same trace. Each part's
trace follows from registers and pointers that are the same in both runs
(`OpTrace.lean`, `ShapeTrace.lean`, `BodyTrace.lean`); what each run computes
between the parts, by its correctness, keeps them the same.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest eval_eq)
open VG.Proof.Ecdsa.Arm (mask32)

/-- The caller's operands of signing. -/
def signIns (pLen qLen c : Nat) : List (Pointer × Nat) :=
  [(.input .p, pLen), (.input .q, qLen), (.input .g, pLen), (.input .y, pLen), (.input .x, qLen),
    (.input .nonce, qLen), (.input .digest, c)]

/-- Their values. -/
def signVal (s : State) (c : Nat) : Pointer → Nat
  | .input .p => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (arg s 0).toNat)
  | .input .q => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2) + BitVec.ofNat 64 (arg s 0).toNat)
      (arg s 2).toNat)
  | .input .g => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (State.addr (s.gpr .r2) + BitVec.ofNat 64 ((arg s 0).toNat + (arg s 2).toNat)) (arg s 0).toNat)
  | .input .y => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (State.addr (s.gpr .r2) + BitVec.ofNat 64 (2 * (arg s 0).toNat + (arg s 2).toNat)) (arg s 0).toNat)
  | .input .x => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (State.addr (s.gpr .r2) + BitVec.ofNat 64 (3 * (arg s 0).toNat + (arg s 2).toNat)) (arg s 2).toNat)
  | .input .nonce => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat)
  | .input .digest => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 3)) c)
  | _ => 0

/-- Their pointers. -/
def signPtr (s : State) : Pointer → BitVec 32
  | .input .p => s.gpr .r2
  | .input .q => s.gpr .r2 + arg s 0
  | .input .g => s.gpr .r2 + arg s 0 + arg s 2
  | .input .y => s.gpr .r2 + arg s 0 + arg s 2 + arg s 0
  | .input .x => s.gpr .r2 + arg s 0 + arg s 2 + arg s 0 + arg s 0
  | .input .nonce => arg s 1
  | .input .digest => arg s 3
  | _ => 0

theorem signCtx {s t : State} {base : Addr} {size pLen qLen c : Nat} (h : signPre s)
    (hb : State.addr (arg s 5) = base) (hsz : (arg s 6).toNat * 8 = size)
    (E : Env s base size (signFields s) t) (hpl : (arg s 0).toNat = pLen) (hql : (arg s 2).toNat = qLen)
    (hc : c ≤ (arg s 4).toNat) :
    Ctx base size pLen qLen ((pLen + 7) / 8) ((qLen + 7) / 8) (signIns pLen qLen c) (signVal s c) t := by
  have hv := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsw := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  subst hpl hql
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have big : 15712 < size := by rw [← hsz]; unfold Spec.Dsa.scratchWords at hsw; omega
  obtain ⟨Ip, Iq, Ig, Iy, Ix⟩ := signKeyIn h hb hsz E
  refine ⟨⟨E.ws, big, wp, wq, qp, q32⟩, fun i hi => ?_⟩
  simp only [signIns, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Ip
  · exact Iq
  · exact Ig
  · exact Iy
  · exact Ix
  · exact signNonceIn h hb hsz E
  · exact signDigestIn h hb hsz E hc

theorem signPtrs {s t : State} {base : Addr} {size pLen qLen c : Nat} (E : Env s base size (signFields s) t) :
    ∀ i ∈ signIns pLen qLen c, pointerValue base t i.1 = signPtr s i.1 := by
  intro i hi
  simp only [signIns, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact E.field (d := 64) (v := s.gpr .r2) (by simp)
  · exact E.field (d := 68) (v := s.gpr .r2 + arg s 0) (by simp)
  · exact E.field (d := 72) (v := s.gpr .r2 + arg s 0 + arg s 2) (by simp)
  · exact E.field (d := 76) (v := s.gpr .r2 + arg s 0 + arg s 2 + arg s 0) (by simp)
  · exact E.field (d := 80) (v := s.gpr .r2 + arg s 0 + arg s 2 + arg s 0 + arg s 0) (by simp)
  · exact E.field (d := 88) (v := arg s 1) (by simp)
  · exact E.field (d := 92) (v := arg s 3) (by simp)

/-- The key's public bytes, the same in two runs that leak the same. -/
theorem sign_keyBytes {s₁ s₂ : State} (h₁ : signPre s₁) (hl : signLeak s₁ = signLeak s₂)
    (hr2 : s₁.gpr .r2 = s₂.gpr .r2) (hr3 : s₁.gpr .r3 = s₂.gpr .r3) (a0 : arg s₁ 0 = arg s₂ 0)
    (a2 : arg s₁ 2 = arg s₂ 2) {o l : Nat} (hol : o + l ≤ 3 * (arg s₁ 0).toNat + (arg s₁ 2).toNat) :
    Spec.Rsa.bytesAt s₁.mem (State.addr (s₁.gpr .r2) + BitVec.ofNat 64 o) l =
      Spec.Rsa.bytesAt s₂.mem (State.addr (s₁.gpr .r2) + BitVec.ofNat 64 o) l := by
  have r3 := h₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [signLeak, Spec.Dsa.publicBytesLeak] at hl
  rw [← a0, ← a2, ← hr2, ← hr3] at hl
  have E := List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h) |>.mp
    (List.append_inj hl (by simp [Spec.Rsa.bytesAt])).1
  rw [← VG.Proof.Dsa.bytesAt_prefix, ← VG.Proof.Dsa.bytesAt_prefix,
    show min (s₁.gpr .r3).toNat (3 * (arg s₁ 0).toNat + (arg s₁ 2).toNat) =
      3 * (arg s₁ 0).toNat + (arg s₁ 2).toNat by omega] at E
  rw [← VG.Proof.Dsa.bytesAt_slice _ _ hol, ← VG.Proof.Dsa.bytesAt_slice _ _ hol, E]

theorem sign_constantTime : ConstantTime isa signArm.pre signArm.pub (Entry.operation true) := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ pub => ?_
  obtain ⟨hsp, hl, hr0, _, hr2, hr3, ha⟩ := pub
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide)
  have a4 := ha 4 (by decide)
  have a5 := ha 5 (by decide)
  have a6 := ha 6 (by decide)
  obtain ⟨sp₁, _, wr₁, _, _, _, _, dOA₁, _, _, _, dSA₁, _, _, _, _, fS₁, hv, _, r3₁, hsw⟩ := id h₁
  obtain ⟨_, _, wr₂, _, _, _, _, dOA₂, _, _, _, dSA₂, _, _, _, _, _, _, _, _, _⟩ := id h₂
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 128 * (arg s₁ 0).toNat ≤ (arg s₁ 6).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  have hb₂ : State.addr (arg s₂ 5) = State.addr (arg s₁ 5) := by rw [a5]
  have hz₂ : (arg s₂ 6).toNat * 8 = (arg s₁ 6).toNat * 8 := by rw [a6]
  simp only [Entry.operation, Core.sequence, List.foldr, ↓reduceIte]
  refine SameTrace.seq (SameTrace.of_relCT (entry_relCT 28 _ rfl) (agree_args (n := 7) hsp (by omega_arith) ha
      (fun r hr => by
        rw [wr₁] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dOA₁.symm
        · exact dSA₁.symm)
      (fun r hr => by
        rw [wr₂] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dOA₂.symm
        · exact dSA₂.symm)))
    (WP.mono (signEntry_ok h₁) fun u I => Env.of_installed I (by omega_arith))
    (WP.mono (signEntry_ok h₂) fun u I => by
      have E := Env.of_installed I (by rw [hz₂]; omega_arith)
      rwa [hb₂, hz₂] at E)
    fun u₁ u₂ E₁ E₂ => ?_
  refine widthDispatch_trace true _ E₁.ws E₂.ws (by omega_arith) (by omega_arith) (widths_mem hv) (by decide)
    (by rw [E₁.field (d := 100) (v := arg s₁ 0) (by simp)]) (by rw [E₁.field (d := 104) (v := arg s₁ 2) (by simp)])
    (by rw [E₂.field (d := 100) (v := arg s₂ 0) (by simp), a0])
    (by rw [E₂.field (d := 104) (v := arg s₂ 2) (by simp), a2])
    fun t₁ t₂ R₁ M₁ R₂ M₂ => ?_
  have F₁ := E₁.of_mem R₁ (by decide) M₁
  have F₂ := E₂.of_mem R₂ (by decide) M₂
  have hz : 4960 ≤ (arg s₁ 6).toNat * 8 := by omega_arith
  obtain ⟨Ip₁, Iq₁, -, -, -⟩ := signKeyIn h₁ rfl rfl F₁
  obtain ⟨Ip₂, Iq₂, -, -, -⟩ := signKeyIn h₂ hb₂ hz₂ F₂
  have Rp₂ : Ready t₂ (State.addr (arg s₁ 5)) (.input .p) (arg s₁ 0).toNat := by rw [a0]; exact Ip₂.toReady
  have Rq₂ : Ready t₂ (State.addr (arg s₁ 5)) (.input .q) (arg s₁ 2).toNat := by rw [a2]; exact Iq₂.toReady
  have pe : ∀ {u₁ u₂ : State} (G₁ : Env s₁ (State.addr (arg s₁ 5)) ((arg s₁ 6).toNat * 8) (signFields s₁) u₁)
      (G₂ : Env s₂ (State.addr (arg s₁ 5)) ((arg s₁ 6).toNat * 8) (signFields s₂) u₂) {c : Nat},
      ∀ i ∈ signIns (arg s₁ 0).toNat (arg s₁ 2).toNat c, PtrEq (State.addr (arg s₁ 5)) u₁ u₂ i.1 := by
    intro u₁ u₂ G₁ G₂ c i hi
    unfold PtrEq
    rw [signPtrs G₁ i hi, signPtrs (pLen := (arg s₁ 0).toNat) (qLen := (arg s₁ 2).toNat) (c := c) G₂ i hi]
    simp only [signIns, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [signPtr, hr2, a0, a1, a2, a3]
  have key := fun {o l : Nat} (h : o + l ≤ 3 * (arg s₁ 0).toNat + (arg s₁ 2).toNat) =>
    sign_keyBytes h₁ hl hr2 hr3 a0 a2 (o := o) (l := l) h
  have kp := key (o := 0) (l := (arg s₁ 0).toNat) (by omega_arith)
  have kq := key (o := (arg s₁ 0).toNat) (l := (arg s₁ 2).toNat) (by omega_arith)
  rw [BitVec.add_zero] at kp
  have Pe : operand (State.addr (arg s₁ 5)) t₁ (.input .p) (arg s₁ 0).toNat =
      operand (State.addr (arg s₁ 5)) t₂ (.input .p) (arg s₁ 0).toNat := by
    have P₂ := Ip₂.value
    rw [← a0, ← hr2] at P₂
    rw [Ip₁.value, P₂, kp]
  have Qe : operand (State.addr (arg s₁ 5)) t₁ (.input .q) (arg s₁ 2).toNat =
      operand (State.addr (arg s₁ 5)) t₂ (.input .q) (arg s₁ 2).toNat := by
    have Q₂ := Iq₂.value
    rw [← a0, ← a2, ← hr2] at Q₂
    rw [Iq₁.value, Q₂, kq]
  unfold Entry.sized
  refine SameTrace.assoc_left (SameTrace.seq (check_trace F₁.ws F₂.ws hz hz wp wq Ip₁.toReady Rp₂ Iq₁.toReady Rq₂
      (pe F₁ F₂ (c := 0) (.input .p, (arg s₁ 0).toNat) (by simp [signIns]))
      (pe F₁ F₂ (c := 0) (.input .q, (arg s₁ 2).toNat) (by simp [signIns])))
    (check_ok F₁.ws hz wp wq Ip₁.toReady Iq₁.toReady rfl rfl) (check_ok F₂.ws hz wp wq Rp₂ Rq₂ rfl rfl)
    fun v₁ v₂ ⟨Z₁, K₁, D₁, S₁, O₁⟩ ⟨Z₂, K₂, D₂, S₂, O₂⟩ => ?_)
  have kee : ∀ r ∈ shapeRanges, r.1 + r.2 ≤ (arg s₁ 6).toNat * 8 ∧
      (r.1 + r.2 ≤ 64 ∨ 164 ≤ r.1 ∨ (112 ≤ r.1 ∧ r.1 + r.2 ≤ 128)) := fun r hr => by
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith
  have G₁ := F₁.keep (signFields_ok s₁) S₁ (by decide) O₁ kee
  have G₂ := F₂.keep (signFields_ok s₂) S₂ (by decide) O₂ kee
  refine SameTrace.seq_ite (by rw [eval_eq, eval_eq, Z₁, Z₂, Pe, Qe]) (fun _ => ?_) (fun hf => ?_)
  · exact failure_trace true G₁.ws G₂.ws (by omega_arith) (by omega_arith)
      (fun _ => by
        rw [G₁.field (d := 96) (v := s₁.gpr .r0) (by simp), G₂.field (d := 96) (v := s₂.gpr .r0) (by simp), hr0])
      (fun _ => by
        rw [G₁.field (d := 104) (v := arg s₁ 2) (by simp), G₂.field (d := 104) (v := arg s₂ 2) (by simp), a2])
  · have valid : shapeValid (operand (State.addr (arg s₁ 5)) t₁ (.input .p) (arg s₁ 0).toNat)
        (operand (State.addr (arg s₁ 5)) t₁ (.input .q) (arg s₁ 2).toNat) := by
      rw [eval_eq, Z₁] at hf
      exact Classical.not_not.mp (of_decide_eq_false (Option.some.inj hf))
    have valid₂ : shapeValid (operand (State.addr (arg s₁ 5)) t₂ (.input .p) (arg s₁ 0).toNat)
        (operand (State.addr (arg s₁ 5)) t₂ (.input .q) (arg s₁ 2).toNat) := by rw [← Pe, ← Qe]; exact valid
    have kg := key (o := (arg s₁ 0).toNat + (arg s₁ 2).toNat) (l := (arg s₁ 0).toNat) (by omega_arith)
    have ky := key (o := 2 * (arg s₁ 0).toNat + (arg s₁ 2).toNat) (l := (arg s₁ 0).toNat) (by omega_arith)
    have Vp : signVal s₂ 0 (.input .p) = signVal s₁ 0 (.input .p) := by
      simp only [signVal]; rw [← a0, ← hr2, kp]
    have Vq : signVal s₂ 0 (.input .q) = signVal s₁ 0 (.input .q) := by
      simp only [signVal]; rw [← a0, ← a2, ← hr2, kq]
    have hm₁ : maskW (State.addr (arg s₁ 5)) v₁ = BitVec.allOnes 32 := by rw [K₁]; simp [mask32, valid]
    rw [Ip₁.value, Iq₁.value] at valid
    -- The digest's prefix, the same in both runs.
    let c := min (arg s₁ 4).toNat (qWidth (signVal s₁ 0 (.input .q)))
    have hc₁ : countValue (State.addr (arg s₁ 5)) v₁ Core.digestPrefix = c := by
      refine D₁.trans ?_
      rw [F₁.field (d := 108) (v := arg s₁ 4) (by simp), Iq₁.value]
      rfl
    have hc₂ : countValue (State.addr (arg s₁ 5)) v₂ Core.digestPrefix = c := by
      refine D₂.trans ?_
      rw [F₂.field (d := 108) (v := arg s₂ 4) (by simp), ← a4, ← Qe, Iq₁.value]
      rfl
    have C₁ := signCtx h₁ rfl rfl G₁ rfl rfl (Nat.min_le_left _ _ : c ≤ (arg s₁ 4).toNat)
    have C₂ := signCtx h₂ hb₂ hz₂ G₂ (by rw [a0] : (arg s₂ 0).toNat = (arg s₁ 0).toNat)
      (by rw [a2] : (arg s₂ 2).toNat = (arg s₁ 2).toNat) (by rw [← a4]; exact Nat.min_le_left _ _ : c ≤ (arg s₂ 4).toNat)
    have X : Pair (State.addr (arg s₁ 5)) ((arg s₁ 6).toNat * 8) ((arg s₁ 6).toNat * 8) (arg s₁ 0).toNat
        (arg s₁ 2).toNat (((arg s₁ 0).toNat + 7) / 8) (((arg s₁ 2).toNat + 7) / 8)
        (signIns (arg s₁ 0).toNat (arg s₁ 2).toNat c) (signVal s₁ c) (signVal s₂ c) v₁ v₂ :=
      ⟨C₁, C₂, pe G₁ G₂⟩
    have mp : (.input .p, (arg s₁ 0).toNat) ∈ signIns (arg s₁ 0).toNat (arg s₁ 2).toNat c := by simp [signIns]
    have mq : (.input .q, (arg s₁ 2).toNat) ∈ signIns (arg s₁ 0).toNat (arg s₁ 2).toNat c := by simp [signIns]
    have mg : (.input .g, (arg s₁ 0).toNat) ∈ signIns (arg s₁ 0).toNat (arg s₁ 2).toNat c := by simp [signIns]
    have my : (.input .y, (arg s₁ 0).toNat) ∈ signIns (arg s₁ 0).toNat (arg s₁ 2).toNat c := by simp [signIns]
    have mx : (.input .x, (arg s₁ 2).toNat) ∈ signIns (arg s₁ 0).toNat (arg s₁ 2).toNat c := by simp [signIns]
    have mk : (.input .nonce, (arg s₁ 2).toNat) ∈ signIns (arg s₁ 0).toNat (arg s₁ 2).toNat c := by simp [signIns]
    have md : (.input .digest, c) ∈ signIns (arg s₁ 0).toNat (arg s₁ 2).toNat c := by simp [signIns]
    have B₁ := shape_bounds valid
    have Dm₁ : DomainOk (signVal s₁ c (.input .p)) (signVal s₁ c (.input .q)) := ⟨B₁.1, B₁.2.1, B₁.2.2.1, B₁.2.2.2⟩
    have Dm₂ : DomainOk (signVal s₂ c (.input .p)) (signVal s₂ c (.input .q)) := by
      have e₁ : signVal s₂ c (.input .p) = signVal s₁ c (.input .p) := Vp
      have e₂ : signVal s₂ c (.input .q) = signVal s₁ c (.input .q) := Vq
      rw [e₁, e₂]; exact Dm₁
    have hm₂ : maskW (State.addr (arg s₁ 5)) v₂ = BitVec.allOnes 32 := by rw [K₂]; simp [mask32, valid₂]
    have O₁ := signOutput h₁ rfl rfl G₁
    have O₂ := signOutput h₂ hb₂ hz₂ G₂
    rw [← a2] at O₂
    have heo : PtrEq (State.addr (arg s₁ 5)) v₁ v₂ (.input .out) :=
      (G₁.field (d := 96) (v := s₁.gpr .r0) (by simp)).trans
        (hr0.trans (G₂.field (d := 96) (v := s₂.gpr .r0) (by simp)).symm)
    exact SameTrace.seq (signBody_trace X mp mq mg my mx mk md hc₁ hc₂ Dm₁ Dm₂ hm₁ hm₂ O₁ O₂ heo)
      (signBody_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) (X.C₁.inp my) (X.C₁.inp mx) (X.C₁.inp mk)
        (X.C₁.inp md) hc₁ Dm₁.hP Dm₁.hPo Dm₁.hQ Dm₁.hQo hm₁ O₁)
      (signBody_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) (X.C₂.inp my) (X.C₂.inp mx) (X.C₂.inp mk)
        (X.C₂.inp md) hc₂ Dm₂.hP Dm₂.hPo Dm₂.hQ Dm₂.hQo hm₂ O₂)
      fun w₁ w₂ ⟨_, _, Bd₁⟩ ⟨_, _, Bd₂⟩ =>
        tail_trace (G₁.ws.of_rest Bd₁.rest (by decide)) (G₂.ws.of_rest Bd₂.rest (by decide))

end VG.Proof.Dsa.Arm
