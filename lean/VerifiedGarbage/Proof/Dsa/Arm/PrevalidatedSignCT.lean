module

public import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.Arm.KeyTrace
public import VerifiedGarbage.Proof.Dsa.Arm.SignCT
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Dsa.Arm.BodyTrace
import VerifiedGarbage.Proof.Dsa.Arm.ShapeTrace
public import VerifiedGarbage.Proof.Dsa.Arm.OpTrace
import VerifiedGarbage.Proof.Dsa.Arm.ValidateTrace
import VerifiedGarbage.Proof.Dsa.Arm.ScheduleTrace
import VerifiedGarbage.Proof.Dsa.Arm.Sign
import VerifiedGarbage.Proof.Dsa.Arm.ValidateOps
import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.PrivateKeyWitness


-- separate module: the constant-time proof costs more than its imports, and the randomized
-- signer's proofs in `RandomSignVerified.lean` should not re-check it.

/-!
# DSA signing for a validated private key on 32-bit ARM: constant time

Two runs whose public data agree (`signArm.pub`) leak the same trace, as
for the fully checked signer (`SignCT.lean`): the prevalidated signer runs
the same parts but the checks of the key.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest eval_eq)
open VG.Proof.Ecdsa.Arm (mask32)

theorem signPrevCompute_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ c : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (mx : (.input .x, qLen) ∈ ins) (mk : (.input .nonce, qLen) ∈ ins)
    (md : (.input .digest, c) ∈ ins)
    (hc₁ : countValue base s₁ Core.digestPrefix = c) (hc₂ : countValue base s₂ Core.digestPrefix = c)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (PrevalidatedSign.compute pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have Lr : Impl.Dsa.Layout.r = 14720 := rfl
  have Ls : Impl.Dsa.Layout.s = 14752 := rfl
  have L2 : Impl.Dsa.Layout.qMinusTwo = 14912 := rfl
  have ho : 4960 ≤ Impl.Dsa.Layout.qMinusTwo ∧ Impl.Dsa.Layout.qMinusTwo + qLen ≤ 15712 := by omega
  have Q₁ := operand_lt_of (X.C₁.inp mq)
  have Q₂ := operand_lt_of (X.C₂.inp mq)
  have hQ₁ := D₁.hQ
  have hQ₂ := D₂.hQ
  simp only [PrevalidatedSign.compute, Core.sequence, List.foldr]
  refine SameTrace.seq (minus_trace (amount := 2) (output := Impl.Dsa.Layout.qMinusTwo)
      (X.C₁.opPre mq X.C₁.S.wq (by omega) D₁.hQo) (X.C₂.opPre mq X.C₁.S.wq (by omega) D₂.hQo) (X.E _ mq))
    (minus_ok (output := Impl.Dsa.Layout.qMinusTwo) X.C₁.S.ws (by omega) X.C₁.S.wq (X.C₁.inp mq).toReady
      (X.C₁.inp mq).value (by omega) D₁.hQo (by omega) (by decide) (by decide) (by omega) (by decide))
    (minus_ok (output := Impl.Dsa.Layout.qMinusTwo) X.C₂.S.ws (by omega) X.C₁.S.wq (X.C₂.inp mq).toReady
      (X.C₂.inp mq).value (by omega) D₂.hQo (by omega) (by decide) (by decide) (by omega) (by decide))
    fun u₁ u₂ ⟨B₁, St₁⟩ ⟨B₂, St₂⟩ => ?_
  have T₁ := St₁.run (.inr ho)
  have T₂ := St₂.run (.inr ho)
  have X₁ := X.run T₁ T₂
  refine SameTrace.seq (range_trace X₁.C₁.S.ws X₁.C₂.S.ws (by omega_arith) (by omega_arith) X.C₁.S.wq
      (X₁.C₁.inp mq).toReady (X₁.C₂.inp mq).toReady (X₁.C₁.inp mk).toReady (X₁.E _ mq) (X₁.E _ mk) false)
    (range_ok X₁.C₁.S.ws (by omega_arith) X.C₁.S.wq (X₁.C₁.inp mq).toReady (X₁.C₁.inp mk).toReady false)
    (range_ok X₁.C₂.S.ws (by omega_arith) X.C₁.S.wq (X₁.C₂.inp mq).toReady (X₁.C₂.inp mk).toReady false)
    fun v₁ v₂ ⟨_, Sa₁⟩ ⟨_, Sa₂⟩ => ?_
  have R₁ := Sa₁.run (.inl ⟨rfl, rfl⟩)
  have R₂ := Sa₂.run (.inl ⟨rfl, rfl⟩)
  have X₂ := X₁.run R₁ R₂
  have M₁ : localVal base v₁ Impl.Dsa.Layout.qMinusTwo qLen = val₁ (.input .q) - 2 := by
    rw [Sa₁.localVal_eq (by decide) (by omega_arith) (by omega_arith) (by omega_arith)]
    exact localVal_of_bytes B₁ (by omega)
  have M₂ : localVal base v₂ Impl.Dsa.Layout.qMinusTwo qLen = val₂ (.input .q) - 2 := by
    rw [Sa₂.localVal_eq (by decide) (by omega_arith) (by omega_arith) (by omega_arith)]
    exact localVal_of_bytes B₂ (by omega)
  have c₁ := ((countValue_run R₁).trans (countValue_run T₁)).trans hc₁
  have c₂ := ((countValue_run R₂).trans (countValue_run T₂)).trans hc₂
  refine SameTrace.seq (sign_trace X₂ mp mq mg mx mk md c₁ c₂ D₁ D₂)
    (sign_ok X₂.C₁.S (X₂.C₁.inp mp) (X₂.C₁.inp mq) (X₂.C₁.inp mg) (X₂.C₁.inp mx) (X₂.C₁.inp mk) (X₂.C₁.inp md)
      c₁ M₁ D₁.hP D₁.hPo D₁.hQ D₁.hQo)
    (sign_ok X₂.C₂.S (X₂.C₂.inp mp) (X₂.C₂.inp mq) (X₂.C₂.inp mg) (X₂.C₂.inp mx) (X₂.C₂.inp mk) (X₂.C₂.inp md)
      c₂ M₂ D₂.hP D₂.hPo D₂.hQ D₂.hQo)
    fun u₁ u₂ ⟨_, _, _, A₁⟩ ⟨_, _, _, A₂⟩ => ?_
  have X₃ := X₂.run A₁ A₂
  have ok : ∀ o, o < 2 ^ 16 → PtrOk (.local o) := local_ptrOk
  refine SameTrace.assoc_left (SameTrace.seq (zero_trace X₃.C₁.S.ws X₃.C₂.S.ws (by omega_arith) (by omega_arith)
      (ok _ (by omega_arith)) (ptrEq_local X₃.C₁.S.ws X₃.C₂.S.ws _) true)
    (zero_ok X₃.C₁.S.ws (by omega_arith) X.C₁.S.wq
      (localReady (o := Impl.Dsa.Layout.r) (len := qLen) X₃.C₁.S.ws (by omega_arith) (by omega_arith) (by omega_arith)) true)
    (zero_ok X₃.C₂.S.ws (by omega_arith) X.C₁.S.wq
      (localReady (o := Impl.Dsa.Layout.r) (len := qLen) X₃.C₂.S.ws (by omega_arith) (by omega_arith) (by omega_arith)) true)
    fun u₁ u₂ ⟨_, St₁⟩ ⟨_, St₂⟩ => ?_)
  have w₁ := St₁.ws X₃.C₁.S.ws
  have w₂ := St₂.ws X₃.C₂.S.ws
  exact SameTrace.seq (zero_trace w₁ w₂ (by omega_arith) (by omega_arith) (ok _ (by omega_arith)) (ptrEq_local w₁ w₂ _) true)
    (F₁ := fun _ => True) (F₂ := fun _ => True)
    (WP.mono (zero_ok w₁ (by omega_arith) X.C₁.S.wq
      (localReady (o := Impl.Dsa.Layout.s) (len := qLen) w₁ (by omega_arith) (by omega_arith) (by omega_arith)) true) fun _ _ => trivial)
    (WP.mono (zero_ok w₂ (by omega_arith) X.C₁.S.wq
      (localReady (o := Impl.Dsa.Layout.s) (len := qLen) w₂ (by omega_arith) (by omega_arith) (by omega_arith)) true) fun _ _ => trivial)
    fun _ _ _ _ => SameTrace.block_nil

theorem signPrevBody_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ c : Nat} {ins : List (Pointer × Nat)}
    {val₁ val₂ : Pointer → Nat} {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (mx : (.input .x, qLen) ∈ ins) (mk : (.input .nonce, qLen) ∈ ins)
    (md : (.input .digest, c) ∈ ins)
    (hc₁ : countValue base s₁ Core.digestPrefix = c) (hc₂ : countValue base s₂ Core.digestPrefix = c)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q)))
    (hm₁ : maskW base s₁ = BitVec.allOnes 32) (hm₂ : maskW base s₂ = BitVec.allOnes 32)
    (O₁ : Output s₁ base size₁ (2 * qLen)) (O₂ : Output s₂ base size₂ (2 * qLen))
    (heo : PtrEq base s₁ s₂ (.input .out)) :
    SameTrace isa (PrevalidatedSign.body pLen qLen) s₁ s₂ := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := X.C₁.S.lens
  have b₁ := X.C₁.S.big
  have b₂ := X.C₂.S.big
  have Q₁ := operand_lt_of (X.C₁.inp mq)
  have Q₂ := operand_lt_of (X.C₂.inp mq)
  have hQ₁ := D₁.hQ
  have hQ₂ := D₂.hQ
  have Lr : Impl.Dsa.Layout.r = 14720 := rfl
  have Ls : Impl.Dsa.Layout.s = 14752 := rfl
  unfold PrevalidatedSign.body
  refine SameTrace.seq (signPrevCompute_trace X mp mq mg mx mk md hc₁ hc₂ D₁ D₂)
    (signPrevCompute_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) (X.C₁.inp mx) (X.C₁.inp mk)
      (X.C₁.inp md) hc₁ D₁.hP D₁.hPo D₁.hQ D₁.hQo)
    (signPrevCompute_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) (X.C₂.inp mx) (X.C₂.inp mk)
      (X.C₂.inp md) hc₂ D₂.hP D₂.hPo D₂.hQ D₂.hQo)
    fun u₁ u₂ ⟨F₁, Ru₁, Su₁, A₁⟩ ⟨F₂, Ru₂, Su₂, A₂⟩ => ?_
  have X₁ := X.run A₁ A₂
  have hO : ∀ r ∈ runRanges, r.1 + r.2 ≤ 64 ∨ 116 ≤ r.1 := by decide
  have pe : PtrEq base u₁ u₂ (.input .out) := by
    unfold PtrEq
    rw [pointerValue_keep (A₁.rest.gpr .r12 (by decide)) A₁.mem hO (p := .input .out) (by decide : Impl.Dsa.Layout.Field.out ≠ .mask),
      pointerValue_keep (A₂.rest.gpr .r12 (by decide)) A₂.mem hO (p := .input .out) (by decide : Impl.Dsa.Layout.Field.out ≠ .mask)]
    exact heo
  have mu₁ : maskW base u₁ = mask32 (signPrevChecks (val₁ (.input .p)) (val₁ (.input .q)) (val₁ (.input .g))
      (val₁ (.input .x)) (val₁ (.input .nonce)) (val₁ (.input .digest))) := by
    rw [F₁, hm₁, BitVec.allOnes_and]
  have mu₂ : maskW base u₂ = mask32 (signPrevChecks (val₂ (.input .p)) (val₂ (.input .q)) (val₂ (.input .g))
      (val₂ (.input .x)) (val₂ (.input .nonce)) (val₂ (.input .digest))) := by
    rw [F₂, hm₂, BitVec.allOnes_and]
  have qlt₁ : ∀ x, x % val₁ (.input .q) < 256 ^ qLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Q₁
  have qlt₂ : ∀ x, x % val₂ (.input .q) < 256 ^ qLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Q₂
  refine SameTrace.seq (writeScalar_trace X₁.C₁.S.ws X₁.C₂.S.ws (by omega_arith) (by omega_arith) X.C₁.S.wq q32 (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith) pe false)
    (writeScalar_ok X₁.C₁.S.ws b₁ X.C₁.S.wq q32 (by omega_arith) (by omega_arith) Ru₁ (by simp only [rValue]; exact qlt₁ _)
      _ mu₁ (O₁.run A₁) false)
    (writeScalar_ok X₁.C₂.S.ws b₂ X.C₁.S.wq q32 (by omega_arith) (by omega_arith) Ru₂ (by simp only [rValue]; exact qlt₂ _)
      _ mu₂ (O₂.run A₂) false)
    fun v₁ v₂ ⟨_, mv₁, Pv₁, Wv₁, Kv₁, _, Bdv₁⟩ ⟨_, mv₂, Pv₂, Wv₂, Kv₂, _, Bdv₂⟩ => ?_
  have wv₁ := X₁.C₁.S.ws.of_rest Bdv₁.rest (by decide)
  have wv₂ := X₁.C₂.S.ws.of_rest Bdv₂.rest (by decide)
  refine SameTrace.seq (writeScalar_trace wv₁ wv₂ (by omega_arith) (by omega_arith) X.C₁.S.wq q32 (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith) (by unfold PtrEq; rw [Pv₁, Pv₂]; exact pe) true)
    (writeScalar_ok (v := sValue (val₁ (.input .p)) (val₁ (.input .q)) (val₁ (.input .g)) (val₁ (.input .x))
      (val₁ (.input .nonce)) (val₁ (.input .digest))) wv₁ b₁ X.C₁.S.wq q32 (by omega_arith) (by omega_arith)
      (by rw [Kv₁ _ _ (by omega_arith) (by omega_arith)]; exact Su₁) (by simp only [sValue]; exact qlt₁ _) _ (mv₁.trans mu₁)
      ((O₁.run A₁).keep Pv₁ Wv₁) true)
    (writeScalar_ok (v := sValue (val₂ (.input .p)) (val₂ (.input .q)) (val₂ (.input .g)) (val₂ (.input .x))
      (val₂ (.input .nonce)) (val₂ (.input .digest))) wv₂ b₂ X.C₁.S.wq q32 (by omega_arith) (by omega_arith)
      (by rw [Kv₂ _ _ (by omega_arith) (by omega_arith)]; exact Su₂) (by simp only [sValue]; exact qlt₂ _) _ (mv₂.trans mu₂)
      ((O₂.run A₂).keep Pv₂ Wv₂) true)
    fun w₁ w₂ ⟨_, _, _, _, _, _, Bdw₁⟩ ⟨_, _, _, _, _, _, Bdw₂⟩ => ?_
  exact SameTrace.of_relCT result_relCT
    (agree0 (wv₁.of_rest Bdw₁.rest (by decide)) (wv₂.of_rest Bdw₂.rest (by decide)))

theorem signPrevDispatch_trace (widths : List (Nat × Nat))
    {s₁ s₂ : State} {base : Addr} {size₁ size₂ pLen qLen : Nat}
    (h₁ : Ws s₁ base size₁) (h₂ : Ws s₂ base size₂) (hz₁ : 120 ≤ size₁) (hz₂ : 120 ≤ size₂)
    (member : (pLen, qLen) ∈ widths) (bound : ∀ w ∈ widths, w.1 < 2 ^ 16 ∧ w.2 < 2 ^ 16)
    (hp₁ : (hdr base s₁ 100).toNat = pLen) (hq₁ : (hdr base s₁ 104).toNat = qLen)
    (hp₂ : (hdr base s₂ 100).toNat = pLen) (hq₂ : (hdr base s₂ 104).toNat = qLen)
    (body : ∀ t₁ t₂, Rest [.r4, .r5] s₁ t₁ → t₁.mem = s₁.mem → Rest [.r4, .r5] s₂ t₂ → t₂.mem = s₂.mem →
      SameTrace isa (.seq (PrevalidatedSign.sized pLen qLen) Tail) t₁ t₂) :
    SameTrace isa (.seq (PrevalidatedSign.dispatch widths) Tail) s₁ s₂ := by
  induction widths generalizing s₁ s₂ with
  | nil => simp only [List.not_mem_nil] at member
  | cons w rest ih =>
    obtain ⟨wp, wq⟩ := w
    have B := bound (wp, wq) List.mem_cons_self
    unfold PrevalidatedSign.dispatch
    refine SameTrace.assoc_left (SameTrace.seq (widthMatch_trace h₁ h₂ hz₁ hz₂ hp₁ hp₂ B.1)
      (widthMatch_ok h₁ hz₁ hp₁ hq₁ B.1 B.2) (widthMatch_ok h₂ hz₂ hp₂ hq₂ B.1 B.2)
      fun t₁ t₂ ⟨Z₁, R₁, M₁⟩ ⟨Z₂, R₂, M₂⟩ => ?_)
    refine SameTrace.seq_ite (by rw [eval_eq, eval_eq, Z₁, Z₂]) (fun ht => ?_) (fun hf => ?_)
    · have Both : pLen = wp ∧ qLen = wq := of_decide_eq_true (by rw [eval_eq, Z₁] at ht; exact Option.some.inj ht)
      rw [← Both.1, ← Both.2]
      exact body t₁ t₂ R₁ M₁ R₂ M₂
    · have Both : ¬ (pLen = wp ∧ qLen = wq) :=
        of_decide_eq_false (by rw [eval_eq, Z₁] at hf; exact Option.some.inj hf)
      exact ih (h₁.of_rest R₁ (by decide)) (h₂.of_rest R₂ (by decide))
        (by simpa only [List.mem_cons, Prod.mk.injEq, Both, false_or] using member)
        (fun w hw => bound w (List.mem_cons_of_mem _ hw))
        (by simp only [hdr, M₁]; exact hp₁) (by simp only [hdr, M₁]; exact hq₁)
        (by simp only [hdr, M₂]; exact hp₂) (by simp only [hdr, M₂]; exact hq₂)
        fun u₁ u₂ Ru₁ Mu₁ Ru₂ Mu₂ => body u₁ u₂ (R₁.trans Ru₁) (Mu₁.trans M₁) (R₂.trans Ru₂) (Mu₂.trans M₂)

/-- The checks of the key that its validation makes hold. -/
theorem prevSignPre_checks {s : State} (h : prevSignPre s) (c : Nat) :
    publicChecks (signVal s c (.input .p)) (signVal s c (.input .q)) (signVal s c (.input .g))
        (signVal s c (.input .y)) ∧
      (0 < signVal s c (.input .x) ∧ signVal s c (.input .x) < signVal s c (.input .q)) ∧
      signVal s c (.input .g) ^ signVal s c (.input .x) % signVal s c (.input .p) = signVal s c (.input .y) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, fK, _, _, _, hv, _, hr3, _⟩ := h.1
  exact (of_decide_eq_true ((VG.Proof.Dsa.validatePrivateKeyBytes_eq hv
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hr3)
    (signKey _ _ (by omega_arith))).symm.trans h.2)).2

theorem prevSign_constantTime : ConstantTime isa prevSignArm.pre prevSignArm.pub PrevalidatedSign.sign := by
  refine SameTrace.constantTime fun s₁ s₂ h₁' h₂' pub => ?_
  have h₁ := h₁'.1
  have h₂ := h₂'.1
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
  simp only [PrevalidatedSign.sign, Core.sequence, List.foldr]
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
  refine signPrevDispatch_trace _ E₁.ws E₂.ws (by omega_arith) (by omega_arith) (widths_mem hv) (by decide)
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
  unfold PrevalidatedSign.sized
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
    have pc₁ := prevSignPre_checks h₁' c
    have pc₂ := prevSignPre_checks h₂' c
    exact SameTrace.seq (signPrevBody_trace X mp mq mg mx mk md hc₁ hc₂ Dm₁ Dm₂ hm₁ hm₂ O₁ O₂ heo)
      (signPrevBody_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) (X.C₁.inp mx) (X.C₁.inp mk)
        (X.C₁.inp md) hc₁ Dm₁.hP Dm₁.hPo Dm₁.hQ Dm₁.hQo hm₁ O₁ pc₁)
      (signPrevBody_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) (X.C₂.inp mx) (X.C₂.inp mk)
        (X.C₂.inp md) hc₂ Dm₂.hP Dm₂.hPo Dm₂.hQ Dm₂.hQo hm₂ O₂ pc₂)
      fun w₁ w₂ ⟨_, _, Bd₁⟩ ⟨_, _, Bd₂⟩ =>
        tail_trace (G₁.ws.of_rest Bd₁.rest (by decide)) (G₂.ws.of_rest Bd₂.rest (by decide))

end VG.Proof.Dsa.Arm
