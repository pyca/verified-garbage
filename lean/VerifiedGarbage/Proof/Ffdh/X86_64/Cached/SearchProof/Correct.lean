module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Attempt
public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Data
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Outputs
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Branch
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.AttemptCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Guards
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Branch
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.AttemptCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Guards
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Entry
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Layout
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Classify
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.AttemptStep
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Exits

/-! ### `Ffdh.X86_64.Cached.SearchProof.Loop`, which this module and modules that import it used -/

section

/-! # Total correctness of the key-generation controller's loop -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.GenerationSearch
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search hiding attemptRun attemptOrRequest iteration code
open VG.Impl.Ffdh.X86_64.Cached.Search

/-- A finished search's state depends on its result's outcome and octets
consumed, not on its statuses. -/
theorem KeyDone.congr {p : KeyPublic} {original s : State} {r r' : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original r s) (ho : r.outcome = r'.outcome) (hu : r.used = r'.used) :
    KeyDone p original r' s := by
  have hs : r.status = r'.status := by unfold Spec.Ffdh.KeySearchResult.status; rw [ho]
  have hr : r.retries = r'.retries := by unfold Spec.Ffdh.KeySearchResult.retries; rw [ho]
  refine ⟨h.input, h.rd, h.wr, h.rsp, h.r12, h.saved, h.savedR12, h.usedPtr,
    by rw [← hu]; exact h.used, by rw [← hs]; exact h.status, ?_, ?_⟩
  · rw [h.policy]; unfold KeyPublic.policy; rw [hs, hr]
  · have ho' := h.output; unfold KeyOutput at ho' ⊢; rw [← ho]; exact ho'

/-- The loop's state: the search from octet `used`, with `keys` and `scalars`
left, leads to the expected result. -/
def KeyInvariant (p : KeyPublic) (original : State) (expected : Spec.Ffdh.KeySearchResult)
    (n : Nat) (s : State) : Prop :=
  ∃ used keys scalars, n = 128 * keys + scalars + 1 ∧ KeyLive p original used keys scalars s ∧
    expected.outcome = (p.tail (keyRand original) used keys scalars).outcome ∧
    expected.used = (p.tail (keyRand original) used keys scalars).used

theorem key_iteration (v : RoundImpl) {p : KeyPublic} {original s : State}
    {expected : Spec.Ffdh.KeySearchResult} {n : Nat}
    (h : KeyInvariant p original expected n s) :
    WP isa (iteration (attemptCall v)) s fun t =>
      (eval .e t = some false ∧ KeyDone p original expected t) ∨
      (eval .e t = some true ∧ ∃ m < n, KeyInvariant p original expected m t) := by
  obtain ⟨used, keys, scalars, hn, h, ho, hu⟩ := h
  have hlen : (keyRand original).length = p.randLen := by
    rw [← h.random]; simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have done : ∀ (r : Spec.Ffdh.KeySearchResult) t, KeyDone p original r t →
      r.outcome = (p.tail (keyRand original) used keys scalars).outcome →
      r.used = (p.tail (keyRand original) used keys scalars).used →
      WP isa (.block [.mov .rax (.mem (field 14)), .alu .cmp .rax (.imm 4)]) t fun t =>
        (eval .e t = some false ∧ KeyDone p original expected t) ∨
        (eval .e t = some true ∧ ∃ m < n, KeyInvariant p original expected m t) :=
    fun _ _ hd hro hru => WP.mono (done_loop_guard hd) fun _ ⟨hq, hdq⟩ =>
      Or.inl ⟨hq, hdq.congr (hro.trans ho.symm) (hru.trans hu.symm)⟩
  unfold iteration
  change WP isa (.seq _ (.seq _ _)) s _
  refine WP.seq (WP.mono (keys_guard h) fun u ⟨hu1, he⟩ => ?_)
  apply WP.seq
  refine WP.ite (decide (keys = 0)) he ?_ ?_
  · intro hz
    have hz' := of_decide_eq_true hz
    refine WP.mono (key_exhausted hu1) fun t ht => done _ t ht ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_exhausted (Or.inl hz')]
  intro hnz
  have hk : keys ≠ 0 := of_decide_eq_false hnz
  refine WP.seq (WP.mono (scalars_guard hu1) fun u ⟨hu2, he2⟩ => ?_)
  refine WP.ite (decide (scalars = 0)) he2 ?_ ?_
  · intro hz
    have hz' := of_decide_eq_true hz
    refine WP.mono (key_exhausted hu2) fun t ht => done _ t ht ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_exhausted (Or.inr hz')]
  intro hnz2
  have hs : scalars ≠ 0 := of_decide_eq_false hnz2
  unfold attemptOrRequest
  refine WP.seq (WP.mono (room_guard hu2) fun u ⟨hu3, hb⟩ => ?_)
  refine WP.ite _ hb ?_ ?_
  · intro hshort
    have hr : (keyRand original).length - used < p.len := by
      rw [hlen]; exact of_decide_eq_true hshort
    refine WP.mono (key_request hu3) fun t ht => done _ t ht ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_short hk hs hr]
  intro hlong
  have hroom : used + p.len ≤ p.randLen := by
    have := of_decide_eq_false hlong; have := h.used_le; omega_arith
  have hr : p.len ≤ (keyRand original).length - used := by rw [hlen]; omega_using [hroom]
  refine WP.seq (WP.mono (key_attempt_run v hu3 hroom) fun t ⟨ht, hp⟩ => ?_)
  refine WP.mono (key_classify ht hroom (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hs) hp)
    fun q hq => ?_
  rcases attemptStatus_cases (policy := .cached) p.a p.len ((keyRand original).drop used) with h1 | h2 | h3
  · simp only [KeyClassified, h1, ite_true] at hq
    refine done _ q hq ?_ ?_ <;> simp only [KeyPublic.tail, keyTail_accepted hk hs hr h1] <;> rfl
  · simp only [KeyClassified, h2, Nat.reduceEqDiff, ite_true, ite_false] at hq
    refine WP.mono (live_loop_guard hq.1 hq.2) fun z ⟨hz, hzl⟩ => Or.inr ⟨hz, _, ?_,
      used + p.len, keys, scalars - 1, rfl, hzl, ?_, ?_⟩
    · omega_using [hn, hs]
    · rw [ho]; simp only [KeyPublic.tail, keyTail_scalar hk hs hr h2]
    · rw [hu]; simp only [KeyPublic.tail, keyTail_scalar hk hs hr h2]
  · simp only [KeyClassified, h3, Nat.reduceEqDiff, ite_false] at hq
    refine WP.mono (live_loop_guard hq.1 hq.2) fun z ⟨hz, hzl⟩ => Or.inr ⟨hz, _, ?_,
      used + p.len, keys - 1, 128, rfl, hzl, ?_, ?_⟩
    · omega_using [hn, hk, hs]
    · rw [ho]; simp only [KeyPublic.tail, keyTail_public hk hs hr h3]
    · rw [hu]; simp only [KeyPublic.tail, keyTail_public hk hs hr h3]

theorem key_loop (v : RoundImpl) {p : KeyPublic} {original s : State}
    {expected : Spec.Ffdh.KeySearchResult} {n : Nat}
    (h : KeyInvariant p original expected n s) :
    WP isa (.loop (iteration (attemptCall v)) .e) s (KeyDone p original expected) :=
  WP.loop (M := isa) (body := iteration (attemptCall v)) (c := .e)
    (Q := KeyDone p original expected) (KeyInvariant p original expected)
    (fun _ _ h => key_iteration v h) n s h

end VG.Proof.Ffdh.X86_64.Cached.SearchProof

end

end

/-! ### `Ffdh.X86_64.Cached.SearchProof.Start`, which this module and modules that import it used -/

section

/-! # After its entry, the key-generation controller is at the tape's start -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64 (Slots)
open VG.Proof.Ffdh.X86_64.Generation (writeController writeController_frame writeController_word
  controllerValue)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

theorem KeyInput.keys_le {p : KeyPublic} {s : State} (h : KeyInput p s) : p.keys ≤ 128 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hk, -, -⟩ := h.1
  rw [← h.2]; exact hk

theorem KeyInput.scalars_le {p : KeyPublic} {s : State} (h : KeyInput p s) : p.scalars ≤ 128 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hs, -⟩ := h.1
  rw [← h.2]; exact hs

theorem KeyInput.width_word {p : KeyPublic} {s : State} (h : KeyInput p s) :
    s.mem.readW (stackArg s 6 + 16) 64 = BitVec.ofNat 64 (keyLen s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hw, -⟩ := h.1
  exact hw

private theorem word_zero (m : Mem) (B : Addr) : word m B 0 = m.readW B 64 := by
  simp only [Bignum.word, off, BitVec.add_zero]

theorem entry_headers {p : KeyPublic} {s : State} (h : KeyInput p s) :
    Slots (writeController s.mem p.control (entryValues s)) p.control
      (p.headers 0 p.keys p.scalars) := by
  have hw := h.width_word
  cases h.2
  intro e he
  simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [writeController_word _ _ _ (entryValues_bound s) _ (by dsimp only; decide)] <;>
    simp only [keyOfState, controllerValue, entryValues, headValues, tailValues,
      List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ite_true, ite_false,
      Nat.sub_zero, Nat.mul_zero, BitVec.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      Nat.mul_div_cancel _ (by decide : 0 < 8), word_zero]
  · simp only [Bignum.word, off]
    rfl
  · simp only [Bignum.word, off, Nat.reduceMul]
    exact hw.trans (by simp only [keyLen, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  · rfl

theorem key_start {p : KeyPublic} {s : State} (h : KeyInput p s) :
    WP isa (.block entry) s fun t => KeyLive p s 0 p.keys p.scalars t := by
  refine WP.mono (entry_ok h) fun t ⟨hr, hm, k⟩ => ?_
  have hf := writeController_frame s.mem p.control (entryValues s) (entryValues_bound s)
  have hf' : Frame (KeyInput.changes s) s.mem t.mem := by
    rw [hm]
    exact hf.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨inCtl s, by simp [KeyInput.changes, inWrites], by rw [← h.2]; exact fun _ hi => hi⟩
  refine ⟨h, Nat.zero_le _, h.keys_le, h.scalars_le, k.2.1, k.2.2, ?_, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.2]
    exact k.gpr (by decide)
  · intro r hcal hne
    exact k.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hcal
        rcases hcal with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact (hne rfl).elim | decide)
  · rw [hm]
    change word (writeController s.mem p.control (entryValues s)) p.control (8 * 4) = _
    rw [writeController_word _ _ _ (entryValues_bound s) 4 (by decide)]
    rfl
  · rw [h.random_frame hf']
    cases h.2
    rfl
  · rw [h.domain_frame hf']
    cases h.2
    rfl
  · exact h.context_frame hf'
  · exact h.args_frame hf'
  · rw [hm]
    exact entry_headers h

end VG.Proof.Ffdh.X86_64.Cached.SearchProof

end

end

/-! ### `Ffdh.X86_64.Cached.SearchProof.LoopCT`, which the modules that import this one used -/

section

/-! # The key search's loop leaks its public points alone -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search hiding attemptRun attemptOrRequest iteration code
open VG.Impl.Ffdh.X86_64.Cached.Search

private theorem leaf {Φ : KeyPoint → State → Prop} {c : Prog isa}
    (hΦ : ∀ q s, Φ q s → KeyAny q.inputs s) (hc : RelCT isa (Two KeyAny) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q.inputs, hΦ q _ h₁, hΦ q _ h₂⟩) fun _ _ h => h

private theorem branch_ct (v : RoundImpl) :
    RelCT isa (Two KeysGuard) (branch (attemptCall v)) (fun _ _ => True) := by
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (leaf (fun _ _ h => h.1.1.any) key_exhausted_ct) ?_
  refine RelCT.seq (two_piece [.r12, .rsp] (fun q _ _ h₁ h₂ => key_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide) scalars_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm)
    (leaf (fun _ _ h => h.1.1.any) key_exhausted_ct) ?_
  unfold attemptOrRequest
  refine RelCT.seq (two_piece [.r12, .rsp] (fun q _ _ h₁ h₂ => key_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide) room_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm)
    (leaf (fun _ _ h => h.1.1.any) key_request_ct) ?_
  exact RelCT.seq (two_post ((key_attempt_run_ct v).mono
      (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, attempt_of_room h₁, attempt_of_room h₂⟩) fun _ _ h => h)
    fun q s h => key_attempt_ready v q s (attempt_of_room h)) key_classify_ct

theorem key_iteration_ct (v : RoundImpl) :
    RelCT isa (Two KeyCTL) (iteration (attemptCall v)) (fun _ _ => True) := by
  unfold iteration
  change RelCT isa _ (.seq _ (.seq _ _)) _
  refine RelCT.seq (two_piece [.r12, .rsp] key_ctl_pins (by taint_decide) keys_ready) ?_
  exact RelCT.seq (two_post (branch_ct v) (key_branch_ready v))
    (two_taint [.r12] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact (branch_r12 h₁).trans (branch_r12 h₂).symm) (by taint_decide))

def KeyCTStep (q : KeyPoint) (s : State) : Prop :=
  if keyContinues q then eval .e s = some true ∧ KeyCTL (nextKeyPoint q) s
  else eval .e s = some false

theorem key_ct_step (v : RoundImpl) (q : KeyPoint) (s : State) (h : KeyCTL q s) :
    WP isa (iteration (attemptCall v)) s (KeyCTStep q) := by
  unfold iteration
  change WP isa (.seq _ (.seq _ _)) s _
  refine WP.seq (WP.mono (keys_ready q s h) fun u hu => ?_)
  refine WP.seq (WP.mono (key_branch_ready v q u hu) fun t ht => ?_)
  by_cases hc : keyContinues q
  · simp only [KeyBranchResult, hc, ite_true] at ht
    obtain ⟨⟨original, hl, hst⟩, hw⟩ := ht
    rw [← nextKeyPoint_inputs q] at hw
    refine WP.mono (live_loop_guard hl hw) fun z ⟨hz, hzl⟩ => ?_
    simp only [KeyCTStep, hc, ite_true]
    exact ⟨hz, original, hzl, hst⟩
  · simp only [KeyBranchResult, hc, ite_false] at ht
    obtain ⟨_, _, hd⟩ := ht
    refine WP.mono (done_loop_guard hd) fun z ⟨hz, _⟩ => ?_
    simp only [KeyCTStep, hc, ite_false]
    exact hz

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q, n = 128 * q.keys + q.scalars + 1 ∧ KeyCTL q s ∧ KeyCTL q t

private theorem iteration_pair (v : RoundImpl) (n : Nat) :
    RelCT isa (LoopPair n) (iteration (attemptCall v)) fun s t =>
      eval .e s = eval .e t ∧ (eval .e s = some false → True) ∧
      (eval .e s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : KeyPoint) (s : State) (h : n = 128 * q.keys + q.scalars + 1 ∧ KeyCTL q s) :
      WP isa (iteration (attemptCall v)) s fun t => n = 128 * q.keys + q.scalars + 1 ∧ KeyCTStep q t :=
    WP.mono (key_ct_step v q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((key_iteration_ct v).mono
    (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.2, h₂.2⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂⟩ => ⟨q, ⟨hn, h₁⟩, hn, h₂⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, _, h₂⟩
  by_cases hb : keyContinues q
  · simp only [KeyCTStep, hb, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ?_⟩
    refine ⟨128 * (nextKeyPoint q).keys + (nextKeyPoint q).scalars + 1, ?_, nextKeyPoint q, rfl,
      h₁.2, h₂.2⟩
    have := nextKeyPoint_measure hb
    omega_using [hn, this]
  · simp only [KeyCTStep, hb, ite_false] at h₁ h₂
    refine ⟨h₁.trans h₂.symm, fun _ => trivial, fun ht => ?_⟩
    rw [h₁] at ht
    cases ht

theorem key_loop_ct (v : RoundImpl) :
    RelCT isa (Two KeyCTL) (.loop (iteration (attemptCall v)) .e) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration (attemptCall v)) (c := .e)
    (Q := fun _ _ => True) LoopPair (iteration_pair v) (128 * q.keys + q.scalars + 1)
    _ _ _ _ _ _ ⟨q, rfl, hs, ht⟩ he₁ he₂

end VG.Proof.Ffdh.X86_64.Cached.SearchProof

end

end

/-! # The key-generation controller's correctness -/

@[expose] public section

/-! # Returning from the key search: the octets consumed, the status and r12 -/

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

theorem KeyInput.used_scr {p : KeyPublic} {s : State} (h : KeyInput p s) {t : State}
    (hw : t.wr = s.wr) : Scr t p.up 8 := by
  refine Scr.of_mem (by rw [hw, h.1.2.2.2.1, ← h.2]; simp [inWrites, inUsed, keyOfState]) ?_
  rw [← h.2]
  exact h.nowrap (r := inUsed s) (by simp [inWrites])

/-- The word for the octets consumed is apart from the outputs and the
controller's words. -/
theorem KeyInput.used_disjoint {p : KeyPublic} {s : State} (h : KeyInput p s) :
    (⟨p.xp, p.len⟩ : Region).Disjoint ⟨p.up, 8⟩ ∧ (⟨p.yp, p.len⟩ : Region).Disjoint ⟨p.up, 8⟩ ∧
      (⟨p.control, 128⟩ : Region).Disjoint ⟨p.up, 8⟩ := by
  have hpw := h.writes_pairwise
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hrsi, hrcx, -, -, -, -, -⟩ := h.1
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  rw [← h.2]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [inX, inUsed, keyOfState, hrsi] using hpw.1.2.1
  · simpa only [inY, inUsed, keyOfState, hrcx] using hpw.2.1.1
  · simpa only [inUsed, inCtl, keyOfState] using hpw.2.2.1.2.symm

theorem key_finish_values {p : KeyPublic} {original s : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) :
    WP isa (.block finish) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 result.status ∧ t.gpr .r12 = original.gpr .r12 ∧
      t.mem = s.mem.writeW p.up (BitVec.ofNat 64 result.used) ∧
      Keep [.rax, .rcx, .rdx, .r12] s t := by
  have scr := h.input.control_scr (t := s) h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hup : InRegions s.wr p.up 8 := by
    simpa only [off, BitVec.add_zero] using (h.input.used_scr h.wr).st (d := 0) (by decide)
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .r12] (Q := fun t =>
    t.gpr .rax = BitVec.ofNat 64 result.status ∧ t.gpr .r12 = original.gpr .r12 ∧
    t.mem = s.mem.writeW p.up (BitVec.ofNat 64 result.used)) ?_ rfl)
    fun _ ⟨⟨ha, hr, hm⟩, k⟩ => ⟨ha, hr, hm, k⟩
  unfold finish
  xrun [State.ea, field, off, h.r12, h.usedPtr, h.used, h.status, h.savedR12,
    BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, hup,
    hl 120 (by decide), hl 88 (by decide), hl 112 (by decide), hl 32 (by decide)]

/-- What the search returns, for its result. -/
def KeyReturned (p : KeyPublic) (result : Spec.Ffdh.KeySearchResult) (t : State) : Prop :=
  ((t.gpr .rax).setWidth 32).toNat = result.status ∧ KeyOutput p result t.mem ∧
    Spec.Rsa.wordsAt t.mem p.control 4 = p.policy result ∧
    Spec.Rsa.wordsAt t.mem p.up 1 = [BitVec.ofNat 64 result.used]

theorem key_finish {p : KeyPublic} {original s : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) :
    WP isa (.block finish) s fun t => KeyReturned p result t ∧
      (∀ reg ∈ calleeSaved, t.gpr reg = original.gpr reg) ∧ t.rd = original.rd ∧ t.wr = original.wr := by
  refine WP.mono (key_finish_values h) fun t ⟨ha, hr12, hm, k⟩ => ?_
  have hd := h.input.used_disjoint
  have hk := h.input.len_lt
  have hf : Frame [⟨p.up, 8⟩] s.mem t.mem := by
    rw [hm]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hb : ∀ q : Addr, (⟨q, p.len⟩ : Region).Disjoint ⟨p.up, 8⟩ →
      Spec.Rsa.bytesAt t.mem q p.len = Spec.Rsa.bytesAt s.mem q p.len := by
    intro q hq
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hq)
      (show p.len ≤ 2 ^ 64 by omega_using [hk]) (List.mem_range.mp hi)
  have hc (j : Nat) (hj : j < 4) : word t.mem p.control (8 * j) = word s.mem p.control (8 * j) :=
    hf.readW (r := ⟨p.control, 128⟩)
      (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hd.2.2) (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, k.2.1.trans h.rd, k.2.2.trans h.wr⟩
  · rw [ha]
    have : result.status < 4 := by unfold Spec.Ffdh.KeySearchResult.status; split <;> decide
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [this]
  · have ho := h.output
    unfold KeyOutput at ho ⊢
    rw [hb _ hd.1, hb _ hd.2.1]
    exact ho
  · have he : Spec.Rsa.wordsAt t.mem p.control 4 = Spec.Rsa.wordsAt s.mem p.control 4 := by
      change [word t.mem p.control 0, word t.mem p.control 8, word t.mem p.control 16,
        word t.mem p.control 24] = _
      rw [hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide)]
      rfl
    exact he.trans h.policy
  · change [word t.mem p.up 0] = [_]
    rw [hm]
    congr 1
    simpa only [Bignum.word, off, BitVec.add_zero] using
      Mem.readW_writeW_self64 s.mem p.up (BitVec.ofNat 64 result.used)
  · intro reg hreg
    by_cases he : reg = .r12
    · subst he; exact hr12
    · exact (k.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
        rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact (he rfl).elim | decide)).trans (h.saved reg hreg he)

end VG.Proof.Ffdh.X86_64.Cached.SearchProof

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.GenerationSearch
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search hiding attemptRun attemptOrRequest iteration code
open VG.Impl.Ffdh.X86_64.Cached.Search

theorem initial_key_result {p : KeyPublic} {s : State} (h : KeyInput p s) :
    keyResult s = p.tail (keyRand s) 0 p.keys p.scalars := by
  cases h.2
  simp only [keyResult, KeyPublic.tail, keyTail, after, keyOfState, KeyPublic.a, List.drop_zero, GenerationPolicy.search,
    Nat.zero_add]

theorem returned_post {p : KeyPublic} {s t : State} (h : KeyInput p s)
    (hr : KeyReturned p (keyResult s) t) : keyPost s t := by
  cases h.2
  exact hr

theorem key_correct_ok (v : RoundImpl) {s : State} (h : keyPre s) :
    WP isa (code (attemptCall v)) s fun t => keyPost s t ∧
      (∀ reg ∈ calleeSaved, t.gpr reg = s.gpr reg) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  let p := keyOfState s
  have hp : KeyInput p s := ⟨h, rfl⟩
  unfold code
  change WP isa (.seq _ (.seq _ _)) s _
  refine WP.seq (WP.mono (key_start hp) fun u hu => ?_)
  have hinv : KeyInvariant p s (keyResult s) (128 * p.keys + p.scalars + 1) u :=
    ⟨0, p.keys, p.scalars, rfl, hu, by rw [initial_key_result hp], by rw [initial_key_result hp]⟩
  refine WP.seq (WP.mono (key_loop v hinv) fun t ht => ?_)
  refine WP.mono (key_finish ht) fun q ⟨hr, hg, hrd, hwr⟩ => ?_
  exact ⟨returned_post hp hr, hg, hrd, hwr⟩

end VG.Proof.Ffdh.X86_64.Cached.SearchProof
