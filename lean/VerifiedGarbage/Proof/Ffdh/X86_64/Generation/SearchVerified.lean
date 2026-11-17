module

public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Spec.Ffdh.SievedContract
import VerifiedGarbage.Proof.Ffdh.SievedBounds
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchEntryCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchFinishCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchBranch
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchIterationCT
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDone
public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Depth
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchClassify
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchShort
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCandidatePost
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchEntry

/-! ### `Ffdh.X86_64.Generation.SearchStart`, which only this module used -/

section

/-! # Establish the complete parameter-search invariant -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchEntryTail.lean`, which only this module imported.
section

/-! # Capture stack arguments without changing the caller's argument area -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem search_entry_head_args {p : SearchPublic} {s : State} (h : SearchInput p s)
    {t : State} (hm : t.mem = writeController s.mem p.control (searchHeadValues s))
    (k : Keep [.rax, .r8, .r12] s t) (j : Nat) (hj : j < 4) :
    stackArg t j = stackArg s j := by
  have hf := writeController_frame s.mem p.control (searchHeadValues s) (searchHeadValues_bound s)
  have hd : (inputArgs s).Disjoint ⟨p.control, 128⟩ := by
    cases h.2
    exact (h.1.2.2.2.2.2.1 _ (by simp)).symm
  change t.mem.readW (stackArgAddr t j) 64 = _
  have ha : stackArgAddr t j = stackArgAddr s j := by
    simp only [stackArgAddr, k.1 .rsp (by simp)]
  rw [ha, hm]
  exact hf.readW (input_arg_contains s hj) (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact hd) (by decide)

theorem search_entry_tail_ok {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hm : t.mem = writeController s.mem p.control (searchHeadValues s))
    (k : Keep [.rax, .r8, .r12] s t) (hr : t.gpr .r12 = p.control) :
    WP isa (.block entryTail) t fun u =>
      u.mem = writeController t.mem p.control (searchTailValues s) ∧
      Keep [.rax, .r10, .r11] t u := by
  have scr := h.control_scr (s := t) k.2.2
  have hs : ∀ d, d + 8 ≤ 128 → InRegions t.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have ha (j : Nat) (hj : j < 4) : InRegions (t.rd ++ t.wr) (stackArgAddr t j) 8 := by
    simpa only [k.2.1, k.2.2, stackArgAddr, k.1 .rsp (by simp)] using input_args h j hj
  have hv (j : Nat) (hj : j < 4) : t.mem.readW (stackArgAddr t j) 64 = stackArg s j :=
    search_entry_head_args h hm k j hj
  refine WP.keep [.rax, .r10, .r11] ?_ rfl
  unfold entryTail writeController searchTailValues
  simp only [List.foldl_cons, List.foldl_nil]
  have ha0 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 8) 8 := ha 0 (by decide)
  have ha1 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 16) 8 := ha 1 (by decide)
  have ha2 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 24) 8 := ha 2 (by decide)
  have hv0 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s 0 := hv 0 (by decide)
  have hv1 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 16) 64 = stackArg s 1 := hv 1 (by decide)
  have hv2 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s 2 := hv 2 (by decide)
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul,
    hr, ha0, ha1, ha2, hv0, hv1, hv2, hs 88 (by decide), hs 104 (by decide),
    hs 120 (by decide), hs 96 (by decide)]
  rfl

theorem search_entry_ok {p : SearchPublic} {s : State} (h : SearchInput p s) :
    WP isa (.block entry) s fun t =>
      t.gpr .r12 = p.control ∧
      t.mem = writeController s.mem p.control (searchEntryValues s) ∧
      Keep [.rax, .r8, .r12, .r10, .r11] s t := by
  rw [entry, WP.block_append_iff]
  refine WP.mono (search_entry_head_ok h) fun t ⟨hr, hm, k⟩ => ?_
  refine WP.mono (search_entry_tail_ok h hm k hr) fun u ⟨hu, ku⟩ => ?_
  exact ⟨(ku.gpr (by decide)).trans hr,
    by rw [hu, hm, searchEntryValues, writeController_append],
    (k.trans ku).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.Generation
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem searchEntryValues_bound (s : State) : ∀ e ∈ searchEntryValues s, e.1 < 16 := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact searchHeadValues_bound s e he
  · exact searchTailValues_bound s e he

theorem search_entry_headers {p : SearchPublic} {s : State} (h : SearchInput p s) :
    Slots (writeController s.mem p.control (searchEntryValues s)) p.control (p.headers 0 p.remaining) := by
  cases h.2
  have hlen : (pcRand s).length = (stackArg s 0).toNat := by
    simp only [pcRand, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have hwidth : BitVec.ofNat 64 ((s.gpr .r8).setWidth 32).toNat =
      ((s.gpr .r8).setWidth 32).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  intro e he
  simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [writeController_word _ _ _ (searchEntryValues_bound s) _ (by dsimp only; decide)] <;>
    simp only [searchOfState, candidateOfState, SearchPublic.c, controllerValue,
      searchEntryValues, searchHeadValues, searchTailValues, List.foldl_append,
      List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ite_true, ite_false,
      Nat.sub_zero, Nat.mul_zero, off, BitVec.add_zero, BitVec.ofNat_toNat,
      hwidth, hlen, BitVec.setWidth_eq]
  · simp only [Bignum.word, off, BitVec.add_zero]
  · exact h.1.2.2.2.2.2.2.2.2.2.2.1
  · exact h.1.2.2.2.2.2.2.2.2.2.2.2.1
  · rfl
  · rw [Nat.mul_div_cancel _ (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem search_start {p : SearchPublic} {s : State} (h : SearchInput p s) :
    WP isa (.block entry) s fun t => SearchLive p s 0 p.remaining t := by
  refine WP.mono (search_entry_ok h) fun t ⟨hr, hm, k⟩ => ?_
  have hf := writeController_frame s.mem p.control (searchEntryValues s) (searchEntryValues_bound s)
  refine ⟨h, by omega_using [], by omega_using [], k.2.1, k.2.2, ?_, hr, ?_, ?_, ?_, ?_⟩
  · cases h.2
    exact k.gpr (by decide)
  · intro r hcal hne
    exact k.gpr (by cases r <;> simp_all [calleeSaved])
  · rw [hm]
    change word (writeController s.mem p.control (searchEntryValues s)) p.control (8 * 4) = _
    rw [writeController_word _ _ _ (searchEntryValues_bound s) 4 (by decide)]
    rfl
  · have hf' : Frame (s.wr ++ [below (s.gpr .rsp) 160]) s.mem t.mem := by
      rw [hm]
      exact hf.sub fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨inputControl s, List.mem_append_left _ (by rw [h.1.2.2.2.1]; simp), by
          cases h.2; exact fun _ hi => hi⟩
    rw [h.random_frame hf']
    cases h.2
    dsimp only [searchOfState, SearchPublic.c, candidateOfState]
    simp only [pcRand, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  · rw [hm]
    exact search_entry_headers h

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchLoop`, which only this module used -/

section

/-! ### `Ffdh.X86_64.Generation.SearchLoopGuards`, which this module and modules that import it used -/

section

/-! # Only a native rejection continues the search loop -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem done_loop_guard {p : SearchPublic} {original s : State} {result : Spec.Ffdh.ParameterSearchResult}
    (h : SearchDone p original result s) :
    WP isa (.block [.mov .rax (.mem (field 14)), .alu .cmp .rax (.imm 4)]) s fun t =>
      eval .e t = some false ∧ SearchDone p original result t := by
  have hb : result.status < 2 ^ 64 := by cases result <;> dsimp only [Spec.Ffdh.ParameterSearchResult.status] <;> decide
  refine WP.mono (loop_guard (h.input.control_scr h.wr) h.r12 h.status hb)
    fun t ⟨⟨he, hm⟩, k⟩ => ?_
  refine ⟨?_, h.keep k hm (by decide)⟩
  cases result <;> exact he

theorem live_loop_guard {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (hs : word s.mem p.control 112 = 4) :
    WP isa (.block [.mov .rax (.mem (field 14)), .alu .cmp .rax (.imm 4)]) s fun t =>
      eval .e t = some true ∧ SearchLive p original used remaining t := by
  refine WP.mono (loop_guard (status := 4) (h.input.control_scr h.wr) h.r12 hs (by decide))
    fun _ ⟨⟨he, hm⟩, k⟩ => ⟨he, h.keep k hm (by decide)⟩

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchSemantics`, which this module and modules that import it used -/

section

/-! # The native controller's local transitions implement the complete search -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.Proof.Ffdh.SievedGeneration

def searchTail (p : SearchPublic) (used remaining : Nat) : Spec.Ffdh.ParameterSearchResult :=
  (Spec.Ffdh.sievedParameterSearch p.c.bits p.c.gen remaining (p.c.rand.drop used)).consume used

theorem searchTail_zero (p : SearchPublic) (used : Nat) : searchTail p used 0 = .exhausted used := rfl

theorem searchTail_short {p : SearchPublic} {used remaining : Nat} (hr : 0 < remaining)
    (hc : searchCandidate p used = none) : searchTail p used remaining = shortResult p used remaining := by
  cases remaining with
  | zero => omega_using [hr]
  | succ n =>
    unfold searchTail
    rw [Spec.Ffdh.sievedParameterSearch, show Spec.Ffdh.sievedParameterCandidate p.c.bits p.c.gen
      (p.c.rand.drop used) = none from hc]
    simp only [List.length_drop]
    by_cases hb : Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.rand.length - used <;>
      simp [hb, shortResult, Spec.Ffdh.ParameterSearchResult.consume]

theorem searchTail_accept {p : SearchPublic} {used remaining prime : Nat} {rest : List Byte}
    (hr : 0 < remaining) (hc : searchCandidate p used = some (some prime, rest)) :
    searchTail p used remaining = .accepted prime (used + (p.c.rand.length - used - rest.length)) := by
  cases remaining with
  | zero => omega_using [hr]
  | succ n =>
    unfold searchTail
    rw [Spec.Ffdh.sievedParameterSearch, show Spec.Ffdh.sievedParameterCandidate p.c.bits p.c.gen
      (p.c.rand.drop used) = some (some prime, rest) from hc]
    simp only [Spec.Ffdh.ParameterSearchResult.consume, List.length_drop]

theorem searchTail_reject {p : SearchPublic} {used remaining : Nat} {rest : List Byte}
    (hr : 0 < remaining) (hc : searchCandidate p used = some (none, rest)) :
    searchTail p used remaining = searchTail p (used + (p.c.rand.length - used - rest.length))
      (remaining - 1) := by
  simpa only [searchTail, List.length_drop] using search_reject hr hc

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! # Total correctness of the complete native parameter-search loop -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search VG.Proof.Ffdh.X86_64.ParameterCandidate

def SearchInvariant (p : SearchPublic) (original : State) (expected : Spec.Ffdh.ParameterSearchResult)
    (n : Nat) (s : State) : Prop :=
  ∃ used remaining, n = remaining + 1 ∧ SearchLive p original used remaining s ∧
    expected = searchTail p used remaining

theorem search_iteration (v : RoundImpl) {p : SearchPublic} {original s : State}
    {expected : Spec.Ffdh.ParameterSearchResult} {n : Nat}
    (h : SearchInvariant p original expected n s) :
    WP isa (iteration (candidateCode v)) s fun t =>
      (eval .e t = some false ∧ SearchDone p original expected t) ∨
      (eval .e t = some true ∧ ∃ m < n, SearchInvariant p original expected m t) := by
  obtain ⟨used, remaining, hn, h, hexpected⟩ := h
  unfold iteration
  change WP isa (.seq _ (.seq _ _)) s _
  refine WP.seq (WP.mono (remaining_guard h) fun u ⟨hu, he⟩ => ?_)
  apply WP.seq
  refine WP.ite (decide (remaining = 0)) he ?_ ?_
  · intro hz
    have hz' := of_decide_eq_true hz
    have hresult : expected = .exhausted used := by rw [hexpected, hz', searchTail_zero]
    refine WP.mono (search_exhausted hu) fun t ht => ?_
    refine WP.mono (done_loop_guard ht) fun q ⟨hq, hdone⟩ => ?_
    exact Or.inl ⟨hq, by rw [hresult]; exact hdone⟩
  · intro hnz
    have hr : 0 < remaining := by omega_using [of_decide_eq_false hnz]
    refine WP.seq (WP.mono (search_candidate_run v hu) fun t ⟨ht, hp⟩ => ?_)
    refine WP.mono (search_classify ht hr hp) fun q hq => ?_
    cases hc : searchCandidate p used with
    | none =>
      simp only [SearchClassified, hc] at hq
      have hresult : expected = shortResult p used remaining := hexpected.trans (searchTail_short hr hc)
      refine WP.mono (done_loop_guard hq) fun z ⟨hz, hd⟩ => ?_
      exact Or.inl ⟨hz, by rw [hresult]; exact hd⟩
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      cases value with
      | some prime =>
        simp only [SearchClassified, hc] at hq
        have hresult : expected = .accepted prime (used + (p.c.rand.length - used - rest.length)) :=
          hexpected.trans (searchTail_accept hr hc)
        refine WP.mono (done_loop_guard hq) fun z ⟨hz, hd⟩ => ?_
        exact Or.inl ⟨hz, by rw [hresult]; exact hd⟩
      | none =>
        simp only [SearchClassified, hc] at hq
        refine WP.mono (live_loop_guard hq.1 hq.2) fun z ⟨hz, hzlive⟩ => ?_
        refine Or.inr ⟨hz, remaining - 1 + 1, by omega_using [hn, hr], ?_⟩
        exact ⟨used + (p.c.rand.length - used - rest.length), remaining - 1,
          rfl, hzlive, hexpected.trans (searchTail_reject hr hc)⟩

theorem search_loop (v : RoundImpl) {p : SearchPublic} {original s : State}
    {expected : Spec.Ffdh.ParameterSearchResult} {n : Nat}
    (h : SearchInvariant p original expected n s) :
    WP isa (.loop (iteration (candidateCode v)) .e) s (SearchDone p original expected) := by
  exact WP.loop (M := isa) (body := iteration (candidateCode v)) (c := .e)
    (Q := SearchDone p original expected) (SearchInvariant p original expected)
    (fun _ _ h => search_iteration v h) n s h

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchSafety`, which only this module used -/

section

/-! # The complete generation controller's instruction safety and stack bound -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate
open VG.Impl.Ffdh.X86_64.Generation.Search

def searchCode (v : RoundImpl) : Prog isa := code (candidateCode v)

private theorem controller_all (p : Instr → Bool) (c : Prog isa)
    (hp : (code (.block [])).all p = true) (hc : c.all p = true) : (code c).all p = true := by
  unfold code iteration candidateRun at hp ⊢
  simp only [seqs, Code.all, List.all_nil, hc, Bool.and_true] at hp ⊢
  exact hp

private theorem controller_ctlC (c : Prog isa) (hp : ctlC (code (.block [])) = true) (hc : ctlC c = true) :
    ctlC (code c) = true := by
  unfold code iteration candidateRun at hp ⊢
  simp only [seqs, ctlC, hc, Bool.and_true] at hp ⊢
  exact hp

theorem searchCode_sp (v : RoundImpl) : (searchCode v).all (fun i => !isa.writesSp i) = true := by
  exact controller_all _ _ (by decide +kernel) (candidateCode_sp v)

/-- The search loads MXCSR only where the round restores it. -/
theorem searchCode_ctlC (v : RoundImpl) : ctlC (searchCode v) = true :=
  controller_ctlC _ (by decide +kernel) (candidateCode_ctlC v)

theorem searchCode_depth (v : RoundImpl) : (searchCode v).x86_64Depth ≤ 160 := by
  have he : exhausted.x86_64Depth = 0 := rfl
  have hc : classify.x86_64Depth = 0 := rfl
  unfold searchCode code iteration candidateRun
  simp only [seqs, Code.x86_64Depth, Instr.frameBytes, he, hc, Nat.zero_max, Nat.max_zero]
  exact Nat.add_le_add_right (candidateCode_depth v) 32

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchCT`, which only this module used -/

section

/-! # Complete native parameter generation has the specified public-tape leakage -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchCTStep.lean`, which only this module imported.
section

/-! # Public successor states for the native parameter-search timing proof -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Impl.Ffdh.X86_64.Generation.Search

def searchContinues (p : SearchPoint) : Prop := p.remaining ≠ 0 ∧
  Proof.Ffdh.candidateStatus (searchCandidate p.inputs p.used) = 2

instance (p : SearchPoint) : Decidable (searchContinues p) := inferInstanceAs
  (Decidable (p.remaining ≠ 0 ∧ Proof.Ffdh.candidateStatus (searchCandidate p.inputs p.used) = 2))

def nextSearchPoint (p : SearchPoint) : SearchPoint :=
  { p with used := p.used + candidateUsed p.inputs p.used, remaining := p.remaining - 1 }

def SearchCTStep (p : SearchPoint) (s : State) : Prop :=
  if searchContinues p then eval .e s = some true ∧ SearchCTL (nextSearchPoint p) s
  else eval .e s = some false

theorem search_ct_step (v : RoundImpl) (p : SearchPoint) (s : State) (h : SearchCTL p s) :
    WP isa (iteration (candidateCode v)) s (SearchCTStep p) := by
  unfold iteration
  change WP isa (.seq _ (.seq _ _)) s _
  refine WP.seq (WP.mono (remaining_ready p s h) fun u hu => ?_)
  refine WP.seq (WP.mono (branch_ready v p u hu) fun t ht => ?_)
  by_cases hr : p.remaining = 0
  · simp only [SearchBranchResult, hr, ite_true] at ht
    obtain ⟨original, ht⟩ := ht
    refine WP.mono (done_loop_guard ht) fun q ⟨hq, _⟩ => ?_
    simp only [SearchCTStep, show ¬searchContinues p by simp [searchContinues, hr], ite_false]
    exact hq
  · simp only [SearchBranchResult, hr, ite_false] at ht
    obtain ⟨original, ht⟩ := ht
    cases hc : searchCandidate p.inputs p.used with
    | none =>
      simp only [SearchClassified, hc] at ht
      refine WP.mono (done_loop_guard ht) fun q ⟨hq, _⟩ => ?_
      simp only [SearchCTStep, show ¬searchContinues p by simp [searchContinues, hc, Proof.Ffdh.candidateStatus], ite_false]
      exact hq
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      cases value with
      | some prime =>
        simp only [SearchClassified, hc] at ht
        refine WP.mono (done_loop_guard ht) fun q ⟨hq, _⟩ => ?_
        simp only [SearchCTStep, show ¬searchContinues p by simp [searchContinues, hc, Proof.Ffdh.candidateStatus], ite_false]
        exact hq
      | none =>
        simp only [SearchClassified, hc] at ht
        refine WP.mono (live_loop_guard ht.1 ht.2) fun q ⟨hq, hlive⟩ => ?_
        simp only [SearchCTStep, show searchContinues p by simp [searchContinues, hr, hc, Proof.Ffdh.candidateStatus], ite_true]
        exact ⟨hq, original, by simpa only [nextSearchPoint, candidateUsed, hc] using hlive⟩

end VG.Proof.Ffdh.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchLoopCT.lean`, which only this module imported.
section

/-! # Repeated native candidate retries preserve the public timing relation -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Impl.Ffdh.X86_64.Generation.Search

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ p, n = p.remaining + 1 ∧ SearchCTL p s ∧ SearchCTL p t

private theorem iteration_pair (v : RoundImpl) (n : Nat) :
    RelCT isa (LoopPair n) (iteration (candidateCode v)) fun s t =>
      eval .e s = eval .e t ∧ (eval .e s = some false → True) ∧
      (eval .e s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (p : SearchPoint) (s : State) (h : n = p.remaining + 1 ∧ SearchCTL p s) :
      WP isa (iteration (candidateCode v)) s fun t => n = p.remaining + 1 ∧ SearchCTStep p t :=
    WP.mono (search_ct_step v p s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((search_iteration_ct v).mono
    (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.2, h₂.2⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨p, hn, h₁, h₂⟩ => ⟨p, ⟨hn, h₁⟩, hn, h₂⟩) ?_
  rintro s t ⟨p, ⟨hn, h₁⟩, _, h₂⟩
  by_cases hb : searchContinues p
  · simp only [SearchCTStep, hb, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ?_⟩
    refine ⟨(nextSearchPoint p).remaining + 1, ?_, nextSearchPoint p, rfl, h₁.2, h₂.2⟩
    dsimp only [nextSearchPoint]
    omega_using [hn, hb.1]
  · simp only [SearchCTStep, hb, ite_false] at h₁ h₂
    refine ⟨h₁.trans h₂.symm, fun _ => trivial, fun ht => ?_⟩
    rw [h₁] at ht
    cases ht

theorem search_loop_ct (v : RoundImpl) :
    RelCT isa (Two SearchCTL) (.loop (iteration (candidateCode v)) .e) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨p, hs, ht⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration (candidateCode v)) (c := .e)
    (Q := fun _ _ => True) LoopPair (iteration_pair v) (p.remaining + 1)
    _ _ _ _ _ _ ⟨p, rfl, hs, ht⟩ he₁ he₂

end VG.Proof.Ffdh.X86_64.Generation
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Impl.Ffdh.X86_64.Generation.Search

private def initialPoint (p : SearchPublic) : SearchPoint := ⟨p, 0, p.remaining⟩
private def finalPoint (p : SearchPublic) : SearchEndPoint := ⟨p, searchTail p 0 p.remaining⟩

private theorem entry_started (p : SearchPublic) (s : State) (h : SearchInput p s) :
    WP isa (.block entry) s (SearchCTL (initialPoint p)) :=
  WP.mono (search_start h) fun _ ht => ⟨s, ht⟩

private theorem loop_done (v : RoundImpl) (p : SearchPublic) (s : State) (h : SearchCTL (initialPoint p) s) :
    WP isa (.loop (iteration (candidateCode v)) .e) s (SearchCTDone (finalPoint p)) := by
  obtain ⟨original, h⟩ := h
  have hi : SearchInvariant p original (searchTail p 0 p.remaining) (p.remaining + 1) s :=
    ⟨0, p.remaining, rfl, h, rfl⟩
  exact WP.mono (search_loop v hi) fun _ ht => ⟨original, ht⟩

theorem search_code_ct (v : RoundImpl) :
    RelCT isa (Two SearchInput) (searchCode v) (fun _ _ => True) := by
  unfold searchCode code
  change RelCT isa _ (.seq _ (.seq _ _)) _
  exact RelCT.seq (two_post search_entry_ct entry_started)
    (RelCT.seq (two_post (two_map initialPoint (fun _ _ h => h) (search_loop_ct v)) (loop_done v))
      (two_map finalPoint (fun _ _ h => h) search_finish_ct))

private theorem search_public_descriptor {s t : State} (h : searchPub s t) : searchOfState s = searchOfState t := by
  obtain ⟨⟨hsp, hbytes, r0, r1, r2, r3, r4, r5, a0, a1, a2⟩, ac, hw⟩ := h
  have hrand := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hbytes
  have hc : candidateOfState s = candidateOfState t := by
    simp only [candidateOfState, r0, r1, r2, r3, r4, r5, a1, a2, hrand, hsp]
  change [word s.mem (stackArg s 3) 0, word s.mem (stackArg s 3) 8,
    word s.mem (stackArg s 3) 16, word s.mem (stackArg s 3) 24] =
      [word t.mem (stackArg t 3) 0, word t.mem (stackArg t 3) 8,
        word t.mem (stackArg t 3) 16, word t.mem (stackArg t 3) 24] at hw
  have hcounter : s.mem.readW (stackArg s 3) 64 = t.mem.readW (stackArg t 3) 64 := by
    simpa only [Bignum.word, off, BitVec.add_zero] using (List.cons.inj hw).1
  unfold searchOfState
  congr 1
  exact congrArg BitVec.toNat hcounter

theorem search_constantTime (v : RoundImpl) :
    ConstantTime isa searchContract.pre searchContract.pub (searchCode v) := by
  refine RelCT.constantTime ((search_code_ct v).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨searchOfState s, ⟨hs, rfl⟩, ht, (search_public_descriptor hp).symm⟩

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchImplies`, which only this module used -/

section

/-! # Match the complete native controller to its shared callable contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Spec.Ffdh VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem stackArgs_four (s : State) : List.map (stackArg s) (List.range 4) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

private theorem candidate_gpr (s : State) : (candidateState s).gpr = s.gpr := rfl

private theorem candidate_rd (s : State) : (candidateState s).rd =
    [inputRand s, ⟨stackArgAddr s 0, 24⟩] := rfl

private theorem candidate_wr (s : State) : (candidateState s).wr = inputBuffers s := rfl

private theorem candidate_arg (s : State) (j : Nat) : stackArg (candidateState s) j = stackArg s j := rfl

private theorem candidate_argAddr (s : State) (j : Nat) :
    stackArgAddr (candidateState s) j = stackArgAddr s j := rfl

theorem search_implies_pre (s : State) (h : (sievedParameterSearchContract abi 160).pre s) : searchContract.pre s := by
  sig_pre [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow,
    searchContract, searchPre, pcPre, inputRand, inputArgs, inputBuffers,
    inputControl, candidate_gpr, candidate_rd, candidate_wr, candidate_arg, candidate_argAddr, stackArgs_four, List.append_eq] at h
  sig_pre [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow,
    searchContract, searchPre, pcPre, inputRand, inputArgs, inputBuffers,
    inputControl, candidate_gpr, candidate_rd, candidate_wr, candidate_arg, candidate_argAddr, stackArgs_four, List.append_eq] at h
  sig_split h
  sig_reduce [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow,
    searchContract, searchPre, pcPre, inputRand, inputArgs, inputBuffers,
    inputControl, candidate_gpr, candidate_rd, candidate_wr, candidate_arg, candidate_argAddr, stackArgs_four, List.append_eq]
  simp only [candidate_arg, candidate_argAddr, List.forall_mem_cons,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] at *
  have haSub : Region.Sub ⟨stackArgAddr s 0, 24⟩ ⟨stackArgAddr s 0, 32⟩ := by
    simpa only [BitVec.add_zero] using Offset.sub_base (stackArgAddr s 0)
      (d := 0) (n := 24) (k := 32) (by decide)
  have hbSub : Region.Sub (below (s.gpr .rsp) 128) (below (s.gpr .rsp) 160) :=
    Offset.below_mono _ (by decide) (by decide)
  sig_and_intros
  sig_close
  all_goals first
    | (intro x hx; cases hx)
    | exact True.intro
    | with_reducible assumption
    | with_reducible rfl
    | omega
    | with_reducible exact Region.Disjoint.symm ‹_›
    | exact Region.Disjoint.sub_left (r₁ := ⟨stackArgAddr s 0, 32⟩)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) haSub
    | exact Region.Disjoint.sub_right (r₂ := below (s.gpr .rsp) 160)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) hbSub
    | exact Region.Disjoint.sub_right (r₂ := ⟨stackArgAddr s 0, 32⟩)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) haSub
    | exact Region.Disjoint.sub_left (r₁ := below (s.gpr .rsp) 160)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) hbSub
    | exact (Region.Disjoint.sub_right (r₁ := ⟨stackArgAddr s 0, 32⟩)
        (r₂ := below (s.gpr .rsp) 160)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) hbSub).sub_left haSub
    | exact ((Region.Disjoint.sub_right (r₁ := ⟨stackArgAddr s 0, 32⟩)
        (r₂ := below (s.gpr .rsp) 160)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) hbSub).sub_left haSub).symm

theorem search_implies_post : ∀ s t, (sievedParameterSearchContract abi 160).pre s →
    searchContract.post s t → (sievedParameterSearchContract abi 160).post s t := by
  sig_implies_post [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, searchContract,
    searchPost, searchResult, pcRand, stackArgs_four, List.append_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem search_implies_pub (s t : State) (_hs : (sievedParameterSearchContract abi 160).pre s)
    (_ht : (sievedParameterSearchContract abi 160).pre t) (h : (sievedParameterSearchContract abi 160).pub s t) :
    searchContract.pub s t := by
  sig_pub [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackArgs_four,
    List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, rdi, rsi, rdx, rcx, r8, r9, a0, a1, a2, ast⟩ := h
  have hlen : (List.map (fun x => x.toNat) (pcRand s)).length =
      (List.map (fun x => x.toNat) (pcRand t)).length := by
    simp only [pcRand, Spec.Rsa.bytesAt, List.length_map, List.length_range, a0]
  obtain ⟨hbytes, hwords⟩ := List.append_inj hleak hlen
  have hc := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hwords
  exact ⟨⟨hsp, hbytes, rdi, rsi, rdx, rcx, r8, r9, a0, a1, a2⟩, ast, hc⟩

private def searchSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 512 | .r8 => 2 | .r9 => 0x3000
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6011 then 0x80 else if a = 0x6018 then 0x20 else if a = 0x6019 then 0x04
    else if a = 0x6021 then 0x40 else if a = 0x4008 then 0x40 else if a = 0x4010 then 0x40
    else if a = 0x4012 then 0x20 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x6008, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 8⟩, ⟨0x8000, 1056 * 8⟩, ⟨0x4000, 128⟩]

theorem search_implies : searchContract.Implies (sievedParameterSearchContract abi 160) where
  pre := search_implies_pre
  post := search_implies_post
  pub := search_implies_pub
  sat := by
    sig_implies_sat [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow,
      searchContract, searchPre, stackArgs_four, List.append_eq, searchSat]
      [searchSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using searchSat

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! # Verified complete native FFDH parameter generation for every arithmetic backend -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchFinish.lean`, which only this module imported.
section

/-! # Returning a complete native search preserves its output and System V registers -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def SearchReturned (p : SearchPublic) (result : Spec.Ffdh.ParameterSearchResult) (t : State) : Prop :=
  ((t.gpr .rax).setWidth 32).toNat = result.status ∧ SearchOutput p result t.mem ∧
    Spec.Rsa.wordsAt t.mem p.c.up 1 = [BitVec.ofNat 64 result.used] ∧
    Spec.Rsa.wordsAt t.mem p.control 4 =
      [BitVec.ofNat 64 result.remaining, BitVec.ofNat 64 p.c.k,
        BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits), BitVec.ofNat 64 (Proof.Ffdh.requested p.c.bits result)]

theorem search_finish {p : SearchPublic} {original s : State} {result : Spec.Ffdh.ParameterSearchResult}
    (h : SearchDone p original result s) :
    WP isa (.block finish) s fun t => SearchReturned p result t ∧
      (∀ reg ∈ calleeSaved, t.gpr reg = original.gpr reg) ∧ t.rd = original.rd ∧ t.wr = original.wr := by
  refine WP.mono (search_finish_values h) fun t ⟨ha, hr12, hm, k⟩ => ?_
  have hf : Frame [⟨p.c.up, 8⟩] s.mem t.mem := by
    rw [hm]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have ho : Spec.Rsa.bytesAt t.mem p.c.op p.c.k = Spec.Rsa.bytesAt s.mem p.c.op p.c.k := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.input.output_used_disjoint)
      (Nat.le_of_lt h.input.length_lt) (List.mem_range.mp hi)
  have hc (j : Nat) (hj : j < 4) : word t.mem p.control (8 * j) = word s.mem p.control (8 * j) :=
    hf.readW (r := ⟨p.control, 128⟩)
      (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.input.control_used_disjoint) (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, k.2.1.trans h.rd, k.2.2.trans h.wr⟩
  · rw [ha]
    cases result <;> rfl
  · change Spec.Rsa.bytesAt t.mem p.c.op p.c.k = _
    rw [ho]
    exact h.output
  · change [word t.mem p.c.up 0] = [_]
    rw [hm]
    congr 1
    simpa only [Bignum.word, off, BitVec.add_zero] using
      Mem.readW_writeW_self64 s.mem p.c.up (BitVec.ofNat 64 result.used)
  · have he : Spec.Rsa.wordsAt t.mem p.control 4 = Spec.Rsa.wordsAt s.mem p.control 4 := by
      change [word t.mem p.control 0, word t.mem p.control 8, word t.mem p.control 16, word t.mem p.control 24] = _
      rw [hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide)]
      rfl
    exact he.trans h.policy
  · intro reg hreg
    by_cases he : reg = .r12
    · subst he; exact hr12
    · exact (k.gpr (by cases reg <;> simp_all [calleeSaved])).trans (h.saved reg hreg he)

end VG.Proof.Ffdh.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchCorrect.lean`, which only this module imported.
section

/-! # Complete native parameter-generation correctness -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Proof.Ffdh.Generation
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem initial_search_result {p : SearchPublic} {s : State} (h : SearchInput p s) :
    searchResult s = searchTail p 0 p.remaining := by
  cases h.2
  simp only [searchResult, searchTail, searchOfState, SearchPublic.c, candidateOfState,
    List.drop_zero, consume_zero]

theorem returned_post {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hr : SearchReturned p (searchResult s) t) : searchPost s t := by
  have hreq : (searchResult s).Requests (Spec.Ffdh.parameterEntropy (s.gpr .rcx).toNat)
      (Proof.Ffdh.requested (s.gpr .rcx).toNat (searchResult s)) :=
    SievedGeneration.search_requests _ _ _ _
  cases h.2
  simp only [SearchReturned, SearchOutput, searchPost, searchOfState, SearchPublic.c,
    candidateOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hr ⊢
  cases he : searchResult s <;> simp only [he] at hr hreq ⊢ <;>
    exact ⟨hr.1, hr.2.1, hr.2.2.1, _, hr.2.2.2, hreq⟩

theorem search_correct_ok (v : RoundImpl) {s : State} (h : searchPre s) :
    WP isa (code (candidateCode v)) s fun t => searchPost s t ∧
      (∀ reg ∈ calleeSaved, t.gpr reg = s.gpr reg) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  let p := searchOfState s
  have hp : SearchInput p s := ⟨h, rfl⟩
  unfold code
  change WP isa (.seq _ (.seq _ _)) s _
  refine WP.seq (WP.mono (search_start hp) fun u hu => ?_)
  have hinv : SearchInvariant p s (searchResult s) (p.remaining + 1) u :=
    ⟨0, p.remaining, rfl, hu, initial_search_result hp⟩
  refine WP.seq (WP.mono (search_loop v hinv) fun t ht => ?_)
  refine WP.mono (search_finish ht) fun q ⟨hr, hg, hrd, hwr⟩ => ?_
  exact ⟨returned_post hp hr, hg, hrd, hwr⟩

end VG.Proof.Ffdh.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchAbi.lean`, which only this module imported.
section

/-! # Complete native parameter generation preserves the System V ABI -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

private theorem search_return_address (v : RoundImpl) {s t : State} {tr : List Leak}
    (h : searchPre s) (he : Exec isa (searchCode v) s tr t) :
    t.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hrc : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inputControl s) :=
    (h.2.2.2.2.2.1 _ (by simp)).symm
  have hwr := h.2.2.2.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hro, hru, _, hrs, _⟩ := h.1
  have hd := searchCode_depth v
  have hf := Exec.stackFrame (SpSafe.of_all (searchCode_sp v)) he (by omega_using [hd])
  refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · rw [hwr] at hr
    simp only [inputBuffers, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hro, hru, hrs, hrc]
  · obtain rfl := List.mem_singleton.mp hr
    exact Offset.base_disjoint_below _ (by omega_using [hd])

theorem search_correct (v : RoundImpl) (s : State) (h : searchContract.pre s) :
    ∃ tr t, Exec isa (searchCode v) s tr t ∧ abiPreserved s t ∧ searchContract.post s t := by
  obtain ⟨tr, t, he, hp, hg, _, _⟩ := search_correct_ok v h
  exact ⟨tr, t, he, abiPreserved_of_ctl (ctlOk_of_ctlC (searchCode_ctlC v)) he
    ⟨hg, search_return_address v h he⟩, hp⟩

end VG.Proof.Ffdh.X86_64.Generation
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

theorem search_verified (v : RoundImpl) : Verified target (searchCode v)
    (Spec.Ffdh.sievedParameterSearchContract abi 160) := by
  exact Verified.of_correct (search_correct v) (search_constantTime v) search_implies

end VG.Proof.Ffdh.X86_64.Generation
