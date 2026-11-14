module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCandidatePost
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDone
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDoneUpdate
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchMemory
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchTerminal
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchShort
public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchUpdate
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
public import VerifiedGarbage.Proof.Ffdh.Contract

/-! ### `Ffdh.X86_64.Generation.SearchAcceptDone`, which only this module used -/

section

/-! # Successful candidates finish the complete native parameter search -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchAccept.lean`, which only this module imported.
section

/-! # Record final candidate consumption and finish native parameter search -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem accept_prefix {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (consumed : BitVec 64)
    (hu : s.mem.readW p.c.up 64 = consumed) :
    WP isa (.block [
      .mov .rax (.mem (field 7)), .mov .rcx (.mem { base := .rax }),
      .mov .rax (.mem (field 12)), .alu .add .rax (.reg .rcx), .store (field 12) .rax]) s fun t =>
      t.mem = writeController s.mem p.control [(12, BitVec.ofNat 64 used + consumed)] ∧
      Keep [.rax, .rcx] s t := by
  have scr := h.input.control_scr h.wr
  have hs : InRegions s.wr (p.control + BitVec.ofNat 64 96) 8 := scr.st (by decide)
  have hl7 : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 56) 8 := scr.ld (by decide)
  have hl12 : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 96) 8 := scr.ld (by decide)
  have hup : InRegions (s.rd ++ s.wr) p.c.up 8 := by
    simpa only [off, BitVec.add_zero] using (h.input.used_memory h.wr).ld (d := 0) (by decide)
  have hv7 : s.mem.readW (p.control + BitVec.ofNat 64 56) 64 = p.c.up :=
    h.headers (7, p.c.up) (by simp [SearchPublic.headers])
  have hv12 : s.mem.readW (p.control + BitVec.ofNat 64 96) 64 = BitVec.ofNat 64 used :=
    h.headers (12, BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  refine WP.keep [.rax, .rcx] ?_ rfl
  unfold writeController
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, h.r12, hs, hl7, hl12, hup, hu, hv7, hv12,
    BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero]

theorem accept_ok {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (consumed : BitVec 64)
    (hu : s.mem.readW p.c.up 64 = consumed) :
    WP isa (.block accept) s fun t =>
      t.gpr .rax = 1 ∧
      t.mem = writeController s.mem p.control
        ([(12, BitVec.ofNat 64 used + consumed)] ++ terminalValues 1) ∧ Keep [.rax, .rcx] s t := by
  rw [accept, WP.block_append_iff]
  refine WP.mono (accept_prefix h consumed hu) fun u ⟨hm, k⟩ => ?_
  refine WP.mono (terminal_ok (h.input.control_scr (k.2.2.trans h.wr))
    ((k.gpr (by decide)).trans h.r12) 1) fun t ⟨hr, ht, kt⟩ => ?_
  exact ⟨hr, by rw [ht, hm, writeController_append], (k.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.Generation
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem search_accept_done {p : SearchPublic} {original s : State} {used remaining n prime : Nat}
    (h : SearchLive p original used remaining s)
    (hu : s.mem.readW p.c.up 64 = BitVec.ofNat 64 n)
    (hout : Spec.Rsa.bytesAt s.mem p.c.op p.c.k = Spec.Rsa.i2osp prime p.c.k) :
    WP isa (.block accept) s (SearchDone p original (.accepted prime (used + n))) := by
  refine WP.mono (accept_ok h (BitVec.ofNat 64 n) hu) fun t ⟨_, hm, k⟩ => ?_
  let values := [(12, BitVec.ofNat 64 used + BitVec.ofNat 64 n)] ++ terminalValues 1
  have hb : ∀ e ∈ values, e.1 < 16 := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · obtain rfl := List.mem_singleton.mp he
      dsimp only
      decide
    · exact terminalValues_bound 1 e he
  have hkeep : ∀ j ∈ [4, 5, 7], ∀ e ∈ values, j ≠ e.1 := by
    intro j hj e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    simp only [values, terminalValues, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at he
    rcases hj with rfl | rfl | rfl <;> rcases he with rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  have h1 : word s.mem p.control 8 = BitVec.ofNat 64 p.c.k :=
    h.headers (1, BitVec.ofNat 64 p.c.k) (by simp [SearchPublic.headers])
  have h2 : word s.mem p.control 16 = BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits) :=
    h.headers (2, BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)) (by simp [SearchPublic.headers])
  refine done_update h values hb hkeep hm k.2.1 k.2.2
    (fun reg hr => k.gpr (by cases reg <;> simp_all [calleeSaved])) ?_ ?_ ?_ hout
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 12) = _
    rw [writeController_word _ _ _ hb 12 (by decide)]
    simp only [values, terminalValues, controllerValue, List.foldl_append, List.foldl_cons,
      List.foldl_nil, Nat.reduceEqDiff, ite_false, ite_true, ← BitVec.ofNat_add]
    rfl
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 14) = _
    rw [writeController_word _ _ _ hb 14 (by decide)]
    rfl
  · rw [hm, writeController_policy _ _ _ hb]
    simp only [values, terminalValues, controllerValue, List.foldl_append, List.foldl_cons,
      List.foldl_nil, Nat.reduceEqDiff, ite_false, ite_true, h1, h2]
    rfl

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchRejectStep`, which only this module used -/

section

/-! ### `Ffdh.X86_64.Generation.SearchRejectHeaders`, which only this module used -/

section

/-! # A rejected candidate advances the native search invariant -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchReject.lean`, which only this module imported.
section

/-! # Native byte accounting and budget decrement after candidate rejection -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def rejectValues (p : SearchPublic) (used remaining : Nat) (consumed : BitVec 64) : List (Nat × BitVec 64) :=
  [(12, BitVec.ofNat 64 used + consumed), (10, off p.c.rp used + consumed),
    (11, BitVec.ofNat 64 (p.c.rand.length - used) - consumed),
    (0, BitVec.ofNat 64 remaining - 1), (14, 4)]

theorem reject_ok {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (consumed : BitVec 64)
    (hu : s.mem.readW p.c.up 64 = consumed) :
    WP isa (.block reject) s fun t =>
      t.mem = writeController s.mem p.control (rejectValues p used remaining consumed) ∧
      Keep [.rax, .rcx] s t := by
  have scr := h.input.control_scr h.wr
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hs0 : InRegions s.wr p.control 8 := by simpa only [BitVec.add_zero] using hs 0 (by decide)
  have hl0 : InRegions (s.rd ++ s.wr) p.control 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have hup : InRegions (s.rd ++ s.wr) p.c.up 8 := by
    simpa only [off, BitVec.add_zero] using (h.input.used_memory h.wr).ld (d := 0) (by decide)
  have hv (j : Nat) (v : BitVec 64) (hj : (j, v) ∈ p.headers used remaining) :
      s.mem.readW (p.control + BitVec.ofNat 64 (8 * j)) 64 = v := h.headers (j, v) hj
  have hv7 := hv 7 p.c.up (by simp [SearchPublic.headers])
  have hv12 := hv 12 (BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  have hv10 := hv 10 (off p.c.rp used) (by simp [SearchPublic.headers])
  have hv11 := hv 11 (BitVec.ofNat 64 (p.c.rand.length - used)) (by simp [SearchPublic.headers])
  have hv0 : s.mem.readW p.control 64 = BitVec.ofNat 64 remaining := by
    simpa only [Nat.mul_zero, BitVec.add_zero] using hv 0 (BitVec.ofNat 64 remaining) (by simp [SearchPublic.headers])
  have other (i j : Nat) (hi : i < 16) (hj : j < 16) (hne : i ≠ j) :=
    fun (m : Mem) (v : BitVec 64) => controller_read_other m p.control v (i := i) (j := j) hi hj hne
  have other0 (i : Nat) (hi : i < 16) (hne : i ≠ 0) (m : Mem) (v : BitVec 64) :
      (m.writeW (p.control + BitVec.ofNat 64 (8 * i)) v).readW p.control 64 = m.readW p.control 64 := by
    simpa only [Nat.mul_zero, BitVec.add_zero] using other i 0 hi (by decide) hne m v
  refine WP.keep [.rax, .rcx] ?_ rfl
  unfold reject writeController rejectValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, h.r12, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul,
    BitVec.add_zero, hs0, hl0, hup, hu, hv7, hv12, hv10, hv11, hv0,
    hl 56 (by decide), hl 96 (by decide), hl 80 (by decide), hl 88 (by decide),
    hs 96 (by decide), hs 80 (by decide), hs 88 (by decide), hs 112 (by decide),
    other 12 10 (by decide) (by decide) (by decide), other 12 11 (by decide) (by decide) (by decide),
    other 10 11 (by decide) (by decide) (by decide), other0 12 (by decide) (by decide),
    other0 10 (by decide) (by decide), other0 11 (by decide) (by decide)]
  rfl

end VG.Proof.Ffdh.X86_64.Generation
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh.X86_64
open VG.Proof.MlKem.X86_64

theorem rejectValues_bound (p : SearchPublic) (used remaining : Nat) (n : BitVec 64) :
    ∀ e ∈ rejectValues p used remaining n, e.1 < 16 := by
  simp only [rejectValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem reject_headers {p : SearchPublic} {original s : State} {used remaining n : Nat}
    (h : SearchLive p original used remaining s) (hn : n ≤ p.c.rand.length - used)
    (hr : 0 < remaining) :
    Slots (writeController s.mem p.control (rejectValues p used remaining (BitVec.ofNat 64 n)))
      p.control (p.headers (used + n) (remaining - 1)) := by
  have ht := h.input.tape_lt
  have hr64 : remaining < 2 ^ 64 := by
    have hb : p.remaining < 2 ^ 64 := by
      cases h.input.2
      exact (original.mem.readW (stackArg original 3) 64).isLt
    omega_using [h.remaining_le, hb]
  have hn64 : n < 2 ^ 64 := by omega_using [hn, ht]
  have hh := h.headers
  simp only [Slots, SearchPublic.headers, List.forall_mem_cons] at hh
  obtain ⟨h0, h1, h2, h5, h6, h7, h8, h9, h10, h11, h12, h13, h15, _⟩ := hh
  have hd : BitVec.ofNat 64 (p.c.rand.length - used) - BitVec.ofNat 64 n =
      BitVec.ofNat 64 (p.c.rand.length - (used + n)) := by
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ hn64 hn]
    congr 1
    omega_using []
  intro e he
  simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [writeController_word _ _ _ (rejectValues_bound p used remaining _) _ (by dsimp only; decide)] <;>
    simp only [rejectValues, controllerValue, List.foldl_cons, List.foldl_nil,
      Nat.reduceEqDiff, ite_true, ite_false, h0, h1, h2, h5, h6, h7, h8, h9, h10, h11, h12, h13, h15,
      hd, ofNat64_pred hr hr64, off, BitVec.ofNat_add, BitVec.add_assoc]

end VG.Proof.Ffdh.X86_64.Generation

end

end


/-! # A native rejection continues with smaller budgets and the exact suffix -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem search_reject_step {p : SearchPublic} {original s : State} {used remaining n : Nat}
    (h : SearchLive p original used remaining s) (hn : n ≤ p.c.rand.length - used)
    (hr : 0 < remaining) (hu : s.mem.readW p.c.up 64 = BitVec.ofNat 64 n) :
    WP isa (.block reject) s fun t =>
      SearchLive p original (used + n) (remaining - 1) t ∧ word t.mem p.control 112 = 4 := by
  refine WP.mono (reject_ok h (BitVec.ofNat 64 n) hu) fun t ⟨hm, k⟩ => ?_
  have hb := rejectValues_bound p used remaining (BitVec.ofNat 64 n)
  have h4 : ∀ e ∈ rejectValues p used remaining (BitVec.ofNat 64 n), 4 ≠ e.1 := by
    simp only [rejectValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide
  refine ⟨h.control_update (by omega_using [hn, h.used_le])
    (by omega_using [h.remaining_le]) _ hb h4 hm k.2.1 k.2.2
    (fun reg hr => k.gpr (by cases reg <;> simp_all [calleeSaved]))
    (by rw [hm]; exact reject_headers h hn hr), ?_⟩
  rw [hm]
  change word (writeController s.mem p.control (rejectValues p used remaining (BitVec.ofNat 64 n)))
    p.control (8 * 14) = _
  rw [writeController_word _ _ _ hb 14 (by decide)]
  rfl

end VG.Proof.Ffdh.X86_64.Generation

end

end


/-! # The native controller classifies candidate outcomes without host decisions -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def SearchClassified (p : SearchPublic) (original : State) (used remaining : Nat) (t : State) : Prop :=
  match searchCandidate p used with
  | none => SearchDone p original (shortResult p used remaining) t
  | some (some prime, rest) => SearchDone p original
      (.accepted prime (used + (p.c.rand.length - used - rest.length))) t
  | some (none, rest) => SearchLive p original (used + (p.c.rand.length - used - rest.length))
      (remaining - 1) t ∧ word t.mem p.control 112 = 4

theorem normalized_status {s t : State} {status : Nat}
    (hs : ((s.gpr .rax).setWidth 32).toNat = status)
    (ht : t.gpr .rax = ((s.gpr .rax).setWidth 32).setWidth 64) :
    t.gpr .rax = BitVec.ofNat 64 status := by
  apply BitVec.eq_of_toNat_eq
  rw [ht, BitVec.toNat_setWidth, hs, BitVec.toNat_ofNat]

theorem search_classify {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (hr : 0 < remaining)
    (hp : SearchCandidatePost p used s) :
    WP isa classify s (SearchClassified p original used remaining) := by
  unfold classify
  refine WP.seq (WP.mono (candidate_status_guard s) fun u ⟨⟨he, ha, hm⟩, k⟩ => ?_)
  have hu := h.keep k hm (by decide)
  have hs := hp.1
  have hup := hp.used_word
  have hout := hp.2.1
  cases hc : searchCandidate p used with
  | none =>
    rw [hc, Proof.Ffdh.candidateStatus] at hs
    rw [hs] at he
    have hax := normalized_status hs ha
    refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
    refine WP.seq (WP.mono (second_status_guard hax (by decide)) fun v ⟨⟨he2, hm2⟩, k2⟩ => ?_)
    have hv := hu.keep k2 hm2 (by decide)
    refine WP.ite false he2 (fun hf => by cases hf) fun _ => ?_
    change WP isa short v (fun t => SearchClassified p original used remaining t)
    simp only [SearchClassified, hc]
    apply search_short hv
    rw [hm2, hm]
    simpa only [hc] using hout
  | some pair =>
    obtain ⟨value, rest⟩ := pair
    cases value with
    | some prime =>
      rw [hc, Proof.Ffdh.candidateStatus] at hs
      rw [hs] at he
      refine WP.ite true he (fun _ => ?_) (fun hf => by cases hf)
      change WP isa (.block accept) u (fun t => SearchClassified p original used remaining t)
      simp only [SearchClassified, hc]
      apply search_accept_done hu
      · rw [hm]
        simpa only [candidateUsed, hc] using hup
      · rw [hm]
        simpa only [hc] using hout
    | none =>
      rw [hc, Proof.Ffdh.candidateStatus] at hs
      rw [hs] at he
      have hax := normalized_status hs ha
      refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
      refine WP.seq (WP.mono (second_status_guard hax (by decide)) fun v ⟨⟨he2, hm2⟩, k2⟩ => ?_)
      have hv := hu.keep k2 hm2 (by decide)
      refine WP.ite true he2 (fun _ => ?_) (fun hf => by cases hf)
      change WP isa (.block reject) v (fun t => SearchClassified p original used remaining t)
      simp only [SearchClassified, hc]
      apply search_reject_step hv (Nat.sub_le _ _) hr
      rw [hm2, hm]
      simpa only [candidateUsed, hc] using hup

end VG.Proof.Ffdh.X86_64.Generation
