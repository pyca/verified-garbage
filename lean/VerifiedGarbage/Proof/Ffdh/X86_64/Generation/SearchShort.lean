module

public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDone
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitValues
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchTerminate
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ZeroOut
import VerifiedGarbage.Proof.Bignum.Octets

/-! ### `Ffdh.X86_64.Generation.SearchExhausted`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.Generation.SearchClear`, which only this module used -/

section

/-! # Clearing a failed search preserves the native controller -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- A callee-saved register is none of the registers the search's blocks write. -/
private theorem saved_not_scratch {r : Reg} (hr : r ∈ calleeSaved) :
    r ∉ ([.rsi, .rcx, .rax] : List Reg) ∧ r ∉ ([.rax, .rcx] : List Reg) := by
  revert hr; cases r <;> decide

theorem search_clear {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (hdi : s.gpr .rdi = p.control) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroOut 5 6) s fun t =>
      SearchLive p original used remaining t ∧
      Spec.Rsa.bytesAt t.mem p.c.op p.c.k = List.replicate p.c.k 0 ∧
      (∀ j < 16, word t.mem p.control (8 * j) = word s.mem p.control (8 * j)) ∧
      Keep [.rsi, .rcx, .rax] s t := by
  have hk := h.input.width_bounds
  have scr := h.input.control_scr h.wr
  refine WP.mono (controller_zero_out scr hdi (by decide) (by decide) (by decide)
    (h.headers (5, p.c.op) (by simp [SearchPublic.headers]))
    (h.headers (6, BitVec.ofNat 64 p.c.k) (by simp [SearchPublic.headers]))
    (by omega_using [hk.1]) (by omega_using [hk.2]) (h.input.output h.wr))
    fun t ⟨hv, hf, k⟩ => ?_
  have hframe : Frame (inputBuffers original ++ [below (original.gpr .rsp) 160]) s.mem t.mem := by
    intro a ha
    apply hf
    intro i hi he
    have hr : (⟨p.c.op, p.c.k⟩ : Region) ∈ inputBuffers original := by
      cases h.input.2
      exact List.mem_cons_self ..
    apply ha _ (List.mem_append_left _ hr)
    rw [he]
    exact contains_byte _ (by omega_using [hi]) (by omega_using [hi, h.input.length_lt])
  refine ⟨h.restore k.2.1 k.2.2 (fun r hr => k.gpr (saved_not_scratch hr).1) hframe,
    ?_, h.input.control_frame hframe, k⟩
  refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact hv i (List.mem_range.mp hi)

end VG.Proof.Ffdh.X86_64.Generation

end

end


/-! # Exhausted native searches return zero output and a terminal controller -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem search_exhausted {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa exhausted s (SearchDone p original (.exhausted used)) := by
  unfold exhausted
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (search_terminal h 3) fun u ⟨h0, hq, hs⟩ => ?_
  have hmov : WP isa (.block [.mov .rdi (.reg .r12)]) u fun v =>
      (v.gpr .rdi = p.control ∧ v.mem = u.mem) ∧ Keep [.rdi] u v := by
    refine WP.keep [.rdi] ?_ rfl
    xrun [h0.r12]
  refine WP.mono hmov fun v ⟨⟨hdv, hmv⟩, kv⟩ => ?_
  have hv := h0.keep kv hmv (by decide)
  refine WP.mono (search_clear hv hdv) fun t ⟨ht, hout, hw, _⟩ => ?_
  refine done_of_live ht rfl rfl ?_ ?_ hout
  · have hs' : word v.mem p.control 112 = BitVec.ofNat 64 3 := by rw [hmv]; exact hs
    exact (hw 14 (by decide)).trans hs'
  · have hq' : word v.mem p.control 24 = BitVec.ofNat 64 0 := by rw [hmv]; exact hq
    exact (hw 3 (by decide)).trans hq'

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchDoneUpdate`, which this module and modules that import it used -/

section

/-! # Terminal controller writes preserve the accepted output and saved ABI -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem controller_output {p : SearchPublic} {original : State} (h : SearchInput p original)
    {m m' : Mem} (hf : Frame [⟨p.control, 128⟩] m m') :
    Spec.Rsa.bytesAt m' p.c.op p.c.k = Spec.Rsa.bytesAt m p.c.op p.c.k := by
  have hd : (⟨p.c.op, p.c.k⟩ : Region).Disjoint ⟨p.control, 128⟩ := by
    cases h.2
    exact (h.1.2.2.2.2.2.1 _ (List.mem_append_left _ (List.mem_cons_self ..))).symm
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hd)
    (Nat.le_of_lt h.length_lt) (List.mem_range.mp hi)

theorem done_update {p : SearchPublic} {original s t : State} {used remaining : Nat}
    {result : Spec.Ffdh.ParameterSearchResult} (h : SearchLive p original used remaining s)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 16)
    (hkeep : ∀ j ∈ [4, 5, 7], ∀ e ∈ values, j ≠ e.1)
    (hm : t.mem = writeController s.mem p.control values)
    (hread : t.rd = s.rd) (hwrite : t.wr = s.wr)
    (hg : ∀ reg ∈ calleeSaved, t.gpr reg = s.gpr reg)
    (hused : word t.mem p.control 96 = BitVec.ofNat 64 result.used)
    (hstatus : word t.mem p.control 112 = BitVec.ofNat 64 result.status)
    (hpolicy : Spec.Rsa.wordsAt t.mem p.control 4 =
      [BitVec.ofNat 64 result.remaining, BitVec.ofNat 64 p.c.k,
        BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits), BitVec.ofNat 64 (Proof.Ffdh.requested p.c.bits result)])
    (hout : SearchOutput p result s.mem) : SearchDone p original result t := by
  have hw (j : Nat) (hj : j ∈ [4, 5, 7]) :
      word t.mem p.control (8 * j) = word s.mem p.control (8 * j) := by
    have hbound : j < 16 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> decide
    rw [hm, writeController_word _ _ _ hb j hbound, controllerValue_unchanged _ _ _ (hkeep j hj)]
  refine ⟨h.input, hread.trans h.rd, hwrite.trans h.wr,
    (hg .rsp (by decide)).trans h.rsp, (hg .r12 (by decide)).trans h.r12,
    fun reg hr hn => (hg reg hr).trans (h.saved reg hr hn), ?_, ?_, ?_, hused, hstatus, hpolicy, ?_⟩
  · exact (hw 4 (by decide)).trans h.savedR12
  · exact (hw 5 (by decide)).trans (h.headers (5, p.c.op) (by simp [SearchPublic.headers]))
  · exact (hw 7 (by decide)).trans (h.headers (7, p.c.up) (by simp [SearchPublic.headers]))
  · change Spec.Rsa.bytesAt t.mem p.c.op p.c.k = _
    rw [hm, controller_output h.input (writeController_frame _ _ _ hb)]
    exact hout

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchRequestDone`, which only this module used -/

section

/-! ### `Ffdh.X86_64.Generation.SearchRequest`, which only this module used -/

section

/-! # The verified controller selects the exact next entropy request -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem request_ok {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s)
    (ha : s.gpr .rax = BitVec.ofNat 64 (p.c.rand.length - used)) :
    WP isa (.block request) s fun t =>
      t.gpr .rax = 0 ∧
      t.mem = writeController s.mem p.control
        [(3, BitVec.ofNat 64 (parameterRequest p.c.bits (p.c.rand.length - used))), (14, 0)] ∧
      Keep [.rax, .rcx] s t := by
  have scr := h.input.control_scr h.wr
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hv1 : s.mem.readW (p.control + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 p.c.k :=
    h.headers (1, BitVec.ofNat 64 p.c.k) (by simp [SearchPublic.headers])
  have hv2 : s.mem.readW (p.control + BitVec.ofNat 64 16) 64 =
      BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits) :=
    h.headers (2, BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)) (by simp [SearchPublic.headers])
  have hk := h.input.width_bounds.2
  have ht := h.input.tape_bound
  have hc := h.input.entropy_bound
  have hmax : max (p.c.rand.length - used) (256 * p.c.k) ≤ 33555456 :=
    Nat.max_le.mpr ⟨by omega_using [ht, hc], by omega_using [hk]⟩
  have ha64 : p.c.rand.length - used < 2 ^ 64 := by omega_using [ht, hc]
  have hk64 : p.c.k < 2 ^ 64 := by omega_using [hk]
  have hc64 : Spec.Ffdh.parameterEntropy p.c.bits < 2 ^ 64 := by omega_using [hc]
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t =>
    t.gpr .rax = 0 ∧ t.mem = writeController s.mem p.control
      [(3, BitVec.ofNat 64 (parameterRequest p.c.bits (p.c.rand.length - used))), (14, 0)]) ?_ rfl)
    fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨hr, hm, k⟩
  have hmaxeq : max (p.c.rand.length - used) (256 * p.c.k) =
      if p.c.rand.length - used < 256 * p.c.k then 256 * p.c.k else p.c.rand.length - used := by
    by_cases hb : p.c.rand.length - used < 256 * p.c.k
    · simp [hb, Nat.max_eq_right (Nat.le_of_lt hb)]
    · have hk : 256 * p.c.k ≤ p.c.rand.length - used := by omega_using [hb]
      simp [hb, Nat.max_eq_left hk]
  have hmin (a b : Nat) : min a b = if a < b then a else b := by
    by_cases hb : a < b
    · simp [hb, Nat.min_eq_left (Nat.le_of_lt hb)]
    · have hk : b ≤ a := by omega_using [hb]
      simp [hb, Nat.min_eq_right hk]
  have hreq : parameterRequest p.c.bits (p.c.rand.length - used) =
      if 2 * max (p.c.rand.length - used) (256 * p.c.k) < Spec.Ffdh.parameterEntropy p.c.bits
      then 2 * max (p.c.rand.length - used) (256 * p.c.k) else Spec.Ffdh.parameterEntropy p.c.bits := by
    rw [parameterRequest, Entropy.request, ← h.input.width_bits, hmin]
  have ha2 : (p.c.rand.length - used) * 2 < 2 ^ 64 := by
    omega_using [hmax, Nat.le_max_left (p.c.rand.length - used) (256 * p.c.k)]
  have hk2 : p.c.k * 256 * 2 < 2 ^ 64 := by omega_using [hk]
  have han : (BitVec.ofNat 64 (p.c.rand.length - used)).toNat = p.c.rand.length - used :=
    toNat_ofNat_of_lt ha64
  have hkn : (BitVec.ofNat 64 (p.c.k * 256)).toNat = p.c.k * 256 :=
    toNat_ofNat_of_lt (by omega_using [hk])
  have hcn : (BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)).toNat =
      Spec.Ffdh.parameterEntropy p.c.bits := toNat_ofNat_of_lt hc64
  have ha2n : (BitVec.ofNat 64 (2 * (p.c.rand.length - used))).toNat = 2 * (p.c.rand.length - used) :=
    toNat_ofNat_of_lt (by omega_using [ha2])
  have hk2n : (BitVec.ofNat 64 (2 * (p.c.k * 256))).toNat = 2 * (p.c.k * 256) :=
    toNat_ofNat_of_lt (by omega_using [hk2])
  have hshl : BitVec.ofNat 64 p.c.k <<< 8 = BitVec.ofNat 64 (p.c.k * 256) := by
    rw [shift_ofNat]
  have h256 : 256 * p.c.k = p.c.k * 256 := Nat.mul_comm _ _
  rw [h256] at hmaxeq hreq
  unfold request writeController
  simp only [List.foldl_cons, List.foldl_nil]
  by_cases hab : p.c.rand.length - used < p.c.k * 256
  all_goals
    by_cases hcut : 2 * max (p.c.rand.length - used) (p.c.k * 256) < Spec.Ffdh.parameterEntropy p.c.bits
    all_goals
      have hcut' := hcut
      rw [hmaxeq] at hcut'
      first | rw [ite_eq_left hab] at hcut' | rw [ite_eq_right hab] at hcut'
      try simp only [Nat.mul_comm] at hcut'
      xrun [State.ea, field, off, h.r12, ha, hv1, hv2, hshl, BitVec.ofInt_natCast, Nat.reduceMul,
        hl 8 (by decide), hl 16 (by decide), hs 24 (by decide), hs 112 (by decide), eval, execCmov,
        hreq, hmaxeq, hab, hcut, hcut', shift_ofNat, Nat.reducePow, Nat.mul_comm,
        han, hkn, hcn, ha2n, hk2n, decide_true, decide_false, Bool.not_true, Bool.not_false]
      rfl

end VG.Proof.Ffdh.X86_64.Generation

end

end


/-! # Native entropy requests return the remaining budget and consumed prefix -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem search_request_done {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s)
    (ha : s.gpr .rax = BitVec.ofNat 64 (p.c.rand.length - used))
    (hout : Spec.Rsa.bytesAt s.mem p.c.op p.c.k = List.replicate p.c.k 0) :
    WP isa (.block request) s (SearchDone p original
      (.entropy remaining (p.c.rand.length - used) used)) := by
  refine WP.mono (request_ok h ha) fun t ⟨_, hm, k⟩ => ?_
  let values : List (Nat × BitVec 64) :=
    [(3, BitVec.ofNat 64 (parameterRequest p.c.bits (p.c.rand.length - used))), (14, 0)]
  have hb : ∀ e ∈ values, e.1 < 16 := by
    simp only [values, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl) <;> dsimp only <;> decide
  have hkeep : ∀ j ∈ [4, 5, 7], ∀ e ∈ values, j ≠ e.1 := by
    intro j hj e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    simp only [values, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases hj with rfl | rfl | rfl <;> rcases he with rfl | rfl <;> dsimp only <;> decide
  have h0 : word s.mem p.control 0 = BitVec.ofNat 64 remaining :=
    h.headers (0, BitVec.ofNat 64 remaining) (by simp [SearchPublic.headers])
  have h1 : word s.mem p.control 8 = BitVec.ofNat 64 p.c.k :=
    h.headers (1, BitVec.ofNat 64 p.c.k) (by simp [SearchPublic.headers])
  have h2 : word s.mem p.control 16 = BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits) :=
    h.headers (2, BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)) (by simp [SearchPublic.headers])
  have h12 : word s.mem p.control 96 = BitVec.ofNat 64 used :=
    h.headers (12, BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  refine done_update h values hb hkeep hm k.2.1 k.2.2
    (fun reg hr => k.gpr (saved_not_scratch hr).2) ?_ ?_ ?_ hout
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 12) = _
    rw [writeController_word _ _ _ hb 12 (by decide)]
    simp only [values, controllerValue, List.foldl_cons, List.foldl_nil,
      Nat.reduceEqDiff, ite_false, h12]
    rfl
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 14) = _
    rw [writeController_word _ _ _ hb 14 (by decide)]
    rfl
  · rw [hm, writeController_policy _ _ _ hb]
    simp only [values, controllerValue, List.foldl_cons, List.foldl_nil,
      Nat.reduceEqDiff, ite_false, ite_true, h0, h1, h2]
    rfl

end VG.Proof.Ffdh.X86_64.Generation

end

end


/-! # Entropy exhaustion and bounded native refill requests -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem short_guard {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (.block [.mov .rax (.mem (field 11)), .alu .cmp .rax (.mem (field 2))]) s fun t =>
      SearchLive p original used remaining t ∧ t.mem = s.mem ∧
      t.gpr .rax = BitVec.ofNat 64 (p.c.rand.length - used) ∧
      eval .ae t = some (decide (Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.rand.length - used)) := by
  have scr := h.input.control_scr h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hv11 : word s.mem p.control 88 = BitVec.ofNat 64 (p.c.rand.length - used) :=
    h.headers (11, BitVec.ofNat 64 (p.c.rand.length - used)) (by simp [SearchPublic.headers])
  have hv2 : word s.mem p.control 16 = BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits) :=
    h.headers (2, BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)) (by simp [SearchPublic.headers])
  have ht := h.input.tape_lt
  have hc := h.input.entropy_bound
  have hn : (BitVec.ofNat 64 (p.c.rand.length - used)).toNat = p.c.rand.length - used :=
    toNat_ofNat_of_lt (by omega_using [ht])
  have hcn : (BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)).toNat = Spec.Ffdh.parameterEntropy p.c.bits :=
    toNat_ofNat_of_lt (by omega_using [hc])
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (p.c.rand.length - used) ∧
    eval .ae t = some (decide (Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.rand.length - used))) ?_ rfl)
    fun _ ⟨⟨hm, ha, he⟩, k⟩ => ⟨h.keep k hm (by decide), hm, ha, he⟩
  xrun [State.ea, field, off, h.r12, hv11, hv2, hn, hcn, eval, Nat.reduceMul,
    BitVec.ofInt_natCast, hl 88 (by decide), hl 16 (by decide)]
  change (!decide (p.c.rand.length - used < Spec.Ffdh.parameterEntropy p.c.bits)) =
    decide (Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.rand.length - used)
  by_cases hb : Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.rand.length - used
  · simp [hb, show ¬p.c.rand.length - used < Spec.Ffdh.parameterEntropy p.c.bits by omega_using [hb]]
  · simp [hb, show p.c.rand.length - used < Spec.Ffdh.parameterEntropy p.c.bits by omega_using [hb]]

def shortResult (p : SearchPublic) (used remaining : Nat) : Spec.Ffdh.ParameterSearchResult :=
  if Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.rand.length - used then .exhausted used
  else .entropy remaining (p.c.rand.length - used) used

theorem search_short {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s)
    (hout : Spec.Rsa.bytesAt s.mem p.c.op p.c.k = List.replicate p.c.k 0) :
    WP isa short s (SearchDone p original (shortResult p used remaining)) := by
  unfold short
  refine WP.seq (WP.mono (short_guard h) fun u ⟨hu, hm, ha, he⟩ => ?_)
  refine WP.ite (decide (Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.rand.length - used)) he ?_ ?_
  · intro hb
    rw [shortResult, ite_eq_left (of_decide_eq_true hb)]
    exact search_exhausted hu
  · intro hb
    rw [shortResult, ite_eq_right (of_decide_eq_false hb)]
    exact search_request_done hu ha (by rw [hm]; exact hout)

end VG.Proof.Ffdh.X86_64.Generation
