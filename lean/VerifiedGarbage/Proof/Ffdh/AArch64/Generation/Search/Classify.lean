module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Call
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Writes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Contract

/-! # After a candidate: p, the next candidate, or an exit (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame
  controllerValue controllerValue_unchanged)
open VG.Impl.Ffdh.AArch64.Generation.Search
open VG.Impl.Bignum.AArch64 (movi)

/-- The candidate at octet `used` of the tape. -/
abbrev SPub.cand (p : SPub) (used : Nat) : Option (Option Nat × List Byte) :=
  parameterCandidate p.bits p.gen (p.rand.drop used)

/-- The octets the candidate at `used` reads. -/
def SPub.read (p : SPub) (used : Nat) : Nat :=
  match p.cand used with
  | some (_, rest) => (p.randLen - used) - rest.length
  | none => 0

theorem SPub.read_le {p : SPub} {original s : State} {used k : Nat} (h : SLive p original used k s) :
    used + p.read used ≤ p.randLen := by
  have hu := h.used_le
  unfold SPub.read
  split
  · omega
  · omega

theorem status_lt (r : Option (Option Nat × List Byte)) : candidateStatus r < 3 := by
  unfold candidateStatus; split <;> decide

/-- The status and the octets read, after the candidate. -/
theorem search_head {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hp : CandPost p used s) :
    WP isa (.block (head ++ ([.subImm .x .x12 .x9 1] : List Instr))) s fun t =>
      SLive p original used k t ∧ CandPost p used t ∧
      t.gpr .x9 = BitVec.ofNat 64 (candidateStatus (p.cand used)) ∧
      t.gpr .x10 = BitVec.ofNat 64 (p.read used) ∧
      isa.eval (.zero .x .x12) t = some (decide (candidateStatus (p.cand used) = 1)) := by
  have a := h.access
  have hv7 := h.header (j := 7) (v := p.up) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv7
  have hu : InRegions (s.rd ++ s.wr) p.up 8 := by
    refine ⟨⟨p.up, 8⟩, List.mem_append_right _ ?_, ?_⟩
    · rw [h.wr, h.input.1.2.2.2.1, ← h.input.used_eq]; simp [inWrites]
    · simpa only [BitVec.add_zero] using Offset.contains_base p.up (d := 0) (n := 8) (k := 8)
        (by decide) (by decide)
  have hw : s.mem.readW p.up 64 = BitVec.ofNat 64 (p.read used) := by
    have := hp.2.2
    change [word s.mem p.up 0] = _ at this
    simp only [Bignum.word, off, BitVec.add_zero, List.cons.injEq, and_true] at this
    rw [this]; rfl
  have hst := status_lt (p.cand used)
  have h0 : (s.gpr .x0).setWidth 32 = BitVec.ofNat 32 (candidateStatus (p.cand used)) := by
    apply BitVec.eq_of_toNat_eq
    rw [hp.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (WP.keep [.x9, .x10, .x11, .x12] (Q := fun t =>
    (t.gpr .x9 = BitVec.ofNat 64 (candidateStatus (p.cand used)) ∧
      t.gpr .x10 = BitVec.ofNat 64 (p.read used) ∧
      isa.eval (.zero .x .x12) t = some (decide (candidateStatus (p.cand used) = 1))) ∧ t.mem = s.mem) ?_
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨⟨h9, h10, he⟩, hm⟩, k⟩ => ?_
  · unfold head
    brun [ldf, h.x19, hv7, a.ld 56 (by decide), hu, hw,
      VG.Proof.RsaKeyGen.AArch64.exec_addImm_w (show 0 < 4096 by decide), h0]
    refine ⟨?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    · have : ∀ st < 3, ((BitVec.ofNat 32 st + BitVec.ofNat 32 0).setWidth 64 - BitVec.ofNat 64 1 == 0) =
          decide (st = 1) := by decide
      simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq,
        this _ hst]
  · refine ⟨h.keep k hm, ?_, h9, h10, he⟩
    unfold CandPost at hp ⊢
    rw [hm, k.gpr .x0 (by decide)]
    exact hp

/-- A finished search, from a loop state through writes of the controller's
words but the saved `x19` and the pointer to `used`. -/
theorem SLive.doneWrites {p : SPub} {original s t : State} {used k : Nat}
    (h : SLive p original used k s) (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 16)
    (h4 : ∀ e ∈ values, 4 ≠ e.1) (h7 : ∀ e ∈ values, 7 ≠ e.1)
    (hm : t.mem = writeController s.mem p.control values)
    (kp : Keep [.x0, .x1, .x2, .x3, .x9, .x10, .x11, .x12, .x13, .x14, .x15] s t)
    {r : ParameterSearchResult} (hu : word t.mem p.control 96 = BitVec.ofNat 64 r.used)
    (hs : word t.mem p.control 112 = BitVec.ofNat 64 r.status)
    (hp : Spec.Rsa.wordsAt t.mem p.control 4 = p.policy r) (ho : SOutput p r s.mem) :
    SDone p original r t := by
  have hg : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => kp.gpr r (by revert r hr; decide)
  have hw (j : Nat) (hj : j < 16) (hn : ∀ e ∈ values, j ≠ e.1) :
      word t.mem p.control (8 * j) = word s.mem p.control (8 * j) := by
    rw [hm, writeController_word _ _ _ hb j hj, controllerValue_unchanged _ _ _ hn]
  refine ⟨h.input, kp.rd.trans h.rd, kp.wr.trans h.wr, (hg .x19 (by decide)).trans h.x19,
    fun reg hreg h19 h30 => (hg reg hreg).trans (h.saved reg hreg h19 h30),
    fun r hr => (kp.vcs r hr).trans (h.vcs r hr), ?_, ?_, hu, hs, hp, ?_⟩
  · exact (hw 4 (by decide) h4).trans h.savedX19
  · exact (hw 7 (by decide) h7).trans (h.header (j := 7) (by simp [SPub.headers]))
  · unfold SOutput at ho ⊢
    rw [hm, out_frame h.input (writeController_frame s.mem p.control values hb)]
    exact ho

/-! ## An accepted candidate -/

def acceptValues (used : Nat) : List (Nat × BitVec 64) :=
  (12, BitVec.ofNat 64 used) :: terminalValues 1

theorem acceptValues_bound (used : Nat) : ∀ e ∈ acceptValues used, e.1 < 16 := by
  simp only [acceptValues, terminalValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem search_accept {p : SPub} {original s : State} {used k q : Nat} {rest : List Byte}
    (h : SLive p original used k s) (hp : CandPost p used s) (hk : k ≠ 0)
    (hc : p.cand used = some (some q, rest)) (h10 : s.gpr .x10 = BitVec.ofNat 64 (p.read used)) :
    WP isa (.block accept) s (SDone p original (p.tail used k)) := by
  have a := h.access
  have hv12 := h.header (j := 12) (v := BitVec.ofNat 64 used) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv12
  have hn : p.read used = (p.randLen - used) - rest.length := by simp only [SPub.read, hc]
  have e12 : BitVec.ofNat 64 used + BitVec.ofNat 64 (p.read used) =
      BitVec.ofNat 64 (used + ((p.randLen - used) - rest.length)) := by
    rw [hn, ← BitVec.ofNat_add]
  rw [SPub.tail_accept hk h.rand_length hc]
  refine WP.mono (WP.keep [.x10, .x11] (Q := fun t =>
    t.mem = writeController s.mem p.control (acceptValues (used + ((p.randLen - used) - rest.length)))) ?_
      (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, kt⟩ => ?_
  · unfold accept terminal writeController acceptValues terminalValues
    simp only [List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, h.x19, h10, hv12, e12, imm64 (show 0 < 65536 by decide),
      imm64 (show 1 < 65536 by decide), a.ld 96 (by decide), a.st 96 (by decide), a.st0,
      a.st 0 (by decide), a.st 24 (by decide), a.st 112 (by decide)]
    rfl
  have hb := acceptValues_bound (used + ((p.randLen - used) - rest.length))
  have hw (j : Nat) (hj : j < 16) : word t.mem p.control (8 * j) =
      controllerValue (acceptValues (used + ((p.randLen - used) - rest.length))) j
        (word s.mem p.control (8 * j)) := by
    rw [hm, writeController_word _ _ _ hb j hj]
  refine h.doneWrites _ hb (by
      simp only [acceptValues, terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) (by
      simp only [acceptValues, terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) hm kt.mono ?_ ?_ ?_ ?_
  · rw [show (96 : Nat) = 8 * 12 from rfl, hw 12 (by decide)]
    simp only [controllerValue, acceptValues, terminalValues, List.foldl_cons, List.foldl_nil,
      Nat.reduceEqDiff, ite_true, ite_false]
    rfl
  · rw [show (112 : Nat) = 8 * 14 from rfl, hw 14 (by decide)]
    simp only [controllerValue, acceptValues, terminalValues, List.foldl_cons, List.foldl_nil,
      Nat.reduceEqDiff, ite_true, ite_false]
    rfl
  · change [word t.mem p.control (8 * 0), word t.mem p.control (8 * 1), word t.mem p.control (8 * 2),
      word t.mem p.control (8 * 3)] = _
    rw [hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide)]
    simp only [controllerValue, acceptValues, terminalValues, List.foldl_cons, List.foldl_nil,
      Nat.reduceEqDiff, ite_true, ite_false]
    rw [h.header (j := 1) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers]),
      h.header (j := 2) (v := BitVec.ofNat 64 (parameterEntropy p.bits)) (by simp [SPub.headers])]
    rfl
  · have ho := hp.2.1
    simp only [hc] at ho
    exact ho

/-! ## A rejected candidate -/

def rejectValues (p : SPub) (used k : Nat) : List (Nat × BitVec 64) :=
  [(12, BitVec.ofNat 64 used), (10, p.rp + BitVec.ofNat 64 used),
    (11, BitVec.ofNat 64 (p.randLen - used)), (0, BitVec.ofNat 64 k), (14, 4)]

theorem rejectValues_bound (p : SPub) (used k : Nat) : ∀ e ∈ rejectValues p used k, e.1 < 16 := by
  simp only [rejectValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem ofNat_pred {n : Nat} (h0 : 0 < n) (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by
    simp only [BitVec.le_def, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt h]; omega)]
  simp only [BitVec.toNat_ofNat]
  omega

theorem search_reject {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hk : k ≠ 0) (h10 : s.gpr .x10 = BitVec.ofNat 64 (p.read used)) :
    WP isa (.block reject) s fun t =>
      SLive p original (used + p.read used) (k - 1) t ∧ word t.mem p.control 112 = 4 := by
  have a := h.access
  have hv0 := h.header (j := 0) (v := BitVec.ofNat 64 k) (by simp [SPub.headers])
  have hv10 := h.header (j := 10) (v := p.rp + BitVec.ofNat 64 used) (by simp [SPub.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  have hv12 := h.header (j := 12) (v := BitVec.ofNat 64 used) (by simp [SPub.headers])
  simp only [Bignum.word, off] at hv0
  simp only [Bignum.word, off, Nat.reduceMul] at hv10 hv11 hv12
  have hle := SPub.read_le h
  have hlen := h.input.randLen_lt
  have hkl : k < 2 ^ 64 := by have := h.k_le; have := h.input.attempts_lt; omega
  have e12 : BitVec.ofNat 64 used + BitVec.ofNat 64 (p.read used) =
      BitVec.ofNat 64 (used + p.read used) := by rw [← BitVec.ofNat_add]
  have e10 : p.rp + BitVec.ofNat 64 used + BitVec.ofNat 64 (p.read used) =
      p.rp + BitVec.ofNat 64 (used + p.read used) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have e11 : BitVec.ofNat 64 (p.randLen - used) - BitVec.ofNat 64 (p.read used) =
      BitVec.ofNat 64 (p.randLen - (used + p.read used)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by
      simp only [BitVec.le_def, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have e0 := ofNat_pred (Nat.pos_of_ne_zero hk) hkl
  refine WP.mono (WP.keep [.x11, .x12, .x13, .x14, .x15] (Q := fun t =>
    t.mem = writeController s.mem p.control (rejectValues p (used + p.read used) (k - 1))) ?_
      (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, kt⟩ => ?_
  · unfold reject writeController rejectValues
    simp only [List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, h.x19, h10, hv0, hv10, hv11, hv12, e0, e10, e11, e12, imm64 (show 4 < 65536 by decide),
      a.ld0, a.ld 0 (by decide), a.ld 80 (by decide), a.ld 88 (by decide), a.ld 96 (by decide), a.st0, a.st 0 (by decide),
      a.st 80 (by decide), a.st 88 (by decide), a.st 96 (by decide), a.st 112 (by decide)]
    rfl
  have hb := rejectValues_bound p (used + p.read used) (k - 1)
  have hh : Slots t.mem p.control (p.headers (used + p.read used) (k - 1)) := by
    refine headers_after _ hb hm ?_
    intro e he
    simp only [SPub.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, rejectValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [SPub.headers])
  refine ⟨h.update hle (by have := h.k_le; omega) _ hb (by
      simp only [rejectValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) hm kt.mono hh, ?_⟩
  rw [show (112 : Nat) = 8 * 14 from rfl, hm, writeController_word _ _ _ hb 14 (by decide)]
  simp only [controllerValue, rejectValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_true, ite_false]

/-! ## A tape too short for the candidate -/

def requestValues (p : SPub) (used : Nat) : List (Nat × BitVec 64) :=
  [(3, BitVec.ofNat 64 (parameterRequest p.bits (p.randLen - used))), (14, 0)]

theorem requestValues_bound (p : SPub) (used : Nat) : ∀ e ∈ requestValues p used, e.1 < 16 := by
  simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl) <;> dsimp only <;> decide

theorem request_value {p : SPub} {original s : State} {used k : Nat} (h : SLive p original used k s) :
    WP isa (.block (request.take 9)) s fun t =>
      (t.gpr .x10 = BitVec.ofNat 64 (parameterRequest p.bits (p.randLen - used)) ∧ t.mem = s.mem) ∧
        Keep [.x10, .x11, .x12, .x13] s t := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 (parameterEntropy p.bits)) (by simp [SPub.headers])
  have hv6 := h.header (j := 6) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2 hv6 hv11
  have hlen := h.input.len_bounds
  have hl := h.input.len_eq
  have hrl := h.input.randLen_le
  have hb := h.input.bits_bounds
  have hE : parameterEntropy p.bits ≤ 32769 * 1024 := by
    unfold parameterEntropy; omega
  refine WP.keep [.x10, .x11, .x12, .x13] ?_ (by decide) (by decide) (by decide +kernel)
  unfold request
  simp only [List.take_succ_cons, List.take_zero]
  brun [ldf, h.x19, hv2, hv6, hv11, a.ld 16 (by decide), a.ld 48 (by decide), a.ld 88 (by decide),
    shift_ofNat, subs_ge (show p.randLen - used < 2 ^ 64 by omega) (show p.len * 2 ^ 8 < 2 ^ 64 by omega)]
  unfold parameterRequest
  rw [← hl]
  have hA : p.randLen - used ≤ parameterEntropy p.bits := by omega
  generalize p.randLen - used = A at *
  generalize parameterEntropy p.bits = E at *
  by_cases h1 : p.len * 2 ^ 8 ≤ A
  · simp only [h1, decide_true, ite_true, ← BitVec.ofNat_add,
      subs_ge (show A + A < 2 ^ 64 by omega) (show E < 2 ^ 64 by omega)]
    by_cases h2 : E ≤ A + A
    · simp only [h2, decide_true, ite_true]
      congr 1; omega
    · simp only [h2, decide_false, Bool.false_eq_true, ite_false]
      congr 1; omega
  · simp only [h1, decide_false, Bool.false_eq_true, ite_false, ← BitVec.ofNat_add,
      subs_ge (show p.len * 2 ^ 8 + p.len * 2 ^ 8 < 2 ^ 64 by omega) (show E < 2 ^ 64 by omega)]
    by_cases h2 : E ≤ p.len * 2 ^ 8 + p.len * 2 ^ 8
    · simp only [h2, decide_true, ite_true]
      congr 1; omega
    · simp only [h2, decide_false, Bool.false_eq_true, ite_false]
      congr 1; omega

theorem search_request {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hk : k ≠ 0) (hc : p.cand used = none)
    (hshort : ¬parameterEntropy p.bits ≤ p.randLen - used)
    (hout : Spec.Rsa.bytesAt s.mem p.op p.len = List.replicate p.len 0) :
    WP isa (.block request) s (SDone p original (p.tail used k)) := by
  rw [show request = request.take 9 ++ request.drop 9 from (List.take_append_drop _ _).symm,
    WP.block_append_iff]
  refine WP.mono (request_value h) fun v ⟨⟨h10, hmv⟩, kv⟩ => ?_
  have hv := h.keep kv hmv
  have a := hv.access
  refine WP.mono (WP.keep [.x11] (Q := fun t =>
    t.mem = writeController v.mem p.control (requestValues p used)) ?_
      (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, kt⟩ => ?_
  · unfold request writeController requestValues
    simp only [List.drop_succ_cons, List.drop_zero, List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, hv.x19, h10, imm64 (show 0 < 65536 by decide), a.st 24 (by decide), a.st 112 (by decide)]
    rfl
  rw [SPub.tail_short hk h.rand_length hc, ite_eq_right hshort]
  have hb := requestValues_bound p used
  have hw (j : Nat) (hj : j < 16) : word t.mem p.control (8 * j) =
      controllerValue (requestValues p used) j (word v.mem p.control (8 * j)) := by
    rw [hm, writeController_word _ _ _ hb j hj]
  refine hv.doneWrites _ hb (by
      simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl) <;> dsimp only <;> decide) (by
      simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl) <;> dsimp only <;> decide) hm (kt.mono) ?_ ?_ ?_ ?_
  · rw [show (96 : Nat) = 8 * 12 from rfl, hw 12 (by decide)]
    simp only [controllerValue, requestValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_false]
    exact hv.header (j := 12) (v := BitVec.ofNat 64 used) (by simp [SPub.headers])
  · rw [show (112 : Nat) = 8 * 14 from rfl, hw 14 (by decide)]
    simp only [controllerValue, requestValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]
    rfl
  · change [word t.mem p.control (8 * 0), word t.mem p.control (8 * 1), word t.mem p.control (8 * 2),
      word t.mem p.control (8 * 3)] = _
    rw [hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide)]
    simp only [controllerValue, requestValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]
    rw [hv.header (j := 0) (v := BitVec.ofNat 64 k) (by simp [SPub.headers]),
      hv.header (j := 1) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers]),
      hv.header (j := 2) (v := BitVec.ofNat 64 (parameterEntropy p.bits)) (by simp [SPub.headers])]
    rfl
  · unfold SOutput
    rw [hmv]
    exact hout

/-- Whether the tape holds the entropy cap. -/
theorem short_guard {p : SPub} {original s : State} {used k : Nat} (h : SLive p original used k s) :
    WP isa (.block [ldf .x10 11, ldf .x11 2, .subs .x .x12 .x10 .x11, movi .x13 0, movi .x14 1,
        .csel .x .x12 .x14 .x13]) s fun t =>
      (SLive p original used k t ∧ t.mem = s.mem) ∧
        isa.eval (.zero .x .x12) t = some (decide (p.randLen - used < parameterEntropy p.bits)) := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 (parameterEntropy p.bits)) (by simp [SPub.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2 hv11
  have hr := h.input.randLen_lt
  have hE : parameterEntropy p.bits < 2 ^ 64 := by
    have := h.input.bits_bounds; unfold parameterEntropy; omega
  refine WP.mono (WP.keep [.x10, .x11, .x12, .x13, .x14] (Q := fun t =>
    isa.eval (.zero .x .x12) t = some (decide (p.randLen - used < parameterEntropy p.bits)) ∧ t.mem = s.mem) ?_
    (by decide) (by decide) (by decide +kernel)) fun _ ⟨⟨he, hm⟩, k⟩ => ⟨⟨h.keep k hm, hm⟩, he⟩
  brun [ldf, h.x19, hv2, hv11, a.ld 16 (by decide), a.ld 88 (by decide), imm64 (show 0 < 65536 by decide),
    imm64 (show 1 < 65536 by decide), subs_ge (show p.randLen - used < 2 ^ 64 by omega) hE]
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq]
  by_cases hb : parameterEntropy p.bits ≤ p.randLen - used
  · simp only [hb, decide_true, ite_true, show ¬p.randLen - used < parameterEntropy p.bits by omega,
      decide_false]
    decide
  · simp only [hb, decide_false, ite_false, show p.randLen - used < parameterEntropy p.bits by omega,
      decide_true, Bool.false_eq_true]
    decide

theorem search_short {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hk : k ≠ 0) (hc : p.cand used = none)
    (hout : Spec.Rsa.bytesAt s.mem p.op p.len = List.replicate p.len 0) :
    WP isa short s (SDone p original (p.tail used k)) := by
  unfold short
  refine WP.seq (WP.mono (short_guard h) fun u ⟨⟨hu, hm⟩, he⟩ => ?_)
  refine WP.ite _ he ?_ ?_
  · intro hs
    have hs' := of_decide_eq_true hs
    exact search_request hu hk hc (by omega) (by rw [hm]; exact hout)
  · intro hs
    have hs' := of_decide_eq_false hs
    rw [SPub.tail_short hk h.rand_length hc, ite_eq_left (by omega)]
    exact search_exhausted hu

/-! ## The classification -/

/-- Where the candidate at `used` leads: on to the next one after a
rejection, or the end of the search. -/
def SClassified (p : SPub) (original : State) (used k : Nat) (t : State) : Prop :=
  if candidateStatus (p.cand used) = 2 then
    SLive p original (used + p.read used) (k - 1) t ∧ word t.mem p.control 112 = 4
  else SDone p original (p.tail used k) t

theorem test_two {s : State} {st : Nat} (h9 : s.gpr .x9 = BitVec.ofNat 64 st) (hst : st < 3) :
    WP isa (.block [.subImm .x .x12 .x9 2]) s fun t =>
      (isa.eval (.zero .x .x12) t = some (decide (st = 2)) ∧ t.mem = s.mem) ∧ Keep [.x12] s t := by
  refine WP.keep [.x12] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h9]
  have hb : ∀ st < 3, ((BitVec.ofNat 64 st - BitVec.ofNat 64 2) == 0) = decide (st = 2) := by decide
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq, hb st hst]

theorem search_classify {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hk : k ≠ 0) (hp : CandPost p used s) :
    WP isa classify s (SClassified p original used k) := by
  unfold classify
  refine WP.seq (WP.mono (search_head h hp) fun u ⟨hu, hpu, h9, h10, he⟩ => ?_)
  have hst := status_lt (p.cand used)
  cases hc : p.cand used with
  | none =>
    simp only [hc, candidateStatus] at he h9
    refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
    refine WP.seq (WP.mono (test_two h9 (by decide)) fun v ⟨⟨he2, hmv⟩, kv⟩ => ?_)
    refine WP.ite false he2 (fun hf => by cases hf) fun _ => ?_
    have hout := hpu.2.1
    simp only [hc] at hout
    have hs := search_short (hu.keep kv hmv) hk hc (by rw [hmv]; exact hout)
    refine WP.mono hs fun t ht => ?_
    simp only [SClassified, hc, candidateStatus, Nat.reduceEqDiff, ite_false]
    exact ht
  | some pair =>
    obtain ⟨value, rest⟩ := pair
    cases value with
    | some q =>
      simp only [hc, candidateStatus] at he h9
      refine WP.ite true he (fun _ => ?_) (fun hf => by cases hf)
      refine WP.mono (search_accept hu hpu hk hc h10) fun t ht => ?_
      simp only [SClassified, hc, candidateStatus, Nat.reduceEqDiff, ite_false]
      exact ht
    | none =>
      simp only [hc, candidateStatus] at he h9
      refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
      refine WP.seq (WP.mono (test_two h9 (by decide)) fun v ⟨⟨he2, hmv⟩, kv⟩ => ?_)
      refine WP.ite true he2 (fun _ => ?_) (fun hf => by cases hf)
      have hv := hu.keep kv hmv
      refine WP.mono (search_reject hv hk ((kv.gpr .x10 (by decide)).trans h10)) fun t ht => ?_
      simp only [SClassified, hc, candidateStatus, ite_true]
      exact ht

end VG.Proof.Ffdh.AArch64.Generation
