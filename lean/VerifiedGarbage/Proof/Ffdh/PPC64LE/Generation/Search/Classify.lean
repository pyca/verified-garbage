module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Call
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Writes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-! # After a candidate: p, the next candidate, or an exit (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame
  controllerValue controllerValue_unchanged)
open VG.Impl.Ffdh.PPC64LE.Generation.Search

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

/-- The status, the low 32 bits of `r3`. -/
theorem low32 {x : BitVec 64} {st : Nat} (h : (x.setWidth 32).toNat = st) :
    (x <<< 32) >>> 32 = BitVec.ofNat 64 st := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, ← h, BitVec.toNat_setWidth]
  have := x.isLt
  omega

/-- The status and the octets read, after the candidate. -/
theorem search_head {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hp : CandPost p used s) :
    WP isa (.block (head ++ ([.subi .r12 .r9 1] : List Instr))) s fun t =>
      SLive p original used k t ∧ CandPost p used t ∧
      t.gpr .r9 = BitVec.ofNat 64 (candidateStatus (p.cand used)) ∧
      t.gpr .r10 = BitVec.ofNat 64 (p.read used) ∧
      isa.eval (.zero .d .r12) t = some (decide (candidateStatus (p.cand used) = 1)) := by
  have a := h.access
  have hv7 := h.header (j := 7) (v := p.up) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv7
  have hu : InRegions (s.rd ++ s.wr) (p.up + BitVec.ofNat 64 0) 8 := by
    refine ⟨⟨p.up, 8⟩, List.mem_append_right _ ?_, ?_⟩
    · rw [h.wr, h.input.1.2.2.2.1, ← h.input.used_eq]; simp [inWrites]
    · exact Offset.contains_base p.up (d := 0) (n := 8) (k := 8) (by decide) (by decide)
  have hw : s.mem.readW (p.up + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (p.read used) := by
    have := hp.2.2
    change [word s.mem p.up 0] = _ at this
    simp only [Bignum.word, off, List.cons.injEq, and_true] at this
    rw [this]; rfl
  have hst := status_lt (p.cand used)
  have h9 := low32 hp.1
  have hb : ∀ st < 3, (BitVec.ofNat 64 st - BitVec.ofNat 64 1 == 0) = decide (st = 1) := by decide
  refine WP.mono (WP.keep [.r9, .r10, .r11, .r12] (Q := fun t =>
    (t.gpr .r9 = BitVec.ofNat 64 (candidateStatus (p.cand used)) ∧
      t.gpr .r10 = BitVec.ofNat 64 (p.read used) ∧
      isa.eval (.zero .d .r12) t = some (decide (candidateStatus (p.cand used) = 1))) ∧ t.mem = s.mem) ?_
    (by decide)) fun t ⟨⟨⟨h9, h10, he⟩, hm⟩, k⟩ => ?_
  · unfold head
    prun [ldf, h.r31, hv7, a.ld 56 (by decide), hu, hw, h9]
    refine (eval_zero _ _).trans ?_
    rw [RegUpd.gpr_write_self, hb _ hst]
  · refine ⟨h.keep k hm, ?_, h9, h10, he⟩
    unfold CandPost at hp ⊢
    rw [hm, k.gpr .r3 (by decide)]
    exact hp

/-- A finished search, from a loop state through writes of the controller's
words but the saved `r31` and the pointer to `used`. -/
theorem SLive.doneWrites {p : SPub} {original s t : State} {used k : Nat}
    (h : SLive p original used k s) (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 16)
    (h4 : ∀ e ∈ values, 4 ≠ e.1) (h7 : ∀ e ∈ values, 7 ≠ e.1)
    (hm : t.mem = writeController s.mem p.control values)
    (kp : Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] s t)
    {r : ParameterSearchResult} (hu : word t.mem p.control 96 = BitVec.ofNat 64 r.used)
    (hs : word t.mem p.control 112 = BitVec.ofNat 64 r.status)
    (hp : Spec.Rsa.wordsAt t.mem p.control 4 = p.policy r) (ho : SOutput p r s.mem) :
    SDone p original r t := by
  have hg : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => kp.gpr r (by revert r hr; decide)
  have hw (j : Nat) (hj : j < 16) (hn : ∀ e ∈ values, j ≠ e.1) :
      word t.mem p.control (8 * j) = word s.mem p.control (8 * j) := by
    rw [hm, writeController_word _ _ _ hb j hj, controllerValue_unchanged _ _ _ hn]
  refine ⟨h.input, kp.rd.trans h.rd, kp.wr.trans h.wr, (hg .r31 (by decide)).trans h.r31,
    fun reg hreg h31 => (hg reg hreg).trans (h.saved reg hreg h31), ?_, ?_, hu, hs, hp, ?_⟩
  · exact (hw 4 (by decide) h4).trans h.savedR31
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
    (hc : p.cand used = some (some q, rest)) (h10 : s.gpr .r10 = BitVec.ofNat 64 (p.read used)) :
    WP isa (.block accept) s (SDone p original (p.tail used k)) := by
  have a := h.access
  have hv12 := h.header (j := 12) (v := BitVec.ofNat 64 used) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv12
  have hn : p.read used = (p.randLen - used) - rest.length := by simp only [SPub.read, hc]
  have e12 : BitVec.ofNat 64 used + BitVec.ofNat 64 (p.read used) =
      BitVec.ofNat 64 (used + ((p.randLen - used) - rest.length)) := by
    rw [hn, ← BitVec.ofNat_add]
  rw [SPub.tail_accept hk h.rand_length hc]
  refine WP.mono (WP.keep [.r10, .r11] (Q := fun t =>
    t.mem = writeController s.mem p.control (acceptValues (used + ((p.randLen - used) - rest.length)))) ?_
      (by decide)) fun t ⟨hm, kt⟩ => ?_
  · unfold accept terminal writeController acceptValues terminalValues
    simp only [List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil]
    prun [ldf, stf, h.r31, h10, hv12, e12, a.ld 96 (by decide), a.st 96 (by decide), a.st0,
      a.st 0 (by decide), a.st 24 (by decide), a.st 112 (by decide), BitVec.add_zero]
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
    (h : SLive p original used k s) (hk : k ≠ 0) (h10 : s.gpr .r10 = BitVec.ofNat 64 (p.read used)) :
    WP isa (.block reject) s fun t =>
      SLive p original (used + p.read used) (k - 1) t ∧ word t.mem p.control 112 = 4 := by
  have a := h.access
  have hv0 := h.header (j := 0) (v := BitVec.ofNat 64 k) (by simp [SPub.headers])
  have hv10 := h.header (j := 10) (v := p.rp + BitVec.ofNat 64 used) (by simp [SPub.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  have hv12 := h.header (j := 12) (v := BitVec.ofNat 64 used) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.mul_zero, BitVec.add_zero] at hv0
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
  refine WP.mono (WP.keep [.r3, .r4, .r5, .r11, .r12] (Q := fun t =>
    t.mem = writeController s.mem p.control (rejectValues p (used + p.read used) (k - 1))) ?_
      (by decide)) fun t ⟨hm, kt⟩ => ?_
  · unfold reject writeController rejectValues
    simp only [List.foldl_cons, List.foldl_nil]
    prun [ldf, stf, h.r31, h10, hv0, hv10, hv11, hv12, e0, e10, e11, e12,
      a.ld0, a.ld 0 (by decide), a.ld 80 (by decide), a.ld 88 (by decide), a.ld 96 (by decide), a.st0, a.st 0 (by decide),
      a.st 80 (by decide), a.st 88 (by decide), a.st 96 (by decide), a.st 112 (by decide), BitVec.add_zero]
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

end VG.Proof.Ffdh.PPC64LE.Generation
