module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Call
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Writes
public import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # The RSA prime search's classification of a candidate (AArch64)

After its candidate, the search is done (a prime accepted, the tape too
short, or nothing consumed), or goes on past the candidate, with one fewer
counted candidate for a counted rejection (`search_classify`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController controllerValue controllerValue_unchanged)
open VG.Proof.Ffdh.AArch64.Generation (imm64 shift_ofNat)
open VG.Impl.RsaKeyGen.AArch64.Search
open VG.Impl.Bignum.AArch64 (movi)
open VG.Spec.RsaKeyGen (primeEntropy primeRequest PrimeSearchResult candidateStatus candidateOp)

/-- The candidate at octet `used` of the tape. -/
abbrev cand (p : SPub) (original : State) (used : Nat) : Option (Spec.RsaKeyGen.Candidate × List Byte) :=
  candidateOp p.len p.eB (searchP original) ((searchRand original).drop used)

/-- The octets the candidate at `used` consumes. -/
def candUsed (p : SPub) (original : State) (used : Nat) : Nat :=
  match cand p original used with
  | some (_, rest) => (p.randLen - used) - rest.length
  | none => 0

/-- The candidate's status. -/
abbrev candStatus (p : SPub) (original : State) (used : Nat) : Nat := candidateStatus (cand p original used)

theorem status_lt (r : Option (Spec.RsaKeyGen.Candidate × List Byte)) : candidateStatus r < 4 := by
  unfold candidateStatus; split <;> decide

theorem candUsed_le {p : SPub} {original : State} (used : Nat) : candUsed p original used ≤ p.randLen - used := by
  unfold candUsed; split <;> omega

/-- A loop state, whose search from there finishes as `final`. -/
def SIter (p : SPub) (original : State) (final : PrimeSearchResult) (used k : Nat) (s : State) : Prop :=
  SLive p original used k s ∧ ∃ tr, final = (tailOf p original used k).consume used tr

/-- The counted candidates left past a rejected candidate of status `st`. -/
def nextK (st k : Nat) : Nat := k - (st - 2)

/-- Whether the search goes on past its candidate: one was run, rejected
(too close, or counted), and it consumed something. -/
def Continues (p : SPub) (original : State) (used k : Nat) : Prop :=
  k ≠ 0 ∧ (candStatus p original used = 2 ∨ candStatus p original used = 3) ∧ candUsed p original used ≠ 0

instance (p : SPub) (original : State) (used k : Nat) : Decidable (Continues p original used k) := by
  unfold Continues; infer_instance

/-- Where the candidate at `used` leads: on to the next one after a
rejection, or the end of the search. -/
def SClassified (p : SPub) (original : State) (final : PrimeSearchResult) (used k : Nat) (t : State) : Prop :=
  if Continues p original used k then
    SIter p original final (used + candUsed p original used) (nextK (candStatus p original used) k) t ∧
      word t.mem p.F 112 = 4
  else SDone p original final t

/-! ## The head -/

/-- The status and the octets read, after the candidate. -/
theorem search_head {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hp : CandPost p (searchP original) (searchRand original) used s) :
    WP isa (.block (head ++ ([.subImm .x .x12 .x9 1] : List Instr))) s fun t =>
      SLive p original used k t ∧ CandPost p (searchP original) (searchRand original) used t ∧
      t.gpr .x9 = BitVec.ofNat 64 (candStatus p original used) ∧
      t.gpr .x10 = BitVec.ofNat 64 (candUsed p original used) ∧
      isa.eval (.zero .x .x12) t = some (decide (candStatus p original used = 1)) := by
  have a := h.access
  have hv7 := h.header (j := 7) (v := p.up) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv7
  have hu : InRegions (s.rd ++ s.wr) p.up 8 := by
    refine ⟨⟨p.up, 8⟩, List.mem_append_right _ ?_, ?_⟩
    · rw [h.wr, h.input.1.2.2.2.1, ← h.input.used_eq]; simp [inWrites]
    · simpa only [BitVec.add_zero] using Offset.contains_base p.up (d := 0) (n := 8) (k := 8)
        (by decide) (by decide)
  have hw : s.mem.readW p.up 64 = BitVec.ofNat 64 (candUsed p original used) := by
    have := hp.2.2
    change [word s.mem p.up 0] = _ at this
    simp only [Bignum.word, off, BitVec.add_zero, List.cons.injEq, and_true] at this
    rw [this]; rfl
  have hst : candStatus p original used < 4 := status_lt _
  have h0 : (s.gpr .x0).setWidth 32 = BitVec.ofNat 32 (candStatus p original used) := by
    apply BitVec.eq_of_toNat_eq
    rw [hp.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (WP.keep [.x9, .x10, .x11, .x12] (Q := fun t =>
    (t.gpr .x9 = BitVec.ofNat 64 (candStatus p original used) ∧
      t.gpr .x10 = BitVec.ofNat 64 (candUsed p original used) ∧
      isa.eval (.zero .x .x12) t = some (decide (candStatus p original used = 1))) ∧ t.mem = s.mem) ?_
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨⟨h9, h10, he⟩, hm⟩, k⟩ => ?_
  · unfold head
    brun [ldf, h.x19, hv7, a.ld 56 (by decide), hu, hw,
      VG.Proof.RsaKeyGen.AArch64.exec_addImm_w (show 0 < 4096 by decide), h0]
    refine ⟨?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    · have : ∀ st < 4, ((BitVec.ofNat 32 st + BitVec.ofNat 32 0).setWidth 64 - BitVec.ofNat 64 1 == 0) =
          decide (st = 1) := by decide
      simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq,
        this _ hst]
  · refine ⟨h.keep k hm, hp.keep hm (by rw [k.gpr .x0 (by decide)]), h9, h10, he⟩

/-! ## Finishing from a loop state -/

/-- A finished search, from a loop state through writes of the frame's
words 0, 3, 12 and 14. -/
theorem SLive.doneWrites {p : SPub} {original s t : State} {used k : Nat}
    (h : SLive p original used k s) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 = 0 ∨ e.1 = 3 ∨ e.1 = 12 ∨ e.1 = 14)
    (hm : t.mem = writeController s.mem p.F values)
    (kp : Keep [.x0, .x1, .x2, .x3, .x9, .x10, .x11, .x12, .x13, .x14, .x15] s t)
    {r : PrimeSearchResult}
    (h0 : word t.mem p.F (8 * 0) = BitVec.ofNat 64 r.remaining)
    (h3 : word t.mem p.F (8 * 3) = BitVec.ofNat 64 r.requested)
    (h12 : word t.mem p.F (8 * 12) = BitVec.ofNat 64 r.used)
    (h14 : word t.mem p.F (8 * 14) = BitVec.ofNat 64 r.status)
    (ho : Spec.Rsa.bytesAt s.mem p.op p.len =
      match r.outcome with
      | .accepted c => Spec.Rsa.i2osp c p.len
      | _ => List.replicate p.len 0) :
    SDone p original r t := by
  have hb' : ∀ e ∈ values, e.1 < 20 := fun e he => by rcases hb e he with h | h | h | h <;> omega
  have hg : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => kp.gpr r (by revert r hr; decide)
  have hw (j : Nat) (hj : j < 20) (hn : j ≠ 0 ∧ j ≠ 3 ∧ j ≠ 12 ∧ j ≠ 14) :
      word t.mem p.F (8 * j) = word s.mem p.F (8 * j) := by
    rw [hm, frame_word _ _ _ hb' j hj, controllerValue_unchanged _ _ _ fun e he => by
      rcases hb e he with h | h | h | h <;> omega]
  refine ⟨h.input, kp.rd.trans h.rd, kp.wr.trans h.wr, (hg .x19 (by decide)).trans h.x19,
    fun reg hreg h19 h30 => (hg reg hreg).trans (h.saved reg hreg h19 h30),
    fun r hr => (kp.vcs r hr).trans (h.vcs r hr), ?_, ?_, ?_, ?_, ?_, h0, h3, h12, h14, ?_⟩
  · exact (hw 4 (by decide) (by decide)).trans h.savedX19
  · exact (hw 7 (by decide) (by decide)).trans (h.header (by simp [SPub.headers]))
  · exact (hw 18 (by decide) (by decide)).trans (h.header (by simp [SPub.headers]))
  · exact (hw 1 (by decide) (by decide)).trans (h.header (by simp [SPub.headers]))
  · exact (hw 2 (by decide) (by decide)).trans (h.header (by simp [SPub.headers]))
  · rw [hm, out_frame h.input (frame_frame s.mem p.F values hb')]
    exact ho

/-! ## An accepted candidate -/

def acceptValues (used : Nat) : List (Nat × BitVec 64) :=
  (12, BitVec.ofNat 64 used) :: terminalValues 1

theorem acceptValues_mem (used : Nat) :
    ∀ e ∈ acceptValues used, e.1 = 0 ∨ e.1 = 3 ∨ e.1 = 12 ∨ e.1 = 14 := by
  simp only [acceptValues, terminalValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem acceptValues_bound (used : Nat) : ∀ e ∈ acceptValues used, e.1 < 20 := fun e he => by
  rcases acceptValues_mem used e he with h | h | h | h <;> omega

theorem search_accept {p : SPub} {original s : State} {final : PrimeSearchResult} {used k c : Nat}
    {rest : List Byte} (h : SIter p original final used k s)
    (hp : CandPost p (searchP original) (searchRand original) used s) (hk : k ≠ 0)
    (hc : cand p original used = some (.prime c, rest))
    (h10 : s.gpr .x10 = BitVec.ofNat 64 (candUsed p original used)) :
    WP isa (.block accept) s (SDone p original final) := by
  obtain ⟨h, tr, hfinal⟩ := h
  have a := h.access
  have hv12 := h.header (j := 12) (v := BitVec.ofNat 64 used) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv12
  have hn : candUsed p original used = (p.randLen - used) - rest.length := by simp only [candUsed, hc]
  have e12 : BitVec.ofNat 64 used + BitVec.ofNat 64 (candUsed p original used) =
      BitVec.ofNat 64 (used + candUsed p original used) := by rw [← BitVec.ofNat_add]
  have hl := h.rand_length
  have htail : final = ⟨.accepted c, used + candUsed p original used,
      tr ++ VG.Proof.RsaKeyGen.Search.entry p.len p.eB (searchP original) ((searchRand original).drop used)⟩ := by
    rw [hfinal, tailOf, SPub.tail, VG.Proof.RsaKeyGen.Search.search_prime hk hc, hn]
    simp only [Spec.Entropy.Result.consume, List.length_drop, hl]
  refine WP.mono (WP.keep [.x10, .x11] (Q := fun t =>
    t.mem = writeController s.mem p.F (acceptValues (used + candUsed p original used))) ?_
      (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, kt⟩ => ?_
  · unfold accept terminal writeController acceptValues terminalValues
    simp only [List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, h.x19, h10, hv12, e12, imm64 (show 0 < 65536 by decide),
      imm64 (show 1 < 65536 by decide), a.ld 96 (by decide), a.st 96 (by decide), a.st0,
      a.st 0 (by decide), a.st 24 (by decide), a.st 112 (by decide)]
    rfl
  have hb := acceptValues_bound (used + candUsed p original used)
  have hw (j : Nat) (hj : j < 20) : word t.mem p.F (8 * j) =
      controllerValue (acceptValues (used + candUsed p original used)) j (word s.mem p.F (8 * j)) := by
    rw [hm, frame_word _ _ _ hb j hj]
  rw [htail]
  refine h.doneWrites _ (acceptValues_mem _) hm kt.mono ?_ ?_ ?_ ?_ ?_
  · rw [hw 0 (by decide)]; rfl
  · rw [hw 3 (by decide)]; rfl
  · rw [hw 12 (by decide)]; rfl
  · rw [hw 14 (by decide)]; rfl
  · have ho := hp.2.1
    simp only [hc] at ho
    exact ho

/-! ## A rejected candidate -/

def rejectValues (p : SPub) (used k : Nat) : List (Nat × BitVec 64) :=
  [(12, BitVec.ofNat 64 used), (10, p.rp + BitVec.ofNat 64 used),
    (11, BitVec.ofNat 64 (p.randLen - used)), (0, BitVec.ofNat 64 k), (14, 4)]

theorem rejectValues_bound (p : SPub) (used k : Nat) : ∀ e ∈ rejectValues p used k, e.1 < 20 := by
  simp only [rejectValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem ofNat_sub_ofNat' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  have hb : b < 2 ^ 64 := by omega
  rw [BitVec.toNat_sub_of_le (by
    simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]; exact h)]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt (show a - b < 2 ^ 64 by omega)]

theorem ofNat_beq_zero' {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h]
  exact Iff.rfl

/-- The reject block's stores, for a candidate of status `st` (2 or 3) that
consumed `u` octets. -/
theorem reject_ok {p : SPub} {original s : State} {used k u st : Nat}
    (h : SLive p original used k s) (hk : k ≠ 0) (hst : st = 2 ∨ st = 3)
    (hu : used + u ≤ p.randLen)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 st) (h10 : s.gpr .x10 = BitVec.ofNat 64 u) :
    WP isa (.block reject) s fun t =>
      SLive p original (used + u) (nextK st k) t ∧ word t.mem p.F 112 = 4 := by
  have a := h.access
  have hv0 := h.header (j := 0) (v := BitVec.ofNat 64 k) (by simp [SPub.headers])
  have hv10 := h.header (j := 10) (v := p.rp + BitVec.ofNat 64 used) (by simp [SPub.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  have hv12 := h.header (j := 12) (v := BitVec.ofNat 64 used) (by simp [SPub.headers])
  simp only [Bignum.word, off] at hv0
  simp only [Bignum.word, off, Nat.reduceMul] at hv10 hv11 hv12
  have hlen : p.randLen < 2 ^ 64 := by rw [← h.input.2]; exact BitVec.isLt _
  have hkl : k < 2 ^ 64 := by
    have := h.k_le
    have : p.remaining < 2 ^ 64 := by rw [← h.input.2]; exact BitVec.isLt _
    omega
  have e12 : BitVec.ofNat 64 used + BitVec.ofNat 64 u = BitVec.ofNat 64 (used + u) := by
    rw [← BitVec.ofNat_add]
  have e10 : p.rp + BitVec.ofNat 64 used + BitVec.ofNat 64 u = p.rp + BitVec.ofNat 64 (used + u) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have e11 : BitVec.ofNat 64 (p.randLen - used) - BitVec.ofNat 64 u =
      BitVec.ofNat 64 (p.randLen - (used + u)) := by
    rw [ofNat_sub_ofNat' (by omega) (by omega)]; congr 1; omega
  have e15 : BitVec.ofNat 64 st - BitVec.ofNat 64 2 = BitVec.ofNat 64 (st - 2) :=
    ofNat_sub_ofNat' (by omega) (by omega)
  have e0 : BitVec.ofNat 64 k - BitVec.ofNat 64 (st - 2) = BitVec.ofNat 64 (nextK st k) := by
    rw [nextK, ofNat_sub_ofNat' (by omega) hkl]
  refine WP.mono (WP.keep [.x11, .x12, .x13, .x14, .x15] (Q := fun t =>
    t.mem = writeController s.mem p.F (rejectValues p (used + u) (nextK st k))) ?_
      (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, kt⟩ => ?_
  · unfold reject writeController rejectValues
    simp only [List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, h.x19, h9, h10, hv0, hv10, hv11, hv12, e0, e10, e11, e12, e15,
      imm64 (show 4 < 65536 by decide),
      a.ld0, a.ld 0 (by decide), a.ld 80 (by decide), a.ld 88 (by decide), a.ld 96 (by decide), a.st0,
      a.st 0 (by decide), a.st 80 (by decide), a.st 88 (by decide), a.st 96 (by decide), a.st 112 (by decide)]
    rfl
  have hb := rejectValues_bound p (used + u) (nextK st k)
  have hh : Slots t.mem p.F (p.headers (used + u) (nextK st k)) := by
    refine headers_after _ hb hm ?_
    intro e he
    simp only [SPub.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, rejectValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [SPub.headers])
  refine ⟨h.update hu (by have := h.k_le; unfold nextK; omega) _ hb (by
      simp only [rejectValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) hm kt.mono hh, ?_⟩
  rw [show (112 : Nat) = 8 * 14 from rfl, hm, frame_word _ _ _ hb 14 (by decide)]
  simp only [controllerValue, rejectValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_true, ite_false]

/-- The search past a rejected candidate. -/
theorem tail_past {p : SPub} {original : State} {used k : Nat} {x : Spec.RsaKeyGen.Candidate}
    {rest : List Byte} (hk : k ≠ 0) (hl : (searchRand original).length = p.randLen)
    (hres : cand p original used = some (x, rest))
    (hx : x = .close ∨ x = .rejected) (hu0 : candUsed p original used ≠ 0) :
    tailOf p original used k =
      (tailOf p original (used + candUsed p original used)
        (nextK (candStatus p original used) k)).consume (candUsed p original used)
        (VG.Proof.RsaKeyGen.Search.entry p.len p.eB (searchP original) ((searchRand original).drop used)) := by
  have hcu : candUsed p original used = ((searchRand original).drop used).length - rest.length := by
    simp only [candUsed, hres, List.length_drop, hl]
  obtain ⟨n, hn, -, hrest⟩ := VG.Proof.RsaKeyGen.Search.candidateOp_suffix hres
  have hun : candUsed p original used = n := by
    rw [hcu, hrest]; simp only [List.length_drop] at hn ⊢; omega
  have hlt : rest.length < ((searchRand original).drop used).length := by
    rw [hrest]; simp only [List.length_drop] at hn ⊢; omega
  have hd : rest = (searchRand original).drop (used + candUsed p original used) := by
    rw [hrest, List.drop_drop, hun]
  unfold tailOf SPub.tail
  rcases hx with rfl | rfl
  · rw [VG.Proof.RsaKeyGen.Search.search_close hk hres, ite_eq_left_of_eq_true _ _ (eq_true hlt), ← hcu, ← hd]
    simp only [candStatus, hres, candidateStatus, nextK, Nat.sub_self, Nat.sub_zero]
  · rw [VG.Proof.RsaKeyGen.Search.search_rejected hk hres, ite_eq_left_of_eq_true _ _ (eq_true hlt), ← hcu, ← hd]
    simp only [candStatus, hres, candidateStatus, nextK]

theorem search_rejected {p : SPub} {original s : State} {final : PrimeSearchResult} {used k : Nat}
    {x : Spec.RsaKeyGen.Candidate} {rest : List Byte}
    (h : SIter p original final used k s) (hk : k ≠ 0)
    (hres : cand p original used = some (x, rest)) (hx : x = .close ∨ x = .rejected)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 (candStatus p original used))
    (h10 : s.gpr .x10 = BitVec.ofNat 64 (candUsed p original used)) :
    WP isa rejected s (SClassified p original final used k) := by
  obtain ⟨h, tr, hfinal⟩ := h
  have hl := h.rand_length
  have hst : candStatus p original used = 2 ∨ candStatus p original used = 3 := by
    rcases hx with rfl | rfl <;> simp [candStatus, hres, candidateStatus]
  have hlt : candUsed p original used < 2 ^ 64 := by
    have := candUsed_le (p := p) (original := original) used
    have : p.randLen < 2 ^ 64 := by rw [← h.input.2]; exact BitVec.isLt _
    omega
  unfold rejected
  have he : isa.eval (.zero .x .x10) s = some (decide (candUsed p original used = 0)) := by
    rw [eval_zero, h10, ofNat_beq_zero' hlt]
  refine WP.ite _ he (fun hz => ?_) (fun hz => ?_)
  · -- Nothing consumed: the specification's progress check gives up.
    have hz := of_decide_eq_true hz
    have hnc : ¬Continues p original used k := fun hc => hc.2.2 hz
    have hcu : candUsed p original used = ((searchRand original).drop used).length - rest.length := by
      simp only [candUsed, hres, List.length_drop, hl]
    obtain ⟨n, hn, -, hrest⟩ := VG.Proof.RsaKeyGen.Search.candidateOp_suffix hres
    have hlt' : ¬rest.length < ((searchRand original).drop used).length := by
      rw [hrest]; simp only [List.length_drop] at hn hcu ⊢; rw [hrest] at hcu
      simp only [List.length_drop] at hcu; omega
    have htail : tailOf p original used k =
        ⟨.exhausted, 0, VG.Proof.RsaKeyGen.Search.entry p.len p.eB (searchP original) ((searchRand original).drop used)⟩ := by
      unfold tailOf SPub.tail
      rcases hx with rfl | rfl
      · rw [VG.Proof.RsaKeyGen.Search.search_close hk hres, ite_eq_right_of_eq_false _ _ (eq_false hlt')]
      · rw [VG.Proof.RsaKeyGen.Search.search_rejected hk hres, ite_eq_right_of_eq_false _ _ (eq_false hlt')]
    rw [htail] at hfinal
    unfold SClassified
    simp only [hnc, ite_false]
    exact search_exhausted h (by rw [hfinal]; rfl)
  · have hz := of_decide_eq_false hz
    have hc : Continues p original used k := ⟨hk, hst, hz⟩
    have hpast := tail_past hk hl hres hx hz
    rw [hpast, VG.Proof.RsaKeyGen.Search.consume_consume] at hfinal
    unfold SClassified
    simp only [hc, ite_true]
    have hu : used + candUsed p original used ≤ p.randLen := by
      have := candUsed_le (p := p) (original := original) used
      have := h.used_le
      omega
    exact WP.mono (reject_ok h hk hst hu h9 h10) fun t ⟨ht, h4⟩ => ⟨⟨ht, _, hfinal⟩, h4⟩

/-! ## A tape too short for the candidate -/

def requestValues (p : SPub) (used : Nat) : List (Nat × BitVec 64) :=
  [(3, BitVec.ofNat 64 (primeRequest p.len (p.randLen - used))), (14, 0)]

theorem requestValues_mem (p : SPub) (used : Nat) :
    ∀ e ∈ requestValues p used, e.1 = 0 ∨ e.1 = 3 ∨ e.1 = 12 ∨ e.1 = 14 := by
  simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl) <;> dsimp only <;> decide

theorem requestValues_bound (p : SPub) (used : Nat) : ∀ e ∈ requestValues p used, e.1 < 20 := fun e he => by
  rcases requestValues_mem p used e he with h | h | h | h <;> omega

theorem SInput.randLen_le {p : SPub} {s : State} (h : SInput p s) : p.randLen ≤ primeEntropy p.len := by
  rw [← h.2]; exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem request_value {p : SPub} {original s : State} {used k : Nat} (h : SLive p original used k s) :
    WP isa (.block (request.take 9)) s fun t =>
      (t.gpr .x10 = BitVec.ofNat 64 (primeRequest p.len (p.randLen - used)) ∧ t.mem = s.mem) ∧
        Keep [.x10, .x11, .x12, .x13] s t := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 (primeEntropy p.len)) (by simp [SPub.headers])
  have hv6 := h.header (j := 6) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2 hv6 hv11
  have hlen := h.input.len_bounds
  have hrl := h.input.randLen_le
  have hE : primeEntropy p.len ≤ 32769 * 512 := by unfold primeEntropy; omega
  refine WP.keep [.x10, .x11, .x12, .x13] ?_ (by decide) (by decide) (by decide +kernel)
  unfold request
  simp only [List.take_succ_cons, List.take_zero]
  brun [ldf, h.x19, hv2, hv6, hv11, a.ld 16 (by decide), a.ld 48 (by decide), a.ld 88 (by decide),
    shift_ofNat, subs_ge (show p.randLen - used < 2 ^ 64 by omega) (show p.len * 2 ^ 4 < 2 ^ 64 by omega)]
  unfold primeRequest Spec.Entropy.request
  have hA : p.randLen - used ≤ primeEntropy p.len := by omega
  generalize p.randLen - used = A at *
  generalize primeEntropy p.len = E at *
  by_cases h1 : p.len * 2 ^ 4 ≤ A
  · simp only [h1, decide_true, ite_true, ← BitVec.ofNat_add,
      subs_ge (show A + A < 2 ^ 64 by omega) (show E < 2 ^ 64 by omega)]
    by_cases h2 : E ≤ A + A
    · simp only [h2, decide_true, ite_true]
      congr 1; omega
    · simp only [h2, decide_false, Bool.false_eq_true, ite_false]
      congr 1; omega
  · simp only [h1, decide_false, Bool.false_eq_true, ite_false, ← BitVec.ofNat_add,
      subs_ge (show p.len * 2 ^ 4 + p.len * 2 ^ 4 < 2 ^ 64 by omega) (show E < 2 ^ 64 by omega)]
    by_cases h2 : E ≤ p.len * 2 ^ 4 + p.len * 2 ^ 4
    · simp only [h2, decide_true, ite_true]
      congr 1; omega
    · simp only [h2, decide_false, Bool.false_eq_true, ite_false]
      congr 1; omega

theorem search_request {p : SPub} {original s : State} {final : PrimeSearchResult} {used k : Nat}
    (h : SIter p original final used k s) (hk : k ≠ 0) (hc : cand p original used = none)
    (hshort : ¬primeEntropy p.len ≤ p.randLen - used)
    (hout : Spec.Rsa.bytesAt s.mem p.op p.len = List.replicate p.len 0) :
    WP isa (.block request) s (SDone p original final) := by
  obtain ⟨h, tr, hfinal⟩ := h
  have hl := h.rand_length
  rw [show request = request.take 9 ++ request.drop 9 from (List.take_append_drop _ _).symm,
    WP.block_append_iff]
  refine WP.mono (request_value h) fun v ⟨⟨h10, hmv⟩, kv⟩ => ?_
  have hv := h.keep kv hmv
  have a := hv.access
  refine WP.mono (WP.keep [.x11] (Q := fun t =>
    t.mem = writeController v.mem p.F (requestValues p used)) ?_
      (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, kt⟩ => ?_
  · unfold request writeController requestValues
    simp only [List.drop_succ_cons, List.drop_zero, List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, hv.x19, h10, imm64 (show 0 < 65536 by decide), a.st 24 (by decide), a.st 112 (by decide)]
    rfl
  have htail : final = ⟨.entropy k (primeRequest p.len (p.randLen - used)), used,
      tr ++ VG.Proof.RsaKeyGen.Search.entry p.len p.eB (searchP original) ((searchRand original).drop used)⟩ := by
    rw [hfinal, tailOf, SPub.tail, VG.Proof.RsaKeyGen.Search.search_short hk hc]
    simp only [List.length_drop, hl]
    rw [ite_eq_right hshort]
    simp only [Spec.Entropy.Result.consume, Nat.add_zero]
  have hb := requestValues_bound p used
  have hw (j : Nat) (hj : j < 20) : word t.mem p.F (8 * j) =
      controllerValue (requestValues p used) j (word v.mem p.F (8 * j)) := by
    rw [hm, frame_word _ _ _ hb j hj]
  rw [htail]
  refine hv.doneWrites _ (requestValues_mem p used) hm kt.mono ?_ ?_ ?_ ?_ ?_
  · rw [hw 0 (by decide)]
    simp only [controllerValue, requestValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ite_false,
      PrimeSearchResult.remaining]
    exact hv.header (by simp [SPub.headers])
  · rw [hw 3 (by decide)]; rfl
  · rw [hw 12 (by decide)]
    simp only [controllerValue, requestValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ite_false]
    exact hv.header (by simp [SPub.headers])
  · rw [hw 14 (by decide)]; rfl
  · rw [hmv]; exact hout

/-- Whether the tape holds the entropy budget. -/
theorem short_guard {p : SPub} {original s : State} {used k : Nat} (h : SLive p original used k s) :
    WP isa (.block [ldf .x10 11, ldf .x11 2, .subs .x .x12 .x10 .x11, movi .x13 0, movi .x14 1,
        .csel .x .x12 .x14 .x13]) s fun t =>
      (SLive p original used k t ∧ t.mem = s.mem) ∧
        isa.eval (.zero .x .x12) t = some (decide (p.randLen - used < primeEntropy p.len)) := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 (primeEntropy p.len)) (by simp [SPub.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2 hv11
  have hr : p.randLen < 2 ^ 64 := by rw [← h.input.2]; exact BitVec.isLt _
  have hE : primeEntropy p.len < 2 ^ 64 := by
    have := h.input.len_bounds; unfold primeEntropy; omega
  refine WP.mono (WP.keep [.x10, .x11, .x12, .x13, .x14] (Q := fun t =>
    isa.eval (.zero .x .x12) t = some (decide (p.randLen - used < primeEntropy p.len)) ∧ t.mem = s.mem) ?_
    (by decide) (by decide) (by decide +kernel)) fun _ ⟨⟨he, hm⟩, k⟩ => ⟨⟨h.keep k hm, hm⟩, he⟩
  brun [ldf, h.x19, hv2, hv11, a.ld 16 (by decide), a.ld 88 (by decide), imm64 (show 0 < 65536 by decide),
    imm64 (show 1 < 65536 by decide), subs_ge (show p.randLen - used < 2 ^ 64 by omega) hE]
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq]
  by_cases hb : primeEntropy p.len ≤ p.randLen - used
  · simp only [hb, decide_true, ite_true, show ¬p.randLen - used < primeEntropy p.len by omega,
      decide_false]
    decide
  · simp only [hb, decide_false, ite_false, show p.randLen - used < primeEntropy p.len by omega,
      decide_true, Bool.false_eq_true]
    decide

theorem search_short {p : SPub} {original s : State} {final : PrimeSearchResult} {used k : Nat}
    (h : SIter p original final used k s) (hk : k ≠ 0) (hc : cand p original used = none)
    (hout : Spec.Rsa.bytesAt s.mem p.op p.len = List.replicate p.len 0) :
    WP isa short s (SDone p original final) := by
  unfold short
  refine WP.seq (WP.mono (short_guard h.1) fun u ⟨⟨hu, hm⟩, he⟩ => ?_)
  refine WP.ite _ he ?_ ?_
  · intro hs
    have hs' := of_decide_eq_true hs
    exact search_request ⟨hu, h.2⟩ hk hc (by omega) (by rw [hm]; exact hout)
  · intro hs
    have hs' := of_decide_eq_false hs
    obtain ⟨-, tr, hfinal⟩ := h
    have hl := hu.rand_length
    refine search_exhausted hu ?_
    rw [hfinal, tailOf, SPub.tail, VG.Proof.RsaKeyGen.Search.search_short hk hc]
    simp only [List.length_drop, hl]
    rw [ite_eq_left (show primeEntropy p.len ≤ p.randLen - used by omega)]
    simp only [Spec.Entropy.Result.consume, Nat.add_zero]

/-! ## The classification -/

theorem search_classify {p : SPub} {original s : State} {final : PrimeSearchResult} {used k : Nat}
    (h : SIter p original final used k s) (hk : k ≠ 0)
    (hp : CandPost p (searchP original) (searchRand original) used s) :
    WP isa classify s (SClassified p original final used k) := by
  unfold classify
  refine WP.seq (WP.mono (search_head h.1 hp) fun u ⟨hu, hpu, h9, h10, he⟩ => ?_)
  have hiu : SIter p original final used k u := ⟨hu, h.2⟩
  cases hc : cand p original used with
  | none =>
    have hnc : ¬Continues p original used k := fun h => by
      simp only [Continues, candStatus, hc, candidateStatus] at h; omega
    simp only [candStatus, hc, candidateStatus] at he h9
    refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
    refine WP.ite true (by rw [eval_zero, h9]; rfl) (fun _ => ?_) (fun hf => by cases hf)
    have hout := hpu.2.1
    simp only [hc] at hout
    unfold SClassified
    simp only [hnc, ite_false]
    exact search_short hiu hk hc hout
  | some pair =>
    obtain ⟨x, rest⟩ := pair
    cases x with
    | prime c =>
      have hnc : ¬Continues p original used k := fun h => by
        simp only [Continues, candStatus, hc, candidateStatus] at h; omega
      simp only [candStatus, hc, candidateStatus] at he h9
      refine WP.ite true he (fun _ => ?_) (fun hf => by cases hf)
      unfold SClassified
      simp only [hnc, ite_false]
      exact search_accept hiu hpu hk hc h10
    | close =>
      have h9' := h9
      simp only [candStatus, hc, candidateStatus] at he h9'
      refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
      refine WP.ite false (by rw [eval_zero, h9']; rfl) (fun hf => by cases hf) fun _ => ?_
      exact search_rejected hiu hk hc (.inl rfl) h9 h10
    | rejected =>
      have h9' := h9
      simp only [candStatus, hc, candidateStatus] at he h9'
      refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
      refine WP.ite false (by rw [eval_zero, h9']; rfl) (fun hf => by cases hf) fun _ => ?_
      exact search_rejected hiu hk hc (.inr rfl) h9 h10

end VG.Proof.RsaKeyGen.AArch64.Search
