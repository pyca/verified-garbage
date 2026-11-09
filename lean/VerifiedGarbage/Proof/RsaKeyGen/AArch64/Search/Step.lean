module

public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Call
import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Entry
import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.Bignum.AArch64.PubFail
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The search's loop (AArch64)

As on x86-64 (`Proof/RsaKeyGen/X86_64/Search/Step.lean`): after a candidate,
the search accepts its prime, asks for more entropy, gives up, or goes on
past it to the next (`search_classify`); with no counted candidates left it
gives up without one (`search_exhausted`). The loop runs these steps to its
end (`search_loop`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.AArch64 (movi ld)
open VG.Impl.RsaKeyGen.AArch64.Search
open VG.Spec.RsaKeyGen (primeSearch primeEntropy PrimeSearchResult)

/-- A finished search, before `finish` stores its results. -/
structure SearchDone (p : SearchPublic) (original : State) (result : PrimeSearchResult) (s : State) :
    Prop where
  input : SearchInput p original
  rd : s.rd = original.rd
  wr : s.wr = p.frame :: original.wr
  x19 : s.gpr .x19 = p.F
  saved : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x30 → s.gpr r = original.gpr r
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (original.v r).extractLsb' 0 64
  savedX19 : word s.mem p.F 32 = original.gpr .x19
  usedPtr : word s.mem p.F (8 * 7) = p.up
  stp : word s.mem p.F (8 * 18) = p.stp
  len : word s.mem p.F (8 * 1) = BitVec.ofNat 64 p.len
  cap : word s.mem p.F (8 * 2) = BitVec.ofNat 64 (primeEntropy p.len)
  remaining : word s.mem p.F (8 * 0) = BitVec.ofNat 64 result.remaining
  request : word s.mem p.F (8 * 3) = BitVec.ofNat 64 (requested p.len result)
  used : word s.mem p.F (8 * 16) = BitVec.ofNat 64 result.used
  status : word s.mem p.F (8 * 17) = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt s.mem p.op p.len =
    match result.outcome with
    | .accepted c => Spec.Rsa.i2osp c p.len
    | _ => List.replicate p.len 0

/-- A loop state's frame words, read. -/
theorem SearchLive.slot {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) {j : Nat} {v : BitVec 64}
    (hj : (j, v) ∈ p.headers used remaining) : word s.mem p.F (8 * j) = v := h.headers (j, v) hj

/-- A finished search from a loop state whose words agree. -/
theorem done_of_live {p : SearchPublic} {original s : State} {used remaining : Nat}
    {result : PrimeSearchResult} (h : SearchLive p original used remaining s)
    (h0 : word s.mem p.F (8 * 0) = BitVec.ofNat 64 result.remaining)
    (h3 : word s.mem p.F (8 * 3) = BitVec.ofNat 64 (requested p.len result))
    (h16 : word s.mem p.F (8 * 16) = BitVec.ofNat 64 result.used)
    (h17 : word s.mem p.F (8 * 17) = BitVec.ofNat 64 result.status)
    (hout : Spec.Rsa.bytesAt s.mem p.op p.len =
      match result.outcome with
      | .accepted c => Spec.Rsa.i2osp c p.len
      | _ => List.replicate p.len 0) :
    SearchDone p original result s :=
  ⟨h.input, h.rd, h.wr, h.x19, h.saved, h.vcs, h.savedX19,
    h.slot (by simp [SearchPublic.headers]), h.slot (by simp [SearchPublic.headers]),
    h.slot (by simp [SearchPublic.headers]), h.slot (by simp [SearchPublic.headers]),
    h0, h3, h16, h17, hout⟩

theorem SearchDone.keep {p : SearchPublic} {original s t : State} {result : PrimeSearchResult}
    (h : SearchDone p original result s) {rs : List Reg} (k : Keep rs s t) (hm : t.mem = s.mem)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) : SearchDone p original result t := by
  refine ⟨h.input, k.rd.trans h.rd, k.wr.trans h.wr,
    (k.gpr _ (hregs .x19 (by decide))).trans h.x19,
    fun reg hr h19 h30 => (k.gpr reg (hregs reg hr)).trans (h.saved reg hr h19 h30),
    fun r hr => (k.vcs r hr).trans (h.vcs r hr), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  exacts [h.savedX19, h.usedPtr, h.stp, h.len, h.cap, h.remaining, h.request, h.used, h.status, h.output]

/-! ## The frame's stores -/

theorem SearchLive.frame_st {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    ∀ d, d + 8 ≤ 160 → InRegions s.wr (p.F + BitVec.ofNat 64 d) 8 :=
  fun _ hd => (h.input.frame_scr h.wr).st hd

theorem SearchLive.frame_ld' {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    ∀ d, d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 d) 8 :=
  fun d hd => let ⟨r, hr, hc⟩ := h.frame_st d hd; ⟨r, List.mem_append_right _ hr, hc⟩

def terminalValues (status : Nat) : List (Nat × BitVec 64) :=
  [(0, 0), (3, 0), (17, BitVec.ofNat 64 status)]

theorem terminalValues_bound (status : Nat) : ∀ e ∈ terminalValues status, e.1 < 20 := by
  simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

/-- `terminal k`: no counted candidates, no request, and the status `k`. -/
theorem search_terminal {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) {k : Nat} (hk : k = 1 ∨ k = 3) :
    WP isa (.block (terminal k)) s fun t =>
      t.mem = writeFrame s.mem p.F (terminalValues k) ∧ Keep [.x10, .x11] s t := by
  have hs := h.frame_st
  have hs0 : InRegions s.wr p.F 8 := by simpa only [BitVec.add_zero] using hs 0 (by decide)
  rcases hk with rfl | rfl <;>
  refine WP.keep [.x10, .x11] ?_ (by decide) (by decide) (by decide +kernel) <;>
  unfold terminal writeFrame terminalValues <;>
  simp only [List.foldl_cons, List.foldl_nil]
  all_goals
    brun [ldf, stf, h.x19, imm64 (show 0 < 65536 by decide), imm64 (show 1 < 65536 by decide),
      imm64 (show 3 < 65536 by decide), hs0, hs 0 (by decide), hs 24 (by decide), hs 136 (by decide)]
    rfl

theorem SearchPublic.headers_not_3_17 (p : SearchPublic) (used remaining : Nat) :
    ∀ e ∈ p.headers used remaining, e.1 ≠ 3 ∧ e.1 ≠ 17 := by
  simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    dsimp only <;> exact ⟨by decide, by decide⟩

/-- The words but the counted candidates do not depend on them. -/
theorem SearchPublic.headers_other {p : SearchPublic} {used k k' : Nat} {e : Nat × BitVec 64}
    (he : e ∈ p.headers used k) (h0 : e.1 ≠ 0) : e ∈ p.headers used k' := by
  simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he ⊢
  rcases he with rfl | he
  · exact absurd rfl h0
  · exact Or.inr he

theorem SearchPublic.headers_zero {p : SearchPublic} {used k : Nat} {e : Nat × BitVec 64}
    (he : e ∈ p.headers used k) (h0 : e.1 = 0) : e = (0, BitVec.ofNat 64 k) := by
  simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (simp at h0)

/-- Through the terminal stores, a loop state with no counted candidates
left. -/
theorem SearchLive.terminated {p : SearchPublic} {original s t : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (k : Nat)
    (hm : t.mem = writeFrame s.mem p.F (terminalValues k))
    (kt : Keep [.x10, .x11] s t) : SearchLive p original used 0 t := by
  have hb := terminalValues_bound k
  refine h.update h.used_le (Nat.zero_le _) _ hb (by
      simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide) hm kt (by decide) ?_
  intro e he
  rw [hm, writeFrame_word _ _ _ hb e.1 (SearchPublic.headers_bound _ _ _ e he)]
  by_cases h0 : e.1 = 0
  · rw [SearchPublic.headers_zero he h0]
    rfl
  · have h317 := SearchPublic.headers_not_3_17 _ _ _ e he
    rw [frameValue_unchanged _ _ _ (by
      simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl)
      exacts [h0, h317.1, h317.2])]
    exact h.headers e (SearchPublic.headers_other he h0)

/-! ## Zeros at `out` -/

theorem SearchLive.out_region {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) : (⟨p.op, p.len⟩ : Region) = inOut original := by
  rw [← h.input.2]; rfl

/-- A zeroing of `out` changes memory only there. -/
theorem zero_frame {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) {m m' : Mem}
    (hf : ∀ x, (∀ j < p.len, x ≠ p.op + BitVec.ofNat 64 j) → m' x = m x) :
    Frame (SearchInput.callChanges original) m m' := by
  intro a ha
  apply hf
  intro i hi he
  have hk := h.callFacts.nO
  apply ha (inOut original) (by simp [SearchInput.callChanges])
  rw [he, ← h.out_region]
  exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])

theorem search_zero_out {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa zeroOut s fun t =>
      SearchLive p original used remaining t ∧ Spec.Rsa.bytesAt t.mem p.op p.len = List.replicate p.len 0 ∧
      (∀ j < 20, word t.mem p.F (8 * j) = word s.mem p.F (8 * j)) := by
  have hf := h.callFacts
  have hk := hf.nO
  have hl0 : 0 < p.len := by have := hf.len; unfold Spec.RsaKeyGen.primeLenValid at this; omega
  have hL : p.len ≤ 512 := by have := hf.len; unfold Spec.RsaKeyGen.primeLenValid at this; omega
  have hv := h.slot (j := 5) (v := p.op) (by simp [SearchPublic.headers])
  have hv6 := h.slot (j := 6) (v := BitVec.ofNat 64 p.len) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv hv6
  have hl := h.frame_ld' 40 (by decide)
  have hl6 := h.frame_ld' 48 (by decide)
  have hout : ∀ i < p.len, InRegions s.wr (p.op + BitVec.ofNat 64 i) 1 := fun i hi =>
    ⟨⟨p.op, p.len⟩, by
      rw [h.wr, h.input.1.2.2.2.1, h.out_region]; exact List.mem_cons_of_mem _ (by simp [inWrites]),
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])⟩
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = p.op + BitVec.ofNat 64 0 ∧
      t.gpr .x2 = BitVec.ofNat 64 p.len ∧ t.gpr .x3 = 0 ∧ t.mem = s.mem) (by
    brun [ldf, h.x19, imm64 (show 0 < 65536 by decide), hl, hl6, hv, hv6]) (by decide) (by decide)
      (by decide +kernel)) fun s₁ ⟨⟨h1, h2, h3, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_countdown (N := p.len) (by omega) hl0 (BInv s₁ p.op)
    (fun i hi t hI _ => bStep_ok (by omega) h3 (fun i hi => by rw [k₁.wr]; exact hout i hi) hi hI)
    ⟨Keep.refl _ _, h1, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩ h2) fun t hI => ?_
  have hfx : ∀ x, (∀ i < p.len, x ≠ p.op + BitVec.ofNat 64 i) → t.mem x = s.mem x :=
    fun x hx => by rw [hI.frame x hx, hm₁]
  have kk := k₁.trans hI.keep
  have hfr := zero_frame h hfx
  refine ⟨h.restore kk.rd kk.wr kk.sp (fun r hr _ => kk.gpr r (by revert r hr; decide)) kk.vcs hfr, ?_,
    fun j hj => h.input.frame_words hfr j hj⟩
  refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact hI.bytes i (List.mem_range.mp hi)

theorem search_exhausted {p : SearchPublic} {original s : State} {used remaining : Nat}
    {result : PrimeSearchResult} (h : SearchLive p original used remaining s)
    (hr : result = ⟨.exhausted, used, result.trace⟩) :
    WP isa exhausted s (SearchDone p original result) := by
  unfold exhausted
  refine WP.seq (WP.mono (search_terminal h (k := 3) (.inr rfl)) fun u ⟨hm, ku⟩ => ?_)
  have hu := h.terminated 3 hm ku
  refine WP.mono (search_zero_out hu) fun t ⟨ht, hout, hw⟩ => ?_
  have hb := terminalValues_bound 3
  have hwv (j : Nat) (hj : j < 20) : word t.mem p.F (8 * j) =
      frameValue (terminalValues 3) j (word s.mem p.F (8 * j)) := by
    rw [hw j hj, hm, writeFrame_word _ _ _ hb j hj]
  rw [hr]
  refine done_of_live ht ?_ ?_ ?_ ?_ (by simpa only using hout)
  · rw [hwv 0 (by decide)]; rfl
  · rw [hwv 3 (by decide)]; rfl
  · rw [hwv 16 (by decide)]; exact h.slot (by simp [SearchPublic.headers])
  · rw [hwv 17 (by decide)]; rfl

/-! ## The search's tail -/

/-- The search from octet `used` of the tape, with `remaining` counted
candidates left. -/
abbrev tailOf (p : SearchPublic) (original : State) (used remaining : Nat) : PrimeSearchResult :=
  primeSearch p.len p.eB (searchP original) remaining ((searchRand original).drop used)

/-- A loop state, whose search from there finishes as `final`. -/
def SearchIter (p : SearchPublic) (original : State) (final : PrimeSearchResult) (used remaining : Nat)
    (s : State) : Prop :=
  SearchLive p original used remaining s ∧ ∃ tr, final = (tailOf p original used remaining).consume used tr

/-- The candidate's status, from `used`. -/
abbrev candStatus (p : SearchPublic) (original : State) (used : Nat) : Nat :=
  Spec.RsaKeyGen.candidateStatus
    (Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used))

/-- The candidate's consumption, from `used`. -/
abbrev candUsed (p : SearchPublic) (original : State) (used : Nat) : Nat :=
  match Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used) with
  | some (_, rest) => (p.randLen - used) - rest.length
  | none => 0

/-- Whether the search goes on past its candidate: one was run, rejected
(too close, or counted), and it consumed something. -/
def Continues (p : SearchPublic) (original : State) (used remaining : Nat) : Prop :=
  remaining ≠ 0 ∧ (candStatus p original used = 2 ∨ candStatus p original used = 3) ∧
    candUsed p original used ≠ 0

/-- The loop state past a candidate rejected from `used`, with the next
offset and count, and the search from `used` in terms of the one from there. -/
def ContinuePost (p : SearchPublic) (original : State) (final : PrimeSearchResult) (used remaining : Nat)
    (t : State) : Prop :=
  remaining ≠ 0 ∧ ∃ u k, used < u ∧ SearchIter p original final u k t ∧
    u = used + candUsed p original used ∧
    ((k = remaining ∧ candStatus p original used = 2) ∨ (k = remaining - 1 ∧ candStatus p original used = 3)) ∧
    tailOf p original used remaining =
      (tailOf p original u k).consume (u - used)
        (Search.entry p.len p.eB (searchP original) ((searchRand original).drop used))

theorem ContinuePost.continues {p : SearchPublic} {original t : State} {final : PrimeSearchResult}
    {used remaining : Nat} (h : ContinuePost p original final used remaining t) :
    Continues p original used remaining := by
  obtain ⟨hr, u, k, hlt, -, hu, hk, -⟩ := h
  exact ⟨hr, hk.elim (fun h => .inl h.2) (fun h => .inr h.2), by omega⟩

theorem ContinuePost.keep {p : SearchPublic} {original s t : State} {final : PrimeSearchResult}
    {used remaining : Nat} (h : ContinuePost p original final used remaining s) {rs : List Reg}
    (k : Keep rs s t) (hm : t.mem = s.mem) (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) :
    ContinuePost p original final used remaining t :=
  let ⟨hr, u, k', hlt, hi, rest⟩ := h
  ⟨hr, u, k', hlt, ⟨hi.1.keep k hm hregs, hi.2⟩, rest⟩

/-- What an iteration leaves: the search goes on (status 4) past its
candidate, or it is finished. -/
def IterPost (p : SearchPublic) (original : State) (final : PrimeSearchResult) (used remaining : Nat)
    (t : State) : Prop :=
  (word t.mem p.F (8 * 17) = 4 ∧ ContinuePost p original final used remaining t) ∨
    (word t.mem p.F (8 * 17) ≠ 4 ∧ ¬Continues p original used remaining ∧ SearchDone p original final t)

theorem SearchLive.rand_length {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) : (searchRand original).length = p.randLen := by
  rw [← h.input.2]; simp [searchRand, Spec.Rsa.bytesAt, searchOfState]

theorem status_lt (p : SearchPublic) (original : State) (used : Nat) : candStatus p original used < 4 := by
  unfold candStatus Spec.RsaKeyGen.candidateStatus; split <;> decide

/-- The status and the octets the candidate consumed, after it. -/
theorem search_head {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (hp : CandPost p (searchP original) (searchRand original) used s) :
    WP isa (.block (head ++ ([.subImm .x .x12 .x9 1] : List Instr))) s fun t =>
      SearchLive p original used remaining t ∧ CandPost p (searchP original) (searchRand original) used t ∧
      t.gpr .x9 = BitVec.ofNat 64 (candStatus p original used) ∧
      t.gpr .x10 = BitVec.ofNat 64 (candUsed p original used) ∧
      isa.eval (.zero .x .x12) t = some (decide (candStatus p original used = 1)) := by
  have hv7 := h.slot (j := 7) (v := p.up) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv7
  have hu : InRegions (s.rd ++ s.wr) p.up 8 := by
    refine ⟨inUsed original, List.mem_append_right _ ?_, ?_⟩
    · rw [h.wr, h.input.1.2.2.2.1]; exact List.mem_cons_of_mem _ (by simp [inWrites])
    · rw [← h.input.2]; simp only [inUsed, searchOfState, Region.Contains, BitVec.sub_self, BitVec.toNat_zero,
        Nat.zero_add]; decide
  have hw : s.mem.readW p.up 64 = BitVec.ofNat 64 (candUsed p original used) := by
    have := hp.2.2
    change [word s.mem p.up 0] = _ at this
    simp only [Bignum.word, off, BitVec.add_zero, List.cons.injEq, and_true] at this
    exact this
  have hst := status_lt p original used
  have h0 : (s.gpr .x0).setWidth 32 = BitVec.ofNat 32 (candStatus p original used) := by
    apply BitVec.eq_of_toNat_eq
    rw [hp.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (WP.keep [.x9, .x10, .x11, .x12] (Q := fun t =>
    (t.gpr .x9 = BitVec.ofNat 64 (candStatus p original used) ∧
      t.gpr .x10 = BitVec.ofNat 64 (candUsed p original used) ∧
      isa.eval (.zero .x .x12) t = some (decide (candStatus p original used = 1))) ∧ t.mem = s.mem) ?_
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨⟨h9, h10, he⟩, hm⟩, k⟩ => ?_
  · unfold head
    brun [ldf, ld, h.x19, hv7, h.frame_ld' 56 (by decide), hu, hw, BitVec.add_zero,
      VG.Proof.RsaKeyGen.AArch64.exec_addImm_w (show 0 < 4096 by decide), h0]
    refine ⟨?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    · have : ∀ st < 4, ((BitVec.ofNat 32 st).setWidth 64 - BitVec.ofNat 64 1 == 0) =
          decide (st = 1) := by decide
      simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq,
        this _ hst]
  · refine ⟨h.keep k hm, ?_, h9, h10, he⟩
    exact hp.keep hm (by rw [k.gpr .x0 (by decide)])

/-- Through stores of the frame's words but its fixed ones, a finished search
with the words stored. -/
theorem SearchLive.done_after {p : SearchPublic} {original s t : State} {used remaining : Nat}
    {result : PrimeSearchResult} (h : SearchLive p original used remaining s)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 20)
    (hfix : ∀ e ∈ values, e.1 ≠ 1 ∧ e.1 ≠ 2 ∧ e.1 ≠ 4 ∧ e.1 ≠ 7 ∧ e.1 ≠ 18)
    (hm : t.mem = writeFrame s.mem p.F values) {rs : List Reg} (kt : Keep rs s t)
    (hrs : ∀ r ∈ preserved, r ∉ rs)
    (h0 : frameValue values 0 (word s.mem p.F (8 * 0)) = BitVec.ofNat 64 result.remaining)
    (h3 : frameValue values 3 (word s.mem p.F (8 * 3)) = BitVec.ofNat 64 (requested p.len result))
    (h16 : frameValue values 16 (word s.mem p.F (8 * 16)) = BitVec.ofNat 64 result.used)
    (h17 : frameValue values 17 (word s.mem p.F (8 * 17)) = BitVec.ofNat 64 result.status)
    (hout : Spec.Rsa.bytesAt s.mem p.op p.len =
      match result.outcome with
      | .accepted c => Spec.Rsa.i2osp c p.len
      | _ => List.replicate p.len 0) :
    SearchDone p original result t := by
  have hw (j : Nat) (hj : j < 20) : word t.mem p.F (8 * j) = frameValue values j (word s.mem p.F (8 * j)) := by
    rw [hm]; exact writeFrame_word _ _ _ hb j hj
  have hkeep (j : Nat) (hj : j < 20) (hn : ∀ e ∈ values, j ≠ e.1) : word t.mem p.F (8 * j) = word s.mem p.F (8 * j) := by
    rw [hw j hj, frameValue_unchanged _ _ _ hn]
  have hd := h.input.frame_disjoint (r := inOut original) (by simp [SearchInput.callChanges])
  rw [← h.out_region] at hd
  have hn := h.callFacts.nO
  have hbytes : Spec.Rsa.bytesAt t.mem p.op p.len = Spec.Rsa.bytesAt s.mem p.op p.len := by
    rw [hm]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact (writeFrame_frame s.mem p.F values hb).bytes (R := ⟨p.op, p.len⟩)
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hd.symm) (by show p.len ≤ 2 ^ 64; omega)
      (List.mem_range.mp hi)
  refine ⟨h.input, kt.rd.trans h.rd, kt.wr.trans h.wr,
    (kt.gpr _ (hrs .x19 (by decide))).trans h.x19,
    fun r hr hn hs => (kt.gpr r (hrs r hr)).trans (h.saved r hr hn hs),
    fun r hr => (kt.vcs r hr).trans (h.vcs r hr),
    ?_, ?_, ?_, ?_, ?_, by rw [hw 0 (by decide)]; exact h0, by rw [hw 3 (by decide)]; exact h3,
    by rw [hw 16 (by decide)]; exact h16, by rw [hw 17 (by decide)]; exact h17, by rw [hbytes]; exact hout⟩
  · exact (hkeep 4 (by decide) fun e he => (hfix e he).2.2.1.symm).trans h.savedX19
  · exact (hkeep 7 (by decide) fun e he => (hfix e he).2.2.2.1.symm).trans (h.slot (by simp [SearchPublic.headers]))
  · exact (hkeep 18 (by decide) fun e he => (hfix e he).2.2.2.2.symm).trans (h.slot (by simp [SearchPublic.headers]))
  · exact (hkeep 1 (by decide) fun e he => (hfix e he).1.symm).trans (h.slot (by simp [SearchPublic.headers]))
  · exact (hkeep 2 (by decide) fun e he => (hfix e he).2.1.symm).trans (h.slot (by simp [SearchPublic.headers]))

/-! ## Accepting a prime -/

theorem add_ofNat_ofNat (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

def acceptValues (used cu : Nat) : List (Nat × BitVec 64) :=
  (16, BitVec.ofNat 64 used + BitVec.ofNat 64 cu) :: terminalValues 1

theorem search_accept {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    {used remaining c : Nat} {rest : List Byte}
    (h : SearchIter p original final used remaining s) (hc : CandPost p (searchP original) (searchRand original) used s)
    (hr : remaining ≠ 0)
    (hres : Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used) =
      some (.prime c, rest))
    (h10 : s.gpr .x10 = BitVec.ofNat 64 (candUsed p original used)) :
    WP isa (.block accept) s (SearchDone p original final) := by
  obtain ⟨h, tr, hfinal⟩ := h
  have hs := h.frame_st
  have hs0 : InRegions s.wr p.F 8 := by simpa only [BitVec.add_zero] using hs 0 (by decide)
  have h16 := h.slot (j := 16) (v := BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h16
  have hacc : WP isa (.block accept) s fun t =>
      t.mem = writeFrame s.mem p.F (acceptValues used (candUsed p original used)) ∧
        Keep [.x10, .x11] s t := by
    refine WP.keep [.x10, .x11] ?_ (by decide) (by decide) (by decide +kernel)
    unfold accept terminal writeFrame acceptValues terminalValues
    simp only [List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, h.x19, h10, h16, h.frame_ld' 128 (by decide), imm64 (show 0 < 65536 by decide),
      imm64 (show 1 < 65536 by decide), hs0, hs 0 (by decide), hs 24 (by decide), hs 128 (by decide),
      hs 136 (by decide)]
    rfl
  refine WP.mono hacc fun t ⟨ht, kt⟩ => ?_
  have hu : candUsed p original used = ((searchRand original).drop used).length - rest.length := by
    simp only [candUsed, hres, List.length_drop, h.rand_length]
  unfold tailOf at hfinal
  rw [VG.Proof.RsaKeyGen.Search.search_prime hr hres, Spec.Entropy.Result.consume] at hfinal
  subst hfinal
  refine h.done_after _ (by
      simp only [acceptValues, terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) (by
      simp only [acceptValues, terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) ht kt (by decide) rfl rfl ?_ rfl ?_
  · simp only [frameValue, acceptValues, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ↓reduceIte]
    rw [add_ofNat_ofNat, hu]
  · have ho := hc.2.1
    rw [hres] at ho
    exact ho

/-! ## Asking for more entropy -/

theorem ofNat_toNat_lt {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem SearchLive.cap_le {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) : p.randLen ≤ primeEntropy p.len := by
  rw [← h.input.2]; exact h.input.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The next tape's length, with the octets left in `x10` and the budget in
`x11`. -/
theorem request_value {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (h10 : s.gpr .x10 = BitVec.ofNat 64 (p.randLen - used))
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (primeEntropy p.len)) :
    WP isa (.block (request.take 7)) s fun t =>
      (t.gpr .x10 = BitVec.ofNat 64 (primeRequest p.len (p.randLen - used)) ∧ t.mem = s.mem) ∧
        Keep [.x10, .x11, .x12, .x13] s t := by
  have hf := h.callFacts
  have hL : p.len ≤ 512 := hf.len.2.1
  have hcap := h.cap_le
  have hE : primeEntropy p.len < 2 ^ 63 := by unfold primeEntropy; omega
  have hv1 := h.slot (j := 1) (v := BitVec.ofNat 64 p.len) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv1
  have e16 : BitVec.ofNat 64 p.len <<< 4 = BitVec.ofNat 64 (16 * p.len) := by
    rw [SearchInit.shl_ofNat _ _ (by omega)]; congr 1; omega
  refine WP.keep [.x10, .x11, .x12, .x13] ?_ (by decide) (by decide) (by decide +kernel)
  unfold request
  simp only [List.take_succ_cons, List.take_zero]
  brun [ldf, h.x19, hv1, h.frame_ld' 8 (by decide), h10, h11, e16,
    subs_ge (show p.randLen - used < 2 ^ 64 by omega) (show 16 * p.len < 2 ^ 64 by omega)]
  unfold primeRequest Entropy.request
  have hA : p.randLen - used ≤ primeEntropy p.len := by omega
  generalize p.randLen - used = A at *
  generalize primeEntropy p.len = E at *
  by_cases h1 : 16 * p.len ≤ A
  · simp only [h1, decide_true, ite_true, ← BitVec.ofNat_add,
      subs_ge (show A + A < 2 ^ 64 by omega) (show E < 2 ^ 64 by omega)]
    by_cases h2 : E ≤ A + A
    · simp only [h2, decide_true, ite_true]
      congr 1; omega
    · simp only [h2, decide_false, Bool.false_eq_true, ite_false]
      congr 1; omega
  · simp only [h1, decide_false, Bool.false_eq_true, ite_false, ← BitVec.ofNat_add,
      subs_ge (show 16 * p.len + 16 * p.len < 2 ^ 64 by omega) (show E < 2 ^ 64 by omega)]
    by_cases h2 : E ≤ 16 * p.len + 16 * p.len
    · simp only [h2, decide_true, ite_true]
      congr 1; omega
    · simp only [h2, decide_false, Bool.false_eq_true, ite_false]
      congr 1; omega

def requestValues (p : SearchPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(3, BitVec.ofNat 64 (primeRequest p.len (p.randLen - used))), (17, 0)]

/-- `request`, with the octets left in `x10` and the budget in `x11`. -/
theorem request_ok {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (h10 : s.gpr .x10 = BitVec.ofNat 64 (p.randLen - used))
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (primeEntropy p.len)) :
    WP isa (.block request) s fun t =>
      t.mem = writeFrame s.mem p.F (requestValues p used) ∧
        Keep [.x10, .x11, .x12, .x13] s t := by
  rw [show request = request.take 7 ++ request.drop 7 from (List.take_append_drop _ _).symm,
    WP.block_append_iff]
  refine WP.mono (request_value h h10 h11) fun v ⟨⟨hv10, hmv⟩, kv⟩ => ?_
  have hv := h.keep kv hmv
  have hs := hv.frame_st
  refine WP.mono (WP.keep [.x12] (Q := fun t =>
    t.mem = writeFrame v.mem p.F (requestValues p used)) ?_
      (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, kt⟩ => ⟨by rw [hm, hmv], (kv.trans kt).mono⟩
  unfold request writeFrame requestValues
  simp only [List.drop_succ_cons, List.drop_zero, List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, hv.x19, hv10, imm64 (show 0 < 65536 by decide), hs 24 (by decide), hs 136 (by decide)]
  rfl

/-- The short tape's guard: whether the octets left reach the budget. -/
theorem short_guard {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (.block [ldf .x10 13, ldf .x11 2, .subs .x .x12 .x10 .x11, movi .x13 0, movi .x14 1,
        .csel .x .x12 .x14 .x13]) s fun t =>
      ((t.gpr .x10 = BitVec.ofNat 64 (p.randLen - used) ∧ t.gpr .x11 = BitVec.ofNat 64 (primeEntropy p.len) ∧
        t.mem = s.mem) ∧ Keep [.x10, .x11, .x12, .x13, .x14] s t) ∧
        isa.eval (.zero .x .x12) t = some (decide (p.randLen - used < primeEntropy p.len)) := by
  have hf := h.callFacts
  have hL : p.len ≤ 512 := hf.len.2.1
  have hv2 := h.slot (j := 2) (v := BitVec.ofNat 64 (primeEntropy p.len)) (by simp [SearchPublic.headers])
  have hv13 := h.slot (j := 13) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2 hv13
  have hr := hf.rand64
  have hE : primeEntropy p.len < 2 ^ 64 := by unfold primeEntropy; omega
  refine WP.mono (WP.keep [.x10, .x11, .x12, .x13, .x14] (Q := fun t =>
    (t.gpr .x10 = BitVec.ofNat 64 (p.randLen - used) ∧ t.gpr .x11 = BitVec.ofNat 64 (primeEntropy p.len) ∧
      t.mem = s.mem) ∧
    isa.eval (.zero .x .x12) t = some (decide (p.randLen - used < primeEntropy p.len))) ?_
    (by decide) (by decide) (by decide +kernel)) fun _ ⟨⟨hv, he⟩, k⟩ => ⟨⟨hv, k⟩, he⟩
  brun [ldf, h.x19, hv2, hv13, h.frame_ld' 16 (by decide), h.frame_ld' 104 (by decide),
    imm64 (show 0 < 65536 by decide), imm64 (show 1 < 65536 by decide),
    subs_ge (show p.randLen - used < 2 ^ 64 by omega) hE]
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq]
  by_cases hb : primeEntropy p.len ≤ p.randLen - used
  · simp only [hb, decide_true, ite_true, show ¬p.randLen - used < primeEntropy p.len by omega,
      decide_false]
    decide
  · simp only [hb, decide_false, ite_false, show p.randLen - used < primeEntropy p.len by omega,
      decide_true, Bool.false_eq_true]
    decide

theorem search_short {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    {used remaining : Nat}
    (h : SearchIter p original final used remaining s) (hc : CandPost p (searchP original) (searchRand original) used s)
    (hr : remaining ≠ 0)
    (hres : Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used) = none) :
    WP isa short s (SearchDone p original final) := by
  obtain ⟨h, tr, hfinal⟩ := h
  unfold tailOf at hfinal
  rw [VG.Proof.RsaKeyGen.Search.search_short hr hres, List.length_drop, h.rand_length] at hfinal
  unfold short
  refine WP.seq (WP.mono (short_guard h) fun u ⟨⟨⟨h10, h11, hmu⟩, ku⟩, he⟩ => ?_)
  have hu := h.keep ku hmu
  refine WP.ite _ he (fun hb => ?_) (fun hb => ?_)
  · have hb := of_decide_eq_true hb
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at hfinal
    subst hfinal
    refine WP.mono (request_ok hu h10 h11) fun t ⟨ht, kt⟩ => ?_
    refine hu.done_after _ (by
        simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl) <;> dsimp only <;> decide) (by
        simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl) <;> dsimp only <;> decide) ht kt (by decide) ?_ rfl ?_ rfl ?_
    · simp only [frameValue, requestValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ↓reduceIte]
      rw [hu.slot (j := 0) (v := BitVec.ofNat 64 remaining) (by simp [SearchPublic.headers])]
      rfl
    · simp only [frameValue, requestValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ↓reduceIte]
      rw [hu.slot (j := 16) (v := BitVec.ofNat 64 used) (by simp [SearchPublic.headers])]
      rfl
    · have ho := hc.2.1
      rw [hres] at ho
      rw [hmu]
      exact ho
  · have hb := of_decide_eq_false hb
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))] at hfinal
    exact search_exhausted hu (by rw [hfinal]; rfl)

/-! ## Going on past a candidate -/

/-- The words but the offset's and the count's do not depend on them. -/
theorem SearchPublic.headers_fixed {p : SearchPublic} {used k used' k' : Nat} {e : Nat × BitVec 64}
    (he : e ∈ p.headers used k) (h0 : e.1 ≠ 0) (h12 : e.1 ≠ 12) (h13 : e.1 ≠ 13) (h16 : e.1 ≠ 16) :
    e ∈ p.headers used' k' := by
  simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he ⊢
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | (exact absurd rfl ‹_›) | simp

/-- A loop state at a later offset, through the stores of its words. -/
theorem SearchLive.moved {p : SearchPublic} {original s t : State} {used remaining used' remaining' : Nat}
    (h : SearchLive p original used remaining s) (hu : used' ≤ p.randLen) (hk : remaining' ≤ p.remaining)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 20) (h4 : ∀ e ∈ values, 4 ≠ e.1)
    (hm : t.mem = writeFrame s.mem p.F values) {rs : List Reg} (kt : Keep rs s t)
    (hrs : ∀ r ∈ preserved, r ∉ rs)
    (hother : ∀ e ∈ values, e.1 = 0 ∨ e.1 = 12 ∨ e.1 = 13 ∨ e.1 = 16 ∨ e.1 = 17)
    (hnew : ∀ e ∈ p.headers used' remaining', e.1 = 0 ∨ e.1 = 12 ∨ e.1 = 13 ∨ e.1 = 16 →
      frameValue values e.1 (word s.mem p.F (8 * e.1)) = e.2) :
    SearchLive p original used' remaining' t := by
  refine h.update hu hk values hb h4 hm kt hrs ?_
  intro e he
  rw [hm, writeFrame_word _ _ _ hb e.1 (SearchPublic.headers_bound _ _ _ e he)]
  by_cases hc : e.1 = 0 ∨ e.1 = 12 ∨ e.1 = 13 ∨ e.1 = 16
  · exact hnew e he hc
  · simp only [not_or] at hc
    obtain ⟨c0, c12, c13, c16⟩ := hc
    have h17 := (SearchPublic.headers_not_3_17 _ _ _ e he).2
    rw [frameValue_unchanged _ _ _ (fun x hx => by
      rcases hother x hx with h | h | h | h | h <;> rw [h] <;> with_reducible assumption)]
    exact h.headers e (SearchPublic.headers_fixed he c0 c12 c13 c16)

theorem ofNat_sub_ofNat {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ofNat_toNat_lt (a := b) (by omega), ofNat_toNat_lt ha]; exact h),
    ofNat_toNat_lt (a := a) ha, ofNat_toNat_lt (a := b) (by omega), ofNat_toNat_lt (a := a - b) (by omega)]

theorem ofNat_beq_zero {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  · rintro rfl; rfl

def advanceValues (p : SearchPublic) (used u : Nat) : List (Nat × BitVec 64) :=
  [(12, p.rp + BitVec.ofNat 64 used + BitVec.ofNat 64 u),
    (13, BitVec.ofNat 64 (p.randLen - used) - BitVec.ofNat 64 u),
    (16, BitVec.ofNat 64 used + BitVec.ofNat 64 u), (17, BitVec.ofNat 64 4)]

/-- `advance` past `u` octets (`x10`), and whether the status (`x9`) was 2. -/
theorem advance_ok {p : SearchPublic} {original s : State} {used remaining u : Nat}
    (h : SearchLive p original used remaining s) (h10 : s.gpr .x10 = BitVec.ofNat 64 u) :
    WP isa (.block advance) s fun t =>
      (t.mem = writeFrame s.mem p.F (advanceValues p used u) ∧
        isa.eval (.zero .x .x13) t = some (s.gpr .x9 - BitVec.ofNat 64 2 == 0)) ∧
        Keep [.x11, .x12, .x13, .x14] s t := by
  have hs := h.frame_st
  have h12 := h.slot (j := 12) (v := p.rp + BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  have h13 := h.slot (j := 13) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SearchPublic.headers])
  have h16 := h.slot (j := 16) (v := BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h12 h13 h16
  refine WP.keep [.x11, .x12, .x13, .x14] ?_ (by decide) (by decide) (by decide +kernel)
  unfold advance writeFrame advanceValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.x19, h10, h.frame_ld' 96 (by decide), h.frame_ld' 104 (by decide),
    h.frame_ld' 128 (by decide), h12, h13, h16, imm64 (show 4 < 65536 by decide),
    hs 96 (by decide), hs 104 (by decide), hs 128 (by decide), hs 136 (by decide)]
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq]

theorem count_ok {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (.block count) s fun t =>
      t.mem = writeFrame s.mem p.F [(0, BitVec.ofNat 64 remaining - BitVec.ofNat 64 1)] ∧
        Keep [.x11] s t := by
  have hs := h.frame_st
  have hs0 : InRegions s.wr p.F 8 := by simpa only [BitVec.add_zero] using hs 0 (by decide)
  have hl0 : InRegions (s.rd ++ s.wr) p.F 8 := by simpa only [BitVec.add_zero] using h.frame_ld' 0 (by decide)
  have h0 := h.slot (j := 0) (v := BitVec.ofNat 64 remaining) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul, BitVec.add_zero] at h0
  refine WP.keep [.x11] ?_ (by decide) (by decide) (by decide +kernel)
  unfold count writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.x19, Nat.mul_zero, BitVec.add_zero, hl0, h0, hs0]

theorem SearchDone.status_ne {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    (h : SearchDone p original final s) : word s.mem p.F (8 * 17) ≠ 4 := by
  rw [h.status]
  intro he
  have := congrArg BitVec.toNat he
  rw [ofNat_toNat_lt (by
    unfold Spec.Entropy.Result.status Spec.Entropy.Outcome.status; split <;> decide)] at this
  revert this
  unfold Spec.Entropy.Result.status Spec.Entropy.Outcome.status
  split <;> decide

/-- A candidate rejected, too close or otherwise, at `used`: the search from
there is the search from after it. -/
theorem tail_past {p : SearchPublic} {original : State} {used remaining u : Nat} {x : Spec.RsaKeyGen.Candidate}
    {rest : List Byte} (hr : remaining ≠ 0)
    (hres : Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used) =
      some (x, rest))
    (hx : x = .close ∨ x = .rejected) (hu : u = ((searchRand original).drop used).length - rest.length)
    (hu0 : u ≠ 0) :
    tailOf p original used remaining =
      (tailOf p original (used + u) (if x = .close then remaining else remaining - 1)).consume u
        (Search.entry p.len p.eB (searchP original) ((searchRand original).drop used)) := by
  obtain ⟨n, hn, -, hrest⟩ := Search.candidateOp_suffix hres
  have hun : u = n := by
    rw [hu, hrest]; simp only [List.length_drop] at hn ⊢; omega
  have hl : rest.length < ((searchRand original).drop used).length := by
    rw [hrest]; simp only [List.length_drop] at hn ⊢; omega
  have hu' : ((searchRand original).drop used).length - rest.length = u := hu.symm
  have hd : rest = (searchRand original).drop (used + u) := by rw [hrest, List.drop_drop, hun]
  unfold tailOf
  rcases hx with rfl | rfl
  · rw [VG.Proof.RsaKeyGen.Search.search_close hr hres, ite_eq_left_of_eq_true _ _ (eq_true hl), hu', hd]
    simp only [↓reduceIte]
  · rw [VG.Proof.RsaKeyGen.Search.search_rejected hr hres, ite_eq_left_of_eq_true _ _ (eq_true hl), hu', hd]
    simp only [reduceCtorEq, ↓reduceIte]

theorem search_reject {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    {used remaining : Nat} {x : Spec.RsaKeyGen.Candidate} {rest : List Byte}
    (h : SearchIter p original final used remaining s) (hr : remaining ≠ 0)
    (hres : Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used) =
      some (x, rest))
    (hx : x = .close ∨ x = .rejected)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 (if x = .close then 2 else 3))
    (h10 : s.gpr .x10 = BitVec.ofNat 64 (candUsed p original used)) :
    WP isa reject s (IterPost p original final used remaining) := by
  obtain ⟨h, tr, hfinal⟩ := h
  have hf := h.callFacts
  have hlen := h.rand_length
  have hcu : candUsed p original used = ((searchRand original).drop used).length - rest.length := by
    simp only [candUsed, hres, List.length_drop, hlen]
  have hcu64 : candUsed p original used < 2 ^ 64 := by
    have : candUsed p original used ≤ p.randLen := by unfold candUsed; split <;> omega
    have := hf.rand64; omega
  unfold reject
  refine WP.ite _ (by rw [eval_zero, h10, ofNat_beq_zero hcu64]) (fun hz => ?_) (fun hz => ?_)
  · -- Nothing consumed: the specification's progress check gives up.
    have hz := of_decide_eq_true hz
    obtain ⟨n, hn, hL, hrest⟩ := Search.candidateOp_suffix hres
    have hlt : ¬rest.length < ((searchRand original).drop used).length := by omega
    have htail : tailOf p original used remaining = ⟨.exhausted, 0,
        Search.entry p.len p.eB (searchP original) ((searchRand original).drop used)⟩ := by
      unfold tailOf
      rcases hx with rfl | rfl
      · rw [VG.Proof.RsaKeyGen.Search.search_close hr hres, ite_eq_right_of_eq_false _ _ (eq_false hlt)]
      · rw [VG.Proof.RsaKeyGen.Search.search_rejected hr hres, ite_eq_right_of_eq_false _ _ (eq_false hlt)]
    rw [htail] at hfinal
    refine WP.mono (search_exhausted h (result := final) (by rw [hfinal]; rfl)) fun t' hd => ?_
    exact .inr ⟨hd.status_ne, fun ⟨_, _, h⟩ => h hz, hd⟩
  · have hz := of_decide_eq_false hz
    have hu0 : candUsed p original used ≠ 0 := hz
    have hpast := tail_past (u := candUsed p original used) hr hres hx hcu hu0
    rw [hpast, VG.Proof.RsaKeyGen.Search.consume_consume] at hfinal
    have hule : candUsed p original used ≤ p.randLen - used := by
      rw [hcu, List.length_drop, hlen]; omega
    refine WP.seq (WP.mono (advance_ok h h10) fun v ⟨⟨hmv, hev⟩, kv⟩ => ?_)
    rw [h9] at hev
    have hbound : ∀ e ∈ advanceValues p used (candUsed p original used), e.1 < 20 ∧ 4 ≠ e.1 ∧
          (e.1 = 0 ∨ e.1 = 12 ∨ e.1 = 13 ∨ e.1 = 16 ∨ e.1 = 17) := by
      simp only [advanceValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide
    have h12 : p.rp + BitVec.ofNat 64 used + BitVec.ofNat 64 (candUsed p original used) =
        p.rp + BitVec.ofNat 64 (used + candUsed p original used) := by
      rw [BitVec.add_assoc, add_ofNat_ofNat]
    have h13 : BitVec.ofNat 64 (p.randLen - used) - BitVec.ofNat 64 (candUsed p original used) =
        BitVec.ofNat 64 (p.randLen - (used + candUsed p original used)) := by
      rw [ofNat_sub_ofNat hule (by have := hf.rand64; omega)]; congr 1; omega
    have h16 : BitVec.ofNat 64 used + BitVec.ofNat 64 (candUsed p original used) =
        BitVec.ofNat 64 (used + candUsed p original used) := add_ofNat_ofNat _ _
    have hu' : used + candUsed p original used ≤ p.randLen := by omega
    have h17 : word v.mem p.F (8 * 17) = 4 := by
      rw [hmv, writeFrame_word _ _ _ (fun e he => (hbound e he).1) 17 (by decide)]; rfl
    -- The loop state past the candidate, with as many counted candidates.
    have hvl : SearchLive p original (used + candUsed p original used) remaining v := by
      refine h.moved hu' h.remaining_le _ (fun e he => (hbound e he).1) (fun e he => (hbound e he).2.1)
        hmv kv (by decide) (fun e he => (hbound e he).2.2) ?_
      intro e he hc'
      simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> simp only [Nat.reduceEqDiff, false_or, or_false, or_self] at hc' <;>
        simp only [frameValue, advanceValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ↓reduceIte,
          h12, h13, h16]
      exact h.slot (by simp [SearchPublic.headers])
    refine WP.ite _ hev (fun hb => ?_) (fun hb => ?_)
    · -- Too close: not counted.
      have hxc : x = .close := by
        rcases hx with rfl | rfl
        · rfl
        · simp only [reduceCtorEq, ↓reduceIte] at hb; cases hb
      subst hxc
      simp only [↓reduceIte] at hfinal
      exact WP.block_nil (.inl ⟨h17, hr, _, remaining, by omega, ⟨hvl, _, hfinal⟩, rfl,
        .inl ⟨rfl, by simp only [candStatus, hres]; rfl⟩,
        by rw [hpast, Nat.add_sub_cancel_left]; simp only [↓reduceIte]⟩)
    · -- Rejected: one fewer counted candidate.
      have hxr : x = .rejected := by
        rcases hx with rfl | rfl
        · simp only [↓reduceIte] at hb; cases hb
        · rfl
      subst hxr
      simp only [reduceCtorEq, ↓reduceIte] at hfinal
      refine WP.mono (count_ok hvl) fun w ⟨hmw, kw⟩ => ?_
      have hb0 : ∀ e ∈ [(0, BitVec.ofNat 64 remaining - BitVec.ofNat 64 1)], e.1 < 20 ∧ 4 ≠ e.1 ∧
          (e.1 = 0 ∨ e.1 = 12 ∨ e.1 = 13 ∨ e.1 = 16 ∨ e.1 = 17) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro _ rfl; dsimp only; decide
      have hrem : remaining < 2 ^ 64 :=
        Nat.lt_of_le_of_lt h.remaining_le (by rw [← h.input.2]; exact BitVec.isLt _)
      have hwl : SearchLive p original (used + candUsed p original used) (remaining - 1) w := by
        refine hvl.moved hu' (by have := h.remaining_le; omega) _ (fun e he => (hb0 e he).1)
          (fun e he => (hb0 e he).2.1) hmw kw (by decide) (fun e he => (hb0 e he).2.2) ?_
        intro e he hc'
        simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl <;> simp only [Nat.reduceEqDiff, false_or, or_false, or_self] at hc' <;>
          simp only [frameValue, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ↓reduceIte]
        · exact ofNat_sub_ofNat (by omega) hrem
        all_goals exact hvl.slot (by simp [SearchPublic.headers])
      have h17w : word w.mem p.F (8 * 17) = 4 := by
        rw [hmw, writeFrame_word _ _ _ (fun e he => (hb0 e he).1) 17 (by decide)]; exact h17
      exact .inl ⟨h17w, hr, _, remaining - 1, by omega, ⟨hwl, _, hfinal⟩, rfl,
        .inr ⟨rfl, by simp only [candStatus, hres]; rfl⟩,
        by rw [hpast, Nat.add_sub_cancel_left]; simp only [reduceCtorEq, ↓reduceIte]⟩

/-! ## The classification -/

theorem search_classify {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    {used remaining : Nat} (h : SearchIter p original final used remaining s)
    (hc : CandPost p (searchP original) (searchRand original) used s) (hr : remaining ≠ 0) :
    WP isa classify s (IterPost p original final used remaining) := by
  unfold classify
  refine WP.seq (WP.mono (search_head h.1 hc) fun u ⟨hu, hcu, h9, h10, he⟩ => ?_)
  have hu' : SearchIter p original final used remaining u := ⟨hu, h.2⟩
  cases hres : Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used) with
  | none =>
    simp only [candStatus, hres, Spec.RsaKeyGen.candidateStatus] at he h9
    refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
    refine WP.ite true (by rw [eval_zero, h9]; rfl) (fun _ => ?_) (fun hf => by cases hf)
    refine WP.mono (search_short hu' hcu hr hres) fun t hd => .inr ⟨hd.status_ne, fun ⟨_, hs, _⟩ => ?_, hd⟩
    simp [candStatus, hres, Spec.RsaKeyGen.candidateStatus] at hs
  | some pr =>
    obtain ⟨x, rest⟩ := pr
    cases x with
    | prime c =>
      simp only [candStatus, hres, Spec.RsaKeyGen.candidateStatus] at he h9
      refine WP.ite true he (fun _ => ?_) (fun hf => by cases hf)
      exact WP.mono (search_accept hu' hcu hr hres h10) fun t hd =>
        .inr ⟨hd.status_ne, fun ⟨_, hs, _⟩ => by simp [candStatus, hres, Spec.RsaKeyGen.candidateStatus] at hs, hd⟩
    | close =>
      simp only [candStatus, hres, Spec.RsaKeyGen.candidateStatus] at he h9
      refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
      refine WP.ite false (by rw [eval_zero, h9]; rfl) (fun hf => by cases hf) fun _ => ?_
      exact search_reject hu' hr hres (.inl rfl) (by rw [h9]; rfl) h10
    | rejected =>
      simp only [candStatus, hres, Spec.RsaKeyGen.candidateStatus] at he h9
      refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
      refine WP.ite false (by rw [eval_zero, h9]; rfl) (fun hf => by cases hf) fun _ => ?_
      exact search_reject hu' hr hres (.inr rfl) (by rw [h9]; rfl) h10

/-! ## An iteration -/

/-- What an iteration leaves, with the loop's condition. -/
def LoopStep (p : SearchPublic) (original : State) (final : PrimeSearchResult) (used remaining : Nat)
    (t : State) : Prop :=
  (isa.eval (.zero .x .x9) t = some true ∧ ContinuePost p original final used remaining t) ∨
    (isa.eval (.zero .x .x9) t = some false ∧ ¬Continues p original used remaining ∧ SearchDone p original final t)

theorem iter_guard {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (.block [ldf .x9 0]) s fun t =>
      (isa.eval (.zero .x .x9) t = some (decide (remaining = 0)) ∧ t.mem = s.mem) ∧ Keep [.x9] s t := by
  have hl0 : InRegions (s.rd ++ s.wr) p.F 8 := by simpa only [BitVec.add_zero] using h.frame_ld' 0 (by decide)
  have h0 := h.slot (j := 0) (v := BitVec.ofNat 64 remaining) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul, BitVec.add_zero] at h0
  have hz : (BitVec.ofNat 64 remaining == 0) = decide (remaining = 0) :=
    ofNat_beq_zero (Nat.lt_of_le_of_lt h.remaining_le (by rw [← h.input.2]; exact BitVec.isLt _))
  refine WP.keep [.x9] ?_ (by decide) (by decide) (by decide +kernel)
  brun [ldf, h.x19, Nat.mul_zero, BitVec.add_zero, hl0, h0]
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq, hz]

theorem sub4_beq (x : BitVec 64) : (x - BitVec.ofNat 64 4 == 0) = (x == 4) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h
    have := congrArg (· + BitVec.ofNat 64 4) h
    simp only [BitVec.sub_add_cancel] at this
    exact this
  · rintro rfl; rfl

theorem iter_test {p : SearchPublic} {original s : State} {final : PrimeSearchResult} {used : Nat}
    {remaining : Nat} (h : IterPost p original final used remaining s) :
    WP isa (.block [ldf .x9 17, .subImm .x .x9 .x9 4]) s (LoopStep p original final used remaining) := by
  have hregs : s.gpr .x19 = p.F ∧ ∃ o : State, SearchInput p o ∧ s.wr = p.frame :: o.wr := by
    rcases h with ⟨-, -, _, _, -, ⟨hi, -⟩, -⟩ | ⟨-, -, hd⟩
    · exact ⟨hi.x19, _, hi.input, hi.wr⟩
    · exact ⟨hd.x19, _, hd.input, hd.wr⟩
  obtain ⟨hr19, o, hi, hw⟩ := hregs
  have scr := hi.frame_scr hw
  have hl : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 136) 8 :=
    let ⟨r, hr, hc⟩ := scr.st (d := 136) (by decide); ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep [.x9] (Q := fun t =>
    isa.eval (.zero .x .x9) t = some (word s.mem p.F (8 * 17) - BitVec.ofNat 64 4 == 0) ∧ t.mem = s.mem) (by
      brun [ldf, hr19, hl, Nat.reduceMul]
      simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨he, hm⟩, k⟩ => ?_
  rw [sub4_beq] at he
  rcases h with ⟨h17, hc⟩ | ⟨h17, hn, hd⟩
  · exact .inl ⟨by rw [he, h17]; rfl, hc.keep k hm⟩
  · exact .inr ⟨by rw [he]; simp only [beq_eq_false_iff_ne.mpr h17], hn, hd.keep k hm⟩

theorem search_iteration (c : Cand) {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    {used remaining : Nat} (h : SearchIter p original final used remaining s) :
    WP isa (iteration c.call) s (LoopStep p original final used remaining) := by
  unfold iteration
  refine WP.seq (WP.mono (iter_guard h.1) fun u ⟨⟨he, hmu⟩, ku⟩ => ?_)
  have hu : SearchIter p original final used remaining u := ⟨h.1.keep ku hmu, h.2⟩
  refine WP.seq (WP.ite _ he (fun hz => ?_) (fun hz => ?_))
  · have hz := of_decide_eq_true hz
    subst hz
    obtain ⟨hl, tr, hfinal⟩ := hu
    unfold tailOf at hfinal
    rw [VG.Proof.RsaKeyGen.Search.search_zero] at hfinal
    exact WP.mono (search_exhausted hl (result := final) (by rw [hfinal]; rfl)) fun t hd =>
      iter_test (.inr ⟨hd.status_ne, fun ⟨h, _⟩ => h rfl, hd⟩)
  · have hz := of_decide_eq_false hz
    refine WP.seq (WP.mono (search_candidate_run c hu.1) fun t ⟨ht, hc⟩ => ?_)
    exact WP.mono (search_classify ⟨ht, hu.2⟩ hc hz) fun _ hp => iter_test hp

theorem search_loop (c : Cand) {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    {used remaining : Nat} (h : SearchIter p original final used remaining s) :
    WP isa (.loop (iteration c.call) (.zero .x .x9)) s (SearchDone p original final) := by
  refine WP.loop (M := isa)
    (fun n t => ∃ u k, n = p.randLen - u + 1 ∧ SearchIter p original final u k t) ?_
    (p.randLen - used + 1) s ⟨used, remaining, rfl, h⟩
  rintro n t ⟨u, k, rfl, ht⟩
  refine WP.mono (search_iteration c ht) fun t' hs => ?_
  rcases hs with ⟨he, -, u', k', hlt, ht', -⟩ | ⟨he, -, hd⟩
  · have hle := ht'.1.used_le
    exact .inr ⟨he, _, by omega, u', k', rfl, ht'⟩
  · exact .inl ⟨he, hd⟩

/-! ## The loop in its frame -/

theorem consume_zero (r : PrimeSearchResult) : r.consume 0 [] = r := by
  cases r; simp [Spec.Entropy.Result.consume]

theorem search_initial {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hl : SearchLive p s 0 p.remaining t) : SearchIter p s (searchResult s) 0 p.remaining t := by
  refine ⟨hl, [], ?_⟩
  rw [consume_zero]
  rw [← h.2]
  simp only [searchResult, tailOf, searchOfState, List.drop_zero]

theorem depth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

theorem iteration_depth (c : Cand) : (iteration c.call).aarch64Depth = 2 := by
  simp only [iteration, candidateRun, exhausted, zeroOut, classify, short, reject,
    Impl.Bignum.AArch64.countLoop, Code.aarch64Depth, Cand.call, depth_of_noFrames c.noFrames,
    Instr.frameUnits]
  rfl

/-- After the frame saving `x30`: a finished search, with `x30` and the stack
pointer back. -/
theorem SearchDone.popped {p : SearchPublic} {original s : State} {r : PrimeSearchResult}
    (h : SearchDone p original r s) (v sp : BitVec 64) :
    SearchDone p original r { s.write .x .x30 v with sp := sp } := by
  refine ⟨h.input, h.rd, h.wr, ?_, fun reg hr h19 h30 => ?_, h.vcs, h.savedX19, h.usedPtr, h.stp,
    h.len, h.cap, h.remaining, h.request, h.used, h.status, h.output⟩
  · show (s.write .x .x30 v).gpr .x19 = _
    rw [RegUpd.gpr_write]; exact h.x19
  · show (s.write .x .x30 v).gpr reg = _
    rw [RegUpd.gpr_write, ite_eq_right h30]; exact h.saved reg hr h19 h30

theorem search_body (c : Cand) {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hx : t.gpr .x19 = p.F) (hm : t.mem = writeFrame s.mem p.F (entryValues s))
    (k : Keep entryRegs (allocated 160 s) t) :
    WP isa (search c.call) t fun u =>
      SearchDone p s (searchResult s) u ∧ u.gpr .x30 = s.gpr .x30 ∧ u.sp = p.F := by
  have hl := search_start h hx hm k
  have htsp : t.sp = p.F := k.sp.trans (alloc_sp h)
  have hroom : 208 ≤ p.sp.toNat := h.room
  have hF := h.F_toNat
  have hsp : 16 ≤ t.sp.toNat := by
    rw [htsp, hF]; exact Nat.le_sub_of_add_le (Nat.le_trans (by decide) hroom)
  unfold search
  refine WP.frameReg hsp ?_ ?_ ?_
  · intro R hR
    rw [k.wr, alloc_wr h] at hR
    rw [htsp]
    rcases List.mem_cons.mp hR with rfl | hR
    · rw [F_16]
      have hs := Offset.sep_below p.sp 208 (a := 176) (n := 16) (b := 160) (k := 160) (by decide) (by decide)
        (Or.inl (by decide)) (by decide) (by decide)
      exact fun x hx hy => hs x (Nat.lt_of_succ_le (by simpa only [Region.Contains] using hx))
        (Nat.lt_of_succ_le (by simpa only [Region.Contains, SearchPublic.F] using hy))
    · rw [h.1.2.2.2.1] at hR
      have hd := h.stack_disjoint (r := R) (List.mem_append_left _ hR)
      refine hd.sub_left ?_
      rw [F_16, h.sp_eq]
      exact Offset.sub_below s.sp (a := 176) (b := 208) (by decide) (by decide)
  · refine WP.mono (search_loop c (search_initial h hl)) fun u hu => ?_
    refine ⟨hu.popped _ _, ?_, htsp⟩
    show (u.write .x .x30 (t.gpr .x30)).gpr .x30 = _
    rw [RegUpd.gpr_write, ite_eq_left rfl]
    exact k.gpr .x30 (by decide)
  · show 16 * (Code.loop (iteration c.call) (.zero .x .x9)).aarch64Depth + 16 < 2 ^ 64
    simp only [Code.aarch64Depth, iteration_depth c]
    decide

end VG.Proof.RsaKeyGen.AArch64.Search
