module

public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Call
import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ZeroOut
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SearchInit
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets

/-! # The search's loop

After a candidate, the search accepts its prime, asks for more entropy,
gives up, or goes on past it to the next (`search_classify`); with no
counted candidates left it gives up without one (`search_exhausted`). The
loop runs these steps to its end (`search_loop`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Search

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)
open VG.Impl.RsaKeyGen.X86_64.Search
open VG.Spec.RsaKeyGen (primeSearch primeEntropy PrimeSearchResult)

/-- A finished search, before `finish` stores its results. -/
structure SearchDone (p : SearchPublic) (original : State) (result : PrimeSearchResult) (s : State) :
    Prop where
  input : SearchInput p original
  rd : s.rd = original.rd
  wr : s.wr = p.frame :: original.wr
  rsp : s.gpr .rsp = p.F
  r12 : s.gpr .r12 = p.F
  saved : ∀ r ∈ calleeSaved, r ≠ .r12 → r ≠ .rsp → s.gpr r = original.gpr r
  savedR12 : word s.mem p.F 32 = original.gpr .r12
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
  ⟨h.input, h.rd, h.wr, h.rsp, h.r12, h.saved, h.savedR12,
    h.slot (by simp [SearchPublic.headers]), h.slot (by simp [SearchPublic.headers]),
    h.slot (by simp [SearchPublic.headers]), h.slot (by simp [SearchPublic.headers]),
    h0, h3, h16, h17, hout⟩

/-! ## The frame's stores -/

/-- The frame's words but `values`, through stores of them. -/
theorem stores_words (m : Mem) (B : Addr) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 20) {j : Nat} (hj : j < 20) (hnot : ∀ e ∈ values, j ≠ e.1) :
    word (writeFrame m B values) B (8 * j) = word m B (8 * j) := by
  rw [writeFrame_word _ _ _ hb j hj, frameValue_unchanged _ _ _ hnot]

/-- `terminal k`: no counted candidates, no request, and the status `k`. -/
theorem search_terminal {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (k : Nat) :
    WP isa (.block (terminal k)) s fun t =>
      t.mem = writeFrame s.mem p.F [(0, 0), (3, 0), (17, (BitVec.ofNat 32 k).setWidth 64)] ∧
        Keep [.rax] s t := by
  have scr := h.input.frame_scr h.wr
  have hs : ∀ d, d + 8 ≤ 160 → InRegions s.wr (p.F + BitVec.ofNat 64 d) 8 := fun _ hd => scr.st hd
  have hs0 : InRegions s.wr p.F 8 := by simpa only [BitVec.add_zero] using hs 0 (by decide)
  refine WP.keep [.rax] ?_ rfl
  unfold terminal writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hs0, hs 24 (by decide), hs 136 (by decide)]
  rfl

/-! ## Giving up -/

open VG.Proof.Rsa.X86_64 (OutOk)

theorem SearchLive.out_region {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) : (⟨p.op, p.len⟩ : Region) = inOut original := by
  rw [← h.input.2]; rfl

theorem SearchLive.output {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) : OutOk s p.F 160 p.op p.len := by
  have hin : inOut original ∈ s.wr := by
    rw [h.wr, h.input.1.2.2.2.1]; exact List.mem_cons_of_mem _ (by simp [inWrites])
  have hn := h.input.nowrap (r := inOut original) (by simp [inWrites])
  have hd := h.input.frame_disjoint (r := inOut original) (by simp [SearchInput.callChanges])
  rw [← h.out_region] at hin hn hd
  simp only at hn
  refine ⟨fun i hi => ⟨_, hin, contains_byte _ hi (by omega)⟩, fun i hi => Nat.le_of_not_lt fun hlt =>
    hd _ (by simp only [ofs] at hlt; simp only [Region.Contains]; omega) (contains_byte _ hi (by omega))⟩

theorem search_clear {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (hdi : s.gpr .rdi = p.F) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroOut 5 6) s fun t =>
      SearchLive p original used remaining t ∧
      Spec.Rsa.bytesAt t.mem p.op p.len = List.replicate p.len 0 ∧
      (∀ j < 20, word t.mem p.F (8 * j) = word s.mem p.F (8 * j)) ∧
      Keep [.rsi, .rcx, .rax] s t := by
  have hf := h.callFacts
  have hl := hf.len
  have scr := h.input.frame_scr h.wr
  refine WP.mono (VG.Proof.Ffdh.X86_64.Generation.controller_zero_out (sPtr := 5) (sLen := 6) (op := p.op)
    (len := p.len) scr hdi (by decide) (by decide) (by decide)
    (h.slot (by simp [SearchPublic.headers])) (h.slot (by simp [SearchPublic.headers]))
    (by unfold Spec.RsaKeyGen.primeLenValid at hl; omega) (by unfold Spec.RsaKeyGen.primeLenValid at hl; omega)
    h.output) fun t ⟨hv, hfr, k⟩ => ?_
  have hframe : Frame (SearchInput.callChanges original) s.mem t.mem := by
    intro a ha
    apply hfr
    intro i hi he
    apply ha (inOut original) (by simp [SearchInput.callChanges])
    rw [he, ← h.out_region]
    exact contains_byte _ hi (by have := hf.nO; omega)
  refine ⟨h.restore k.2.1 k.2.2 (fun r hr => k.gpr (by cases r <;> simp_all [calleeSaved])) hframe,
    ?_, h.input.frame_words hframe, k⟩
  refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact hv i (List.mem_range.mp hi)

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

/-- Through the frame's stores but the saved r12, a loop state with no
counted candidates left. -/
theorem SearchLive.terminated {p : SearchPublic} {original s t : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (k : Nat)
    (hm : t.mem = writeFrame s.mem p.F [(0, 0), (3, 0), (17, (BitVec.ofNat 32 k).setWidth 64)])
    (kt : Keep [.rax] s t) : SearchLive p original used 0 t := by
  have hb : ∀ e ∈ [(0, (0 : BitVec 64)), (3, 0), (17, (BitVec.ofNat 32 k).setWidth 64)], e.1 < 20 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide
  refine h.update h.used_le (Nat.zero_le _) _ hb (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide) hm kt.2.1 kt.2.2
    (fun r hr => kt.gpr (by cases r <;> simp_all [calleeSaved])) ?_
  intro e he
  rw [hm, writeFrame_word _ _ _ hb e.1 (SearchPublic.headers_bound _ _ _ e he)]
  by_cases h0 : e.1 = 0
  · rw [SearchPublic.headers_zero he h0]
    rfl
  · have h317 := SearchPublic.headers_not_3_17 _ _ _ e he
    rw [frameValue_unchanged _ _ _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl)
      exacts [h0, h317.1, h317.2])]
    exact h.headers e (SearchPublic.headers_other he h0)

theorem search_exhausted {p : SearchPublic} {original s : State} {used remaining : Nat}
    {result : PrimeSearchResult} (h : SearchLive p original used remaining s)
    (hr : result = ⟨.exhausted, used, result.trace⟩) :
    WP isa exhausted s (SearchDone p original result) := by
  unfold exhausted
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (search_terminal h 3) fun u ⟨hm, ku⟩ => ?_
  have hu := h.terminated 3 hm ku
  have hmov : WP isa (.block [.mov .rdi (.reg .r12)]) u fun v =>
      (v.gpr .rdi = p.F ∧ v.mem = u.mem) ∧ Keep [.rdi] u v := by
    refine WP.keep [.rdi] ?_ rfl
    xrun [hu.r12]
  refine WP.mono hmov fun v ⟨⟨hdv, hmv⟩, kv⟩ => ?_
  have hv := hu.keep kv hmv (by decide)
  refine WP.mono (search_clear hv hdv) fun t ⟨ht, hout, hw, _⟩ => ?_
  have hb : ∀ e ∈ [(0, (0 : BitVec 64)), (3, 0), (17, (BitVec.ofNat 32 3).setWidth 64)], e.1 < 20 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl) <;> decide
  have hwv (j : Nat) (hj : j < 20) : word t.mem p.F (8 * j) =
      frameValue [(0, (0 : BitVec 64)), (3, 0), (17, (BitVec.ofNat 32 3).setWidth 64)] j (word s.mem p.F (8 * j)) := by
    rw [hw j hj, hmv, hm, writeFrame_word _ _ _ hb j hj]
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
    (k : Keep rs s t) (hm : t.mem = s.mem) (hregs : ∀ reg ∈ calleeSaved, reg ∉ rs) :
    ContinuePost p original final used remaining t :=
  let ⟨hr, u, k', hlt, hi, rest⟩ := h
  ⟨hr, u, k', hlt, ⟨hi.1.keep k hm hregs, hi.2⟩, rest⟩

/-- What an iteration leaves: the search goes on (status 4) past its
candidate, or it is finished. -/
def IterPost (p : SearchPublic) (original : State) (final : PrimeSearchResult) (used remaining : Nat)
    (t : State) : Prop :=
  (word t.mem p.F (8 * 17) = 4 ∧ ContinuePost p original final used remaining t) ∨
    (word t.mem p.F (8 * 17) ≠ 4 ∧ ¬Continues p original used remaining ∧ SearchDone p original final t)

theorem search_load_used {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (hc : CandPost p (searchP original) (searchRand original) used s) :
    WP isa (.block loadUsed) s fun t =>
      (t.gpr .rcx = BitVec.ofNat 64 (candUsed p original used) ∧ t.mem = s.mem) ∧ Keep [.rcx] s t := by
  have hl : ∀ d, d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 d) 8 := fun d hd =>
    let ⟨r, hr, hc⟩ := (h.input.frame_scr h.wr).st hd
    ⟨r, List.mem_append_right _ hr, hc⟩
  have hin : InRegions (s.rd ++ s.wr) p.up 8 := by
    refine ⟨inUsed original, List.mem_append_right _ ?_, ?_⟩
    · rw [h.wr, h.input.1.2.2.2.1]; exact List.mem_cons_of_mem _ (by simp [inWrites])
    · rw [← h.input.2]; simp only [inUsed, searchOfState, Region.Contains, BitVec.sub_self, BitVec.toNat_zero,
        Nat.zero_add]; decide
  have hu : s.mem.readW p.up 64 = BitVec.ofNat 64 (candUsed p original used) := by
    have := hc.2.2
    change [word s.mem p.up 0] = _ at this
    have h' := (List.cons.inj this).1
    simp only [Bignum.word, off, BitVec.add_zero] at h'
    exact h'
  have h7 := h.slot (j := 7) (v := p.up) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h7
  refine WP.keep [.rcx] ?_ rfl
  unfold loadUsed
  xrun [State.ea, field, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero, h.r12,
    hl 56 (by decide), h7, hin, hu]

/-- Through stores of the frame's words but its fixed ones, a finished search
with the words stored. -/
theorem SearchLive.done_after {p : SearchPublic} {original s t : State} {used remaining : Nat}
    {result : PrimeSearchResult} (h : SearchLive p original used remaining s)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 20)
    (hfix : ∀ e ∈ values, e.1 ≠ 1 ∧ e.1 ≠ 2 ∧ e.1 ≠ 4 ∧ e.1 ≠ 7 ∧ e.1 ≠ 18)
    (hm : t.mem = writeFrame s.mem p.F values) {rs : List Reg} (kt : Keep rs s t)
    (hrs : ∀ r ∈ calleeSaved, r ∉ rs)
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
  refine ⟨h.input, kt.2.1.trans h.rd, kt.2.2.trans h.wr, (kt.gpr (hrs .rsp (by decide))).trans h.rsp,
    (kt.gpr (hrs .r12 (by decide))).trans h.r12, fun r hr hn hs => (kt.gpr (hrs r hr)).trans (h.saved r hr hn hs),
    ?_, ?_, ?_, ?_, ?_, by rw [hw 0 (by decide)]; exact h0, by rw [hw 3 (by decide)]; exact h3,
    by rw [hw 16 (by decide)]; exact h16, by rw [hw 17 (by decide)]; exact h17, by rw [hbytes]; exact hout⟩
  · exact (hkeep 4 (by decide) fun e he => (hfix e he).2.2.1.symm).trans h.savedR12
  · exact (hkeep 7 (by decide) fun e he => (hfix e he).2.2.2.1.symm).trans (h.slot (by simp [SearchPublic.headers]))
  · exact (hkeep 18 (by decide) fun e he => (hfix e he).2.2.2.2.symm).trans (h.slot (by simp [SearchPublic.headers]))
  · exact (hkeep 1 (by decide) fun e he => (hfix e he).1.symm).trans (h.slot (by simp [SearchPublic.headers]))
  · exact (hkeep 2 (by decide) fun e he => (hfix e he).2.1.symm).trans (h.slot (by simp [SearchPublic.headers]))

/-! ## Accepting a prime -/

theorem add_ofNat_ofNat (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem SearchLive.rand_length {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) : (searchRand original).length = p.randLen := by
  rw [← h.input.2]; simp [searchRand, Spec.Rsa.bytesAt, searchOfState]

theorem SearchLive.frame_in {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) {t : State} (hw : t.wr = s.wr) :
    (∀ d, d + 8 ≤ 160 → InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 d) 8) ∧
      (∀ d, d + 8 ≤ 160 → InRegions t.wr (p.F + BitVec.ofNat 64 d) 8) ∧ InRegions t.wr p.F 8 := by
  have scr := h.input.frame_scr (hw.trans h.wr)
  refine ⟨fun d hd => let ⟨r, hr', hc⟩ := scr.st hd; ⟨r, List.mem_append_right _ hr', hc⟩,
    fun d hd => scr.st hd, by simpa only [BitVec.add_zero] using scr.st (d := 0) (by decide)⟩

/-- The accepted candidate's octets consumed, and the prime's status. -/
theorem accept_tail_ok {p : SearchPublic} {original s u : State} {used remaining cu : Nat}
    (h : SearchLive p original used remaining s) (hw : u.wr = s.wr)
    (hr12 : u.gpr .r12 = p.F) (hm : u.mem = s.mem) (hrcx : u.gpr .rcx = BitVec.ofNat 64 cu) :
    WP isa (.block (([.mov .rax (.mem (field 16)), .alu .add .rax (.reg .rcx), .store (field 16) .rax] : List Instr) ++
      terminal 1)) u fun t =>
      t.mem = writeFrame s.mem p.F [(16, BitVec.ofNat 64 used + BitVec.ofNat 64 cu), (0, 0), (3, 0),
        (17, (BitVec.ofNat 32 1).setWidth 64)] ∧ Keep [.rax] u t := by
  obtain ⟨hl, hs, hs0⟩ := h.frame_in hw
  have h16 := h.slot (j := 16) (v := BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h16
  refine WP.keep [.rax] ?_ rfl
  unfold terminal writeFrame
  simp only [List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    hr12, hm, hrcx, hl 128 (by decide), h16, hs0, hs 24 (by decide), hs 128 (by decide), hs 136 (by decide)]
  rfl

theorem search_accept {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    {used remaining c : Nat} {rest : List Byte}
    (h : SearchIter p original final used remaining s) (hc : CandPost p (searchP original) (searchRand original) used s)
    (hr : remaining ≠ 0)
    (hres : Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used) =
      some (.prime c, rest)) :
    WP isa (.block accept) s (SearchDone p original final) := by
  obtain ⟨h, tr, hfinal⟩ := h
  rw [accept, List.append_assoc, WP.block_append_iff]
  refine WP.mono (search_load_used h hc) fun u ⟨⟨hrcx, hmu⟩, ku⟩ => ?_
  have hr12 : u.gpr .r12 = p.F := (ku.gpr (by decide)).trans h.r12
  refine WP.mono (accept_tail_ok h ku.2.2 hr12 hmu hrcx) fun t ⟨ht, kt⟩ => ?_
  have hu : candUsed p original used = ((searchRand original).drop used).length - rest.length := by
    simp only [candUsed, hres, List.length_drop, h.rand_length]
  unfold tailOf at hfinal
  rw [VG.Proof.RsaKeyGen.Search.search_prime hr hres, Spec.Entropy.Result.consume] at hfinal
  subst hfinal
  refine h.done_after _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) ht (ku.trans kt)
    (by intro r hr; cases r <;> simp_all [calleeSaved]) rfl rfl ?_ rfl ?_
  · simp only [frameValue, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ↓reduceIte]
    rw [add_ofNat_ofNat, hu]
  · have ho := hc.2.1
    rw [hres] at ho
    exact ho

/-! ## Asking for more entropy -/

theorem ofNat_toNat_lt {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `request`, with the octets left in rax: the next tape's length. -/
theorem request_ok {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (hra : s.gpr .rax = BitVec.ofNat 64 (p.randLen - used)) :
    WP isa (.block request) s fun t =>
      t.mem = writeFrame s.mem p.F [(3, BitVec.ofNat 64 (primeRequest p.len (p.randLen - used))),
        (17, (BitVec.ofNat 32 0).setWidth 64)] ∧ Keep [.rax, .rcx] s t := by
  obtain ⟨hl, hs, -⟩ := h.frame_in (t := s) rfl
  have hf := h.callFacts
  have hL : p.len ≤ 512 := hf.len.2.1
  have hcap : p.randLen ≤ primeEntropy p.len := by
    rw [← h.input.2]; exact h.input.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have h1 := h.slot (j := 1) (v := BitVec.ofNat 64 p.len) (by simp [SearchPublic.headers])
  have h2 := h.slot (j := 2) (v := BitVec.ofNat 64 (primeEntropy p.len)) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h1 h2
  have h16 : BitVec.ofNat 64 p.len <<< 4 = BitVec.ofNat 64 (16 * p.len) := by
    rw [SearchInit.shl_ofNat _ _ (by omega)]; congr 1; omega
  have hle : primeEntropy p.len < 2 ^ 63 := by unfold primeEntropy; omega
  have hreq : primeRequest p.len (p.randLen - used) =
      min (2 * max (p.randLen - used) (16 * p.len)) (primeEntropy p.len) := rfl
  have ta := ofNat_toNat_lt (a := p.randLen - used) (by omega)
  have t16 := ofNat_toNat_lt (a := 16 * p.len) (by omega)
  have tc := ofNat_toNat_lt (a := primeEntropy p.len) (by omega)
  have sa : BitVec.ofNat 64 (p.randLen - used) <<< 1 = BitVec.ofNat 64 (2 * (p.randLen - used)) := by
    rw [SearchInit.shl_ofNat _ _ (by omega)]; congr 1; omega
  have s16 : BitVec.ofNat 64 (16 * p.len) <<< 1 = BitVec.ofNat 64 (2 * (16 * p.len)) := by
    rw [SearchInit.shl_ofNat _ _ (by omega)]; congr 1; omega
  have t2a := ofNat_toNat_lt (a := 2 * (p.randLen - used)) (by omega)
  have t216 := ofNat_toNat_lt (a := 2 * (16 * p.len)) (by omega)
  refine WP.keep [.rax, .rcx] ?_ rfl
  unfold request writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  rcases Nat.lt_or_ge (p.randLen - used) (16 * p.len) with c1 | c1
  · rcases Nat.lt_or_ge (2 * (16 * p.len)) (primeEntropy p.len) with c2 | c2
    · have e1 := decide_eq_true c1
      have e2 := decide_eq_true c2
      xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, eval, execCmov,
        h.r12, hra, hl 8 (by decide), hl 16 (by decide), h1, h2, h16, hs 24 (by decide), hs 136 (by decide),
        ta, t16, tc, s16, t216, e1, e2]
      rw [hreq, Nat.max_eq_right (by omega), Nat.min_eq_left (by omega)]
      rfl
    · have e1 := decide_eq_true c1
      have e2 := decide_eq_false (Nat.not_lt.mpr c2)
      xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, eval, execCmov,
        h.r12, hra, hl 8 (by decide), hl 16 (by decide), h1, h2, h16, hs 24 (by decide), hs 136 (by decide),
        ta, t16, tc, s16, t216, e1, e2]
      rw [hreq, Nat.max_eq_right (by omega), Nat.min_eq_right (by omega)]
      rfl
  · rcases Nat.lt_or_ge (2 * (p.randLen - used)) (primeEntropy p.len) with c2 | c2
    · have e1 := decide_eq_false (Nat.not_lt.mpr c1)
      have e2 := decide_eq_true c2
      xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, eval, execCmov,
        h.r12, hra, hl 8 (by decide), hl 16 (by decide), h1, h2, h16, hs 24 (by decide), hs 136 (by decide),
        ta, t16, tc, sa, t2a, e1, e2]
      rw [hreq, Nat.max_eq_left (by omega), Nat.min_eq_left (by omega)]
      rfl
    · have e1 := decide_eq_false (Nat.not_lt.mpr c1)
      have e2 := decide_eq_false (Nat.not_lt.mpr c2)
      xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, eval, execCmov,
        h.r12, hra, hl 8 (by decide), hl 16 (by decide), h1, h2, h16, hs 24 (by decide), hs 136 (by decide),
        ta, t16, tc, sa, t2a, e1, e2]
      rw [hreq, Nat.max_eq_left (by omega), Nat.min_eq_right (by omega)]
      rfl

/-- The short tape's guard: whether the octets left reach the budget. -/
theorem short_guard {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (.block [.mov .rax (.mem (field 13)), .alu .cmp .rax (.mem (field 2))]) s fun t =>
      (t.gpr .rax = BitVec.ofNat 64 (p.randLen - used) ∧
        eval .ae t = some (decide (primeEntropy p.len ≤ p.randLen - used)) ∧ t.mem = s.mem) ∧
      Keep [.rax] s t := by
  obtain ⟨hl, -, -⟩ := h.frame_in (t := s) rfl
  have hf := h.callFacts
  have hL : p.len ≤ 512 := hf.len.2.1
  have h2 := h.slot (j := 2) (v := BitVec.ofNat 64 (primeEntropy p.len)) (by simp [SearchPublic.headers])
  have h13 := h.slot (j := 13) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h2 h13
  have ta := ofNat_toNat_lt (a := p.randLen - used) (by have := hf.rand64; omega)
  have tc := ofNat_toNat_lt (a := primeEntropy p.len) (by unfold primeEntropy; omega)
  refine WP.keep [.rax] ?_ rfl
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, eval,
    h.r12, hl 104 (by decide), hl 16 (by decide), h2, h13, ta, tc]
  by_cases hc : primeEntropy p.len ≤ p.randLen - used
  · simp only [show ¬p.randLen - used < primeEntropy p.len by omega, decide_false, Bool.not_false, hc, decide_true]
  · simp only [show p.randLen - used < primeEntropy p.len by omega, decide_true, Bool.not_true, hc, decide_false]

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
  refine WP.seq (WP.mono (short_guard h) fun u ⟨⟨hra, hae, hmu⟩, ku⟩ => ?_)
  have hu := h.keep ku hmu (by decide)
  refine WP.ite _ hae (fun hb => ?_) (fun hb => ?_)
  · have hb := of_decide_eq_true hb
    rw [ite_eq_left_of_eq_true _ _ (eq_true hb)] at hfinal
    exact search_exhausted hu (by rw [hfinal]; rfl)
  · have hb := of_decide_eq_false hb
    rw [ite_eq_right_of_eq_false _ _ (eq_false hb)] at hfinal
    subst hfinal
    refine WP.mono (request_ok hu hra) fun t ⟨ht, kt⟩ => ?_
    refine hu.done_after _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl) <;> dsimp only <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl) <;> dsimp only <;> decide) ht kt
      (by intro r hr; cases r <;> simp_all [calleeSaved]) ?_ rfl ?_ rfl ?_
    · simp only [frameValue, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ↓reduceIte]
      rw [hu.slot (j := 0) (v := BitVec.ofNat 64 remaining) (by simp [SearchPublic.headers])]
      rfl
    · simp only [frameValue, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ↓reduceIte]
      rw [hu.slot (j := 16) (v := BitVec.ofNat 64 used) (by simp [SearchPublic.headers])]
      rfl
    · have ho := hc.2.1
      rw [hres] at ho
      rw [hmu]
      exact ho

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
    (hrs : ∀ r ∈ calleeSaved, r ∉ rs)
    (hother : ∀ e ∈ values, e.1 = 0 ∨ e.1 = 12 ∨ e.1 = 13 ∨ e.1 = 16 ∨ e.1 = 17)
    (hnew : ∀ e ∈ p.headers used' remaining', e.1 = 0 ∨ e.1 = 12 ∨ e.1 = 13 ∨ e.1 = 16 →
      frameValue values e.1 (word s.mem p.F (8 * e.1)) = e.2) :
    SearchLive p original used' remaining' t := by
  refine h.update hu hk values hb h4 hm kt.2.1 kt.2.2 (fun r hr => kt.gpr (hrs r hr)) ?_
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

theorem reject_head {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (hc : CandPost p (searchP original) (searchRand original) used s) :
    WP isa (.block (([.mov .rdx (.reg .rax)] : List Instr) ++ loadUsed ++ ([.alu .test .rcx (.reg .rcx)] : List Instr))) s fun t =>
      (t.gpr .rdx = s.gpr .rax ∧ t.gpr .rcx = BitVec.ofNat 64 (candUsed p original used) ∧
        eval .e t = some (decide (candUsed p original used = 0)) ∧ t.mem = s.mem) ∧ Keep [.rdx, .rcx] s t := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = s.gpr .rax ∧ t.mem = s.mem) (by xrun) rfl)
    fun u ⟨⟨hdx, hmu⟩, ku⟩ => ?_
  have hu := h.keep ku hmu (by decide)
  refine WP.mono (search_load_used hu (hc.keep hmu (by rw [ku.gpr (by decide)]))) fun v ⟨⟨hcx, hmv⟩, kv⟩ => ?_
  have hf := h.callFacts
  have hz : (BitVec.ofNat 64 (candUsed p original used) == 0) = decide (candUsed p original used = 0) :=
    ofNat64_beq_zero (by
      have : candUsed p original used ≤ p.randLen := by
        unfold candUsed; split <;> omega
      have := hf.rand64; omega)
  refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = v.gpr .rcx ∧
      eval .e t = some (decide (candUsed p original used = 0)) ∧ t.mem = v.mem) (by
    xrun [eval, hcx, BitVec.and_self, hz]) rfl) fun t ⟨⟨hcx', he, hmt⟩, kt⟩ => ?_
  refine ⟨⟨by rw [kt.gpr (by decide), kv.gpr (by decide), hdx], hcx'.trans hcx, he, hmt.trans (hmv.trans hmu)⟩,
    ((ku.trans kv).trans kt).mono (by decide)⟩

theorem ofNat_sub_ofNat {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ofNat_toNat_lt (a := b) (by omega), ofNat_toNat_lt ha]; exact h),
    ofNat_toNat_lt (a := a) ha, ofNat_toNat_lt (a := b) (by omega), ofNat_toNat_lt (a := a - b) (by omega)]

/-- `advance` past `u` octets, and whether the status was 2. -/
theorem advance_ok {p : SearchPublic} {original s : State} {used remaining u : Nat}
    (h : SearchLive p original used remaining s) (hcx : s.gpr .rcx = BitVec.ofNat 64 u) :
    WP isa (.block (advance ++ ([.alu .cmp .rdx (.imm 2)] : List Instr))) s fun t =>
      (t.mem = writeFrame s.mem p.F [(12, p.rp + BitVec.ofNat 64 used + BitVec.ofNat 64 u),
          (13, BitVec.ofNat 64 (p.randLen - used) - BitVec.ofNat 64 u),
          (16, BitVec.ofNat 64 used + BitVec.ofNat 64 u), (17, (BitVec.ofNat 32 4).setWidth 64)] ∧
        eval .e t = some (s.gpr .rdx == 2)) ∧ Keep [.rax, .rdx] s t := by
  obtain ⟨hl, hs, -⟩ := h.frame_in (t := s) rfl
  have h12 := h.slot (j := 12) (v := p.rp + BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  have h13 := h.slot (j := 13) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SearchPublic.headers])
  have h16 := h.slot (j := 16) (v := BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h12 h13 h16
  have h2 : BitVec.signExtend 64 (2 : BitVec 32) = (2 : BitVec 64) := by decide
  refine WP.keep [.rax, .rdx] ?_ rfl
  unfold advance writeFrame
  simp only [List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, eval, h.r12, hcx,
    hl 96 (by decide), hl 104 (by decide), hl 128 (by decide), h12, h13, h16, read_above_store,
    hs 96 (by decide), hs 104 (by decide), hs 128 (by decide), hs 136 (by decide), h2, sub_beq_zero]
  rfl

theorem count_ok {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (.block count) s fun t =>
      t.mem = writeFrame s.mem p.F [(0, BitVec.ofNat 64 remaining - 1)] ∧ Keep [.rax] s t := by
  obtain ⟨hl, -, hs0⟩ := h.frame_in (t := s) rfl
  have h0 := h.slot (j := 0) (v := BitVec.ofNat 64 remaining) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul, BitVec.add_zero] at h0
  have hl0 : InRegions (s.rd ++ s.wr) p.F 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have h1 : BitVec.signExtend 64 (1 : BitVec 32) = (1 : BitVec 64) := by decide
  refine WP.keep [.rax] ?_ rfl
  unfold count writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl0, h0, hs0, h1]

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
    (h : SearchIter p original final used remaining s) (hc : CandPost p (searchP original) (searchRand original) used s)
    (hr : remaining ≠ 0)
    (hres : Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used) =
      some (x, rest))
    (hx : x = .close ∨ x = .rejected)
    (hra : s.gpr .rax = BitVec.ofNat 64 (if x = .close then 2 else 3)) :
    WP isa reject s (IterPost p original final used remaining) := by
  obtain ⟨h, tr, hfinal⟩ := h
  have hf := h.callFacts
  have hlen := h.rand_length
  have hcu : candUsed p original used = ((searchRand original).drop used).length - rest.length := by
    simp only [candUsed, hres, List.length_drop, hlen]
  unfold reject
  refine WP.seq (WP.mono (reject_head h hc) fun t ⟨⟨hdx, hcx, he, hmt⟩, kt⟩ => ?_)
  have ht := h.keep kt hmt (by decide)
  refine WP.ite _ he (fun hz => ?_) (fun hz => ?_)
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
    refine WP.mono (search_exhausted ht (result := final) (by rw [hfinal]; rfl)) fun t' hd => ?_
    exact .inr ⟨hd.status_ne, fun ⟨_, _, h⟩ => h hz, hd⟩
  · have hz := of_decide_eq_false hz
    have hu0 : candUsed p original used ≠ 0 := hz
    have hpast := tail_past (u := candUsed p original used) hr hres hx hcu hu0
    rw [hpast, VG.Proof.RsaKeyGen.Search.consume_consume] at hfinal
    have hule : candUsed p original used ≤ p.randLen - used := by
      rw [hcu, List.length_drop, hlen]; omega
    refine WP.seq (WP.mono (advance_ok ht hcx) fun v ⟨⟨hmv, hev⟩, kv⟩ => ?_)
    have hv := ht
    rw [hdx, hra] at hev
    have hbound : ∀ e ∈ [(12, p.rp + BitVec.ofNat 64 used + BitVec.ofNat 64 (candUsed p original used)),
        (13, BitVec.ofNat 64 (p.randLen - used) - BitVec.ofNat 64 (candUsed p original used)),
        (16, BitVec.ofNat 64 used + BitVec.ofNat 64 (candUsed p original used)),
        (17, (BitVec.ofNat 32 4).setWidth 64)], e.1 < 20 ∧ 4 ≠ e.1 ∧
          (e.1 = 0 ∨ e.1 = 12 ∨ e.1 = 13 ∨ e.1 = 16 ∨ e.1 = 17) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
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
      refine ht.moved hu' h.remaining_le _ (fun e he => (hbound e he).1) (fun e he => (hbound e he).2.1)
        hmv kv (by decide) (fun e he => (hbound e he).2.2) ?_
      intro e he hc'
      simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> simp only [Nat.reduceEqDiff, false_or, or_false, or_self] at hc' <;>
        simp only [frameValue, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ↓reduceIte, h12, h13, h16]
      exact ht.slot (by simp [SearchPublic.headers])
    refine WP.ite _ hev (fun hb => ?_) (fun hb => ?_)
    · -- Too close: not counted.
      have hxc : x = .close := by
        rcases hx with rfl | rfl
        · rfl
        · simp only [reduceCtorEq, ↓reduceIte] at hb; cases hb
      subst hxc
      simp only [↓reduceIte] at hfinal
      exact WP.block_nil (.inl ⟨h17, hr, _, remaining, by omega, ⟨hvl, _, hfinal⟩, rfl, .inl ⟨rfl, by simp only [candStatus, hres]; rfl⟩,
        by rw [hpast, Nat.add_sub_cancel_left]; simp only [↓reduceIte]⟩)
    · -- Rejected: one fewer counted candidate.
      have hxr : x = .rejected := by
        rcases hx with rfl | rfl
        · simp only [↓reduceIte] at hb; cases hb
        · rfl
      subst hxr
      simp only [reduceCtorEq, ↓reduceIte] at hfinal
      refine WP.mono (count_ok hvl) fun w ⟨hmw, kw⟩ => ?_
      have hb0 : ∀ e ∈ [(0, BitVec.ofNat 64 remaining - 1)], e.1 < 20 ∧ 4 ≠ e.1 ∧
          (e.1 = 0 ∨ e.1 = 12 ∨ e.1 = 13 ∨ e.1 = 16 ∨ e.1 = 17) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro _ rfl; dsimp only; decide
      have hwl : SearchLive p original (used + candUsed p original used) (remaining - 1) w := by
        refine hvl.moved hu' (by have := h.remaining_le; omega) _ (fun e he => (hb0 e he).1)
          (fun e he => (hb0 e he).2.1) hmw kw (by decide) (fun e he => (hb0 e he).2.2) ?_
        intro e he hc'
        simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl <;> simp only [Nat.reduceEqDiff, false_or, or_false, or_self] at hc' <;>
          simp only [frameValue, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ↓reduceIte]
        · exact ofNat64_pred (by omega)
            (Nat.lt_of_le_of_lt h.remaining_le (by rw [← h.input.2]; exact BitVec.isLt _))
        all_goals exact hvl.slot (by simp [SearchPublic.headers])
      have h17w : word w.mem p.F (8 * 17) = 4 := by
        rw [hmw, writeFrame_word _ _ _ (fun e he => (hb0 e he).1) 17 (by decide)]; exact h17
      exact .inl ⟨h17w, hr, _, remaining - 1, by omega, ⟨hwl, _, hfinal⟩, rfl, .inr ⟨rfl, by simp only [candStatus, hres]; rfl⟩,
        by rw [hpast, Nat.add_sub_cancel_left]; simp only [reduceCtorEq, ↓reduceIte]⟩

/-! ## The loop -/

/-- The candidate's status, zero-extended, compared with 1. -/
theorem classify_head (s : State) {st : Nat} (hst : ((s.gpr .rax).setWidth 32).toNat = st) (h4 : st < 4) :
    WP isa (.block [.mov32 .rax (.reg .rax), .alu .cmp .rax (.imm 1)]) s fun t =>
      (t.gpr .rax = BitVec.ofNat 64 st ∧ eval .e t = some (decide (st = 1)) ∧ t.mem = s.mem) ∧
        Keep [.rax] s t := by
  have hr : (s.gpr .rax).setWidth 32 = BitVec.ofNat 32 st := by
    apply BitVec.eq_of_toNat_eq; rw [hst, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hz : ((BitVec.ofNat 32 st).setWidth 64 - BitVec.signExtend 64 (1 : BitVec 32) == 0) = decide (st = 1) := by
    rcases (show st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 by omega) with rfl | rfl | rfl | rfl <;> decide
  have he : (BitVec.ofNat 32 st).setWidth 64 = BitVec.ofNat 64 st := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  refine WP.keep [.rax] ?_ rfl
  xrun [eval, hr, hz]
  refine ⟨he, ?_⟩
  rcases (show st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

theorem test_rax (s : State) {st : Nat} (hra : s.gpr .rax = BitVec.ofNat 64 st) (h4 : st < 4) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) s fun t =>
      (t.gpr .rax = s.gpr .rax ∧ eval .e t = some (decide (st = 0)) ∧ t.mem = s.mem) ∧ Keep [.rax] s t := by
  have hz : (BitVec.ofNat 64 st == 0) = decide (st = 0) := ofNat64_beq_zero (by omega)
  refine WP.keep [.rax] ?_ rfl
  xrun [eval, hra, BitVec.and_self, hz]

theorem SearchIter.keep {p : SearchPublic} {original s t : State} {final : PrimeSearchResult}
    {used remaining : Nat} (h : SearchIter p original final used remaining s) {rs : List Reg}
    (k : Keep rs s t) (hm : t.mem = s.mem) (hregs : ∀ reg ∈ calleeSaved, reg ∉ rs) :
    SearchIter p original final used remaining t := ⟨h.1.keep k hm hregs, h.2⟩

theorem search_classify {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    {used remaining : Nat} (h : SearchIter p original final used remaining s)
    (hc : CandPost p (searchP original) (searchRand original) used s) (hr : remaining ≠ 0) :
    WP isa classify s (IterPost p original final used remaining) := by
  have hst := hc.1
  have h4 : Spec.RsaKeyGen.candidateStatus
      (Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used)) < 4 := by
    unfold Spec.RsaKeyGen.candidateStatus; split <;> decide
  unfold classify
  refine WP.seq (WP.mono (classify_head s hst h4) fun u ⟨⟨hra, he1, hmu⟩, ku⟩ => ?_)
  have hu := h.keep ku hmu (by decide)
  have hlow : (u.gpr .rax).setWidth 32 = (s.gpr .rax).setWidth 32 := by
    rw [hra]; apply BitVec.eq_of_toNat_eq
    have hst' : (s.gpr .rax).toNat % 2 ^ 32 = Spec.RsaKeyGen.candidateStatus
        (Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used)) := by
      rw [← BitVec.toNat_setWidth]; exact hst
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat, hst', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hcu := hc.keep hmu hlow
  refine WP.ite _ he1 (fun h1 => ?_) (fun h1 => ?_)
  · have h1 := of_decide_eq_true h1
    cases hres : Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used) with
    | none => rw [hres] at h1; cases h1
    | some pr =>
      obtain ⟨x, rest⟩ := pr
      cases x with
      | prime c =>
        exact WP.mono (search_accept hu hcu hr hres) fun t hd =>
          .inr ⟨hd.status_ne, fun ⟨_, hs, _⟩ => by simp [candStatus, hres, Spec.RsaKeyGen.candidateStatus] at hs, hd⟩
      | close => rw [hres] at h1; cases h1
      | rejected => rw [hres] at h1; cases h1
  · refine WP.seq (WP.mono (test_rax u hra h4) fun v ⟨⟨hrv, he0, hmv⟩, kv⟩ => ?_)
    have hv := hu.keep kv hmv (by decide)
    have hcv := hcu.keep hmv (by rw [hrv])
    refine WP.ite _ he0 (fun h0 => ?_) (fun h0 => ?_)
    · have h0 := of_decide_eq_true h0
      cases hres : Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used) with
      | none =>
        refine WP.mono (search_short hv hcv hr hres) fun t hd => .inr ⟨hd.status_ne, fun ⟨_, hs, _⟩ => ?_, hd⟩
        simp [candStatus, hres, Spec.RsaKeyGen.candidateStatus] at hs
      | some pr =>
        obtain ⟨x, rest⟩ := pr
        cases x <;> (rw [hres] at h0; cases h0)
    · have h0 := of_decide_eq_false h0
      have h1 := of_decide_eq_false h1
      cases hres : Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used) with
      | none => rw [hres] at h0; exact absurd rfl h0
      | some pr =>
        obtain ⟨x, rest⟩ := pr
        cases x with
        | prime c => rw [hres] at h1; exact absurd rfl h1
        | close =>
          refine search_reject hv hcv hr hres (.inl rfl) ?_
          rw [hrv, hra, hres]; rfl
        | rejected =>
          refine search_reject hv hcv hr hres (.inr rfl) ?_
          rw [hrv, hra, hres]; rfl

/-! ## An iteration -/

/-- What an iteration leaves, with the loop's condition. -/
def LoopStep (p : SearchPublic) (original : State) (final : PrimeSearchResult) (used remaining : Nat)
    (t : State) : Prop :=
  (eval .e t = some true ∧ ContinuePost p original final used remaining t) ∨
    (eval .e t = some false ∧ ¬Continues p original used remaining ∧ SearchDone p original final t)

theorem iter_guard {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (.block [.mov .rax (.mem (field 0)), .alu .test .rax (.reg .rax)]) s fun t =>
      (eval .e t = some (decide (remaining = 0)) ∧ t.mem = s.mem) ∧ Keep [.rax] s t := by
  obtain ⟨hl, -, -⟩ := h.frame_in (t := s) rfl
  have hl0 : InRegions (s.rd ++ s.wr) p.F 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have h0 := h.slot (j := 0) (v := BitVec.ofNat 64 remaining) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul, BitVec.add_zero] at h0
  have hz : (BitVec.ofNat 64 remaining == 0) = decide (remaining = 0) :=
    ofNat64_beq_zero (Nat.lt_of_le_of_lt h.remaining_le (by rw [← h.input.2]; exact BitVec.isLt _))
  refine WP.keep [.rax] ?_ rfl
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero, eval,
    h.r12, hl0, h0, BitVec.and_self, hz]

theorem iter_test {p : SearchPublic} {original s : State} {final : PrimeSearchResult} {used : Nat}
    {remaining : Nat} (h : IterPost p original final used remaining s) :
    WP isa (.block [.mov .rax (.mem (field 17)), .alu .cmp .rax (.imm 4)]) s (LoopStep p original final used remaining) := by
  have hregs : s.gpr .r12 = p.F ∧ ∃ o : State, SearchInput p o ∧ s.wr = p.frame :: o.wr := by
    rcases h with ⟨-, -, _, _, -, ⟨hi, -⟩, -⟩ | ⟨-, -, hd⟩
    · exact ⟨hi.r12, _, hi.input, hi.wr⟩
    · exact ⟨hd.r12, _, hd.input, hd.wr⟩
  obtain ⟨hr12, o, hi, hw⟩ := hregs
  have scr := hi.frame_scr hw
  have hl : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 136) 8 :=
    let ⟨r, hr, hc⟩ := scr.st (d := 136) (by decide); ⟨r, List.mem_append_right _ hr, hc⟩
  have h4 : BitVec.signExtend 64 (4 : BitVec 32) = (4 : BitVec 64) := by decide
  refine WP.mono (WP.keep [.rax] (Q := fun t => eval .e t = some (word s.mem p.F (8 * 17) - 4 == 0) ∧
    t.mem = s.mem) (by
      xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, eval, hr12, hl, h4]) rfl) fun t ⟨⟨he, hm⟩, k⟩ => ?_
  rw [sub_beq_zero] at he
  rcases h with ⟨h17, hc⟩ | ⟨h17, hn, hd⟩
  · exact .inl ⟨by rw [he, h17]; rfl, hc.keep k hm (by decide)⟩
  · refine .inr ⟨by rw [he]; simp only [beq_eq_false_iff_ne.mpr h17], hn, ?_⟩
    exact ⟨hd.input, k.2.1.trans hd.rd, k.2.2.trans hd.wr, (k.gpr (by decide)).trans hd.rsp,
      (k.gpr (by decide)).trans hd.r12, fun r hr hn hs => (k.gpr (by cases r <;> simp_all [calleeSaved])).trans
        (hd.saved r hr hn hs), by rw [hm]; exact hd.savedR12, by rw [hm]; exact hd.usedPtr,
      by rw [hm]; exact hd.stp, by rw [hm]; exact hd.len, by rw [hm]; exact hd.cap, by rw [hm]; exact hd.remaining,
      by rw [hm]; exact hd.request, by rw [hm]; exact hd.used, by rw [hm]; exact hd.status,
      by rw [hm]; exact hd.output⟩

theorem search_iteration (v : RoundImpl) {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    {used remaining : Nat} (h : SearchIter p original final used remaining s) :
    WP isa (iteration (candidateCall v)) s (LoopStep p original final used remaining) := by
  unfold iteration
  change WP isa (.seq _ (.seq _ _)) s _
  refine WP.seq (WP.mono (iter_guard h.1) fun u ⟨⟨he, hmu⟩, ku⟩ => ?_)
  have hu := h.keep ku hmu (by decide)
  refine WP.seq (WP.ite _ he (fun hz => ?_) (fun hz => ?_))
  · have hz := of_decide_eq_true hz
    subst hz
    obtain ⟨hl, tr, hfinal⟩ := hu
    unfold tailOf at hfinal
    rw [VG.Proof.RsaKeyGen.Search.search_zero] at hfinal
    exact WP.mono (search_exhausted hl (result := final) (by rw [hfinal]; rfl)) fun t hd =>
      iter_test (.inr ⟨hd.status_ne, fun ⟨h, _⟩ => h rfl, hd⟩)
  · have hz := of_decide_eq_false hz
    refine WP.seq (WP.mono (search_candidate_run v hu.1) fun t ⟨ht, hc⟩ => ?_)
    exact WP.mono (search_classify ⟨ht, hu.2⟩ hc hz) fun _ hp => iter_test hp

theorem search_loop (v : RoundImpl) {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    {used remaining : Nat} (h : SearchIter p original final used remaining s) :
    WP isa (.loop (iteration (candidateCall v)) .e) s (SearchDone p original final) := by
  refine WP.loop (M := isa)
    (fun n t => ∃ u k, n = p.randLen - u + 1 ∧ SearchIter p original final u k t) ?_
    (p.randLen - used + 1) s ⟨used, remaining, rfl, h⟩
  rintro n t ⟨u, k, rfl, ht⟩
  refine WP.mono (search_iteration v ht) fun t' hs => ?_
  rcases hs with ⟨he, -, u', k', hlt, ht', -⟩ | ⟨he, -, hd⟩
  · have hle := ht'.1.used_le
    exact .inr ⟨he, _, by omega, u', k', rfl, ht'⟩
  · exact .inl ⟨he, hd⟩

end VG.Proof.RsaKeyGen.X86_64.Search
