module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Call
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Entry
import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The search's loop (RISCV64)

As on AArch64 (`Proof/RsaKeyGen/AArch64/Search/Step.lean`): after a
candidate, the search accepts its prime, asks for more entropy, gives up, or
goes on past it to the next (`search_classify`); with no counted candidates
left it gives up without one (`search_exhausted`). The loop runs these steps
to its end (`search_loop`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Search

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.RISCV64 VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64 (countLoop)
open VG.Impl.RsaKeyGen.RISCV64.Search
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeRequest PrimeSearchResult)

/-- A finished search, before `finish` stores its results. -/
structure SearchDone (p : SearchPublic) (original : State) (result : PrimeSearchResult) (s : State) :
    Prop where
  input : SearchInput p original
  rd : s.rd = original.rd
  wr : s.wr = p.frame :: original.wr
  s0 : s.gpr .s0 = p.F
  saved : ∀ r ∈ preserved, r ≠ .s0 → s.gpr r = original.gpr r
  savedS0 : word s.mem p.F 32 = original.gpr .s0
  usedPtr : word s.mem p.F (8 * 7) = p.up
  stp : word s.mem p.F (8 * 18) = p.stp
  len : word s.mem p.F (8 * 1) = BitVec.ofNat 64 p.len
  cap : word s.mem p.F (8 * 2) = BitVec.ofNat 64 (primeEntropy p.len)
  remaining : word s.mem p.F (8 * 0) = BitVec.ofNat 64 result.remaining
  request : word s.mem p.F (8 * 3) = BitVec.ofNat 64 result.requested
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
    (h3 : word s.mem p.F (8 * 3) = BitVec.ofNat 64 result.requested)
    (h16 : word s.mem p.F (8 * 16) = BitVec.ofNat 64 result.used)
    (h17 : word s.mem p.F (8 * 17) = BitVec.ofNat 64 result.status)
    (hout : Spec.Rsa.bytesAt s.mem p.op p.len =
      match result.outcome with
      | .accepted c => Spec.Rsa.i2osp c p.len
      | _ => List.replicate p.len 0) :
    SearchDone p original result s :=
  ⟨h.input, h.rd, h.wr, h.s0, h.saved, h.savedS0,
    h.slot (by simp [SearchPublic.headers]), h.slot (by simp [SearchPublic.headers]),
    h.slot (by simp [SearchPublic.headers]), h.slot (by simp [SearchPublic.headers]),
    h0, h3, h16, h17, hout⟩

theorem SearchDone.keep {p : SearchPublic} {original s t : State} {result : PrimeSearchResult}
    (h : SearchDone p original result s) {rs : List Reg} (k : KeepS rs s t) (hm : t.mem = s.mem)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) : SearchDone p original result t := by
  refine ⟨h.input, k.rd.trans h.rd, k.wr.trans h.wr,
    (k.gpr _ (hregs .s0 (by decide))).trans h.s0,
    fun reg hr h31 => (k.gpr reg (hregs reg hr)).trans (h.saved reg hr h31), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  exacts [h.savedS0, h.usedPtr, h.stp, h.len, h.cap, h.remaining, h.request, h.used, h.status, h.output]

/-! ## The frame's stores -/

theorem SearchLive.frame_st {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    ∀ d, d + 8 ≤ 160 → InRegions s.wr (p.F + BitVec.ofNat 64 d) 8 :=
  fun _ hd => (h.input.frame_scr h.wr).st hd

theorem SearchLive.frame_ld' {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    ∀ d, d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 d) 8 :=
  fun d hd => let ⟨r, hr, hc⟩ := h.frame_st d hd; ⟨r, List.mem_append_right _ hr, hc⟩


theorem SearchLive.frame_al' {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    ∀ d, d + 8 ≤ 160 → d % 8 = 0 → (p.F + BitVec.ofNat 64 d).toNat % 8 = 0 :=
  fun _ hd h8 => (h.input.frame_scr h.wr).al8 hd h8

def terminalValues (status : Nat) : List (Nat × BitVec 64) :=
  [(0, 0), (3, 0), (17, BitVec.ofNat 64 status)]

theorem terminalValues_bound (status : Nat) : ∀ e ∈ terminalValues status, e.1 < 20 := by
  simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

/-- `terminal k`: no counted candidates, no request, and the status `k`. -/
theorem search_terminal {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) {k : Nat} (hk : k = 1 ∨ k = 3) :
    WP isa (.block (terminal k)) s fun t =>
      t.mem = writeFrame s.mem p.F (terminalValues k) ∧ KeepS [.t2, .t3] s t := by
  have hs := h.frame_st
  have ha := h.frame_al'
  have ha0 : (p.F + BitVec.ofNat 64 0).toNat % 8 = 0 := ha 0 (by decide) (by decide)
  rcases hk with rfl | rfl <;>
  refine WP.keep' [.t2, .t3] ?_ (by decide) <;>
  unfold terminal writeFrame terminalValues <;>
  simp only [List.foldl_cons, List.foldl_nil]
  all_goals
    brun [ldf, stf, h.s0, exec_li, hs 0 (by decide), hs 24 (by decide), hs 136 (by decide), ha0,
      ha 24 (by decide) (by decide), ha 136 (by decide) (by decide), off]
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
    (hm : t.mem = writeFrame s.mem p.F (terminalValues k)) (hy : t.syms = s.syms)
    (kt : KeepS [.t2, .t3] s t) : SearchLive p original used 0 t := by
  have hb := terminalValues_bound k
  refine h.update h.used_le (Nat.zero_le _) _ hb (by
      simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide) hm hy kt (by decide) ?_
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

/-- `out_len` zeros at `out`, from its address in `a1`, its length in `a2`,
and zero in `a3`, as in the FFDH searches
(`Proof/Ffdh/RISCV64/Generation/Search/Writes.lean`). -/
theorem zeroLoop_ok {s : State} {O : Addr} {k : Nat} (ho : ∀ i < k, InRegions s.wr (off O i) 1)
    (hk : 1 ≤ k) (hk' : k < 2 ^ 63)
    (h3 : s.gpr .a1 = O) (h4 : s.gpr .a2 = BitVec.ofNat 64 k) (h5 : s.gpr .a3 = BitVec.ofNat 64 0) :
    WP isa (countLoop .a2 [.store .b .a3 .a1 0, .addi .a1 .a1 1]) s fun t =>
      ((∀ i < k, t.mem (off O i) = 0) ∧ Outside O 0 k s.mem t.mem) ∧ KeepS [.a1, .a2, .a3] s t := by
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .a1 = off O j ∧ t.gpr .a3 = BitVec.ofNat 64 0 ∧ Outside O 0 j s.mem t.mem ∧
      (∀ i < j, t.mem (off O i) = 0) ∧ KeepS [.a1, .a2, .a3] s t
  refine WP.mono (wp_countdown (body := .block ([.store .b .a3 .a1 0, .addi .a1 .a1 1] ++
      ([.addi .a2 .a2 (-1)] : List Instr)))
    (cnt := .a2) (N := k) (by omega) (by omega) Inv (fun j hj t ⟨t3, t5, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [h3]; simp [off], h5, Outside.refl _ _ _ _, fun _ h => absurd h (by omega),
      KeepS.refl _ _⟩ h4) fun t ⟨_, _, tout, tb, tk⟩ => ⟨⟨tb, tout⟩, tk⟩
  have hst : WP isa (.block [.store .b .a3 .a1 0, .addi .a1 .a1 1, .addi .a2 .a2 (-1)]) t fun t' =>
      t' = (({ t with mem := t.mem.write (off O j) 1 ((BitVec.ofNat 64 0).setWidth 8) } :
          State).write .a1 (off O (j + 1))).write .a2 (t.gpr .a2 - BitVec.ofNat 64 1) := by
    have hs : InRegions t.wr (off O j) 1 := by rw [tk.wr]; exact ho j hj
    brun [t3, t5, hs]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw1 := write1_outside t.mem O (d := j) ((BitVec.ofNat 64 0).setWidth 8) (by omega)
  refine ⟨⟨by gsimp, by gsimp; exact t5, ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; exact (tout.mono (Nat.le_refl _) (by omega)).trans (hw1.mono (by omega) (by omega))
  · intro i hi
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hw1 _ (by simp only [Mont.ofs]; rw [Mem.sub_ofNat_toNat O (by omega)]; omega)]; exact tb i hi
    · rw [write1_self]; rfl
  · exact tk.trans' (((KeepS.mem _ _).trans (KeepS.write _ _ _)).trans (KeepS.write _ _ _)).mono

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
  have hout : ∀ i < p.len, InRegions s.wr (off p.op i) 1 := fun i hi =>
    ⟨⟨p.op, p.len⟩, by
      rw [h.wr, h.input.wr_eq, h.out_region]; exact List.mem_cons_of_mem _ (by simp [inWrites]),
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])⟩
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keepS [.a1, .a2, .a3] (Q := fun t => t.gpr .a1 = p.op ∧
      t.gpr .a2 = BitVec.ofNat 64 p.len ∧ t.gpr .a3 = BitVec.ofNat 64 0 ∧ t.mem = s.mem) (by
    brun [ldf, h.s0, hl, hl6, hv, hv6, exec_li, h.frame_al' 40 (by decide) (by decide),
      h.frame_al' 48 (by decide) (by decide)]) (by decide +kernel)) fun s₁ ⟨⟨⟨h3, h4, h5, hm₁⟩, k₁⟩, hy₁⟩ => ?_)
  refine VG.RISCV64.WP.mono_syms (zeroLoop_ok (fun i hi => by rw [k₁.wr]; exact hout i hi) (by omega)
    (by omega) h3 h4 h5) fun t ⟨⟨tb, tout⟩, kt⟩ hyt => ?_
  have hfx : ∀ x, (∀ i < p.len, x ≠ p.op + BitVec.ofNat 64 i) → t.mem x = s.mem x := by
    intro x hx
    rw [tout x (Or.inr ?_), hm₁]
    by_contra hc
    exact hx (x - p.op).toNat (by simp only [ofs] at hc; omega)
      (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel])
  have kk := k₁.trans kt
  have hfr := zero_frame h hfx
  refine ⟨h.restore kk.rd kk.wr kk.sp (hyt.trans hy₁) (fun r hr => kk.gpr r (by revert r hr; decide)) hfr, ?_,
    fun j hj => h.input.frame_words hfr j hj⟩
  refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact tb i (List.mem_range.mp hi)

theorem search_exhausted {p : SearchPublic} {original s : State} {used remaining : Nat}
    {result : PrimeSearchResult} (h : SearchLive p original used remaining s)
    (hr : result = ⟨.exhausted, used, result.trace⟩) :
    WP isa exhausted s (SearchDone p original result) := by
  unfold exhausted
  refine WP.seq (VG.RISCV64.WP.mono_syms (search_terminal h (k := 3) (.inr rfl)) fun u ⟨hm, ku⟩ hyu => ?_)
  have hu := h.terminated 3 hm hyu ku
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
    (k : KeepS rs s t) (hm : t.mem = s.mem) (hy : t.syms = s.syms)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) :
    ContinuePost p original final used remaining t :=
  let ⟨hr, u, k', hlt, hi, rest⟩ := h
  ⟨hr, u, k', hlt, ⟨hi.1.keep k hm hy hregs, hi.2⟩, rest⟩

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

/-- The status, the low 32 bits of `a0`. -/
theorem low32 {x : BitVec 64} {st : Nat} (h : (x.setWidth 32).toNat = st) :
    (x <<< 32) >>> 32 = BitVec.ofNat 64 st := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, ← h, BitVec.toNat_setWidth]
  have := x.isLt
  omega

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero r) s = some (s.gpr r == 0) := rfl


/-- The status and the octets the candidate consumed, after it. -/
theorem search_head {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (hp : CandPost p (searchP original) (searchRand original) used s) :
    WP isa (.block (head ++ ([.addi .t4 .t1 (-1)] : List Instr))) s fun t =>
      SearchLive p original used remaining t ∧ CandPost p (searchP original) (searchRand original) used t ∧
      t.gpr .t1 = BitVec.ofNat 64 (candStatus p original used) ∧
      t.gpr .t2 = BitVec.ofNat 64 (candUsed p original used) ∧
      isa.eval (.zero .t4) t = some (decide (candStatus p original used = 1)) := by
  have hv7 := h.slot (j := 7) (v := p.up) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv7
  have hu : InRegions (s.rd ++ s.wr) (p.up + BitVec.ofNat 64 0) 8 := by
    refine ⟨inUsed original, List.mem_append_right _ ?_, ?_⟩
    · rw [h.wr, h.input.wr_eq]; exact List.mem_cons_of_mem _ (by simp [inWrites])
    · rw [← h.input.2]; simp only [inUsed, searchOfState, Region.Contains, BitVec.add_zero, BitVec.sub_self,
        BitVec.toNat_zero, Nat.zero_add]; decide
  have hw : s.mem.readW (p.up + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (candUsed p original used) := by
    have := hp.2.2
    change [word s.mem p.up 0] = _ at this
    simp only [Bignum.word, off, List.cons.injEq, and_true] at this
    exact this
  have hst := status_lt p original used
  have h0 := low32 hp.1
  have hua : (p.up + BitVec.ofNat 64 0).toNat % 8 = 0 := by
    rw [BitVec.add_zero, ← h.input.2]; exact h.input.used_al
  refine WP.mono (WP.keepS [.t1, .t2, .t3, .t4] (Q := fun t =>
    (t.gpr .t1 = BitVec.ofNat 64 (candStatus p original used) ∧
      t.gpr .t2 = BitVec.ofNat 64 (candUsed p original used) ∧
      isa.eval (.zero .t4) t = some (decide (candStatus p original used = 1))) ∧ t.mem = s.mem) ?_
    (by decide +kernel)) fun t ⟨⟨⟨⟨h9, h10, he⟩, hm⟩, k⟩, hy⟩ => ?_
  · unfold head
    brun [ldf, h.s0, hv7, h.frame_ld' 56 (by decide), h.frame_al' 56 (by decide) (by decide), hu, hua, hw, h0]
    refine (eval_zero _ _).trans ?_
    have : ∀ st < 4, ((BitVec.ofNat 64 st - BitVec.ofNat 64 1) == 0) = decide (st = 1) := by decide
    simp only [RegUpd.gpr_write_self, this _ hst]
  · refine ⟨h.keep k hm hy, ?_, h9, h10, he⟩
    exact hp.keep hm (by rw [k.gpr .a0 (by decide)])

/-- Through stores of the frame's words but its fixed ones, a finished search
with the words stored. -/
theorem SearchLive.done_after {p : SearchPublic} {original s t : State} {used remaining : Nat}
    {result : PrimeSearchResult} (h : SearchLive p original used remaining s)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 20)
    (hfix : ∀ e ∈ values, e.1 ≠ 1 ∧ e.1 ≠ 2 ∧ e.1 ≠ 4 ∧ e.1 ≠ 7 ∧ e.1 ≠ 18)
    (hm : t.mem = writeFrame s.mem p.F values) {rs : List Reg} (kt : KeepS rs s t)
    (hrs : ∀ r ∈ preserved, r ∉ rs)
    (h0 : frameValue values 0 (word s.mem p.F (8 * 0)) = BitVec.ofNat 64 result.remaining)
    (h3 : frameValue values 3 (word s.mem p.F (8 * 3)) = BitVec.ofNat 64 result.requested)
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
    (kt.gpr _ (hrs .s0 (by decide))).trans h.s0,
    fun r hr hn => (kt.gpr r (hrs r hr)).trans (h.saved r hr hn),
    ?_, ?_, ?_, ?_, ?_, by rw [hw 0 (by decide)]; exact h0, by rw [hw 3 (by decide)]; exact h3,
    by rw [hw 16 (by decide)]; exact h16, by rw [hw 17 (by decide)]; exact h17, by rw [hbytes]; exact hout⟩
  · exact (hkeep 4 (by decide) fun e he => (hfix e he).2.2.1.symm).trans h.savedS0
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
    (h10 : s.gpr .t2 = BitVec.ofNat 64 (candUsed p original used)) :
    WP isa (.block accept) s (SearchDone p original final) := by
  obtain ⟨h, tr, hfinal⟩ := h
  have hs := h.frame_st
  have h16 := h.slot (j := 16) (v := BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h16
  have hacc : WP isa (.block accept) s fun t =>
      t.mem = writeFrame s.mem p.F (acceptValues used (candUsed p original used)) ∧
        KeepS [.t2, .t3] s t := by
    refine WP.keep' [.t2, .t3] ?_ (by decide)
    unfold accept terminal writeFrame acceptValues terminalValues
    simp only [List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil]
    have ha := h.frame_al'
    have ha0 : (p.F + BitVec.ofNat 64 0).toNat % 8 = 0 := ha 0 (by decide) (by decide)
    brun [ldf, stf, h.s0, h10, h16, exec_li, h.frame_ld' 128 (by decide), hs 0 (by decide), hs 24 (by decide),
      hs 128 (by decide), hs 136 (by decide), off, ha0, ha 24 (by decide) (by decide),
      ha 128 (by decide) (by decide), ha 136 (by decide) (by decide)]
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
  rw [← h.input.2]; exact h.input.base.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ltu_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (if BitVec.ofNat 64 a < BitVec.ofNat 64 b then (1 : BitVec 64) else 0) =
      BitVec.ofNat 64 (if a < b then 1 else 0) := by
  have : (BitVec.ofNat 64 a < BitVec.ofNat 64 b) ↔ a < b := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : a < b
  · simp only [this, h, ↓reduceIte]; rfl
  · simp only [this, h, ↓reduceIte]; rfl

theorem sel_max (x y : Nat) :
    (BitVec.ofNat 64 x ^^^ BitVec.ofNat 64 y) &&& (0#64 - BitVec.ofNat 64 (if x < y then 1 else 0)) ^^^
      BitVec.ofNat 64 x = BitVec.ofNat 64 (max x y) := by
  by_cases h : x < y
  · simp only [h, ↓reduceIte]
    rw [show (0#64 - BitVec.ofNat 64 1) = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      BitVec.xor_comm (BitVec.ofNat 64 x), BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero,
      Nat.max_eq_right (by omega)]
  · simp only [h, ↓reduceIte]
    rw [show (0#64 - BitVec.ofNat 64 0) = 0#64 by decide, BitVec.and_zero, BitVec.zero_xor,
      Nat.max_eq_left (by omega)]

theorem sel_min (x y : Nat) :
    (BitVec.ofNat 64 x ^^^ BitVec.ofNat 64 y) &&& (0#64 - BitVec.ofNat 64 (if x < y then 1 else 0)) ^^^
      BitVec.ofNat 64 y = BitVec.ofNat 64 (min x y) := by
  by_cases h : x < y
  · simp only [h, ↓reduceIte]
    rw [show (0#64 - BitVec.ofNat 64 1) = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, Nat.min_eq_left (by omega)]
  · simp only [h, ↓reduceIte]
    rw [show (0#64 - BitVec.ofNat 64 0) = 0#64 by decide, BitVec.and_zero, BitVec.zero_xor,
      Nat.min_eq_right (by omega)]

/-- The next tape's length, with the octets left in `t2` and the budget in
`t3`. -/
theorem request_value {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (h10 : s.gpr .t2 = BitVec.ofNat 64 (p.randLen - used))
    (h11 : s.gpr .t3 = BitVec.ofNat 64 (primeEntropy p.len)) :
    WP isa (.block (request.take 15)) s fun t =>
      (t.gpr .t6 = BitVec.ofNat 64 (primeRequest p.len (p.randLen - used)) ∧ t.mem = s.mem) ∧
        KeepS [.t0, .t5, .t6, .t4] s t := by
  have hf := h.callFacts
  have hL : p.len ≤ 512 := hf.len.2.1
  have hcap := h.cap_le
  have hE : primeEntropy p.len < 2 ^ 32 := by unfold primeEntropy; omega
  have hv1 := h.slot (j := 1) (v := BitVec.ofNat 64 p.len) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv1
  have e16 : BitVec.ofNat 64 p.len <<< 4 = BitVec.ofNat 64 (p.len * 2 ^ 4) :=
    SearchInit.shl_ofNat _ _ (by omega)
  have hA : p.randLen - used ≤ primeEntropy p.len := by omega
  have m1 := sel_max (p.randLen - used) (p.len * 2 ^ 4)
  have e2 : BitVec.ofNat 64 (max (p.randLen - used) (p.len * 2 ^ 4)) +
      BitVec.ofNat 64 (max (p.randLen - used) (p.len * 2 ^ 4)) =
      BitVec.ofNat 64 (2 * max (p.randLen - used) (p.len * 2 ^ 4)) := by
    rw [← BitVec.ofNat_add, Nat.two_mul]
  have m2 := sel_min (2 * max (p.randLen - used) (p.len * 2 ^ 4)) (primeEntropy p.len)
  refine WP.keep' [.t0, .t5, .t6, .t4] ?_ (by decide)
  unfold request sel
  simp only [Bool.false_eq_true, ite_true, ite_false, List.cons_append, List.nil_append, List.take_succ_cons,
    List.take_zero]
  brun [ldf, h.s0, hv1, h.frame_ld' 8 (by decide), h.frame_al' 8 (by decide) (by decide), exec_li, h10, h11, e16,
    ltu_ofNat (show p.randLen - used < 2 ^ 64 by omega) (show p.len * 2 ^ 4 < 2 ^ 64 by omega),
    m1, e2,
    ltu_ofNat (show 2 * max (p.randLen - used) (p.len * 2 ^ 4) < 2 ^ 64 by omega)
      (show primeEntropy p.len < 2 ^ 64 by omega), m2]
  unfold primeRequest Spec.Entropy.request
  congr 2
  omega

def requestValues (p : SearchPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(3, BitVec.ofNat 64 (primeRequest p.len (p.randLen - used))), (17, 0)]

/-- `request`, with the octets left in `t2` and the budget in `t3`. -/
theorem request_ok {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (h10 : s.gpr .t2 = BitVec.ofNat 64 (p.randLen - used))
    (h11 : s.gpr .t3 = BitVec.ofNat 64 (primeEntropy p.len)) :
    WP isa (.block request) s fun t =>
      t.mem = writeFrame s.mem p.F (requestValues p used) ∧ KeepS [.t0, .t5, .t6, .t4] s t := by
  rw [show request = request.take 15 ++ request.drop 15 from (List.take_append_drop _ _).symm,
    WP.block_append_iff]
  refine VG.RISCV64.WP.mono_syms (request_value h h10 h11) fun v ⟨⟨hv7, hmv⟩, kv⟩ hyv => ?_
  have hv := h.keep kv hmv hyv
  have hs := hv.frame_st
  refine WP.mono (WP.keep' [.t4] (Q := fun t =>
    t.mem = writeFrame v.mem p.F (requestValues p used)) ?_
      (by decide)) fun t ⟨hm, kt⟩ => ⟨by rw [hm, hmv], (kv.trans kt).mono⟩
  unfold request sel writeFrame requestValues
  simp only [Bool.false_eq_true, ite_true, ite_false, List.cons_append, List.nil_append, List.drop_succ_cons,
    List.drop_zero, List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, hv.s0, hv7, exec_li, hs 24 (by decide), hs 136 (by decide), off,
    hv.frame_al' 24 (by decide) (by decide), hv.frame_al' 136 (by decide) (by decide)]
  rfl

/-- The short tape's guard: whether the octets left reach the budget. -/
theorem short_guard {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (.block [ldf .t2 13, ldf .t3 2, .sltu .t4 .t2 .t3]) s fun t =>
      (((t.gpr .t2 = BitVec.ofNat 64 (p.randLen - used) ∧ t.gpr .t3 = BitVec.ofNat 64 (primeEntropy p.len) ∧
        t.mem = s.mem) ∧ KeepS [.t2, .t3, .t4] s t) ∧ t.syms = s.syms) ∧
        isa.eval (.zero .t4) t = some (decide (primeEntropy p.len ≤ p.randLen - used)) := by
  have hf := h.callFacts
  have hL : p.len ≤ 512 := hf.len.2.1
  have hv2 := h.slot (j := 2) (v := BitVec.ofNat 64 (primeEntropy p.len)) (by simp [SearchPublic.headers])
  have hv13 := h.slot (j := 13) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2 hv13
  have hcap := h.cap_le
  have hE : primeEntropy p.len < 2 ^ 63 := by unfold primeEntropy; omega
  have hs := ltu_ofNat (a := p.randLen - used) (b := primeEntropy p.len) (by omega) (by omega)
  refine WP.mono (WP.keepS [.t2, .t3, .t4] (Q := fun t =>
    (t.gpr .t2 = BitVec.ofNat 64 (p.randLen - used) ∧ t.gpr .t3 = BitVec.ofNat 64 (primeEntropy p.len) ∧
      t.mem = s.mem) ∧
    isa.eval (.zero .t4) t = some (decide (primeEntropy p.len ≤ p.randLen - used))) ?_
    (by decide)) fun _ ⟨⟨⟨hv, he⟩, k⟩, hy⟩ => ⟨⟨⟨hv, k⟩, hy⟩, he⟩
  brun [ldf, h.s0, hv2, hv13, h.frame_ld' 16 (by decide), h.frame_ld' 104 (by decide),
    h.frame_al' 16 (by decide) (by decide), h.frame_al' 104 (by decide) (by decide), hs]
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self]
  by_cases hb : p.randLen - used < primeEntropy p.len
  · simp only [hb, ↓reduceIte, show ¬primeEntropy p.len ≤ p.randLen - used by omega, decide_false]
    decide
  · simp only [hb, ↓reduceIte, show primeEntropy p.len ≤ p.randLen - used by omega, decide_true]
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
  refine WP.seq (WP.mono (short_guard h) fun u ⟨⟨⟨⟨h10, h11, hmu⟩, ku⟩, hyu⟩, he⟩ => ?_)
  have hu := h.keep ku hmu hyu
  refine WP.ite _ he (fun hb => ?_) (fun hb => ?_)
  · have hb := of_decide_eq_true hb
    rw [ite_eq_left_of_eq_true _ _ (eq_true hb)] at hfinal
    exact search_exhausted hu (by rw [hfinal]; rfl)
  · have hb := of_decide_eq_false hb
    rw [ite_eq_right_of_eq_false _ _ (eq_false hb)] at hfinal
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
    (hm : t.mem = writeFrame s.mem p.F values) (hy : t.syms = s.syms) {rs : List Reg} (kt : KeepS rs s t)
    (hrs : ∀ r ∈ preserved, r ∉ rs)
    (hother : ∀ e ∈ values, e.1 = 0 ∨ e.1 = 12 ∨ e.1 = 13 ∨ e.1 = 16 ∨ e.1 = 17)
    (hnew : ∀ e ∈ p.headers used' remaining', e.1 = 0 ∨ e.1 = 12 ∨ e.1 = 13 ∨ e.1 = 16 →
      frameValue values e.1 (word s.mem p.F (8 * e.1)) = e.2) :
    SearchLive p original used' remaining' t := by
  refine h.update hu hk values hb h4 hm hy kt hrs ?_
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

/-- `advance` past `u` octets (`t2`), and whether the status (`t1`) was 2. -/
theorem advance_ok {p : SearchPublic} {original s : State} {used remaining u : Nat}
    (h : SearchLive p original used remaining s) (h10 : s.gpr .t2 = BitVec.ofNat 64 u) :
    WP isa (.block advance) s fun t =>
      (t.mem = writeFrame s.mem p.F (advanceValues p used u) ∧
        isa.eval (.zero .t5) t = some (s.gpr .t1 - BitVec.ofNat 64 2 == 0)) ∧
        KeepS [.t3, .t4, .t5, .t6] s t := by
  have hs := h.frame_st
  have h12 := h.slot (j := 12) (v := p.rp + BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  have h13 := h.slot (j := 13) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [SearchPublic.headers])
  have h16 := h.slot (j := 16) (v := BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h12 h13 h16
  refine WP.keep' [.t3, .t4, .t5, .t6] ?_ (by decide +kernel)
  unfold advance writeFrame advanceValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.s0, h10, h.frame_ld' 96 (by decide), h.frame_ld' 104 (by decide),
    h.frame_ld' 128 (by decide), h12, h13, h16, hs 96 (by decide), hs 104 (by decide), hs 128 (by decide),
    hs 136 (by decide), off, exec_li, h.frame_al' 96 (by decide) (by decide), h.frame_al' 104 (by decide) (by decide),
    h.frame_al' 128 (by decide) (by decide), h.frame_al' 136 (by decide) (by decide)]
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self]

theorem count_ok {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (.block count) s fun t =>
      t.mem = writeFrame s.mem p.F [(0, BitVec.ofNat 64 remaining - BitVec.ofNat 64 1)] ∧
        KeepS [.t3] s t := by
  have hs := h.frame_st
  have h0 := h.slot (j := 0) (v := BitVec.ofNat 64 remaining) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h0
  refine WP.keep' [.t3] ?_ (by decide)
  unfold count writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.s0, h.frame_ld' 0 (by decide), h0, hs 0 (by decide), off,
    h.frame_al' 0 (by decide) (by decide)]

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
    (h9 : s.gpr .t1 = BitVec.ofNat 64 (if x = .close then 2 else 3))
    (h10 : s.gpr .t2 = BitVec.ofNat 64 (candUsed p original used)) :
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
    refine WP.seq (VG.RISCV64.WP.mono_syms (advance_ok h h10) fun v ⟨⟨hmv, hev⟩, kv⟩ hyv => ?_)
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
        hmv hyv kv (by decide) (fun e he => (hbound e he).2.2) ?_
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
      refine VG.RISCV64.WP.mono_syms (count_ok hvl) fun w ⟨hmw, kw⟩ hyw => ?_
      have hb0 : ∀ e ∈ [(0, BitVec.ofNat 64 remaining - BitVec.ofNat 64 1)], e.1 < 20 ∧ 4 ≠ e.1 ∧
          (e.1 = 0 ∨ e.1 = 12 ∨ e.1 = 13 ∨ e.1 = 16 ∨ e.1 = 17) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro _ rfl; dsimp only; decide
      have hrem : remaining < 2 ^ 64 :=
        Nat.lt_of_le_of_lt h.remaining_le (by rw [← h.input.2]; exact BitVec.isLt _)
      have hwl : SearchLive p original (used + candUsed p original used) (remaining - 1) w := by
        refine hvl.moved hu' (by have := h.remaining_le; omega) _ (fun e he => (hb0 e he).1)
          (fun e he => (hb0 e he).2.1) hmw hyw kw (by decide) (fun e he => (hb0 e he).2.2) ?_
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
  (isa.eval (.zero .t1) t = some true ∧ ContinuePost p original final used remaining t) ∨
    (isa.eval (.zero .t1) t = some false ∧ ¬Continues p original used remaining ∧ SearchDone p original final t)

theorem iter_guard {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (.block [ldf .t1 0]) s fun t =>
      ((isa.eval (.zero .t1) t = some (decide (remaining = 0)) ∧ t.mem = s.mem) ∧ KeepS [.t1] s t) ∧
        t.syms = s.syms := by
  have h0 := h.slot (j := 0) (v := BitVec.ofNat 64 remaining) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h0
  have hz : (BitVec.ofNat 64 remaining == 0) = decide (remaining = 0) :=
    ofNat_beq_zero (Nat.lt_of_le_of_lt h.remaining_le (by rw [← h.input.2]; exact BitVec.isLt _))
  refine WP.keepS [.t1] ?_ (by decide)
  brun [ldf, h.s0, h.frame_ld' 0 (by decide), h0, h.frame_al' 0 (by decide) (by decide)]
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self, hz]

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
    WP isa (.block [ldf .t1 17, .addi .t1 .t1 (-4)]) s (LoopStep p original final used remaining) := by
  have hregs : s.gpr .s0 = p.F ∧ ∃ o : State, SearchInput p o ∧ s.wr = p.frame :: o.wr := by
    rcases h with ⟨-, -, _, _, -, ⟨hi, -⟩, -⟩ | ⟨-, -, hd⟩
    · exact ⟨hi.s0, _, hi.input, hi.wr⟩
    · exact ⟨hd.s0, _, hd.input, hd.wr⟩
  obtain ⟨hs0, o, hi, hw⟩ := hregs
  have scr := hi.frame_scr hw
  have hl : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 136) 8 :=
    let ⟨r, hr, hc⟩ := scr.st (d := 136) (by decide); ⟨r, List.mem_append_right _ hr, hc⟩
  refine VG.RISCV64.WP.mono_syms (WP.keep' [.t1] (Q := fun t =>
    isa.eval (.zero .t1) t = some (word s.mem p.F (8 * 17) - BitVec.ofNat 64 4 == 0) ∧ t.mem = s.mem) (by
      brun [ldf, hs0, hl, scr.al8 (d := 136) (by decide) (by decide)]
      refine (eval_zero _ _).trans ?_
      rw [RegUpd.gpr_write_self]) (by decide)) fun t ⟨⟨he, hm⟩, k⟩ hy => ?_
  rw [sub4_beq] at he
  rcases h with ⟨h17, hc⟩ | ⟨h17, hn, hd⟩
  · exact .inl ⟨by rw [he, h17]; rfl, hc.keep k hm hy⟩
  · exact .inr ⟨by rw [he]; simp only [beq_eq_false_iff_ne.mpr h17], hn, hd.keep k hm⟩

theorem search_iteration (c : Cand) {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    {used remaining : Nat} (h : SearchIter p original final used remaining s) :
    WP isa (iteration c.call) s (LoopStep p original final used remaining) := by
  unfold iteration
  refine WP.seq (WP.mono (iter_guard h.1) fun u ⟨⟨⟨he, hmu⟩, ku⟩, hyu⟩ => ?_)
  have hu : SearchIter p original final used remaining u := ⟨h.1.keep ku hmu hyu, h.2⟩
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
    WP isa (.loop (iteration c.call) (.zero .t1)) s (SearchDone p original final) := by
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

theorem iteration_sdepth (c : Cand) : sdepth (iteration c.call) ≤ 320 := by
  have := c.stack
  simp only [iteration, candidateRun, exhausted, zeroOut, classify, short, reject,
    Impl.Bignum.RISCV64.countLoop, sdepth, Cand.call, Instr.frameBytes]
  omega

/-- A finished search, through code that keeps what it states. -/
theorem SearchDone.of_eq {p : SearchPublic} {original s t : State} {r : PrimeSearchResult}
    (h : SearchDone p original r s) (hg : ∀ reg ∈ preserved, t.gpr reg = s.gpr reg) (hm : t.mem = s.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : SearchDone p original r t := by
  refine ⟨h.input, hrd.trans h.rd, hwr.trans h.wr, (hg .s0 (by decide)).trans h.s0,
    fun reg hr h31 => (hg reg hr).trans (h.saved reg hr h31), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  exacts [h.savedS0, h.usedPtr, h.stp, h.len, h.cap, h.remaining, h.request, h.used, h.status, h.output]

theorem F_16 (p : SearchPublic) : p.F - 16 = p.sp - BitVec.ofNat 64 176 := by
  rw [SearchPublic.F, BitVec.sub_sub]; rfl

theorem search_body (c : Cand) {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hx : t.gpr .s0 = p.F) (hm : t.mem = writeFrame s.mem p.F (entryValues s))
    (k : Keep entryRegs (allocd 160 s) t) (htsp : t.sp = p.F) (hy : t.syms = s.syms) :
    WP isa (search c.call) t fun u =>
      SearchDone p s (searchResult s) u ∧ u.gpr .ra = t.gpr .ra ∧ u.sp = p.F := by
  have hl := search_start h hx hm k htsp hy
  have hroom : stackUse ≤ s.sp.toNat := h.base.2.2.1
  have h496 : stackUse = 496 := rfl
  have hsp : 16 ≤ t.sp.toNat := by
    rw [htsp]
    show 16 ≤ (p.sp - BitVec.ofNat 64 160).toNat
    rw [h.sp_eq, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
    simp only [BitVec.toNat_ofNat]; omega
  unfold search
  refine WP.frameRegAny hsp ?_ (WP.mono (search_loop c (search_initial h hl)) fun u hu => ?_)
    (by have := iteration_sdepth c; show sdepth (iteration c.call) + 16 < 2 ^ 64; omega)
  · intro R hR
    rw [k.2.2, alloc_wr h] at hR
    rw [htsp, F_16]
    rcases List.mem_cons.mp hR with rfl | hR
    · have hs := Offset.sep_below p.sp 496 (a := 176) (n := 16) (b := 160) (k := 160) (by decide) (by decide)
        (Or.inl (by decide)) (by decide) (by decide)
      exact fun x hx hy => hs x (Nat.lt_of_succ_le (by simpa only [Region.Contains] using hx))
        (Nat.lt_of_succ_le (by simpa only [Region.Contains, SearchPublic.frame, SearchPublic.F] using hy))
    · rw [h.wr_eq] at hR
      have hd := h.stack_disjoint (r := R) (List.mem_append_left _ hR)
      rw [h.sp_eq]
      exact hd.sub_left (Offset.sub_below s.sp (a := 176) (b := 496) (by decide) (by decide))
  · refine ⟨hu.of_eq (fun reg hr => by
        show (u.write .ra (t.gpr .ra)).gpr reg = _
        rw [RegUpd.gpr_write, ite_eq_right (by revert reg hr; decide)]) rfl rfl rfl,
      RegUpd.gpr_write_self u .ra (t.gpr .ra), htsp⟩
