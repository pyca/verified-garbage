module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Call
import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Entry
import VerifiedGarbage.Proof.Bignum.AArch64.PubFail
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
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
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeRequest PrimeSearchResult)

/-- A finished search, before `finish` stores its results. -/
structure SearchDone (p : SearchPublic) (original : State) (result : PrimeSearchResult) (s : State) :
    Prop where
  input : SearchInput p original
  rd : s.rd = original.rd
  wr : s.wr = p.frame :: original.wr
  sp : s.sp = p.F - 16
  x19 : s.gpr .x19 = p.F
  saved : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x30 → s.gpr r = original.gpr r
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (original.v r).extractLsb' 0 64
  savedX19 : word s.mem p.F 32 = original.gpr .x19
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
  ⟨h.input, h.rd, h.wr, h.sp, h.x19, h.saved, h.vcs, h.savedX19,
    h.slot (by simp [SearchPublic.headers]), h.slot (by simp [SearchPublic.headers]),
    h.slot (by simp [SearchPublic.headers]), h.slot (by simp [SearchPublic.headers]),
    h0, h3, h16, h17, hout⟩

theorem SearchDone.keep {p : SearchPublic} {original s t : State} {result : PrimeSearchResult}
    (h : SearchDone p original result s) {rs : List Reg} (k : Keep rs s t) (hm : t.mem = s.mem)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) : SearchDone p original result t := by
  refine ⟨h.input, k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp,
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

/-- The frame's words but `values`, through stores of them. -/
theorem stores_words (m : Mem) (B : Addr) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 20) {j : Nat} (hj : j < 20) (hnot : ∀ e ∈ values, j ≠ e.1) :
    word (writeFrame m B values) B (8 * j) = word m B (8 * j) := by
  rw [writeFrame_word _ _ _ hb j hj, frameValue_unchanged _ _ _ hnot]

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

end VG.Proof.RsaKeyGen.AArch64.Search
