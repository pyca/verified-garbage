module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Call
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ZeroOut
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets

/-! # One step of the search's loop

After a candidate, the search accepts its prime, asks for more entropy,
gives up, or goes on past it to the next (`search_classify`); with no
counted candidates left it gives up without one (`search_exhausted`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Search

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.Search
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeRequest PrimeSearchResult)

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
  request : word s.mem p.F (8 * 3) = BitVec.ofNat 64 result.requested
  used : word s.mem p.F (8 * 16) = BitVec.ofNat 64 result.used
  status : word s.mem p.F (8 * 17) = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt s.mem p.op p.len =
    match result.outcome with
    | .accepted c => Spec.Rsa.i2osp c p.len
    | _ => List.replicate p.len 0

/-- A loop state's frame words, read. -/
theorem SearchLive.word {p : SearchPublic} {original s : State} {used remaining : Nat}
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
  ⟨h.input, h.rd, h.wr, h.rsp, h.r12, h.saved, h.savedR12,
    h.word (by simp [SearchPublic.headers]), h.word (by simp [SearchPublic.headers]),
    h.word (by simp [SearchPublic.headers]), h.word (by simp [SearchPublic.headers]),
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
    (h.word (by simp [SearchPublic.headers])) (h.word (by simp [SearchPublic.headers]))
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
  · rw [hwv 16 (by decide)]; exact h.word (by simp [SearchPublic.headers])
  · rw [hwv 17 (by decide)]; rfl

end VG.Proof.RsaKeyGen.X86_64.Search
