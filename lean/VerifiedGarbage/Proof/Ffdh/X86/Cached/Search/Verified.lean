module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.Frame
public import VerifiedGarbage.Impl.Ffdh.X86.Cached
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Ffdh.CachedSat
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.Frame
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.Loop
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.Loop
import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.Classify
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.Classify
public import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
public import VerifiedGarbage.Proof.Ffdh.X86.Entry
import VerifiedGarbage.Proof.Ffdh.X86.Cached.AttemptVerified
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.AttemptVerified
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
meta import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.AllocFrame
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
meta import VerifiedGarbage.Proof.Ffdh.X86.Entry
meta import VerifiedGarbage.Impl.Ffdh.X86.Cached
meta import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Rc2.PairMem
meta import VerifiedGarbage.Proof.Framework.X86.Spill
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Ffdh.X86.Cached.Search.CT`, which only this module used -/

section

/-! ### `Ffdh.X86.Cached.Search.Correct`, which only this module used -/

section

/-! # The key search against its contract (x86)

The entry, the loop from its first state and the finish run the search from
the tape's start (`operation_ok`), which is `vettedKeySearch`; so the code meets
`vg_ffdh_generate_key_search`'s contract (`correct`).
-/

@[expose] public section

/-! ## The key search's finish (x86)

From a finished search, `finish` writes the octets consumed to `used` (64
bits), returns the status and restores the caller's `esi` (`finish_ok`):
the state's four public words, `used`, the outputs, the callee-saved
registers and the return address are as the contract asks (`Fin`).
-/

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search
open VG.Proof.Dsa.X86 (argumentPointer)

/-- What the contract asks after a search with the result `r`. -/
structure Fin (o : State) (r : KeySearchResult) (t : State) : Prop where
  eax : t.gpr .eax = BitVec.ofNat 32 r.status
  saved : ∀ q ∈ calleeSaved, t.gpr q = o.gpr q
  ret : t.mem.readW ((o.gpr .esp).setWidth 64) 32 = o.mem.readW ((o.gpr .esp).setWidth 64) 32
  output : Output (ofState o) r t.mem
  policy : Spec.Rsa.wordsAt t.mem (argumentPointer o 12) 4 =
    [BitVec.ofNat 64 r.retries.keys, BitVec.ofNat 64 r.retries.scalars, BitVec.ofNat 64 (arg o 7).toNat,
      BitVec.ofNat 64 (if r.status = 0 then (arg o 7).toNat else 0)]
  used : Spec.Rsa.wordsAt t.mem (argumentPointer o 4) 1 = [BitVec.ofNat 64 r.used]

theorem Done.st {o s : State} {r : KeySearchResult} (h : Done (ofState o) o r s) :
    St o doneDs (doneF (ofState o) (o.gpr .esi) r) s :=
  ⟨h.input.1, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, h.words⟩

/-- A 64-bit word of two 32-bit halves, the high one zero. -/
theorem word64 {m : Mem} {a : Addr} {k : Nat} (hk : k < 2 ^ 32) (lo : m.readW a 32 = BitVec.ofNat 32 k)
    (hi : m.readW (a + BitVec.ofNat 64 4) 32 = 0) : m.readW a 64 = BitVec.ofNat 64 k := by
  rw [Proof.Rc2.Word32.read64_pair, lo, hi]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  rw [Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega_using [hk])]

/-- The return address, apart from every region the run writes. -/
theorem ret_apart {o : State} (A : KeySearchABI o) : ∀ r ∈ frameR o, (retR o).Disjoint r := by
  have h1 : 228 ≤ (o.gpr .esp).toNat := A.stackLow
  have hl : (retR o).Disjoint (lowR o) := by
    show Region.Disjoint ⟨(o.gpr .esp).setWidth 64, 4⟩ ⟨(o.gpr .esp).setWidth 64 - BitVec.ofNat 64 228, 228⟩
    exact Offset.base_disjoint_below _ (by omega_using [])
  exact apart A A.retX A.retY A.retU A.retB A.retS A.retA hl

/-- A word of the state at offset `d`, as `wordsAt` addresses it. -/
theorem st_addr {o : State} (A : KeySearchABI o) {d : Nat} (hd : d + 4 ≤ 128) :
    addr (arg o 12) d = argumentPointer o 12 + BitVec.ofNat 64 d := Spill.addr_eq_of A.sBound hd

theorem finish_ok {o s : State} {r : KeySearchResult} (h : Done (ofState o) o r s) :
    WP isa (.block finish) s (Fin o r) := by
  have S := h.st
  have A := h.input.1
  have hA : Aligned doneDs := by decide
  have hS := A.sBound
  have hub := A.uBound
  obtain ⟨hk, hc, hu⟩ := h.small
  have hR : (ofState o).randLen < 2 ^ 32 := (arg o 9).isLt
  unfold finish
  refine S.ld (Or.inr (Or.inl rfl)) (d := upOff) (by decide) (by decide) fun t₁ S₁ g₁ _ _ m₁ => ?_
  refine S₁.ld (Or.inl rfl) (d := usedOff) (by decide) (by decide) fun t₂ S₂ g₂ o₂ _ m₂ => ?_
  have ec : t₂.gpr .ecx = arg o 4 := by rw [o₂ .ecx (by decide), g₁]; rfl
  have uIn : ∀ t : State, t.wr = o.wr → ∀ d, d + 4 ≤ 8 →
      InRegions t.wr (argumentPointer o 4 + BitVec.ofNat 64 d) 4 := fun t ht d hd =>
    ⟨uR o, by rw [ht, A.wr]; simp, Offset.contains_base _ hd (by omega_using [hd])⟩
  refine wp_storeS (show t₂.ea (at_ .ecx 0) = argumentPointer o 4 + BitVec.ofNat 64 0 by
      show (t₂.gpr .ecx + BitVec.ofNat 32 0).setWidth 64 = _; rw [ec]; exact addr_eq (by omega_using []))
    (uIn t₂ S₂.wr 0 (by decide)) fun t₃ M₃ => ?_
  refine wp_movi fun t₄ U₄ => ?_
  refine wp_storeS (show t₄.ea (at_ .ecx 4) = argumentPointer o 4 + BitVec.ofNat 64 4 by
      show (t₄.gpr .ecx + BitVec.ofNat 32 4).setWidth 64 = _
      rw [U₄.other _ (by decide), M₃.gpr, ec]; exact addr_eq (by omega_using [hub]))
    (by rw [U₄.wr, M₃.wr]; exact uIn t₂ S₂.wr 4 (by decide)) fun t₅ M₅ => ?_
  -- The stores at `used`.
  have mem₅ : t₅.mem = (t₂.mem.writeW (argumentPointer o 4 + BitVec.ofNat 64 0) (BitVec.ofNat 32 r.used)).writeW
      (argumentPointer o 4 + BitVec.ofNat 64 4) (0 : BitVec 32) := by
    rw [M₅.mem, U₄.gpr, U₄.mem, M₃.mem, g₂]; rfl
  have fu : Frame [uR o] t₂.mem t₅.mem := by
    rw [mem₅]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by omega_using []))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by omega_using []))
  have S₅ : St o doneDs (doneF (ofState o) (o.gpr .esi) r) t₅ := by
    refine ⟨A, M₅.rd.trans (U₄.rd.trans (M₃.rd.trans S₂.rd)), M₅.wr.trans (U₄.wr.trans (M₃.wr.trans S₂.wr)),
      ?_, ?_, fun q hq hne => ?_, S₂.frame.trans (fu.mono fun r hr => ?_), S₂.words.frame hS hA fu fun r hr => ?_⟩
    · rw [M₅.gpr, U₄.other _ (by decide), M₃.gpr, S₂.esp]
    · rw [M₅.gpr, U₄.other _ (by decide), M₃.gpr, S₂.esi]
    · rw [M₅.gpr, U₄.other _ (saved_ne (Or.inl rfl) hq), M₃.gpr, S₂.saved q hq hne]
    · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ (by rw [A.wr]; simp)
    · simp only [List.mem_singleton] at hr; subst hr; exact A.us.symm
  refine S₅.ld (Or.inl rfl) (d := statusOff) (by decide) (by decide) fun t₆ S₆ g₆ o₆ _ m₆ => ?_
  refine wp_ldm S₆.esi (S₆.rIn (d := savedOff) (by decide)) fun t₇ U₇ => WP.block_nil ?_
  have m₇ : t₇.mem = t₅.mem := by rw [U₇.mem, m₆]
  have m₂ : t₂.mem = s.mem := by rw [m₂, m₁]
  refine ⟨?_, fun q hq => ?_, ?_, ?_, ?_, ?_⟩
  · rw [U₇.other _ (by decide), g₆]; simp [doneF, statusOff]
  · by_cases hq' : q = .esi
    · subst hq'; rw [U₇.gpr, S₆.words.get (d := savedOff) (by decide)]; simp [doneF, savedOff]
    · rw [U₇.other _ hq', S₆.saved q hq hq']
  · rw [m₇]; exact S₅.frame.readW (Region.contains_self _ _) (ret_apart A) (by decide)
  · have out := h.output
    have kx : Spec.Rsa.bytesAt t₇.mem (argumentPointer o 0) (arg o 7).toNat =
        Spec.Rsa.bytesAt s.mem (argumentPointer o 0) (arg o 7).toNat := by
      rw [m₇, ← m₂]
      exact bytes_frame fu (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [← xR_eq A]; exact A.xu) (by omega_using [])
    have ky : Spec.Rsa.bytesAt t₇.mem (argumentPointer o 2) (arg o 7).toNat =
        Spec.Rsa.bytesAt s.mem (argumentPointer o 2) (arg o 7).toNat := by
      rw [m₇, ← m₂]
      exact bytes_frame fu (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [← yR_eq A]; exact A.yu) (by omega_using [])
    unfold Output at out ⊢
    split at out <;> exact ⟨kx.trans out.1, ky.trans out.2⟩
  · have W : ∀ d ∈ doneDs, t₇.mem.readW (addr (arg o 12) d) 32 = doneF (ofState o) (o.gpr .esi) r d := by
      intro d hd; rw [m₇]; exact S₅.words.get hd
    have hl : (arg o 7).toNat < 2 ^ 32 := (arg o 7).isLt
    unfold Spec.Rsa.wordsAt
    rw [show List.range 4 = [0, 1, 2, 3] from rfl]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨word64 (by omega_using [hk]) ?_ ?_, word64 (by omega_using [hc]) ?_ ?_, word64 hl ?_ ?_, word64 (by split <;> omega_using []) ?_ ?_⟩
    · rw [← st_addr A (d := 0) (by decide), W 0 (by decide)]; simp [doneF]
    · rw [Offset.add_add, ← st_addr A (d := 4) (by decide), W 4 (by decide)]; simp [doneF]
    · rw [← st_addr A (d := 8) (by decide), W 8 (by decide)]; simp [doneF]
    · rw [Offset.add_add, ← st_addr A (d := 12) (by decide), W 12 (by decide)]; simp [doneF]
    · rw [← st_addr A (d := 16) (by decide), W 16 (by decide)]; simp [doneF, ofState]
    · rw [Offset.add_add, ← st_addr A (d := 20) (by decide), W 20 (by decide)]; simp [doneF]
    · rw [← st_addr A (d := 24) (by decide), W 24 (by decide)]; simp [doneF, ofState]
    · rw [Offset.add_add, ← st_addr A (d := 28) (by decide), W 28 (by decide)]; simp [doneF]
  · unfold Spec.Rsa.wordsAt
    rw [show List.range 1 = [0] from rfl]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    rw [m₇, mem₅]
    refine word64 (by omega_using [hu, hR]) ?_ ?_
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
        show (8 * 0 : Nat) = 0 from rfl, Mem.readW_writeW_self32]
    · rw [show (8 * 0 : Nat) = 0 from rfl, Offset.add_add, Mem.readW_writeW_self32]

end VG.Proof.Ffdh.X86.Cached.Search

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Spec.Ffdh
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The search the contract specifies. -/
abbrev searchOf (o : State) : KeySearchResult :=
  vettedKeySearch (ofState o).a (ofState o).len ⟨(ofState o).keys, (ofState o).scalars⟩ (randOf o)

theorem tail_zero (o : State) :
    Same ((ofState o).tail (randOf o) 0 (ofState o).keys (ofState o).scalars) (searchOf o) := by
  simp only [Same, KPub.tail, keyTail, after, List.drop_zero, Nat.zero_add]
  exact ⟨rfl, rfl⟩

theorem operation_ok {o : State} (A : KeySearchABI o) :
    WP isa Impl.Ffdh.X86.Cached.Search.code o (Fin o (searchOf o)) := by
  unfold Impl.Ffdh.X86.Cached.Search.code
  refine WP.seq (WP.mono (entry_ok A) fun s hs => ?_)
  refine WP.seq (WP.mono (loop_ok hs) fun t ht => ?_)
  exact finish_ok (ht.congr (tail_zero o))

theorem correct (s : State) (h : (Spec.Ffdh.cachedKeySearchContract abi stack).pre s) :
    ∃ trace t, Exec isa Impl.Ffdh.X86.Cached.Search.code s trace t ∧ abiPreserved s t ∧
      (Spec.Ffdh.cachedKeySearchContract abi stack).post s t := by
  obtain ⟨trace, t, E, F⟩ := operation_ok (keySearchABI_of h)
  refine ⟨trace, t, E, ⟨F.saved, F.ret⟩, ?_⟩
  have out := F.output
  unfold Output at out
  sig_post [Spec.Ffdh.cachedKeySearchContract, Spec.Ffdh.cachedKeySearchSig, Spec.Ffdh.keySearchSig, abi, argSlots, argVal, argBytes]
  refine ⟨?_, out, F.policy, F.used⟩
  rw [BitVec.setWidth_append_eq_right, F.eax, toNat_ofNat_lt (by have := status_le (searchOf s); omega_using [this])]
  rfl

end VG.Proof.Ffdh.X86.Cached.Search

end

end

/-! ### `Ffdh.X86.Cached.Search.CTLoop`, which only this module used -/

section

/-! ### `Ffdh.X86.Cached.Search.CTClassify`, which only this module used -/

section

/-! ### `Ffdh.X86.Cached.Search.CTAttempt`, which only this module used -/

section

/-! ### `Ffdh.X86.Cached.Search.CTZero`, which only this module used -/

section

/-! # Two runs of the key search's exits (x86)

Two runs relate by public words (`At`): the public descriptor, and the
state's words at offsets that hold the same in both (never the caller's
`esi`). The taint analysis checks a piece of code from `esi` and `esp`,
which they fix; a piece that addresses memory through words loaded from
the state is checked with those registers fixed too, after a piece that
loads them (`zeroOut_ct`). The exits without an attempt leak nothing but
what those words fix (`exhausted_ct`, `request_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)

/-- Public words: the descriptor, offsets and their words. -/
abbrev Pw := KPub × List Nat × (Nat → BitVec 32)

/-- A run's state whose words at the offsets `a.2.1` hold `a.2.2`. -/
def At (a : Pw) (s : State) : Prop := ∃ o, ofState o = a.1 ∧ St o a.2.1 a.2.2 s

theorem at_pins : Pins At [.esi, .esp] := by
  intro a s₁ s₂ ⟨o₁, e₁, h₁⟩ ⟨o₂, e₂, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.esi, h₂.esi]; show (ofState o₁).S = (ofState o₂).S; rw [e₁, e₂]
  · rw [h₁.esp, h₂.esp]; show (ofState o₁).sp = (ofState o₂).sp; rw [e₁, e₂]

/-- A loop state's public words: all it keeps but the caller's `esi`. -/
def pubDs : List Nat := [0, 4, 8, 12, 16, 20, 28, 36, 40, 44, 48, 52, 56, 60, 64, 68, 76]

theorem pubDs_aligned : Aligned pubDs := by decide

theorem liveF_pub (p : KPub) (e e' : BitVec 32) (used keys scalars : Nat) :
    ∀ d ∈ pubDs, liveF p e used keys scalars d = liveF p e' used keys scalars d := by
  simp only [pubDs, List.mem_cons, List.not_mem_nil, or_false]
  rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rfl

/-- The public words of a loop state. -/
abbrev liveAt (p : KPub) (used keys scalars : Nat) : Pw := (p, pubDs, liveF p 0 used keys scalars)

theorem Live.at {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s) :
    At (liveAt p used keys scalars) s := by
  have S := h.st
  obtain ⟨A, rfl⟩ := h.input
  exact ⟨o, rfl, (S.sub (by decide : ∀ d ∈ pubDs, d ∈ liveDs)).congr (liveF_pub _ _ _ _ _ _)⟩

/-- Public words from which the outputs are zeroed. -/
def ZAt (a : Pw) (s : State) : Prop :=
  At a s ∧ Aligned a.2.1 ∧ xOff ∈ a.2.1 ∧ yOff ∈ a.2.1 ∧ lenOff ∈ a.2.1 ∧ a.2.2 xOff = a.1.xp ∧
    a.2.2 yOff = a.1.yp ∧ a.2.2 lenOff = BitVec.ofNat 32 a.1.len

theorem zeroHead_ok {d : Nat} (hd4 : d + 4 ≤ 128) (a : Pw) (s : State) (h : At a s) (hd : d ∈ a.2.1)
    (hl : lenOff ∈ a.2.1) :
    WP isa (.block [.mov .edx (.mem (st d)), .mov .ecx (.mem (st lenOff)), .mov .eax (.imm 0)]) s fun t =>
      At a t ∧ t.gpr .edx = a.2.2 d ∧ t.gpr .ecx = a.2.2 lenOff := by
  obtain ⟨o, e, S⟩ := h
  refine S.ld (Or.inr (Or.inr rfl)) hd hd4 fun t₁ S₁ g₁ _ _ _ => ?_
  refine S₁.ld (Or.inr (Or.inl rfl)) hl (by decide) fun t₂ S₂ g₂ o₂ _ _ => ?_
  refine wp_movi fun t₃ U₃ => WP.block_nil ⟨⟨o, e, S₂.reg U₃ (Or.inl rfl)⟩, ?_, ?_⟩
  · rw [U₃.other _ (by decide), o₂ _ (by decide), g₁]
  · rw [U₃.other _ (by decide), g₂]

theorem zeroOut_ct {d : Nat} (hd4 : d + 4 ≤ 128) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (hchk : (taint.check (τr [.esi, .esp])
      (.block [.mov .edx (.mem (st d)), .mov .ecx (.mem (st lenOff)), .mov .eax (.imm 0)]) hc).isSome = true) :
    RelCT isa (Two fun a s => At a s ∧ d ∈ a.2.1 ∧ lenOff ∈ a.2.1) (zeroOut d) fun _ _ => True := by
  unfold zeroOut
  refine RelCT.seq (two_piece (Ψ := fun a t => At a t ∧ t.gpr .edx = a.2.2 d ∧ t.gpr .ecx = a.2.2 lenOff)
    [.esi, .esp] (fun a _ _ h₁ h₂ => at_pins a _ _ h₁.1 h₂.1) hchk
    fun a s h => zeroHead_ok hd4 a s h.1 h.2.1 h.2.2) ?_
  refine two_taint [.edx, .ecx, .esi, .esp] (fun a s₁ s₂ h₁ h₂ r hr => ?_) (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | hr
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2, h₂.2.2]
  · exact at_pins a _ _ h₁.1 h₂.1 r (by simpa using hr)

theorem zeroOne_keep {a : Pw} {s : State} (h : ZAt a s) {d : Nat} (hd : d = xOff ∨ d = yOff) :
    WP isa (zeroOut d) s (ZAt a) := by
  obtain ⟨p, ds, f⟩ := a
  obtain ⟨⟨o, e, S⟩, hA, hx, hy, hl, ex, ey, el⟩ := h
  subst e
  have A := S.abi
  have xs : (stR (arg o 12)).Disjoint ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← xR_eq A]; exact A.xs.symm
  have ys : (stR (arg o 12)).Disjoint ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← yR_eq A]; exact A.ys.symm
  have xb : (arg o 0).toNat + (arg o 7).toNat ≤ 2 ^ 32 := by have := A.xBound; rw [A.xLen] at this; exact this
  have yb : (arg o 2).toNat + (arg o 7).toNat ≤ 2 ^ 32 := by have := A.yBound; rw [A.yLen] at this; exact this
  have xin : (⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ : Region) ∈ o.wr := by
    rw [← xR_eq A, A.wr]; exact List.mem_cons_self ..
  have yin : (⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ : Region) ∈ o.wr := by
    rw [← yR_eq A, A.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  rcases hd with rfl | rfl
  · exact WP.mono (S.zeroOne hA ex el hx hl (by decide) xin xs xb) fun u hu =>
      ⟨⟨o, rfl, hu.1⟩, hA, hx, hy, hl, ex, ey, el⟩
  · exact WP.mono (S.zeroOne hA ey el hy hl (by decide) yin ys yb) fun u hu =>
      ⟨⟨o, rfl, hu.1⟩, hA, hx, hy, hl, ex, ey, el⟩

theorem zeroOutputs_ct : RelCT isa (Two ZAt) zeroOutputs fun _ _ => True := by
  unfold zeroOutputs
  refine RelCT.seq (two_post (Ψ := ZAt) (two_map id (fun a s h => ⟨h.1, h.2.2.1, h.2.2.2.2.1⟩)
    (zeroOut_ct (d := xOff) (by decide) (by taint_decide))) fun a s h => zeroOne_keep h (Or.inl rfl)) ?_
  exact two_map id (fun a s h => ⟨h.1, h.2.2.2.1, h.2.2.2.2.1⟩)
    (zeroOut_ct (d := yOff) (by decide) (by taint_decide))

/-- The loop's public data: the descriptor, the octets consumed and the budgets. -/
abbrev Lp := KPub × Nat × Nat × Nat

abbrev Lp.at (q : Lp) : Pw := liveAt q.1 q.2.1 q.2.2.1 q.2.2.2

/-- `terminal 3`'s words. -/
abbrev exhaustedAt (q : Lp) : Pw :=
  (q.1, statusOff :: requestOff :: scalarsOff :: keysOff :: pubDs,
    upd (upd (upd (upd q.at.2.2 keysOff 0) scalarsOff 0) requestOff 0) statusOff (BitVec.ofNat 32 3))

theorem exhausted_ct : RelCT isa (Two fun (q : Lp) s => At q.at s) exhausted fun _ _ => True := by
  unfold exhausted
  refine RelCT.seq (two_piece (Ψ := fun q t => ZAt (exhaustedAt q) t) [.esi, .esp]
    (fun q _ _ h₁ h₂ => at_pins _ _ _ h₁ h₂) (by taint_decide) fun q s h => ?_)
    (two_map exhaustedAt (fun _ _ h => h) zeroOutputs_ct)
  obtain ⟨o, e, S⟩ := h
  refine WP.mono (S.terminal pubDs_aligned 3) fun t ⟨St, _⟩ => ⟨⟨o, e, St⟩,
    show Aligned (statusOff :: requestOff :: scalarsOff :: keysOff :: pubDs) by decide,
    show xOff ∈ statusOff :: requestOff :: scalarsOff :: keysOff :: pubDs by decide,
    show yOff ∈ statusOff :: requestOff :: scalarsOff :: keysOff :: pubDs by decide,
    show lenOff ∈ statusOff :: requestOff :: scalarsOff :: keysOff :: pubDs by decide, ?_, ?_, ?_⟩
  all_goals simp [upd, liveF, xOff, yOff, lenOff, statusOff, requestOff, scalarsOff, keysOff]

/-- `request`'s first block: the request `p_len`, the status 0. -/
theorem St.requestBlock {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    (hl : lenOff ∈ ds) :
    WP isa (.block [.mov .eax (.mem (st lenOff)), .store (st requestOff) .eax, .mov .eax (.imm 0),
      .store (st statusOff) .eax]) s fun t =>
      St o (statusOff :: requestOff :: ds) (upd (upd f requestOff (f lenOff)) statusOff 0) t := by
  refine h.ld (Or.inl rfl) hl (by decide) fun t₁ S₁ g₁ _ _ _ => ?_
  refine S₁.stw hA (d := requestOff) (by decide) (by decide) fun t₂ S₂ G₂ _ _ _ => ?_
  refine wp_movi fun t₃ U₃ => ?_
  have S₃ := S₂.reg U₃ (Or.inl rfl)
  refine S₃.stw (hA.cons (by decide) (by decide)) (d := statusOff) (by decide) (by decide)
    fun t₄ S₄ _ _ _ _ => WP.block_nil ?_
  rw [g₁, U₃.gpr] at S₄
  exact S₄

/-- `request`'s words. -/
abbrev requestAt (q : Lp) : Pw :=
  (q.1, statusOff :: requestOff :: pubDs, upd (upd q.at.2.2 requestOff (q.at.2.2 lenOff)) statusOff 0)

theorem request_ct : RelCT isa (Two fun (q : Lp) s => At q.at s) request fun _ _ => True := by
  unfold request
  refine RelCT.seq (two_piece (Ψ := fun q t => ZAt (requestAt q) t) [.esi, .esp]
    (fun q _ _ h₁ h₂ => at_pins _ _ _ h₁ h₂) (by taint_decide) fun q s h => ?_)
    (two_map requestAt (fun _ _ h => h) zeroOutputs_ct)
  obtain ⟨o, e, S⟩ := h
  refine WP.mono (S.requestBlock pubDs_aligned (show lenOff ∈ pubDs by decide)) fun t St => ⟨⟨o, e, St⟩,
    show Aligned (statusOff :: requestOff :: pubDs) by decide, show xOff ∈ statusOff :: requestOff :: pubDs by decide,
    show yOff ∈ statusOff :: requestOff :: pubDs by decide, show lenOff ∈ statusOff :: requestOff :: pubDs by decide,
    ?_, ?_, ?_⟩
  all_goals simp [upd, liveF, xOff, yOff, lenOff, statusOff, requestOff]

end VG.Proof.Ffdh.X86.Cached.Search

end

end

/-! # Two runs of an attempt (x86)

Two runs with the same public descriptor, octets consumed and budgets, whose
attempts have the same status, pass `vg_ffdh_generate_key` the same
arguments and the same public data (`callee_pub`), so their attempts leak
the same (`attempt_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite argumentPointer)

/-- Two entry states with the same public descriptor have the same arguments but the state's
words. -/
theorem args_eq {o₁ o₂ : State} (e : ofState o₁ = ofState o₂) {i : Nat}
    (hi : i = 0 ∨ i = 2 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨
      i = 14) :
    arg o₁ i = arg o₂ i := by
  have ofn : ∀ {x y : BitVec 32}, x.toNat = y.toNat → x = y := BitVec.eq_of_toNat_eq
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact congrArg KPub.xp e
  · exact congrArg KPub.yp e
  · exact congrArg KPub.up e
  · exact congrArg KPub.dp e
  · exact ofn (congrArg KPub.dlen e)
  · exact ofn (congrArg KPub.len e)
  · exact congrArg KPub.rp e
  · exact ofn (congrArg KPub.randLen e)
  · exact congrArg KPub.B e
  · exact ofn (congrArg KPub.slen e)
  · exact congrArg KPub.S e
  · exact congrArg KPub.C e
  · exact ofn (congrArg KPub.clen e)

theorem callArg_eq {o₁ o₂ : State} (e : ofState o₁ = ofState o₂) (used j : Nat) :
    callArg o₁ used j = callArg o₂ used j := by
  unfold callArg
  rw [args_eq e (i := 0) (by omega_using []), args_eq e (i := 2) (by omega_using []), args_eq e (i := 5) (by omega_using []),
    args_eq e (i := 6) (by omega_using []), args_eq e (i := 7) (by omega_using []), args_eq e (i := 8) (by omega_using []),
    args_eq e (i := 10) (by omega_using []), args_eq e (i := 11) (by omega_using []), args_eq e (i := 13) (by omega_using []),
    args_eq e (i := 14) (by omega_using [])]

theorem callee_pub {o₁ o₂ t₁ t₂ : State} {ds₁ ds₂ : List Nat} {f₁ f₂ : Nat → BitVec 32} {used : Nat}
    (e : ofState o₁ = ofState o₂) (h₁ : Fr o₁ ds₁ f₁ t₁) (h₂ : Fr o₂ ds₂ f₂ t₂)
    (hu : used + (arg o₁ 7).toNat ≤ (arg o₁ 9).toNat) (a₁ : ArgsAt o₁ used 13 t₁.mem) (a₂ : ArgsAt o₂ used 13 t₂.mem)
    (hst : attemptStatus .cached (ofState o₁).a (ofState o₁).len ((randOf o₁).drop used) =
      attemptStatus .cached (ofState o₂).a (ofState o₂).len ((randOf o₂).drop used)) (rd wr : List Region) :
    (Proof.Ffdh.cachedGenerateKeyContract abi Proof.Ffdh.X86.stack).pub (t₁.callEntry.withRegions rd wr)
      (t₂.callEntry.withRegions rd wr) := by
  have A₁ := h₁.abi
  have A₂ := h₂.abi
  have hu₂ : used + (arg o₂ 7).toNat ≤ (arg o₂ 9).toNat := by
    rw [← args_eq e (i := 7) (by omega_using []), ← args_eq e (i := 9) (by omega_using [])]; exact hu
  have sp : o₁.gpr .esp = o₂.gpr .esp := congrArg KPub.sp e
  sig_pub [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi, argSlots, argVal, argBytes]
  refine ⟨by simp only [h₁.esp, h₂.esp, sp], ?_⟩
  have c₁ := fun j (hj : j < 13) => ce_arg A₁ h₁.esp a₁ rd wr hj
  have c₂ := fun j (hj : j < 13) => ce_arg A₂ h₂.esp a₂ rd wr hj
  simp only [c₁ 0 (by decide), c₁ 1 (by decide), c₁ 2 (by decide), c₁ 3 (by decide), c₁ 4 (by decide),
    c₁ 5 (by decide), c₁ 6 (by decide), c₁ 7 (by decide), c₁ 8 (by decide), c₁ 9 (by decide), c₁ 10 (by decide),
    c₁ 11 (by decide), c₁ 12 (by decide),
    c₂ 0 (by decide), c₂ 1 (by decide), c₂ 2 (by decide), c₂ 3 (by decide), c₂ 4 (by decide),
    c₂ 5 (by decide), c₂ 6 (by decide), c₂ 7 (by decide), c₂ 8 (by decide), c₂ 9 (by decide), c₂ 10 (by decide),
    c₂ 11 (by decide), c₂ 12 (by decide)]
  have ca := callArg_eq e used
  refine ⟨?_, ca 0, ca 1, ca 2, ca 3, ca 4, ca 5, ca 6, ca 7, ca 8, ca 9, ca 10, ca 11, ca 12⟩
  rw [ret_eq A₁ h₁.esp, ret_eq A₂ h₂.esp]
  have b₁ := entry_bytes h₁ hu (t₁.unknowns 0)
  have b₂ := entry_bytes h₂ hu₂ (t₂.unknowns 0)
  simp only [callArg, Nat.reduceEqDiff, ↓reduceIte, argumentPointer] at b₁ b₂ ⊢
  rw [b₁.1, b₁.2, b₂.1, b₂.2]
  have hd : (ofState o₁).dom = (ofState o₂).dom := congrArg KPub.dom e
  show List.map _ (ofState o₁).dom ++ [attemptStatus .cached (ofState o₁).a (ofState o₁).len ((randOf o₁).drop used)] =
    List.map _ (ofState o₂).dom ++ [attemptStatus .cached (ofState o₂).a (ofState o₂).len ((randOf o₂).drop used)]
  rw [hd, hst]

/-- Relating two runs for each public datum. -/
theorem two_of {α : Type} {Φ : α → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ a, RelCT isa (fun s₁ s₂ => Φ a s₁ ∧ Φ a s₂) c Q) : RelCT isa (Two Φ) c Q :=
  fun _ _ _ _ _ _ ⟨a, h₁, h₂⟩ e₁ e₂ => h a _ _ _ _ _ _ ⟨h₁, h₂⟩ e₁ e₂

/-- An attempt's public data: the loop's, and the attempt's status. -/
abbrev Ap := Lp × Nat

def AttAt (k : Ap) (s : State) : Prop :=
  ∃ o, Live k.1.1 o k.1.2.1 k.1.2.2.1 k.1.2.2.2 s ∧ k.1.2.1 + k.1.1.len ≤ k.1.1.randLen ∧
    attemptStatus .cached k.1.1.a k.1.1.len ((randOf o).drop k.1.2.1) = k.2

/-- In the attempt's frame. -/
def FrAt (k : Ap) (f : State) : Prop := ∃ s, AttAt k s ∧ f = allocFrame argsBytes s

/-- With the arguments in the frame. -/
def CallAt (k : Ap) (t : State) : Prop :=
  ∃ o, ofState o = k.1.1 ∧ Fr o liveDs (liveF k.1.1 (o.gpr .esi) k.1.2.1 k.1.2.2.1 k.1.2.2.2) t ∧
    ArgsAt o k.1.2.1 13 t.mem ∧ k.1.2.1 + k.1.1.len ≤ k.1.1.randLen ∧
    attemptStatus .cached k.1.1.a k.1.1.len ((randOf o).drop k.1.2.1) = k.2

theorem frAt_pins : Pins FrAt [.esi, .esp] := by
  intro k f₁ f₂ ⟨s₁, ⟨o₁, L₁, _⟩, e₁⟩ ⟨s₂, ⟨o₂, L₂, _⟩, e₂⟩ r hr
  subst e₁ e₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [allocFrame_gpr _ _ (by decide), allocFrame_gpr _ _ (by decide), L₁.esi, L₂.esi]
  · rw [allocFrame_esp, allocFrame_esp, L₁.esp, L₂.esp]

/-- What the callee reads and writes, from the public descriptor. -/
abbrev callRdK (p : KPub) (used : Nat) : List Region :=
  [⟨p.dp.setWidth 64, p.dlen⟩, ⟨(p.rp + BitVec.ofNat 32 used).setWidth 64, p.len⟩, ⟨p.C.setWidth 64, p.clen * 8⟩]
abbrev callWrK (p : KPub) : List Region :=
  [⟨p.xp.setWidth 64, p.len⟩, ⟨p.yp.setWidth 64, p.len⟩, ⟨p.B.setWidth 64, p.slen * 8⟩,
    ⟨p.sp.setWidth 64 - 228#64 + BitVec.ofNat 64 176, 52⟩]

theorem call_ct (k : Ap) :
    RelCT isa (fun t₁ t₂ => CallAt k t₁ ∧ CallAt k t₂)
      (.call "vg_ffdh_generate_key_cached" Impl.Ffdh.X86.Cached.Generate.code) fun _ _ => True := by
  refine RelCT.call Proof.Ffdh.X86.Cached.verified.1 Proof.Ffdh.X86.Cached.verified.2.1
    (callRdK k.1.1 k.1.2.1) (callWrK k.1.1) fun t₁ t₂ ⟨⟨o₁, e₁, F₁, a₁, hu₁, st₁⟩, ⟨o₂, e₂, F₂, a₂, hu₂, st₂⟩⟩ => ?_
  obtain ⟨⟨p, used, keys, scalars⟩, st⟩ := k
  dsimp only at e₁ e₂ F₁ F₂ a₁ a₂ hu₁ hu₂ st₁ st₂ ⊢
  subst e₁
  have r₁ : callRdK (ofState o₁) used = callRd o₁ used := rfl
  have w₁ : callWrK (ofState o₁) = callWr o₁ := rfl
  have r₂ : callRdK (ofState o₂) used = callRd o₂ used := rfl
  have w₂ : callWrK (ofState o₂) = callWr o₂ := rfl
  have c₁ := call_covers (t := t₁) F₁.abi hu₁ F₁.rd F₁.wr
  have hu₂' : used + (arg o₂ 7).toNat ≤ (arg o₂ 9).toNat := by have := hu₂; rw [← e₂] at this; exact this
  have c₂ := call_covers (t := t₂) F₂.abi hu₂' F₂.rd F₂.wr
  have eqR : callRd o₂ used = callRd o₁ used := by rw [← r₁, ← r₂, e₂]
  have eqW : callWr o₂ = callWr o₁ := by rw [← w₁, ← w₂, e₂]
  rw [r₁, w₁]
  rw [eqR, eqW] at c₂
  refine ⟨call_pre F₁.abi hu₁ F₁.esp a₁ F₁.frame, ?_, callee_pub e₂.symm F₁ F₂ hu₁ a₁ a₂ (st₁.trans (by rw [e₂]; exact st₂.symm)) _ _,
    c₁.1, c₁.2, c₂.1, c₂.2, ?_⟩
  · rw [← eqR, ← eqW]
    exact call_pre F₂.abi hu₂' F₂.esp a₂ F₂.frame
  · rw [F₁.esp, F₂.esp, show o₁.gpr .esp = o₂.gpr .esp from (congrArg KPub.sp e₂).symm]

theorem attempt_ct : RelCT isa (Two AttAt) attempt fun _ _ => True := by
  unfold attempt
  refine RelCT.frameAlloc ((RelCT.seq (two_piece (Ψ := CallAt) [.esi, .esp] frAt_pins (by taint_decide)
    fun k f ⟨s, ⟨o, L, hu, st⟩, e⟩ => ?_) (two_of call_ct)).mono
      (fun a b ⟨s₁, s₂, ⟨k, h₁, h₂⟩, e₁, e₂⟩ => ⟨k, ⟨s₁, h₁, e₁⟩, ⟨s₂, h₂, e₂⟩⟩) fun _ _ h => h)
  subst e
  have S := L.st
  obtain ⟨A, e⟩ := L.input
  obtain ⟨⟨p, used, keys, scalars⟩, sta⟩ := k
  dsimp only at e S hu st ⊢
  subst e
  exact WP.mono (arguments_ok S.alloc) fun t ⟨F, a⟩ => ⟨o, rfl, F, a, hu, st⟩

end VG.Proof.Ffdh.X86.Cached.Search

end

end

/-! # Two runs after an attempt (x86)

After attempts with the same status, `classify` branches alike in both
runs, and each of its blocks is checked by the taint analysis from `esi`
and `esp` (`classify_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)

/-- A run's state with the public descriptor `p`. -/
def Any (p : KPub) (s : State) : Prop := ∃ o ds f, ofState o = p ∧ St o ds f s

theorem any_pins {α : Type} {Φ : α → State → Prop} (g : α → KPub) (h : ∀ a s, Φ a s → Any (g a) s) :
    Pins Φ [.esi, .esp] := by
  intro a s₁ s₂ h₁ h₂ r hr
  obtain ⟨o₁, _, _, e₁, S₁⟩ := h a s₁ h₁
  obtain ⟨o₂, _, _, e₂, S₂⟩ := h a s₂ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [S₁.esi, S₂.esi]; show (ofState o₁).S = (ofState o₂).S; rw [e₁, e₂]
  · rw [S₁.esp, S₂.esp]; show (ofState o₁).sp = (ofState o₂).sp; rw [e₁, e₂]

/-- After an attempt with the status `k.2`. -/
def ClsAt (k : Ap) (u : State) : Prop :=
  ∃ o, ofState o = k.1.1 ∧ St o liveDs (liveF k.1.1 (o.gpr .esi) k.1.2.1 k.1.2.2.1 k.1.2.2.2) u ∧
    u.gpr .eax = BitVec.ofNat 32 k.2 ∧ (1 ≤ k.2 ∧ k.2 ≤ 3) ∧ k.1.2.1 + k.1.1.len ≤ k.1.1.randLen

/-- The status in `edx` compared with `j`. -/
def CmpAt (j : Nat) (k : Ap) (t : State) : Prop :=
  Any k.1.1 t ∧ (1 ≤ k.2 ∧ k.2 ≤ 3) ∧ t.gpr .edx = BitVec.ofNat 32 k.2 ∧ isa.eval .e t = some (decide (k.2 = j))

theorem cmp_ok {k : Ap} {t : State} {i : Nat} (h : CmpAt i k t) (j : Nat) (hj : j ≤ 3) :
    WP isa (.block [.alu .cmp .edx (.imm (BitVec.ofNat 32 j))]) t (CmpAt j k) := by
  obtain ⟨⟨o, ds, f, e, S⟩, hk, he, _⟩ := h
  refine wp_cmpi fun t' F _ z => WP.block_nil ⟨⟨o, ds, f, e, S.fupd F⟩, hk, by rw [F.gpr]; exact he, ?_⟩
  exact cmp_status hk.2 hj he z

theorem ne_of {j : Nat} {k : Ap} {s : State} (h : CmpAt j k s) (hf : isa.eval .e s = some false) : k.2 ≠ j := by
  rw [h.2.2.2] at hf
  simpa using hf

/-- A branch never taken: the status is 1, 2 or 3. -/
theorem never {k : Ap} {s : State} (h : CmpAt 3 k s ∧ isa.eval .e s = some false) (h1 : k.2 ≠ 1) (h2 : k.2 ≠ 2) :
    False := by
  obtain ⟨⟨_, hk, _, he⟩, hf⟩ := h
  rw [he] at hf
  simp only [Option.some.injEq, decide_eq_false_iff_not] at hf
  omega_using [h1, h2, hk, hf]

theorem classify_ct : RelCT isa (Two ClsAt) classify fun _ _ => True := by
  unfold classify
  refine RelCT.seq (two_piece (Ψ := CmpAt 1) [.esi, .esp]
    (any_pins (fun k => k.1.1) fun k s ⟨o, e, S, _⟩ => ⟨o, _, _, e, S⟩) (by taint_decide)
    fun k u ⟨o, e, S, he, hk, hr⟩ => ?_) ?_
  · obtain ⟨⟨p, used, keys, scalars⟩, st⟩ := k
    dsimp only at e S he hk hr ⊢
    subst e
    exact advance_ok S hr fun t S' hed _ => wp_cmpi fun t' F _ z => WP.block_nil
      ⟨⟨o, _, _, rfl, S'.fupd F⟩, hk, by rw [F.gpr, hed, he], cmp_status hk.2 (by decide) (hed.trans he) z⟩
  refine two_ite (fun k _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm)
    (two_taint [.esi, .esp] (any_pins (fun k => k.1.1) fun _ _ h => h.1.1) (by taint_decide)) ?_
  refine RelCT.seq (two_piece (Ψ := fun k t => CmpAt 2 k t ∧ k.2 ≠ 1) [.esi, .esp]
    (any_pins (fun k => k.1.1) fun _ _ h => h.1.1) (by taint_decide)
    fun k t h => WP.mono (cmp_ok h.1 2 (by decide)) fun _ h' => ⟨h', ne_of h.1 h.2⟩) ?_
  refine two_ite (fun k _ _ h₁ h₂ => h₁.1.2.2.2.trans h₂.1.2.2.2.symm)
    (two_taint [.esi, .esp] (any_pins (fun k => k.1.1) fun _ _ h => h.1.1.1) (by taint_decide)) ?_
  refine RelCT.seq (two_piece (Ψ := fun k t => CmpAt 3 k t ∧ k.2 ≠ 1 ∧ k.2 ≠ 2) [.esi, .esp]
    (any_pins (fun k => k.1.1) fun _ _ h => h.1.1.1) (by taint_decide)
    fun k t h => WP.mono (cmp_ok h.1.1 3 (by decide)) fun _ h' => ⟨h', h.1.2, ne_of h.1.1 h.2⟩) ?_
  refine two_ite (fun k _ _ h₁ h₂ => h₁.1.2.2.2.trans h₂.1.2.2.2.symm)
    (two_taint [.esi, .esp] (any_pins (fun k => k.1.1) fun _ _ h => h.1.1.1) (by taint_decide)) ?_
  exact fun _ _ _ _ _ _ ⟨k, h₁, _⟩ => (never ⟨h₁.1.1, h₁.2⟩ h₁.1.2.1 h₁.1.2.2).elim

end VG.Proof.Ffdh.X86.Cached.Search

end

end

/-! # Two runs of the key search's loop (x86)

Two runs at the same loop point (`LiveCT`: the public descriptor, the octets
consumed, the budgets and the statuses of the attempts still to come) branch
alike (`branch_ct`), and their next points are the same function of it
(`ct_step`), so the loop leaks the points alone (`loop_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)

/-- A loop point: the loop's public data and the statuses still to come. -/
abbrev Kp := Lp × List Nat

def LiveCT (q : Kp) (s : State) : Prop :=
  ∃ o, Live q.1.1 o q.1.2.1 q.1.2.2.1 q.1.2.2.2 s ∧
    (q.1.1.tail (randOf o) q.1.2.1 q.1.2.2.1 q.1.2.2.2).statuses = q.2

theorem Live.any {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s) :
    Any p s := ⟨o, _, _, h.input.2, h.st⟩

theorem liveCT_any (q : Kp) (s : State) (h : LiveCT q s) : Any q.1.1 s := let ⟨_, L, _⟩ := h; L.any

/-- `mov eax, [esi + d]; test eax, eax` on a budget. -/
theorem budget_ok {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s)
    {d : Nat} (hd : d = keysOff ∨ d = scalarsOff) :
    WP isa (.block [.mov .eax (.mem (st d)), .alu .test .eax (.reg .eax)]) s fun t =>
      Live p o used keys scalars t ∧
        isa.eval .e t = some (decide ((if d = keysOff then keys else scalars) = 0)) := by
  have S := h.st
  have hkl := h.keys_le
  have hcl := h.scalars_le
  have hul := h.used_le
  obtain ⟨A, rfl⟩ := h.input
  rcases hd with rfl | rfl
  · refine S.ld (Or.inl rfl) (d := keysOff) (by decide) (by decide) fun t₁ S₁ g₁ _ _ _ => ?_
    refine wp_test fun t₂ F₂ z₂ => WP.block_nil ⟨(S₁.fupd F₂).live hul hkl hcl, ?_⟩
    exact test_zero (k := keys) (by omega_using [hkl]) g₁ z₂
  · refine S.ld (Or.inl rfl) (d := scalarsOff) (by decide) (by decide) fun t₁ S₁ g₁ _ _ _ => ?_
    refine wp_test fun t₂ F₂ z₂ => WP.block_nil ⟨(S₁.fupd F₂).live hul hkl hcl, ?_⟩
    exact test_zero (k := scalars) (by omega_using [hcl]) g₁ z₂

/-- `room`: the borrow when the tape holds less than an attempt. -/
theorem room_ok {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s) :
    WP isa (.block room) s fun t => Live p o used keys scalars t ∧
      isa.eval .b t = some (decide (p.randLen - used < p.len)) := by
  have S := h.st
  have hkl := h.keys_le
  have hcl := h.scalars_le
  have hul := h.used_le
  obtain ⟨A, rfl⟩ := h.input
  have hR : (ofState o).randLen < 2 ^ 32 := (arg o 9).isLt
  have hL : (ofState o).len < 2 ^ 32 := (arg o 7).isLt
  unfold room
  refine S.ld (Or.inl rfl) (d := leftOff) (by decide) (by decide) fun t₅ S₅ g₅ _ _ _ => ?_
  refine S₅.ld (Or.inr (Or.inl rfl)) (d := lenOff) (by decide) (by decide) fun t₆ S₆ g₆ o₆ _ _ => ?_
  refine wp_cmp fun t₇ F₇ c₇ _ => WP.block_nil ⟨(S₆.fupd F₇).live hul hkl hcl, ?_⟩
  show t₇.cf = _
  rw [c₇, o₆ .eax (by decide), g₅, g₆]
  simp only [liveF, leftOff, lenOff, ↓reduceIte, Nat.reduceEqDiff]
  rw [toNat_ofNat_lt (by omega_using [hR]), toNat_ofNat_lt hL]

/-- The status of the next attempt, from the statuses still to come. -/
theorem head_status {p : KPub} {o : State} {used keys scalars : Nat} {sts : List Nat}
    (h : (p.tail (randOf o) used keys scalars).statuses = sts) (hk : keys ≠ 0) (hs : scalars ≠ 0)
    (hr : p.len ≤ (randOf o).length - used) : attemptStatus .cached p.a p.len ((randOf o).drop used) = sts.headD 0 := by
  have := keyTail_statuses_head (policy := .cached) (a := p.a) (len := p.len) (rand := randOf o) (used := used) hk hs hr
  rw [KPub.tail] at h
  rw [h] at this
  cases sts with
  | nil => cases this
  | cons x xs => simp only [List.head?_cons, Option.some.injEq] at this; simp [this]

theorem rand_length {o : State} : (randOf o).length = (ofState o).randLen := by
  simp only [randOf, Spec.Rsa.bytesAt, List.length_map, List.length_range]; rfl

theorem ne_of_eval {s : State} {b : Prop} [Decidable b] (h : isa.eval .e s = some (decide b))
    (hf : isa.eval .e s = some false) : ¬ b := by
  rw [h] at hf; simpa using hf

theorem branch_ct : RelCT isa (Two LiveCT) branch fun _ _ => True := by
  unfold branch
  refine RelCT.seq (two_piece (Ψ := fun q t => LiveCT q t ∧ isa.eval .e t = some (decide (q.1.2.2.1 = 0)))
    [.esi, .esp] (any_pins (fun q => q.1.1) liveCT_any) (by taint_decide)
    fun q s ⟨o, L, hs⟩ => WP.mono (budget_ok L (Or.inl rfl)) fun t ⟨L', e⟩ => ⟨⟨o, L', hs⟩, by simpa using e⟩) ?_
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (two_map (fun q => q.1) (fun q s ⟨⟨⟨o, L, _⟩, _⟩, _⟩ => L.at) exhausted_ct) ?_
  refine RelCT.seq (two_piece (Ψ := fun q t => (LiveCT q t ∧ q.1.2.2.1 ≠ 0) ∧
      isa.eval .e t = some (decide (q.1.2.2.2 = 0)))
    [.esi, .esp] (any_pins (fun q => q.1.1) fun q s h => liveCT_any q s h.1.1) (by taint_decide)
    fun q s ⟨⟨⟨o, L, hs⟩, e⟩, hf⟩ => WP.mono (budget_ok L (Or.inr rfl)) fun t ⟨L', e'⟩ =>
      ⟨⟨⟨o, L', hs⟩, ne_of_eval e hf⟩, by simpa [scalarsOff, keysOff] using e'⟩) ?_
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (two_map (fun q => q.1) (fun q s ⟨⟨⟨⟨o, L, _⟩, _⟩, _⟩, _⟩ => L.at) exhausted_ct) ?_
  unfold attemptOrRequest
  refine RelCT.seq (two_piece (Ψ := fun q t => (LiveCT q t ∧ q.1.2.2.1 ≠ 0 ∧ q.1.2.2.2 ≠ 0) ∧
      isa.eval .b t = some (decide (q.1.1.randLen - q.1.2.1 < q.1.1.len)))
    [.esi, .esp] (any_pins (fun q => q.1.1) fun q s h => liveCT_any q s h.1.1.1) (by taint_decide)
    fun q s ⟨⟨⟨⟨o, L, hs⟩, hk⟩, e⟩, hf⟩ => WP.mono (room_ok L) fun t ⟨L', e'⟩ =>
      ⟨⟨⟨o, L', hs⟩, hk, ne_of_eval e hf⟩, e'⟩) ?_
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (two_map (fun q => q.1) (fun q s ⟨⟨⟨⟨o, L, _⟩, _⟩, _⟩, _⟩ => L.at) request_ct) ?_
  -- The attempt, with the status the statuses still to come begin with.
  have hatt : ∀ (q : Kp) s, ((LiveCT q s ∧ q.1.2.2.1 ≠ 0 ∧ q.1.2.2.2 ≠ 0) ∧
      isa.eval .b s = some (decide (q.1.1.randLen - q.1.2.1 < q.1.1.len))) ∧ isa.eval .b s = some false →
      AttAt (q.1, q.2.headD 0) s := by
    intro q s h
    obtain ⟨⟨⟨⟨o, L, hs⟩, hk, hc⟩, e⟩, hf⟩ := h
    rw [e] at hf
    simp only [Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt] at hf
    have hp := L.input.2
    have hr : q.1.1.len ≤ (randOf o).length - q.1.2.1 := by rw [← hp, rand_length, hp]; exact hf
    have hu := L.used_le
    exact ⟨o, L, by dsimp only; omega_using [hf, hu], head_status hs hk hc hr⟩
  refine RelCT.seq (two_post (Ψ := fun q t => ClsAt (q.1, q.2.headD 0) t)
    (two_map (fun q => (q.1, q.2.headD 0)) hatt attempt_ct) fun q s h => ?_)
    (two_map (fun q => (q.1, q.2.headD 0)) (fun _ _ h => h) classify_ct)
  obtain ⟨o, L, hu, st⟩ := hatt q s h
  dsimp only at L hu st
  have hp := L.input.2
  have hc := attemptStatus_cases (policy := .cached) q.1.1.a q.1.1.len ((randOf o).drop q.1.2.1)
  refine WP.mono (attempt_ok L hu) fun u ⟨Su, eu, _⟩ => ⟨o, hp, Su, by rw [eu, st], ?_, hu⟩
  dsimp only; rw [← st]; omega_using [hc]

theorem Done.any {p : KPub} {o s : State} {r : KeySearchResult} (h : Done p o r s) : Any p s := by
  obtain ⟨A, rfl⟩ := h.input
  exact ⟨o, _, _, rfl, ⟨A, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, h.words⟩⟩

theorem iteration_ct : RelCT isa (Two LiveCT) iteration fun _ _ => True := by
  unfold iteration
  refine RelCT.seq (two_post (Ψ := fun q t => Any q.1.1 t) branch_ct fun q s ⟨o, L, _⟩ => WP.mono (branch_ok L)
    fun v hv => ?_) (two_taint [.esi, .esp] (any_pins (fun q => q.1.1) fun _ _ h => h) (by taint_decide))
  rcases hv with ⟨D, _⟩ | ⟨_, _, _, ⟨_, R, _⟩ | ⟨_, R, _⟩⟩
  · exact D.any
  · exact R.any
  · exact R.any

/-- Whether the loop goes on after an iteration from `q`: an attempt was made and rejected. -/
def Kp.cont (q : Kp) : Prop :=
  q.1.2.2.1 ≠ 0 ∧ q.1.2.2.2 ≠ 0 ∧ q.1.2.1 + q.1.1.len ≤ q.1.1.randLen ∧ (q.2.headD 0 = 2 ∨ q.2.headD 0 = 3)

instance (q : Kp) : Decidable q.cont := inferInstanceAs (Decidable (_ ∧ _))

/-- The loop point after a rejection. -/
def Kp.next (q : Kp) : Kp :=
  if q.2.headD 0 = 2 then ((q.1.1, q.1.2.1 + q.1.1.len, q.1.2.2.1, q.1.2.2.2 - 1), q.2.tail)
  else ((q.1.1, q.1.2.1 + q.1.1.len, q.1.2.2.1 - 1, 128), q.2.tail)

def CTStep (q : Kp) (s : State) : Prop :=
  if q.cont then isa.eval .e s = some true ∧ LiveCT q.next s else isa.eval .e s = some false

theorem ct_step (q : Kp) (s : State) (h : LiveCT q s) : WP isa iteration s (CTStep q) := by
  obtain ⟨⟨p, used, keys, scalars⟩, sts⟩ := q
  obtain ⟨o, L, hs⟩ := h
  dsimp only at L hs
  have hp := L.input.2
  have hlen : (randOf o).length = p.randLen := by rw [← hp, rand_length]
  unfold iteration
  refine WP.seq (WP.mono (branch_ok L) fun v hv => ?_)
  rcases hv with ⟨D, stop⟩ | ⟨hk, hc, hr, ⟨h2, R⟩ | ⟨h3, R⟩⟩
  · refine WP.mono (guard_done D) fun t ⟨he, _⟩ => ?_
    have nc : ¬ Kp.cont ((p, used, keys, scalars), sts) := by
      intro hco
      obtain ⟨hk, hc, hr, h23⟩ := hco
      dsimp only at hk hc hr h23
      refine stop ⟨hk, hc, hr, ?_⟩
      rw [head_status hs hk hc (by rw [hlen]; omega_using [hr])]
      exact h23
    simp only [CTStep, nc, ite_false]
    exact he
  · refine WP.mono (guard_rej R) fun t ⟨he, Lt⟩ => ?_
    have e2 : sts.headD 0 = 2 := by rw [← head_status hs hk hc (by rw [hlen]; omega_using [hr])]; exact h2
    have co : Kp.cont ((p, used, keys, scalars), sts) := ⟨hk, hc, hr, Or.inl e2⟩
    simp only [CTStep, co, ite_true, Kp.next, e2]
    refine ⟨he, o, Lt, ?_⟩
    have := hs
    show (keyTail .cached _ _ _ _ _ _).statuses = sts.tail
    rw [KPub.tail, keyTail_scalar hk hc (by rw [hlen]; omega_using [hr]) h2] at this
    rw [← this]; rfl
  · refine WP.mono (guard_rej R) fun t ⟨he, Lt⟩ => ?_
    have e3 : sts.headD 0 = 3 := by rw [← head_status hs hk hc (by rw [hlen]; omega_using [hr])]; exact h3
    have co : Kp.cont ((p, used, keys, scalars), sts) := ⟨hk, hc, hr, Or.inr e3⟩
    simp only [CTStep, co, ite_true, Kp.next, e3]
    refine ⟨he, o, Lt, ?_⟩
    have := hs
    show (keyTail .cached _ _ _ _ _ _).statuses = sts.tail
    rw [KPub.tail, keyTail_public hk hc (by rw [hlen]; omega_using [hr]) h3] at this
    rw [← this]; rfl

/-- The loop's measure. -/
def Kp.measure (q : Kp) : Nat := 129 * q.1.2.2.1 + q.1.2.2.2

theorem Kp.next_measure {q : Kp} (h : q.cont) : q.next.measure < q.measure := by
  obtain ⟨hk, hc, _, _⟩ := h
  unfold Kp.next Kp.measure
  split <;> dsimp only <;> omega_arith

private def LoopPair (n : Nat) (s t : State) : Prop := ∃ q : Kp, n = q.measure ∧ LiveCT q s ∧ LiveCT q t

private theorem iteration_pair (n : Nat) :
    RelCT isa (LoopPair n) iteration fun s t =>
      isa.eval .e s = isa.eval .e t ∧ (isa.eval .e s = some false → True) ∧
      (isa.eval .e s = some true → ∃ m < n, LoopPair m s t) := by
  have hc := two_post (Φ := fun (q : Kp) s => n = q.measure ∧ LiveCT q s)
    (Ψ := fun q t => n = q.measure ∧ CTStep q t) (iteration_ct.mono
    (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.2, h₂.2⟩) fun _ _ h => h) fun q s h =>
      WP.mono (ct_step q s h.2) fun _ ht => ⟨h.1, ht⟩
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂⟩ => ⟨q, ⟨hn, h₁⟩, hn, h₂⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, _, h₂⟩
  by_cases hb : q.cont
  · simp only [CTStep, hb, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ⟨q.next.measure, ?_, q.next, rfl, h₁.2, h₂.2⟩⟩
    rw [hn]; exact Kp.next_measure hb
  · simp only [CTStep, hb, ite_false] at h₁ h₂
    refine ⟨h₁.trans h₂.symm, fun _ => trivial, fun ht => ?_⟩
    have : isa.eval .e s = some false := h₁
    rw [this] at ht
    cases ht

theorem loop_ct : RelCT isa (Two LiveCT) (.loop iteration .e) fun _ _ => True := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration) (c := .e) (Q := fun _ _ => True) LoopPair iteration_pair
    q.measure _ _ _ _ _ _ ⟨q, rfl, hs, ht⟩ he₁ he₂

end VG.Proof.Ffdh.X86.Cached.Search

end

end

/-! # The key search in constant time (x86)

Two runs whose public data agree start at the same loop point: the
arguments, the domain, the budgets and the statuses of the search's
attempts (`pub_point`). The entry is checked by the taint analysis from
`esp`, then from `esp` and the state's pointer (`entry_ct`); the loop leaks
its points alone (`loop_ct`); `finish` stores through `used`, which the
descriptor fixes (`finish_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite argumentPointer)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The loop point an entry state starts at. -/
def entryPt (s : State) : Kp :=
  ((ofState s, 0, (ofState s).keys, (ofState s).scalars), (searchOf s).statuses)

/-- An entry state at the point `q`. -/
def EntAt (q : Kp) (s : State) : Prop := KeySearchABI s ∧ entryPt s = q

theorem entAt_live {q : Kp} {s : State} (h : EntAt q s) :
    WP isa (.block entry) s (LiveCT q) := by
  obtain ⟨A, rfl⟩ := h
  refine WP.mono (entry_ok A) fun t L => ⟨s, L, ?_⟩
  simp only [entryPt, KPub.tail, keyTail, after, List.drop_zero]
  rfl

theorem entry_ct : RelCT isa (Two EntAt) (.block entry) (Two LiveCT) := by
  refine two_post ?_ fun q s h => entAt_live h
  rw [show entry = [.mov .eax (.mem (argAt 0 12))] ++ entry.drop 1 from rfl]
  refine RelCT.block_append (RelCT.seq (two_piece
    (Ψ := fun (q : Kp) t => t.gpr .eax = q.1.1.S ∧ t.gpr .esp = q.1.1.sp) [.esp]
    (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact congrArg (fun q : Kp => q.1.1.sp) (h₁.2.trans h₂.2.symm)) (by taint_decide) fun q s ⟨A, e⟩ => ?_)
    (two_taint [.eax, .esp] (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2, h₂.2]) (by taint_decide)))
  subst e
  have e12 : argAt 0 12 = ⟨.esp, 4 + 4 * 12⟩ := by simp [argAt, at_]
  have r12 : readSrc s (.mem (argAt 0 12)) = some (arg s 12) := by
    rw [e12, readSrc_mem rfl ⟨_, List.mem_append_right _ (aR_mem A), arg_in A (i := 12) (by decide)⟩]; rfl
  exact wp_movS r12 fun t U _ => WP.block_nil ⟨U.gpr, by rw [U.other _ (by decide)]; rfl⟩

/-- A finished search with the public descriptor `p`. -/
def DoneAt (p : KPub) (s : State) : Prop := ∃ o r, Done p o r s

theorem finish_ct : RelCT isa (Two fun (q : Kp) s => DoneAt q.1.1 s) (.block finish) fun _ _ => True := by
  have pin : Pins (fun (q : Kp) t => Any q.1.1 t ∧ t.gpr .ecx = q.1.1.up) [.esi, .esp] :=
    any_pins (fun q => q.1.1) fun _ _ h => h.1
  rw [show finish = [.mov .ecx (.mem (st upOff))] ++ finish.drop 1 from rfl]
  refine RelCT.block_append (RelCT.seq (two_piece
    (Ψ := fun (q : Kp) t => Any q.1.1 t ∧ t.gpr .ecx = q.1.1.up) [.esi, .esp]
    (any_pins (fun (q : Kp) => q.1.1) fun q s ⟨_, _, D⟩ => D.any) (by taint_decide) fun q s ⟨o, r, D⟩ => ?_)
    (two_taint [.ecx, .esi, .esp] (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.2, h₂.2]
      · exact pin q s₁ s₂ h₁ h₂ .esi (by decide)
      · exact pin q s₁ s₂ h₁ h₂ .esp (by decide))
      (by taint_decide)))
  obtain ⟨⟨p, x⟩, sts⟩ := q
  dsimp only at D ⊢
  obtain ⟨A, rfl⟩ := D.input
  have S : St o doneDs (doneF (ofState o) (o.gpr .esi) r) s :=
    ⟨A, D.rd, D.wr, D.esp, D.esi, D.saved, D.frame, D.words⟩
  exact S.ld (Or.inr (Or.inl rfl)) (d := upOff) (by decide) (by decide) fun t St g _ _ _ =>
    WP.block_nil ⟨⟨o, _, _, rfl, St⟩, by rw [g]; rfl⟩

theorem wordsAt4 (m : Mem) (p : Addr) : Spec.Rsa.wordsAt m p 4 =
    [m.readW (p + BitVec.ofNat 64 0) 64, m.readW (p + BitVec.ofNat 64 8) 64, m.readW (p + BitVec.ofNat 64 16) 64,
      m.readW (p + BitVec.ofNat 64 24) 64] := rfl

/-- Two entry states whose public data agree start at the same loop point. -/
theorem pub_point {s t : State} (H : (Spec.Ffdh.cachedKeySearchContract abi stack).pub s t) : entryPt s = entryPt t := by
  sig_pub [Spec.Ffdh.cachedKeySearchContract, Spec.Ffdh.cachedKeySearchSig, Spec.Ffdh.keySearchSig, abi, argSlots, argVal, argBytes] at H
  obtain ⟨SP, L, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := H
  have inj : ∀ {l l' : List Byte}, l.map (fun x => x.toNat) = l'.map (fun x => x.toNat) → l = l' :=
    fun h => (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp h
  obtain ⟨L₁₂, L₃⟩ := List.append_inj L (by simp [Spec.Rsa.bytesAt, Spec.Rsa.wordsAt, a6])
  obtain ⟨L₁, L₂⟩ := List.append_inj L₁₂ (by simp [Spec.Rsa.bytesAt, a6])
  have D := inj L₁
  rw [wordsAt4, wordsAt4] at L₂
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at L₂
  obtain ⟨k, c, _, _⟩ := L₂
  rw [BitVec.add_zero, BitVec.add_zero] at k
  have e : ofState s = ofState t := by
    simp only [ofState, KPub.mk.injEq]
    exact ⟨SP, a12, a0, a2, a4, a5, a8, a10, congrArg BitVec.toNat a7, congrArg BitVec.toNat a6,
      congrArg BitVec.toNat a9, congrArg BitVec.toNat a11, k, c, D, a13, congrArg BitVec.toNat a14⟩
  simp only [entryPt, e]
  exact congrArg _ L₃

theorem code_ct : RelCT isa (Two EntAt) Impl.Ffdh.X86.Cached.Search.code fun _ _ => True := by
  unfold Impl.Ffdh.X86.Cached.Search.code
  exact RelCT.seq entry_ct (RelCT.seq (two_post (Ψ := fun (q : Kp) s => DoneAt q.1.1 s) loop_ct
    fun q s ⟨o, L, _⟩ => WP.mono (loop_ok L) fun t D => ⟨o, _, D⟩) finish_ct)

theorem constantTime : ConstantTime isa (Spec.Ffdh.cachedKeySearchContract abi stack).pre
    (Spec.Ffdh.cachedKeySearchContract abi stack).pub Impl.Ffdh.X86.Cached.Search.code := by
  intro s t tr ur sf tf S T H E F
  exact (code_ct _ _ _ _ _ _ ⟨entryPt s, ⟨keySearchABI_of S, rfl⟩, ⟨keySearchABI_of T, (pub_point H).symm⟩⟩
    E F).1

end VG.Proof.Ffdh.X86.Cached.Search

end

end

/-! # `vg_ffdh_generate_key_search_cached` on i686 against its contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86

/-- x, y of 64 bytes, `used`, the domain of 128 (`CachedSat.domain`), an empty tape, a working space of
1056 words, a state with the width 64 and the domain's context, apart. -/
def satBase (a : Addr) : Byte :=
  if a = 0x20005 then 0x10
  else if a = 0x20008 then 64
  else if a = 0x2000d then 0x20
  else if a = 0x20010 then 64
  else if a = 0x20015 then 0x50
  else if a = 0x20019 then 0x30
  else if a = 0x2001c then 128
  else if a = 0x20020 then 64
  else if a = 0x20025 then 0x40
  else if a = 0x2002d then 0x90
  else if a = 0x20030 then 0x20
  else if a = 0x20031 then 4
  else if a = 0x20035 then 0x60
  else if a = 0x2003a then 0x10
  else if a = 0x2003c then 0x13
  else if a = 0x2003d then 1
  else if a = 0x6010 then 64 else CachedSat.domainMem a

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := CachedSat.withContext satBase
  rd := [⟨0x3000, 128⟩, ⟨0x4000, 0⟩, ⟨0x100000, 2200⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x5000, 8⟩, ⟨0x9000, 8448⟩, ⟨0x6000, 128⟩, ⟨0x20004, 60⟩]

theorem sat_read {a : Addr} {w : Nat} (small : a.toNat + w / 8 ≤ 0x100000) :
    satState.mem.readW a w = Mem.readW satBase a w :=
  CachedSat.readW_outside _ small

theorem sat_arg (i : Nat) (hi : i < 15) : arg satState i = Mem.readW satBase (argAddr satState i) 32 := by
  unfold arg
  refine sat_read ?_
  have small : ∀ i < 15, (argAddr satState i).toNat + 32 / 8 ≤ 0x100000 := by decide
  exact small i hi

theorem sat_domain : Spec.Rsa.bytesAt satState.mem 0x3000 128 = CachedSat.domain := by
  rw [show satState.mem = CachedSat.withContext satBase from rfl, CachedSat.domain_unchanged]
  apply CachedSat.bytesAt_eq
  have : ∀ i < 128, satBase (0x3000 + BitVec.ofNat 64 i) = CachedSat.domainMem (0x3000 + BitVec.ofNat 64 i) := by
    decide
  exact this

theorem satisfiable : ∃ s, (Spec.Ffdh.cachedKeySearchContract abi stack).pre s := by
  have a0 : arg satState 0 = 0x1000 := by rw [sat_arg 0 (by decide)]; decide
  have a1 : arg satState 1 = 64 := by rw [sat_arg 1 (by decide)]; decide
  have a2 : arg satState 2 = 0x2000 := by rw [sat_arg 2 (by decide)]; decide
  have a3 : arg satState 3 = 64 := by rw [sat_arg 3 (by decide)]; decide
  have a4 : arg satState 4 = 0x5000 := by rw [sat_arg 4 (by decide)]; decide
  have a5 : arg satState 5 = 0x3000 := by rw [sat_arg 5 (by decide)]; decide
  have a6 : arg satState 6 = 128 := by rw [sat_arg 6 (by decide)]; decide
  have a7 : arg satState 7 = 64 := by rw [sat_arg 7 (by decide)]; decide
  have a8 : arg satState 8 = 0x4000 := by rw [sat_arg 8 (by decide)]; decide
  have a9 : arg satState 9 = 0 := by rw [sat_arg 9 (by decide)]; decide
  have a10 : arg satState 10 = 0x9000 := by rw [sat_arg 10 (by decide)]; decide
  have a11 : arg satState 11 = 1056 := by rw [sat_arg 11 (by decide)]; decide
  have a12 : arg satState 12 = 0x6000 := by rw [sat_arg 12 (by decide)]; decide
  have a13 : arg satState 13 = 0x100000 := by rw [sat_arg 13 (by decide)]; decide
  have a14 : arg satState 14 = 275 := by rw [sat_arg 14 (by decide)]; decide
  have e : argAddr satState 0 = 0x20004 := by decide
  refine ⟨satState, ?_⟩
  sig_pre [Spec.Ffdh.cachedKeySearchContract, Spec.Ffdh.cachedKeySearchSig, Spec.Ffdh.keySearchSig, abi, argSlots,
    argVal, argBytes, stackBelow, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Ffdh.generationContextAt]
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, e]
  sig_and_intros
  all_goals first
    | (change Spec.Ffdh.domainValid 64 (Spec.Rsa.bytesAt satState.mem 0x3000 128) = true
       rw [sat_domain]; exact CachedSat.domain_valid)
    | (change Spec.Ffdh.generationPrecompute 64 (Spec.Rsa.bytesAt satState.mem 0x3000 128) =
          some (Spec.Rsa.wordsAt satState.mem 0x100000 275)
       rw [sat_domain]; exact (CachedSat.canonical satBase).2)
    | (rw [CachedSat.readW_outside _ (by decide)]; decide)
    | exact Region.disjoint_of_sep (by decide)
    | rfl
    | decide

theorem verified : Verified target Impl.Ffdh.X86.Cached.Search.code (Spec.Ffdh.cachedKeySearchContract abi stack) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Ffdh.X86.Cached.Search
