module

public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Steps
import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Entry

/-! # The key search's exits without an attempt (x86)

From a loop state, `exhausted` (a budget at zero) and `request` (the tape
too short) end the search with zeros at both outputs (`exhausted_ok`,
`request_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch
open VG.Proof.Dsa.X86 (argumentPointer)

theorem Live.st {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s) :
    St o liveDs (liveF p (o.gpr .esi) used keys scalars) s := by
  obtain ⟨A, rfl⟩ := h.input
  exact ⟨A, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, h.words⟩

theorem liveDs_aligned : Aligned liveDs := by decide

/-- A run's state, with the words a finished search leaves. -/
theorem St.done {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {r : KeySearchResult}
    (hs : ∀ d ∈ doneDs, d ∈ ds) (he : ∀ d ∈ doneDs, f d = doneF (ofState o) (o.gpr .esi) r d)
    (hout : Output (ofState o) r s.mem) : Done (ofState o) o r s :=
  ⟨⟨h.abi, rfl⟩, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, (h.words.sub hs).congr he, hout⟩

/-- The width's word: `p_len`, below `2³²`. -/
theorem len_ofNat {o : State} : BitVec.ofNat 32 (ofState o).len = arg o 7 := by
  simp only [ofState, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem exhausted_ok {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s) :
    WP isa exhausted s (Done p o ⟨.exhausted, used, []⟩) := by
  have S := h.st
  obtain ⟨A, rfl⟩ := h.input
  have hA := liveDs_aligned
  unfold exhausted terminal
  refine WP.seq (wp_movi fun t₁ U₁ => ?_)
  have S₁ := S.reg U₁ (Or.inl rfl)
  refine S₁.stw hA (d := keysOff) (by decide) (by decide) fun t₂ S₂ G₂ _ _ => ?_
  refine S₂.stw (hA.cons (by decide) (by decide)) (d := scalarsOff) (by decide) (by decide)
    fun t₃ S₃ G₃ _ _ => ?_
  refine S₃.stw ((hA.cons (by decide) (by decide)).cons (by decide) (by decide)) (d := requestOff)
    (by decide) (by decide) fun t₄ S₄ G₄ _ _ => ?_
  refine wp_movi fun t₅ U₅ => ?_
  have S₅ := S₄.reg U₅ (Or.inl rfl)
  refine S₅.stw (((hA.cons (by decide) (by decide)).cons (by decide) (by decide)).cons (by decide) (by decide))
    (d := statusOff) (by decide) (by decide) fun t₆ S₆ G₆ _ _ => WP.block_nil ?_
  have e₂ : t₂.gpr .eax = 0 := by rw [G₂, U₁.gpr]
  have e₃ : t₃.gpr .eax = 0 := by rw [G₃, e₂]
  simp only [U₁.gpr, e₂, e₃, U₅.gpr] at S₆
  have hA₆ : Aligned (statusOff :: requestOff :: scalarsOff :: keysOff :: liveDs) := by decide
  refine WP.mono (S₆.zeroOutputs hA₆ (by simp [upd, liveF, ofState, xOff, statusOff, requestOff, scalarsOff,
      keysOff]) (by simp [upd, liveF, ofState, yOff, statusOff, requestOff, scalarsOff, keysOff])
    (by simp [upd, liveF, ofState, lenOff, statusOff, requestOff, scalarsOff, keysOff]) (by decide) (by decide)
    (by decide)) fun u ⟨Su, Zx, Zy, _, _⟩ => ?_
  refine Su.done (by decide) ?_ ⟨Zx, Zy⟩
  simp only [doneDs, List.mem_cons, List.not_mem_nil, or_false]
  rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp [upd, liveF, doneF, statusOff, requestOff, scalarsOff, keysOff, KeySearchResult.retries,
      KeySearchResult.status, ofState]

theorem request_ok {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s) :
    WP isa request s (Done p o ⟨.entropy ⟨keys, scalars⟩, used, []⟩) := by
  have S := h.st
  obtain ⟨A, rfl⟩ := h.input
  have hA := liveDs_aligned
  unfold request
  refine WP.seq (S.ld (Or.inl rfl) (d := lenOff) (by decide) (by decide) fun t₁ S₁ g₁ _ _ => ?_)
  refine S₁.stw hA (d := requestOff) (by decide) (by decide) fun t₂ S₂ G₂ _ _ => ?_
  refine wp_movi fun t₃ U₃ => ?_
  have S₃ := S₂.reg U₃ (Or.inl rfl)
  refine S₃.stw (hA.cons (by decide) (by decide)) (d := statusOff) (by decide) (by decide)
    fun t₄ S₄ G₄ _ _ => WP.block_nil ?_
  simp only [g₁, U₃.gpr] at S₄
  have hA₄ : Aligned (statusOff :: requestOff :: liveDs) := by decide
  refine WP.mono (S₄.zeroOutputs hA₄ (by simp [upd, liveF, ofState, xOff, statusOff, requestOff])
    (by simp [upd, liveF, ofState, yOff, statusOff, requestOff])
    (by simp [upd, liveF, ofState, lenOff, statusOff, requestOff]) (by decide) (by decide)
    (by decide)) fun u ⟨Su, Zx, Zy, _, _⟩ => ?_
  refine Su.done (by decide) ?_ ⟨Zx, Zy⟩
  simp only [doneDs, List.mem_cons, List.not_mem_nil, or_false]
  rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp [upd, liveF, doneF, statusOff, requestOff, lenOff, KeySearchResult.retries, KeySearchResult.status,
      ofState]

end VG.Proof.Ffdh.X86.KeySearch
