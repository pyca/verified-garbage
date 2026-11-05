module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Loop
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Loop
meta import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
meta import VerifiedGarbage.Proof.Framework.Offset

-- separate module: the search's constant-time proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # The search's loop points (i686)

Two runs of the search whose public data agree are at the same point of
the loop (`Pt`: the octets consumed, the counted candidates left and the
trace so far), from which the next candidate's leak, its status and the
octets it consumes are public (`leak_of`, `status_eq`, `used_eq`); the loop
state fixes the stack pointer and the registers of the point
(`live_pins`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Proof.Dsa.X86 (Two Pins)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy PrimeSearchResult candidateOp)

/-- A block's head, then its tail and what follows. -/
theorem RelCT.seq_block_append {M : ISA} {P Q : M.State → M.State → Prop} {l₁ l₂ : List M.Instr} {c : Prog M}
    (h : RelCT M P (.seq (.block l₁) (.seq (.block l₂) c)) Q) : RelCT M P (.seq (.block (l₁ ++ l₂)) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq b₁ c₁ =>
    cases e₂ with
    | seq b₂ c₂ =>
      rw [Exec.block_iff, execBlock_append] at b₁ b₂
      obtain ⟨⟨a₁, u₁⟩, ha₁, hb₁⟩ := Option.bind_eq_some_iff.mp b₁
      obtain ⟨⟨d₁, w₁⟩, hc₁, he₁⟩ := Option.map_eq_some_iff.mp hb₁
      obtain ⟨⟨a₂, u₂⟩, ha₂, hb₂⟩ := Option.bind_eq_some_iff.mp b₂
      obtain ⟨⟨d₂, w₂⟩, hc₂, he₂⟩ := Option.map_eq_some_iff.mp hb₂
      simp only [Prod.mk.injEq] at he₁ he₂
      obtain ⟨rfl, rfl⟩ := he₁
      obtain ⟨rfl, rfl⟩ := he₂
      obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.block ha₁) (.seq (.block hc₁) c₁))
        (.seq (.block ha₂) (.seq (.block hc₂) c₂))
      simp only [List.append_assoc] at ht ⊢
      exact ⟨ht, hq⟩

/-- Two postconditions of a block, which runs one way. -/
theorem WP.block_and {M : ISA} {is : List M.Instr} {s : M.State} {Q₁ Q₂ : M.State → Prop}
    (h₁ : WP M (.block is) s Q₁) (h₂ : WP M (.block is) s Q₂) : WP M (.block is) s fun t => Q₁ t ∧ Q₂ t := by
  induction is generalizing s with
  | nil => exact WP.block_nil_iff.mpr ⟨WP.block_nil_iff.mp h₁, WP.block_nil_iff.mp h₂⟩
  | cons i is ih =>
    obtain ⟨a, ea, ha⟩ := WP.block_cons_iff.mp h₁
    obtain ⟨b, eb, hb⟩ := WP.block_cons_iff.mp h₂
    rw [ea] at eb
    cases eb
    exact WP.block_cons_iff.mpr ⟨a, ea, ih ha hb⟩

/-- A point of the loop: octets consumed, counted candidates left, trace so far. -/
abbrev Pt := Nat × Nat × List Nat

/-- A loop state of a run whose public data is `p` and whose search's trace is `T`. -/
def LiveCT (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop :=
  ∃ o, (searchResult o).trace = T ∧ SearchLive p o q.1 q.2.1 s ∧
    searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2

/-- The next candidate's leak, from the trace. -/
def nextLeak (T tr : List Nat) : List Nat :=
  ((T.drop tr.length).drop 1).take ((T.drop tr.length).headD 0)

def pubStatus (T tr : List Nat) : Nat := Search.statusOfLeak (nextLeak T tr)
def pubUsed (p : SearchPublic) (T tr : List Nat) : Nat := Search.usedOfLeak p.len (nextLeak T tr)

/-- Whether the search goes on past the next candidate, from public data. -/
def pubCont (p : SearchPublic) (T : List Nat) (q : Pt) : Prop :=
  q.2.1 ≠ 0 ∧ q.1 + p.len ≤ p.randLen ∧ (pubStatus T q.2.2 = 2 ∨ pubStatus T q.2.2 = 3) ∧
    pubUsed p T q.2.2 ≠ 0

instance (p : SearchPublic) (T : List Nat) (q : Pt) : Decidable (pubCont p T q) := by
  unfold pubCont; infer_instance

/-- The point past the next candidate. -/
def nextPt (p : SearchPublic) (T : List Nat) (q : Pt) : Pt :=
  (q.1 + pubUsed p T q.2.2, if pubStatus T q.2.2 = 3 then q.2.1 - 1 else q.2.1,
    q.2.2 ++ ((nextLeak T q.2.2).length :: nextLeak T q.2.2))

/-- With candidates left, the next leak is the candidate's. -/
theorem leak_of {p : SearchPublic} {T : List Nat} {q : Pt} {o : State}
    (hT : (searchResult o).trace = T) (hfin : searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2)
    (hk : q.2.1 ≠ 0) :
    nextLeak T q.2.2 = Spec.RsaKeyGen.candidateLeak p.len p.eB (searchP o) ((searchRand o).drop q.1) := by
  obtain ⟨rest, hr⟩ := Search.search_trace (L := p.len) (eB := p.eB) (pB := searchP o) hk
    ((searchRand o).drop q.1)
  have e : T = q.2.2 ++ (Search.entry p.len p.eB (searchP o) ((searchRand o).drop q.1) ++ rest) := by
    rw [← hT, hfin]
    change q.2.2 ++ (tailOf p o q.1 q.2.1).trace = _
    rw [tailOf, hr]
  unfold nextLeak
  rw [e, List.drop_left]
  simp only [Search.entry, List.cons_append, List.drop_succ_cons, List.drop_zero, List.headD_cons]
  exact List.take_left' rfl

theorem status_eq {p : SearchPublic} {T : List Nat} {q : Pt} {o : State}
    (hT : (searchResult o).trace = T) (hfin : searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2)
    (hk : q.2.1 ≠ 0) : candStatus p o q.1 = pubStatus T q.2.2 := by
  rw [pubStatus, leak_of hT hfin hk, candStatus, candOp, Search.status_of_leak]

theorem used_eq {p : SearchPublic} {T : List Nat} {q : Pt} {o : State} (hi : SearchInput p o)
    (hT : (searchResult o).trace = T) (hfin : searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2)
    (hk : q.2.1 ≠ 0) : candUsed p o q.1 = pubUsed p T q.2.2 := by
  rw [pubUsed, leak_of hT hfin hk, ← Search.used_of_leak, List.length_drop, rand_length hi]
  rfl

theorem cont_iff {p : SearchPublic} {T : List Nat} {q : Pt} {o : State} (hi : SearchInput p o)
    (hT : (searchResult o).trace = T) (hfin : searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2) :
    Cont p o q.1 q.2.1 ↔ pubCont p T q := by
  by_cases hk : q.2.1 = 0
  · exact ⟨fun h => absurd hk h.1, fun h => absurd hk h.1⟩
  · unfold Cont pubCont
    rw [status_eq hT hfin hk, used_eq hi hT hfin hk]

/-- The registers a loop state fixes. -/
theorem live_pins (p : SearchPublic) (T : List Nat) :
    Pins (LiveCT p T) [.esp, .esi, .edi, .ebx] := by
  rintro q s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h₁.sp.trans h₂.sp.symm, h₁.esi.trans h₂.esi.symm, h₁.edi.trans h₂.edi.symm, h₁.ebx.trans h₂.ebx.symm]

/-- The stack pointer, which every state of the search's body fixes. -/
theorem base_pins (p : SearchPublic) : Pins (fun (_ : Unit) s => ∃ o, SearchBase p o s) [.esp] := by
  rintro _ s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact h₁.sp.trans h₂.sp.symm

end VG.Proof.RsaKeyGen.X86.Search
