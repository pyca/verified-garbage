module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedCTState
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSearch
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchCTState
import VerifiedGarbage.Proof.Framework.Omega

/-! # Public seed inputs instantiate the bounded prime-search plan -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def SeedPublic.words (p : SeedPublic) : Nat → BitVec 64 :=
  upd (upd p.context.saved 1 p.seed.ptr) 10 p.seedCursor

def SeedPublic.searchPlan (p : SeedPublic) : SearchPlan :=
  p.context.geo.searchPlan p.seed p.context.rand p.length (searchWords p.context.geo.B p.words) 0
    (by have := p.context.geo.hashSizes.1; omega)
    (by simp [searchWords, words, upd])
    (by simpa [searchWords, words, upd] using p.context.wrappedSlot)
    (by simpa [searchWords, words, upd] using p.context.hashesSlot)
    (by simp [searchWords, upd])
    (by simpa [searchWords, words, upd] using p.context.baseSlot)
    (by simp [searchWords, upd])
    (by simpa [searchWords, words, upd] using p.context.randSlot)
    (by simpa [searchWords, words, upd] using p.context.randLengthSlot)

def SeedPublic.search (p : SeedPublic) : SearchPublic where
  plan := p.searchPlan
  ws := p.ws
  wr := p.wr
  header := by
    change PrimeHeaderLayout (p.context.saved 5) p.wr
    rw [p.context.baseSlot]
    exact p.header
  counter := 0
  used := p.used
  bound := by
    change 0 < 32 * p.context.geo.pLen
    rcases p.context.geo.width with h | h | h <;> omega

def SeedPrimeBefore (n pLen qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  SeedBefore n qLen p s ∧ p.context.geo.pLen = pLen ∧
  Spec.Rsa.bytesAt s.mem (off p.context.geo.B q) p.context.geo.qLen =
    Spec.Dsa.encodeBE p.context.geo.qLen (Spec.Dsa.qCandidate (8 * p.context.geo.qLen) p.seed.bytes)

theorem seedPrime_words {p : SeedPublic} {s : State}
    {W : Nat → BitVec 64} (h : GenerationMemory p.context W s)
    (h1 : W 1 = p.seed.ptr) (h10 : W 10 = p.seedCursor) :
    ∀ k ∈ searchSlots, W k = p.searchPlan.attempt.construct.hash.W k := by
  intro k hk
  change W k = searchWords p.context.geo.B p.words k
  by_cases hk1 : k = 1
  · subst k; simpa [searchWords, SeedPublic.words, upd] using h1
  by_cases hk10 : k = 10
  · subst k; simpa [searchWords, SeedPublic.words, upd] using h10
  have member : k ∈ generationSlots := by
    simp only [searchSlots, generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
    omega
  have neq : k ≠ 0 ∧ k ≠ 2 ∧ k ≠ 27 := by
    simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  simpa [searchWords, SeedPublic.words, upd, hk1, hk10, neq.1, neq.2.1, neq.2.2] using h.slots k member

end VG.Proof.Dsa.X86_64.Generation
