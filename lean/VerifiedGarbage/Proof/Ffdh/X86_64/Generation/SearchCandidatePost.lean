module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchArguments

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Contract
import VerifiedGarbage.Proof.Rsa.BytesFrame

/-! # Translate a candidate invocation to the complete search's byte stream -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

def searchCandidate (p : SearchPublic) (used : Nat) :=
  Spec.Ffdh.sievedParameterCandidate p.c.bits p.c.gen (p.c.rand.drop used)

def candidateUsed (p : SearchPublic) (used : Nat) : Nat :=
  match searchCandidate p used with
  | some (_, rest) => (p.c.rand.length - used) - rest.length
  | none => 0

def SearchCandidatePost (p : SearchPublic) (used : Nat) (t : State) : Prop :=
  ((t.gpr .rax).setWidth 32).toNat = Proof.Ffdh.candidateStatus (searchCandidate p used) ∧
    Spec.Rsa.bytesAt t.mem p.c.op p.c.k =
      (match searchCandidate p used with
        | some (some n, _) => Spec.Rsa.i2osp n p.c.k
        | _ => List.replicate p.c.k 0) ∧
    Spec.Rsa.wordsAt t.mem p.c.up 1 = [BitVec.ofNat 64 (candidateUsed p used)]

theorem search_candidate_result {p : SearchPublic} {original s : State} {used : Nat}
    (h : SearchInput p original) (ha : SearchArgs p used s)
    (hr : pcRand s = p.c.rand.drop used) : pcResult s = searchCandidate p used := by
  obtain ⟨_, _, _, hc, hg, _⟩ := ha
  unfold pcResult searchCandidate
  rw [hc, hg, hr]
  have hb : p.c.bits < 2 ^ 64 := by
    cases h.2
    exact (original.gpr .rcx).isLt
  have hgen : p.c.gen < 2 ^ 32 := by
    cases h.2
    exact ((original.gpr .r8).setWidth 32).isLt
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb,
    BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64), Nat.mod_eq_of_lt hgen]

theorem search_candidate_post {p : SearchPublic} {original s t : State} {used : Nat}
    (h : SearchInput p original) (ha : SearchArgs p used s)
    (hr : pcRand s = p.c.rand.drop used)
    (hl : (stackArg s 0).toNat = p.c.rand.length - used) (hp : pcPost s t) :
    SearchCandidatePost p used t := by
  have hk : p.c.k < 2 ^ 64 := by
    cases h.2
    exact (original.gpr .rsi).isLt
  simp only [SearchCandidatePost, pcPost, ha.1, ha.2.1, ha.2.2.1,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, search_candidate_result h ha hr, hl,
    candidateUsed] at hp ⊢
  cases he : searchCandidate p used with
  | none => simpa only [he] using hp
  | some pair =>
    obtain ⟨value, rest⟩ := pair
    cases value <;> simpa only [he] using hp

theorem SearchCandidatePost.freed {p : SearchPublic} {used bytes : Nat} {t : State}
    (h : SearchCandidatePost p used t) : SearchCandidatePost p used (freed bytes t) := by
  exact h

theorem SearchCandidatePost.used_word {p : SearchPublic} {used : Nat} {s : State}
    (h : SearchCandidatePost p used s) : s.mem.readW p.c.up 64 = BitVec.ofNat 64 (candidateUsed p used) := by
  have hh := h.2.2
  change [word s.mem p.c.up 0] = [_] at hh
  have he := (List.cons.inj hh).1
  simpa only [Bignum.word, off, BitVec.add_zero] using he

/-- The output and the used count lie apart from the search's stack. -/
theorem SearchInput.stack_outputs {p : SearchPublic} {original : State} (h : SearchInput p original) :
    (below (original.gpr .rsp) 160).Disjoint ⟨p.c.op, p.c.k⟩ ∧
      (below (original.gpr .rsp) 160).Disjoint ⟨p.c.up, 8⟩ := by
  have hd := h.1.2.2.2.2.2.2.2.2.1
  cases h.2
  exact ⟨hd _ (by simp [inputBuffers, searchOfState, SearchPublic.c, candidateOfState]),
    hd _ (by simp [inputBuffers, searchOfState, SearchPublic.c, candidateOfState])⟩

/-- `SearchCandidatePost` holds whatever the bytes of a frame on the search's
stack hold once released. -/
theorem SearchCandidatePost.lost {p : SearchPublic} {original t t' : State} {used : Nat}
    (h : SearchInput p original) (hc : SearchCandidatePost p used t) (hr : t'.gpr .rax = t.gpr .rax)
    {R : Region} (fm : Frame [R] t.mem t'.mem) (hR : R.Sub (below (original.gpr .rsp) 160)) :
    SearchCandidatePost p used t' := by
  obtain ⟨ho, hu⟩ := SearchInput.stack_outputs h
  have hk : p.c.k < 2 ^ 64 := by cases h.2; exact (original.gpr .rsi).isLt
  have sep : ∀ {B : Region}, (below (original.gpr .rsp) 160).Disjoint B → ∀ q ∈ [R], B.Disjoint q :=
    fun hB q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact fun x h₁ h₂ => hB x (hR x h₂) h₁
  obtain ⟨a, b, c⟩ := hc
  refine ⟨by rw [hr]; exact a, ?_, ?_⟩
  · rw [Proof.Rsa.rsa_bytes_frame fm hk (sep ho)]; exact b
  · rw [Proof.Rsa.wordsAt_frame fm (by decide) (sep hu)]; exact c

end VG.Proof.Ffdh.X86_64.Generation
