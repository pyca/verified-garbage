module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchArguments

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Contract

/-! # Translate a candidate invocation to the complete search's byte stream -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

def searchCandidate (p : SearchPublic) (used : Nat) :=
  Spec.Ffdh.parameterCandidate p.c.bits p.c.gen (p.c.rand.drop used)

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

theorem SearchCandidatePost.keep {p : SearchPublic} {used : Nat} {s t : State}
    (h : SearchCandidatePost p used s) (hm : t.mem = s.mem)
    (hr : (t.gpr .rax).setWidth 32 = (s.gpr .rax).setWidth 32) : SearchCandidatePost p used t := by
  exact ⟨by rw [hr]; exact h.1, by rw [hm]; exact h.2⟩

end VG.Proof.Ffdh.X86_64.Generation
