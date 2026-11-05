module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Tests
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Result
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieved
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Halve
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# An FFDH parameter candidate on PPC64LE: the tests

`tests_ok`: one witness of p, then q's if it passed, then p's others if q
passed, and their result (`Proof.Ffdh.ParameterCandidate.sievedTests`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses onPass sievedTests)

theorem stat_one {n : Nat} (hn : n < 2 ^ 60) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 1 == 0) = decide (n = 1) := by
  by_cases h : n = 1
  · subst h; decide
  · rw [decide_eq_false h]
    apply Bool.eq_false_iff.mpr
    intro he
    have := congrArg BitVec.toNat (beq_iff_eq.mp he)
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [h0] at this
    omega_arith

/-- `hStat` against 1. -/
theorem stat1_ok {C : Nat} {p : PP} {mb N v : Nat} {s : State} (M : MSt p mb N C s) (hv : v < 2 ^ 60)
    (hS : word s.mem p.B 160 = BitVec.ofNat 64 v) :
    WP isa (.block [ldh .r3 hStat, .subi .r3 .r3 1]) s fun t =>
      isa.eval (.zero .d .r3) t = some (decide (v = 1)) ∧ MSt p mb N C t ∧ t.mem = s.mem := by
  have l160 : InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 160) 8 := M.st.ld (d := 160) (by decide)
  refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 v - BitVec.ofNat 64 1 ∧ t.mem = s.mem)
    (by simp only [ldh, hStat]; prun [M.st.r31, l160, show s.mem.readW (p.B + BitVec.ofNat 64 160) 64 =
      BitVec.ofNat 64 v from hS]) (by decide)) fun t ⟨⟨t3, tm⟩, k⟩ => ?_
  exact ⟨by rw [eval_zero, t3, stat_one hv], M.frm (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k
    (by decide) (k.gpr _ (by decide)) (k.gpr _ (by decide)) (k.gpr _ (by decide)), tm⟩

/-- After a test that ended with `res`: the end of the candidate when it did
not pass (`qResult`), else `cont` from octet `u` of the tape. -/
theorem stage_ok {C : Nat} {p : PP} {mb N : Nat} {t₁ : State} {res : Option (Bool × List Byte)}
    {k : List Byte → Option (Option Nat × List Byte)} {cont : Prog isa} (e₁ : MrEnd p mb N C res t₁)
    (hcont : ∀ u t₂, u ≤ p.r.length → res = some (true, p.r.drop u) → MSt p mb N C t₂ → t₂.mem = t₁.mem →
      word t₂.mem p.B 152 = BitVec.ofNat 64 u → WP isa cont t₂ (CEnd p (k (p.r.drop u)))) :
    WP isa (.seq (.block [ldh .r3 hStat, .subi .r3 .r3 1]) (.ite (.zero .d .r3) cont qResult)) t₁
      (CEnd p (onPass res k)) := by
  obtain ⟨M₁, hnone, hsome⟩ := e₁
  rcases res with _ | ⟨b, rest⟩
  · refine WP.seq (WP.mono (stat1_ok M₁ (v := 0) (by decide) (hnone rfl)) fun t₂ ⟨hz, M₂, hm⟩ => ?_)
    refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
    exact qResult_ok (resQ := none) ⟨M₂, fun _ => (by rw [hm]; exact hnone rfl), fun _ _ h => (by cases h)⟩
      (fun _ h => by cases h)
  · obtain ⟨hS, u, hul, rfl, hUu⟩ := hsome b rest rfl
    refine WP.seq (WP.mono (stat1_ok M₁ (v := if b then 1 else 2) (by cases b <;> decide) hS)
      fun t₂ ⟨hz, M₂, hm⟩ => ?_)
    cases b
    · refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
      have e₂ : MrEnd p mb N C (some (false, p.r.drop u)) t₂ := by
        refine ⟨M₂, fun h => (by cases h), fun b' rest' h => ?_⟩
        cases h
        exact ⟨by rw [hm]; exact hS, u, hul, rfl, by rw [hm]; exact hUu⟩
      exact qResult_ok e₂ (fun _ h => by cases h)
    · refine WP.ite true hz (fun _ => ?_) (fun h => absurd h (by decide))
      exact hcont u t₂ hul rfl M₂ hm (by rw [hm]; exact hUu)

/-- q, from p in array 0. -/
theorem halveQ_from {K : Nat} {p : PP} {s : State} {c u : Nat} (M : MSt p p.bits c K s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hU : word s.mem p.B 152 = BitVec.ofNat 64 u) :
    WP isa halveQ s fun t => St p t ∧ wv t.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = (c - 1) / 2 ∧
      word t.mem p.B 152 = BitVec.ofNat 64 u := by
  have hb1 := M.st.dims.b1
  have hb2 := M.st.dims.b2
  have hdn := M.st.dims.n
  obtain ⟨hpo, _, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hpo
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  have hn₂ : wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = c := by
    rw [← Pre.val32_eq_wv]; exact M.prep.n
  refine WP.mono (halveQ_ok M.st M.ph.r10 M.ph.r11 hn₂ (by omega_arith) (by omega_arith)
    (by rw [hsl]; omega_arith)) fun t₃ ⟨⟨hq₃, _, f₃⟩, k₃⟩ => ⟨?_, ?_, ?_⟩
  · exact M.st.step (Frm.toMut f₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hsl]; exact InMut.arrays (by decide) (by simp only [saveBytes]; omega_arith)
      · exact InMut.hdr (i := 25) (by decide)) k₃ (by decide) (by decide)
  · rw [hq₃]; omega_arith
  · rw [f₃.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hsl]; exact .inl (by dsimp only; omega_arith)
      · exact .inl (by decide)) (by decide)]
    exact hU

/-- The tests, once the shape passed: one witness of p, all of q's, then
p's others, `used` after p's octets. -/
theorem tests_ok (R : RoundImpl) {p : PP} {s : State} {c : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L))) (hqo : ((c - 1) / 2) % 2 = 1)
    (hU : word s.mem p.B 152 = BitVec.ofNat 64 p.L) (hL : p.L ≤ p.r.length) :
    WP isa (tests R.name R.code) s (CEnd p (sievedTests c (p.r.drop p.L))) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hdn := h.dims.n
  have hbq : Spec.RsaKeyGen.bitLength ((c - 1) / 2) = p.bits - 1 := by
    rw [hc]; exact VG.Proof.Ffdh.ParameterCandidate.half_bitLength (by omega_arith) _
  have hbp : Spec.RsaKeyGen.bitLength c = p.bits := by
    rw [hc]; exact (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (by omega_arith) _).1
  obtain ⟨hpo, _, hcu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hcu hpo
  unfold sievedTests tests
  rw [hbq, hbp]
  -- p's first witness.
  refine WP.seq (WP.mono (testP1_ok R h hc hU hL hL) fun t₁ e₁ => ?_)
  refine stage_ok e₁ fun u₁ t₂ hu₁ _ M₂ _ hU₂ => ?_
  -- q, from p in array 0, and its test.
  unfold testQ
  refine WP.seq (WP.mono (halveQ_from M₂ hc hU₂) fun t₃ ⟨st₃, hq₃, hU₃⟩ => ?_)
  refine WP.seq (WP.mono (testQ_ok R st₃ hc hq₃ hqo hU₃ hu₁) fun t₄ e₄ => ?_)
  refine stage_ok e₄ fun u₂ t₅ hu₂ _ M₅ _ hU₅ => ?_
  -- p's other witnesses.
  unfold testRest
  refine WP.seq (WP.mono (testPR_ok R M₅.st hc hU₅ hu₂ hL) fun t₆ e₆ => ?_)
  exact pResult_ok e₆ hcu

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
