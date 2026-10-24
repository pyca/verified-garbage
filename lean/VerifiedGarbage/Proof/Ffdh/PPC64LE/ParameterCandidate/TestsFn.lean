module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Tests
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Result
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Checked
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# An FFDH parameter candidate on PPC64LE: the tests

`tests_ok`: the test of q, then of p if q passed, and their result.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses testsSpec)

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
    omega

/-- `hStat` against 1. -/
theorem stat1_ok {p : PP} {mb N v : Nat} {s : State} (M : MSt p mb N s) (hv : v < 2 ^ 60)
    (hS : word s.mem p.B 160 = BitVec.ofNat 64 v) :
    WP isa (.block [ldh .r3 hStat, .subi .r3 .r3 1]) s fun t =>
      isa.eval (.zero .d .r3) t = some (decide (v = 1)) ∧ MSt p mb N t ∧ t.mem = s.mem := by
  have l160 : InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 160) 8 := M.st.ld (d := 160) (by decide)
  refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 v - BitVec.ofNat 64 1 ∧ t.mem = s.mem)
    (by simp only [ldh, hStat]; prun [M.st.r31, l160, show s.mem.readW (p.B + BitVec.ofNat 64 160) 64 =
      BitVec.ofNat 64 v from hS]) (by decide)) fun t ⟨⟨t3, tm⟩, k⟩ => ?_
  exact ⟨by rw [eval_zero, t3, stat_one hv], M.frm (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k
    (by decide) (k.gpr _ (by decide)) (k.gpr _ (by decide)) (k.gpr _ (by decide)), tm⟩

/-- The tests, once the shape passed: q in array 0 (in p's width), `used`
after p's octets. -/
theorem tests_ok (R : RoundImpl) {p : PP} {s : State} {c : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hq : wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = (c - 1) / 2) (hqo : ((c - 1) / 2) % 2 = 1)
    (hU : word s.mem p.B 152 = BitVec.ofNat 64 p.L) (hL : p.L ≤ p.r.length) :
    WP isa (tests R.name R.code) s (CEnd p (testsSpec c (p.r.drop p.L))) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hbq : Spec.RsaKeyGen.bitLength ((c - 1) / 2) = p.bits - 1 := by
    rw [hc]; exact VG.Proof.Ffdh.ParameterCandidate.half_bitLength (by omega) _
  have hbp : Spec.RsaKeyGen.bitLength c = p.bits := by
    rw [hc]; exact (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (by omega) _).1
  obtain ⟨_, _, hcu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hcu
  unfold testsSpec tests
  rw [hbq, hbp]
  refine WP.seq (WP.mono (testQ_ok R h hc hq hqo hU hL) fun t₁ e₁ => ?_)
  generalize checkWitnesses ((c - 1) / 2) (Spec.Ffdh.primeChecks (p.bits - 1)) (p.r.drop p.L) = resQ at e₁ ⊢
  obtain ⟨M₁, hnone, hsome⟩ := e₁
  rcases resQ with _ | ⟨b, rest⟩
  · refine WP.seq (WP.mono (stat1_ok M₁ (v := 0) (by decide) (hnone rfl)) fun t₂ ⟨hz, M₂, hm⟩ => ?_)
    refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
    exact qResult_ok (resQ := none) ⟨M₂, fun _ => (by rw [hm]; exact hnone rfl), fun _ _ h => (by cases h)⟩
      (fun _ h => by cases h)
  · obtain ⟨hS, u, hul, rfl, hUu⟩ := hsome b rest rfl
    refine WP.seq (WP.mono (stat1_ok M₁ (v := if b then 1 else 2) (by cases b <;> decide) hS)
      fun t₂ ⟨hz, M₂, hm⟩ => ?_)
    have e₂ : MrEnd p (p.bits - 1) ((c - 1) / 2) (some (b, p.r.drop u)) t₂ := by
      refine ⟨M₂, fun h => (by cases h), fun b' rest' h => ?_⟩
      cases h
      exact ⟨by rw [hm]; exact hS, u, hul, rfl, by rw [hm]; exact hUu⟩
    cases b
    · refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
      exact qResult_ok e₂ (fun _ h => by cases h)
    · refine WP.ite true hz (fun _ => ?_) (fun h => absurd h (by decide))
      refine WP.seq (WP.mono (testP_ok R M₂.st hc (by rw [hm]; exact hUu) hul hL) fun t₃ e₃ => ?_)
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Option.bind]
      generalize checkWitnesses c (Spec.Ffdh.primeChecks p.bits) (p.r.drop u) = resP at e₃ ⊢
      refine WP.mono (pResult_ok e₃ hcu) fun t ht => ?_
      rcases resP with _ | ⟨_ | _, _⟩ <;> exact ht

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
