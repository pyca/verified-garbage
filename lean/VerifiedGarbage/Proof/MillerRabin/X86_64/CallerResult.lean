module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerCall
import VerifiedGarbage.Proof.Framework.Omega

/-! # Reuse the Montgomery context after the actual shared round call -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.MillerRabin.X86_64.Caller
open VG.Proof.MlKem.X86_64

private theorem call_header (w j : Nat) (hj : j < 16) :
    ∀ r ∈ callRanges w, 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j := by
  simp only [callRanges, mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, pad, slot, hdrBytes, aR1,
    Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  and_intros <;> left <;> omega_arith

private theorem call_array (w j : Nat) (hj : j ∈ [0, 24, 25, 26]) :
    ∀ r ∈ callRanges w, slot w j + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl
  all_goals
    simp only [callRanges, mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, pad, slot, hdrBytes, aR1,
      Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
    and_intros <;> omega_arith

private theorem call_exponent (w : Nat) :
    ∀ r ∈ callRanges w, slot w aE + 8 * (w + 1) ≤ r.1 ∨ r.1 + r.2 ≤ slot w aE := by
  simp only [callRanges, mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, pad, slot, hdrBytes, aR1, aE,
    Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  and_intros <;> omega_arith

theorem call_result_ok (v : RoundImpl) {s : State} {B : Addr} {Z w c bm b : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c) (hd : MrDims B Z w)
    (hZ : slot w 28 ≤ Z) (hr : Room s B Z)
    (ho : c % 2 = 1) (h3 : 3 ≤ c)
    (hx : wv s.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c) :
    WP isa (call v.name v.code) s fun t =>
      (∃ bm', MrCtx t B Z w mi c bm') ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) ∧
      WorkFrame B (callRanges w) [below (s.gpr .rsp) 128] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.good.scr.nowrap
  have hz := hZ
  refine WP.mono (call_ok v hc he hd hZ hr ho h3 hx) ?_
  rintro t ⟨hdi, hflag, hf, hk, _⟩
  have hext : ∀ r ∈ [below (s.gpr .rsp) 128], Region.Disjoint ⟨B, Z⟩ r := by
    intro r h
    simp only [List.mem_singleton] at h
    subst r
    exact hr.disjoint
  have hHdr : ∀ j < 16, word t.mem B (8 * j) = word s.mem B (8 * j) := by
    intro j hj
    exact hf.word_eq (d := 8 * j) (call_header w j hj) (by
      have hh := hdr_lt_slot w 28 (by omega_arith : j < 32)
      omega_arith) hn hext
  have hArr : ∀ j ∈ [0, 24, 25, 26], wv t.mem B (slot w j) w = wv s.mem B (slot w j) w := by
    intro j hj
    apply hf.wv_eq (d := slot w j) (call_array w j hj) ?_ hn hext
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;>
      simp only [slot, hdrBytes] at hz ⊢ <;> omega_arith
  have hg : Good t B Z w mi := ⟨hc.good.scr.congr hk.2.2, hdi,
    ⟨(hHdr sW (by decide)).trans hc.good.hdr.hw,
      (hHdr sMinv (by decide)).trans hc.good.hdr.hminv,
      fun j hj => (hHdr (sArr j) (by unfold sArr; omega_arith)).trans (hc.good.hdr.harr j hj)⟩⟩
  refine ⟨⟨wv t.mem B (slot w aB) w, ⟨hg, ?_, (hArr aN (by simp [aN])).trans hc.n, rfl,
    (hArr aR1 (by simp [aR1])).trans hc.r1, (hArr aRm1 (by simp [aRm1])).trans hc.rm1⟩⟩,
    ⟨(hArr aE (by simp [aE])).trans he.e, ?_⟩, hflag, hf, hk⟩
  · rw [hf.word_eq (d := slot w aN) (fun r hr => by
      have hh := call_array w 0 (by simp) r hr
      have := hd.w4
      simpa only [aN] using hh.imp (fun h => by omega_arith) id) (by
        simp only [slot, hdrBytes, aN] at hz ⊢; omega_arith) hn hext]
    exact hc.inv
  · rw [hf.word_eq (d := slot w aE + 8 * w) (fun r hr => by
      have hh := call_exponent w r hr
      omega_arith) (by simp only [slot, hdrBytes, aE] at hz ⊢; omega_arith) hn hext]
    exact he.l

end VG.Proof.MillerRabin.X86_64.Caller
