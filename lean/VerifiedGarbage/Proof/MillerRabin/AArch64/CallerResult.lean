module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Rsa.Ranges
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! # Recover the arithmetic context after a shared-round call -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64.Caller

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.RsaKeyGen.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.MillerRabin.AArch64
open VG.Impl.Rsa.AArch64.Keys
open VG.Impl.MillerRabin.AArch64.Caller
open VG.Proof.MlKem.AArch64 (Keep)

private theorem call_mut (w : Nat) : ∀ r ∈ callRanges w, KMut r := by
  simp only [callRanges, mutRanges, Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, KMut, pad, slot, hdrBytes, aOne,
    Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, sW, sMinv, sArr, sStride, sFn]
  and_intros <;> omega_arith

private theorem call_minv (w : Nat) :
    ∀ r ∈ callRanges w, 8 * sMinv + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMinv := by
  simp only [callRanges, mutRanges, Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, pad, slot, hdrBytes, aOne, sMinv,
    Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  and_intros <;> omega_arith

private theorem call_array (w j : Nat) (hj : j ∈ [0, 4, 9, 10, 27]) :
    ∀ r ∈ callRanges w, slot w j + 8 * (w + 1) ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [callRanges, mutRanges, Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, pad, slot, hdrBytes, aOne,
      Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
    and_intros <;> omega_arith

theorem call_result_ok (M : Mont) (name : String) (hnf : (round M.mm).noFrames = true)
    {s : State} {B : Addr} {Z w c bm b : Nat}
    (hc : MrCtx s B Z w c bm) (he : ECtx s.mem B w c)
    (h4 : 4 ≤ w) (h128 : w ≤ 128) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (ho : c % 2 = 1) (h3 : 3 ≤ c)
    (hx : wv s.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c) :
    WP isa (call name (round M.mm)) s fun t =>
      (∃ bm', MrCtx t B Z w c bm') ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) ∧
      Frm B (callRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (call_frame_ok M name hnf hc he h4 h128 hEZ ho h3 hx) ?_
  rintro t ⟨hflag, hf, hk⟩
  have htws := hc.ws.congr' hf (call_mut w) hk (by decide)
  have hnword : word t.mem B (slot w aN) = word s.mem B (slot w aN) :=
    hf.word_eq (fun r hr => by
      have hh := call_array w 0 (by simp) r hr
      change slot w 0 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ slot w 0
      omega_arith) (by
        have hp := hc.ws.scr.nowrap
        have hz := hc.ws.hZ
        simp only [slot, hdrBytes, aN] at hz ⊢
        omega_arith)
  have hminv : word t.mem B (8 * sMinv) = word s.mem B (8 * sMinv) :=
    hf.word_eq (call_minv w) (by simp only [sMinv]; decide)
  have hinv : ((word t.mem B (slot w aN)).toNat * (word t.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 := by
    rw [hnword, hminv]
    exact hc.inv
  have hread (j : Nat) (hj : j ∈ [0, 4, 9, 10]) :
      wv t.mem B (slot w j) w = wv s.mem B (slot w j) w := by
    apply hf.wv_eq
    · intro r hr
      have hh := call_array w j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; rcases hj with rfl | rfl | rfl | rfl <;> simp) r hr
      omega_arith
    · have hp := hc.ws.scr.nowrap
      have hz := hc.ws.hZ
      have hj16 : j < 16 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega_arith
      have hm := VG.Proof.Bignum.slot_mono w (by omega_arith : j ≤ 16)
      have hs := VG.Proof.Bignum.slot_sep (w := w) (j := j) (k := 16) (by omega_arith)
      omega_arith
  refine ⟨⟨wv t.mem B (slot w aB) w, htws, hinv, ?_, rfl, ?_, ?_⟩, ?_, hflag, hf, hk⟩
  · exact (hread aN (by simp [aN])).trans hc.n
  · exact (hread aR1 (by simp [aR1])).trans hc.r1
  · exact (hread aRm1 (by simp [aRm1])).trans hc.rm1
  · apply he.of_frm hf
    · intro r hr
      exact call_array w 27 (by simp) r hr
    · have hp := hc.ws.scr.nowrap
      omega_arith

end VG.Proof.MillerRabin.AArch64.Caller
