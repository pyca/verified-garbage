module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WitnessRound
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TestWitness

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Sample
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundHeader
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundTailResult
import VerifiedGarbage.Proof.Framework.Omega

/-! A complete native witness iteration through the shared windowed round. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 VG.Proof.MillerRabin.AArch64

def sampleRoundRanges (w : Nat) : List (Nat × Nat) :=
  testRanges w ++ witnessRoundRanges w ++ [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)]

theorem sampleRound_ok (M : Mont) (K : Kernel) {B p : Addr} {Z w N i uni ch : Nat}
    {bs : List Byte} {s : State}
    (h : SampleState B p Z w N bs s) (h4 : 4 ≤ w) (h128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hout : Region.Disjoint ⟨B, Z⟩ ⟨p, bs.length⟩)
    (hodd : N % 2 = 1) (hN : 3 ≤ N)
    (hlen : 2 ≤ bs.length) (hmax : bs.length < 4096) (hw : bs.length ≤ 8 * w)
    (hbits : Spec.RsaKeyGen.bitLength (N - 1) = 8 * bs.length)
    (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hUni : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni)
    (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch)
    (hi : i < 2 ^ 62) (huni : uni < 2 ^ 62) (hch : ch < 2 ^ 62) :
    WP isa (Impl.Dsa.AArch64.Generation.sampleRound M.mm K.run bs.length) s fun t =>
      let wt := Spec.RsaKeyGen.witness (N - 1) (Spec.Rsa.os2ip bs)
      let f := Spec.MillerRabin.round N wt.1
      ModulusReady t B Z w N ∧
      word t.mem B (8 * kStat) = BitVec.ofNat 64 (if f then (if i + 1 < 17 ∨ uni + wt.2.toNat < ch then 4 else 1) else 3) ∧
      (f = true → word t.mem B (8 * kI) = BitVec.ofNat 64 (i + 1) ∧
        word t.mem B (8 * kUni) = BitVec.ofNat 64 (uni + wt.2.toNat)) ∧
      WorkFrame B (sampleRoundRanges w) [⟨p, bs.length⟩] s.mem t.mem ∧ Keep mmRegs s t := by
  dsimp only
  have hz := h.ready.ws.h256
  have hn := h.ready.ws.scr.nowrap
  unfold Impl.Dsa.AArch64.Generation.sampleRound
  refine WP.seq (WP.mono (sampleWitness_ok h hEZ hodd hlen hmax hw hbits)
    fun u ⟨hu, hxu, huu, fu, ku⟩ => ?_)
  have hhdr : ∀ k, k = kI ∨ k = kUni ∨ k = kChecks → word u.mem B (8 * k) = word s.mem B (8 * k) := by
    intro k hk
    apply fu.word_eq (Z := Z)
    · simp only [testRanges, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      rcases hk with rfl | rfl | rfl <;> constructor
      all_goals simp only [slot, hdrBytes, aX, kI, kElen, kUni, kP, kChecks, kE, kU, sFn] <;> omega_arith
    · rcases hk with rfl | rfl | rfl <;> simp only [kI, kElen, kUni, kP, kChecks, kE, sFn] <;> omega
    · exact hn
    · simpa using hout
  refine WP.seq (WP.mono (witnessRound_ok M K hu h4 h128 hEZ hodd hN hxu)
    fun v ⟨hv, hflag, fv, kv⟩ => ?_)
  have hvhdr : ∀ k, k = kI ∨ k = kUni ∨ k = kChecks ∨ k = kU →
      word v.mem B (8 * k) = word u.mem B (8 * k) := by
    intro k hk
    apply fv.word_eq
    · apply round_header_ranges
      rcases hk with rfl | rfl | rfl | rfl <;> decide
    · rcases hk with rfl | rfl | rfl | rfl <;> decide
  refine WP.mono (roundTail_result hv hEZ hflag
    ((hvhdr kI (by simp)).trans ((hhdr kI (by simp)).trans hI))
    ((hvhdr kU (by simp)).trans huu)
    ((hvhdr kUni (by simp)).trans ((hhdr kUni (by simp)).trans hUni))
    ((hvhdr kChecks (by simp)).trans ((hhdr kChecks (by simp)).trans hC)) hi huni hch)
    fun t ⟨ht, hstat, hcount, ft, kt⟩ => ?_
  have fuv : WorkFrame B (testRanges w ++ witnessRoundRanges w) [⟨p, bs.length⟩] s.mem v.mem :=
    (fu.mono fun r hr => List.mem_append_left _ hr).trans
      (fv.work.mono fun r hr => List.mem_append_right _ hr)
  refine ⟨ht, hstat, hcount, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  exact (fuv.mono fun r hr => List.mem_append_left _ hr).trans
    (ft.work.mono fun r hr => List.mem_append_right _ hr)

end VG.Proof.Dsa.AArch64.Generation
