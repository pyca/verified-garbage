module

public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ProbablePrime
import VerifiedGarbage.Proof.Framework.Omega

/-! # Bound every write of the complete native primality operation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Proof.MillerRabin VG.Proof.MillerRabin.X86_64

theorem primeRanges_bound {w : Nat} (hw : w ≤ 48) :
    ∀ r ∈ primeRanges w, r.1 + r.2 ≤ VG.Impl.Dsa.Generation.Layout.arithmeticBytes := by
  simp only [primeRanges, primeTrialRanges, modulusRanges, prepareRanges, r2Ranges, constantRanges,
    drawRoundRanges, sampleRoundRanges, testRanges, witnessRoundRanges, Caller.callRanges,
    mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Caller.pad, slot, hdrBytes, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
    aTab, aAcc, aTmp, aY, aXm, aOne, aR2, aR1, aRm1, aE,
    kElen, kP, kT0, kT1, kT2, kUsed, kI, kUni, kStat, kU, sMinv, sCnt, sFn,
    VG.Impl.Dsa.Generation.Layout.arithmeticBytes]
  and_intros <;> omega

/-- Complete setup and loading fit in the same allocation as the round. -/
theorem checkPrimeRanges_bound {w : Nat} (hw : w ≤ 48) :
    ∀ r ∈ (48, 80) :: (224, 8) :: (128, 128) :: (slot w 0, 8 * (w + 2)) :: primeRanges w,
      r.1 + r.2 ≤ VG.Impl.Dsa.Generation.Layout.arithmeticBytes := by
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | rfl | hr
  · decide
  · decide
  · decide
  · simp only [slot, hdrBytes, VG.Impl.Dsa.Generation.Layout.arithmeticBytes]; omega
  · exact primeRanges_bound hw r hr

/-- Convert an offset-based workspace frame to the global memory frame used
by hashing and the outer parameter-generation controllers. -/
theorem prime_global_frame {B : Addr} {rs : List (Nat × Nat)} {extra : List Region} {m m' : Mem}
    (hf : WorkFrame B rs extra m m')
    (hb : ∀ r ∈ rs, r.1 + r.2 ≤ VG.Impl.Dsa.Generation.Layout.arithmeticBytes) :
    Frame (⟨B, VG.Impl.Dsa.Generation.Layout.arithmeticBytes⟩ :: extra) m m' := by
  intro a ha
  apply hf a (fun r hr => ha r (List.mem_cons_of_mem _ hr))
  intro r hr
  right
  have h := ha ⟨B, VG.Impl.Dsa.Generation.Layout.arithmeticBytes⟩ (by simp)
  change ¬ ofs B a < VG.Impl.Dsa.Generation.Layout.arithmeticBytes at h
  exact Nat.le_trans (hb r hr) (Nat.le_of_not_gt h)

end VG.Proof.Dsa.X86_64.Generation
