module

public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ProbablePrime
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Workspace
import VerifiedGarbage.Proof.Framework.Omega

/-! Bound every write of the complete native candidate-primality call. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Ffdh.AArch64.ParameterCandidate VG.Proof.MillerRabin VG.Proof.MillerRabin.AArch64

theorem primeRanges_bound {w : Nat} (hw : w ≤ 48) :
    ∀ r ∈ primeRanges w, r.1 + r.2 ≤ VG.Impl.Dsa.Generation.Layout.arithmeticBytes := by
  simp only [primeRanges, primeTrialRanges, modulusRanges, mpRanges, mpTail,
    drawRoundRanges, sampleRoundRanges, testRanges, witnessRoundRanges, witnessMontRanges, Caller.callRanges,
    mutRanges, Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Caller.pad, slot, hdrBytes, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
    aX, aTab, aAcc, aTmp, aY, aXm, aOne, aR2, aR1, aRm1, aE,
    kElen, kP, kUsed, kI, kUni, kStat, kU, sMinv, sCnt, sFn,
    VG.Impl.Dsa.Generation.Layout.arithmeticBytes]
  and_intros <;> omega

theorem checkPrimeRanges_bound {w : Nat} (hw : w ≤ 48) :
    ∀ r ∈ workspaceRanges ++ (128, 128) :: (slot w 0, 8 * (w + 2)) :: primeRanges w,
      r.1 + r.2 ≤ VG.Impl.Dsa.Generation.Layout.arithmeticBytes := by
  intro r hr
  simp only [workspaceRanges, List.cons_append, List.nil_append, List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | hr
  · decide
  · decide
  · decide
  · decide
  · simp only [slot, hdrBytes, VG.Impl.Dsa.Generation.Layout.arithmeticBytes]; omega
  · exact primeRanges_bound hw r hr

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

end VG.Proof.Dsa.AArch64.Generation
