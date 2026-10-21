module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

public import VerifiedGarbage.Proof.Rsa.X86.RvOrder
import VerifiedGarbage.Proof.Rsa.X86.RvBatchGcd

/-! # Computing and ordering the two factors from the search result -/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (sub32)

theorem factors_ok {g : Geo} {s0 s : State} {A V : Nat → Nat} {m y : Nat}
    (h : KS g s0 A [mY, aN, aZ, aOne] (fun _ => 0) [] V [sMask] s)
    (modulus : A aN = m) (value : A mY = y) (zero : A aZ = 0) (one : A aOne = 1)
    (odd : m % 2 = 1) (hm : 1 < m) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.factors s fun t =>
      KS g s0 (AF (Nat.gcd (sub32 g.w y 1) m) (m / Nat.gcd (sub32 g.w y 1) m))
        [5, 6, aZero] (fun _ => 0) [] V [sMask] t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.factors
  simp only [seqs, VG.Impl.Rsa.X86.RecoverRt.factorTail]
  refine WP.seq (WP.mono (gcdSet_ok h modulus value zero one) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (batchGcd_ok h1 odd hm) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (divSet_ok h2) fun s3 ⟨h3, top⟩ => ?_)
  refine WP.seq (WP.mono (divide_ok h3 top (Nat.gcd_pos_of_pos_right _ (by omega))) fun s4 h4 => ?_)
  exact order_ok h4

end VG.Proof.Rsa.X86.Recover
