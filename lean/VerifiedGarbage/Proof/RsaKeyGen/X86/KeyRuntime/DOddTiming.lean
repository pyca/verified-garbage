module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseTiming
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ArrayDivision
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DivisionFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-! # The odd-exponent path leaks only public data

Its pieces before and after the inversion of `L mod e` modulo the public exponent are checked by
the taint analysis; the inversion is `inverseFrom_trace`. -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aL aE aU aV kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr

theorem dOdd_divide_public : Public (divFull aL aE aU aV) := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem dOdd_setup_public :
    Public (inverseSetup .exponent (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aV) (.fixed kEv)) := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem dOdd_rest_public : Public (seqs [gcdIsOne .exponent, lAtLeastTwo]) := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem dOdd_finish_public : Public dOddFinish := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

/-- The odd-exponent path's state: the public exponent `e`, also loaded as a number. -/
def OddStart (B : Addr) (Z n e : Nat) (s : State) : Prop :=
  Ws s B Z n 32 ∧ val32 s.mem B kEv 2 = e ∧ num s.mem B n aE = e

theorem dOdd_trace (B : Addr) (Z n e : Nat) (large : 3 ≤ e) (odd : e % 2 = 1) :
    RelCT isa (Both (OddStart B Z n e)) dOdd (VG.X86.Taint.Agree runtimeTaint) := by
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ P E₁ E₂
  have layout : VG.Proof.RsaKeyGen.X86.Key.InverseLayout Z 2 (arr n aV) kEv := by
    have fit := P.1.1.arr_fit (j := aV) (by decide)
    have head := P.1.1.hdr_le
    refine ⟨?_, ?_, Or.inr (VG.Proof.RsaKeyGen.X86.Key.inverse_end_le (by have := P.1.1.size; omega)
      (by decide)), Or.inl (by decide)⟩
    · unfold S at fit
      omega
    · unfold kEv hdr at *
      omega
  refine (?_ : RelCT isa _ dOdd _) s₁ s₂ tr₁ tr₂ t₁ t₂ P E₁ E₂
  unfold dOdd dOddPrepare seqs
  refine RelCT.seq (RelCT.seq (step_trace (Q := FromReady B Z n 32 .exponent (.fixed kEv)) dOdd_divide_public
    fun s ⟨h, E, L⟩ => WP.mono (arrayDivision_ok h (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [L]; omega))
      fun w ⟨hw, Ow, _, _, _⟩ => ?_) (RelCT.seq (inverseFrom_trace (N := 32) (by decide) (by decide)
        layout dOdd_setup_public) (public_trace dOdd_rest_public))) (public_trace dOdd_finish_public)
  have same := VG.Proof.RsaKeyGen.X86.Key.exponent_preserves_e (exponent_division_frame Ow)
  refine ⟨hw, ?_, ?_⟩
  · change val32 w.mem B kEv 2 % 2 = 1
    rw [same, E]
    exact odd
  · change 1 < val32 w.mem B kEv 2
    rw [same, E]
    omega

end VG.Proof.RsaKeyGen.X86.KeyRuntime
