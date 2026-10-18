module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReductionCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReductionCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Double
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Double
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-! # Constant time of the saved generator-exponent calculation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa.X86_64

def DoubleReady (a : Nat) (p : ReductionPublic) (s : State) : Prop :=
  Ws s p.B p.Z p.w ∧ 2 * wv s.mem p.B (slot p.w a) p.w < 2 ^ (64 * p.w)

theorem doubleZero_ct : RelCT isa (Two (DoubleReady 0))
    (Impl.Dsa.X86_64.Generation.doubleArray 0) (fun _ _ => True) := by
  have ct := doubleArray_ct (Φ := DoubleReady 0) (Ψ := fun _ _ => True)
    ReductionPublic.B ReductionPublic.Z ReductionPublic.w (fun _ _ h => h.1) 0 (by taint_decide)
    (fun _ _ h => WP.mono (doubleArray_ok h.1 (by decide : 0 < 16) h.2) (fun _ _ => True.intro))
  exact ct.mono (fun _ _ h => h) (fun _ _ _ => True.intro)

theorem reduceExponent_ct : RelCT isa (Two ReductionStart)
    (.seq Impl.Dsa.X86_64.Generation.reduceCandidate (Impl.Dsa.X86_64.Generation.doubleArray 0))
    (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := DoubleReady 0) reduceCandidate_ct ?_) doubleZero_ct
  intro p s h
  have hxlt : p.x < 2 ^ (64 * p.w) := h.2.1 ▸ wv_lt s.mem p.B (slot p.w 0) p.w
  have bound : 2 * (p.x / (2 * p.q)) ≤ p.x := by
    calc
      2 * (p.x / (2 * p.q)) ≤ p.q * (2 * (p.x / (2 * p.q))) :=
        Nat.le_mul_of_pos_left _ h.2.2.2
      _ = 2 * p.q * (p.x / (2 * p.q)) := by ac_rfl
      _ ≤ p.x := Nat.mul_div_le _ _
  exact WP.mono (reduceCandidate_ok h.1 h.2.1 h.2.2.1 h.2.2.2)
    fun t ⟨ht, _, hq, _, _⟩ => ⟨ht, by rw [hq]; omega⟩

end VG.Proof.Dsa.X86_64.Generation
