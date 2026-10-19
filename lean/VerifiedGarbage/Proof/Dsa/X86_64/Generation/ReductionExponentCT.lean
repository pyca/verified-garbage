module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionState

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReductionCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReductionCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Double
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Double
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReduction
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReduction
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Division
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Increment
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Reduce
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Subtract
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.BitLengthBounds
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Generation.PReduction
meta import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Division
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Increment
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Reduce
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Subtract
meta import VerifiedGarbage.Proof.Ffdh.KeyScalar
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops

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
