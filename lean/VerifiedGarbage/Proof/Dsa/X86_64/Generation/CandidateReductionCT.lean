module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionState
public import Mathlib.Tactic.Set
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionState
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Increment
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Increment
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
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReduction
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Division
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
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReduction
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Division
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
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops

/-! # Constant time of p reduction from X and 2q -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Bignum.X86_64

theorem reductionCopy_ct : RelCT isa (Two ReductionStart) (copyA 4 0) (Two ReductionCopied) := by
  have e : copyA 4 0 = .seq (.block (ws ++ (base 0 .rsi ++ base 4 .rbx)))
      VG.Impl.Rsa.X86_64.copyWords := by simp only [copyA, List.append_assoc]
  rw [e]
  exact ws_ct ReductionPublic.B ReductionPublic.Z ReductionPublic.w (fun _ _ h => h.1)
    (by taint_decide) (fun _ _ h => by rw [← e]; exact reductionCopy_state h)

theorem reductionDivide_ct :
    RelCT isa (Two ReductionCopied) (divmod 0 1 2 3) (Two ReductionDivided) :=
  candidateDivmod_ct ReductionPublic.B ReductionPublic.Z ReductionPublic.w
    (fun _ _ h => h.1.1) (fun _ _ h => reductionDivide_state h)

theorem reductionSubtract_ct : RelCT isa (Two ReductionDivided)
    (Impl.Dsa.X86_64.Generation.subtractRemainder 5 4 1) (Two ReductionSubtracted) :=
  subtractRemainder_ct ReductionPublic.B ReductionPublic.Z ReductionPublic.w
    (fun _ _ h => h.1) 5 4 1 (by taint_decide) (fun _ _ h => reductionSubtract_state h)

theorem reductionIncrement_ct : RelCT isa (Two ReductionSubtracted)
    (.block (Impl.Dsa.X86_64.Generation.incrementEven 5)) (fun _ _ => True) := by
  have ct := incrementEven_ct (Φ := ReductionSubtracted) (Ψ := fun _ _ => True)
    ReductionPublic.B ReductionPublic.Z ReductionPublic.w (fun _ _ h => h.1) 5 (by taint_decide)
    (fun _ _ h => WP.mono (incrementEven_ok h.1 (by decide : 5 < 16) h.2) (fun _ _ => True.intro))
  exact ct.mono (fun _ _ h => h) (fun _ _ _ => True.intro)

theorem reduceCandidate_ct : RelCT isa (Two ReductionStart)
    Impl.Dsa.X86_64.Generation.reduceCandidate (fun _ _ => True) :=
  RelCT.seq reductionCopy_ct (RelCT.seq reductionDivide_ct (RelCT.seq reductionSubtract_ct reductionIncrement_ct))

end VG.Proof.Dsa.X86_64.Generation
