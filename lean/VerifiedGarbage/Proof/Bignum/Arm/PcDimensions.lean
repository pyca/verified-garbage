module

public import VerifiedGarbage.Spec.Rsa.Contract
public import Batteries.Logic
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Mont
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.BasesTail
import VerifiedGarbage.Proof.Bignum.Arm.CsubCT
import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
public import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.InitMetaMemory
import VerifiedGarbage.Proof.Bignum.Arm.LoadArray
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Bignum.Arm.MontRounds
import VerifiedGarbage.Proof.Bignum.Arm.MontRoundsCT
import VerifiedGarbage.Proof.Bignum.Arm.PrepareZero
import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
import VerifiedGarbage.Proof.Bignum.Arm.QuotientStage
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
import VerifiedGarbage.Proof.Bignum.Arm.ReductionStage
import VerifiedGarbage.Proof.Bignum.Arm.Round
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinish
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishMemory
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishSteps
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
import VerifiedGarbage.Proof.Bignum.Arm.RowBody
import VerifiedGarbage.Proof.Bignum.Arm.RowBody2
import VerifiedGarbage.Proof.Bignum.Arm.RowCarry
import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
import VerifiedGarbage.Proof.Bignum.Arm.RowFull
import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Bignum.Arm.Shift
import VerifiedGarbage.Proof.Bignum.Arm.ShiftArgs
import VerifiedGarbage.Proof.Bignum.Arm.ShiftCT
import VerifiedGarbage.Proof.Bignum.Arm.ShiftStep
import VerifiedGarbage.Proof.Bignum.Arm.WideMath
import VerifiedGarbage.Proof.Bignum.Arm.WideValue
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Bignum.Arm.ZeroStep
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
public import VerifiedGarbage.Proof.Bignum.Arm.BasesTail
public import VerifiedGarbage.Proof.Bignum.Arm.CsubCT
public import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
public import VerifiedGarbage.Proof.Bignum.Arm.InitMetaMemory
public import VerifiedGarbage.Proof.Bignum.Arm.LoadArray
public import VerifiedGarbage.Proof.Bignum.Arm.MontMath
public import VerifiedGarbage.Proof.Bignum.Arm.MontRounds
public import VerifiedGarbage.Proof.Bignum.Arm.MontRoundsCT
public import VerifiedGarbage.Proof.Bignum.Arm.PrepareZero
public import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
public import VerifiedGarbage.Proof.Bignum.Arm.QuotientStage
public import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ReductionStage
public import VerifiedGarbage.Proof.Bignum.Arm.Round
public import VerifiedGarbage.Proof.Bignum.Arm.RoundFinish
public import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishMemory
public import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishSteps
public import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
public import VerifiedGarbage.Proof.Bignum.Arm.Row
public import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
public import VerifiedGarbage.Proof.Bignum.Arm.RowBody
public import VerifiedGarbage.Proof.Bignum.Arm.RowBody2
public import VerifiedGarbage.Proof.Bignum.Arm.RowCarry
public import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
public import VerifiedGarbage.Proof.Bignum.Arm.RowFull
public import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
public import VerifiedGarbage.Proof.Bignum.Arm.RowStep
public import VerifiedGarbage.Proof.Bignum.Arm.Shift
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftCT
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftStep
public import VerifiedGarbage.Proof.Bignum.Arm.WideMath
public import VerifiedGarbage.Proof.Bignum.Arm.WideValue
public import VerifiedGarbage.Proof.Bignum.Arm.Zero
public import VerifiedGarbage.Proof.Bignum.Arm.ZeroStep
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.TCB.Arm.Target

/-! # The shared RSA scratch requirement fits the ARMv7 workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm
open VG.Spec.Rsa.Mont (arrAt)

theorem pc_dimensions {k len : Nat} (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (space : Spec.Rsa.publicScratchWords k ≤ len) :
    2 ≤ Spec.Rsa.modulusWords k ∧ Spec.Rsa.modulusWords k < 2 ^ 31 ∧
      arrAt (Spec.Rsa.modulusWords k) 8 ≤ 8 * len ∧
      k ≤ 8 * Spec.Rsa.modulusWords k ∧ 128 * Spec.Rsa.modulusWords k < 2 ^ 32 := by
  simp only [Spec.Rsa.modulusWords, Spec.Rsa.publicScratchWords, arrAt, Spec.Rsa.Mont.hdrBytes] at *
  omega

theorem rsa_bytes_frame {regions : List Region} {m m' : Mem} {src : Addr} {k : Nat}
    (frame : Frame regions m m') (fit : k < 2 ^ 64)
    (sep : ∀ r ∈ regions, (⟨src, k⟩ : Region).Disjoint r) :
    Spec.Rsa.bytesAt m' src k = Spec.Rsa.bytesAt m src k :=
  VG.Proof.Rsa.rsa_bytes_frame frame fit sep

end VG.Proof.Bignum.Arm
