module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Reduce
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArithmeticFrame
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Reduce
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArithmeticFrame
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Candidate reduction arithmetic leaks only its workspace and word count. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Impl.Dsa.AArch64.Generation

abbrev ArithmeticPublic := VG.Proof.Bignum.AArch64.Ws

def ArithmeticGood (p : ArithmeticPublic) (s : State) : Prop := VG.Proof.Rsa.AArch64.Ws s p.B p.Z p.w

theorem doubleArray_ct {dst : Nat} (hd : dst = 0 ∨ dst = 2) :
    RelCT isa (Two ArithmeticGood) (doubleArray dst) (Two ArithmeticGood) := by
  rcases hd with rfl | rfl
  all_goals
    unfold doubleArray
    simp only [List.append_assoc]
    exact ws_ct (fun p : ArithmeticPublic => p.B) (fun p : ArithmeticPublic => p.Z) (fun p : ArithmeticPublic => p.w) (fun _ _ h => h)
      (by taint_decide) (fun _ _ h => doubleArray_ws h (by decide))

theorem copyReduction_ct : RelCT isa (Two ArithmeticGood) (copyA 4 0) (Two ArithmeticGood) := by
  change RelCT isa (Two ArithmeticGood) (.seq (.block (ws ++ (base 0 .x16 ++ base 4 .x17))) copyWords) _
  exact ws_ct (fun p : ArithmeticPublic => p.B) (fun p : ArithmeticPublic => p.Z) (fun p : ArithmeticPublic => p.w) (fun _ _ h => h)
    (by taint_decide) (fun _ _ h => copyArray_ws h (by decide) (by decide) (by decide))

theorem zeroReduction_ct : RelCT isa (Two ArithmeticGood) (zeroA 1) (fun _ _ => True) := by
  change RelCT isa (Two ArithmeticGood) (.seq (.block (ws ++ (base 1 .x8 ++ [movi .x7 0]))) zeroAcc) _
  exact ws_ct0 (fun p : ArithmeticPublic => p.B) (fun p : ArithmeticPublic => p.Z) (fun p : ArithmeticPublic => p.w) (fun _ _ h => h) (by taint_decide)

theorem divideReduction_ct : RelCT isa (Two ArithmeticGood) (divmod 0 1 2 3) (Two ArithmeticGood) := by
  have he : divmod 0 1 2 3 = .seq (zeroA 1) (.seq (.block [.lsl .x .x6 .x12 6])
      (.loop (divStep 0 1 2 3) (.nonzero .x .x6))) := rfl
  rw [he]
  refine pin_seq [.x0, .x12, .x11] (fun p : ArithmeticPublic => wsVal p.B p.w)
    zeroReduction_ct ?_ (by taint_decide) ?_
  · intro p s h
    exact WP.mono (zeroA_ok h (by decide : 1 < 16)) fun _ ⟨_, _, h12, h11, _, hk⟩ =>
      wsVal_of ((hk.gpr .x0 (by decide)).trans h.x0) h12 h11
  · intro p s h
    rw [← he]
    exact divideArray_ws h

theorem subtractReduction_ct : RelCT isa (Two ArithmeticGood) (seqs (subA 5 4 1)) (Two ArithmeticGood) := by
  rw [subA_eq']
  exact ws_ct (fun p : ArithmeticPublic => p.B) (fun p : ArithmeticPublic => p.Z) (fun p : ArithmeticPublic => p.w) (fun _ _ h => h)
    (by taint_decide) (fun _ _ h => subtractArray_ws h)

theorem incrementReduction_ct : RelCT isa (Two ArithmeticGood) (.block (incrementEven 5)) (Two ArithmeticGood) := by
  unfold incrementEven
  simp only [List.append_assoc]
  exact ws_block_ct (fun p : ArithmeticPublic => p.B) (fun p : ArithmeticPublic => p.Z) (fun p : ArithmeticPublic => p.w) (fun _ _ h => h)
    (by taint_decide) (fun _ _ h => incrementEven_ws h (by decide))

theorem reduceCandidate_ct : RelCT isa (Two ArithmeticGood) reduceCandidate (Two ArithmeticGood) :=
  RelCT.seq copyReduction_ct (RelCT.seq divideReduction_ct (RelCT.seq subtractReduction_ct incrementReduction_ct))

end VG.Proof.Dsa.AArch64.Generation
