module

public import VerifiedGarbage.Proof.EcKey.X86.CombCT
public import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import Mathlib.Data.Finset.Attr
import Mathlib.Data.List.Forall2
import Mathlib.Tactic.SetLike
import Batteries.Data.List.Lemmas
import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
import VerifiedGarbage.Proof.Ecdsa.X86.Lit
meta import VerifiedGarbage.Proof.EcKey.X86.CombCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Data.List.Forall2
meta import Mathlib.Tactic.SetLike
meta import Batteries.Data.List.Lemmas
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-! # P-256 public keys on x86 (32-bit): the constant time of the stages around the comb -/

@[expose] public section

namespace VG.Proof.EcKey.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86
open VG.Impl.EcKey.X86 (Args.publicKey)

def pkPrepCode : Prog isa := p256Comb.prepareWith Args.publicKey
def pkTailCode : Prog isa := .seq p256Comb.pPow
  (Impl.EcKey.X86.Cfg.middle p256Comb)
materialize_code pkPrepCode
materialize_code pkTailCode

theorem pkPrep_rel : RelCT isa (VG.X86.Taint.Agree (argτ [.esp] 3 24)) pkPrepCode (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)

theorem pkTail_rel : RelCT isa (VG.X86.Taint.Agree (scratchArgτ 3 true 24)) pkTailCode (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)

/-- The taint checks of the stages of P-256's public key. -/
theorem p256PkCT : PkStagesCT p256Comb := ⟨pkPrep_rel, pkTail_rel⟩

end VG.Proof.EcKey.X86
