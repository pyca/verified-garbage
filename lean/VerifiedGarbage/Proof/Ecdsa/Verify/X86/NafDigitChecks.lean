module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafAddShared
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafPrepChecks
import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
import VerifiedGarbage.Proof.Weierstrass.WinLay
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
import VerifiedGarbage.Proof.Weierstrass.X86.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafAddShared
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafPrepChecks
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
meta import VerifiedGarbage.Proof.Weierstrass.WinLay
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Weierstrass.X86.TComb
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.FieldTiming
import VerifiedGarbage.Proof.Weierstrass.X86.JacAddTiming
meta import VerifiedGarbage.Proof.Ecdsa.X86.Flags
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Weierstrass.X86.FieldTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86.JacAddTiming

/-!
# ECDSA verification on x86 (32-bit): the checks of the digits' additions
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Impl.Ecdsa.X86 VG.Proof.Weierstrass.X86 VG.Proof.Ecdsa.X86

def nafDigitAddZeroQ : Prog isa := (.block (Jacobian.zeroTest nafK.M.n nafK.E.z))
materialize_code nafDigitAddZeroQ

theorem nafDigitAddZeroQ_ct : ScratchCT nafDigitAddZeroQ :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafDigitAddCopyQ : Prog isa := (.block (copyPt nafK.M.n nafK.D nafK.E))
materialize_code nafDigitAddCopyQ

theorem nafDigitAddCopyQ_ct : ScratchCT nafDigitAddCopyQ :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafDigitAddHead : Prog isa := (fprog p256Comb.SP (jacHead nafK.S nafK.R nafK.E))
materialize_code nafDigitAddHead

theorem nafDigitAddHead_ct : ScratchCT nafDigitAddHead :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafDigitAddTail : Prog isa := (fprog p256Comb.SP (jacTail nafK.S nafK.R nafK.E nafK.D))
materialize_code nafDigitAddTail

theorem nafDigitAddTail_ct : ScratchCT nafDigitAddTail :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

theorem nafDigitAdd_checks : JacAddChecks nafK p256Comb.SP nafK.R nafK.E nafK.D :=
  nafAdd_checks nafDigitAddZeroQ_ct nafDigitAddCopyQ_ct nafDigitAddHead_ct nafDigitAddTail_ct

end VG.Proof.Ecdsa.Verify.X86
