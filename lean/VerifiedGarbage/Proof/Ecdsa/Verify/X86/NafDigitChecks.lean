import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafAddShared

/-!
# ECDSA verification on x86 (32-bit): the checks of the digits' additions
-/

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
