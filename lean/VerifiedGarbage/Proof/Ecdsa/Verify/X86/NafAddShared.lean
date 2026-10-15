module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafPrepChecks
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafPrepChecks
public import VerifiedGarbage.Proof.Weierstrass.X86.NafTableTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86.NafTableTiming
import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P256
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P256
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.X25519.X86.Column
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.X25519.X86.Column

/-!
# ECDSA verification on x86 (32-bit): the checks shared by the NAF's additions

The table's additions (`NafPointChecks`) and the digits' (`NafDigitChecks`)
add to the same point `R`, into the same `D`: the checks of the code that
reads only those are the same, made once here, so that the two modules check
the rest in parallel.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Impl.Ecdsa.X86 VG.Proof.Weierstrass.X86 VG.Proof.Ecdsa.X86

def nafK : WinCfg := Impl.Ecdsa.Verify.X86.Cfg.nafQ p256Comb

def nafAddZeroP : Prog isa := (.block (Jacobian.zeroTest nafK.M.n nafK.R.z))
materialize_code nafAddZeroP

theorem nafAddZeroP_ct : ScratchCT nafAddZeroP :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by native_taint_decide)

def nafAddZeroH : Prog isa := (.block (Jacobian.zeroTest nafK.M.n nafK.S.t3))
materialize_code nafAddZeroH

theorem nafAddZeroH_ct : ScratchCT nafAddZeroH :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by native_taint_decide)

def nafAddZeroR : Prog isa := (.block (Jacobian.zeroTest nafK.M.n nafK.S.t5))
materialize_code nafAddZeroR

theorem nafAddZeroR_ct : ScratchCT nafAddZeroR :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by native_taint_decide)

def nafAddCopyP : Prog isa := (.block (copyPt nafK.M.n nafK.D nafK.R))
materialize_code nafAddCopyP

theorem nafAddCopyP_ct : ScratchCT nafAddCopyP :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by native_taint_decide)

def nafAddDouble : Prog isa := (fprog p256Comb.SP (dblJMul nafK.S nafK.R nafK.D))
materialize_code nafAddDouble

theorem nafAddDouble_ct : ScratchCT nafAddDouble :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by native_taint_decide)

def nafAddInfinity : Prog isa := (.block (Jacobian.infinity nafK nafK.D))
materialize_code nafAddInfinity

theorem nafAddInfinity_ct : ScratchCT nafAddInfinity :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by native_taint_decide)

/-- The checks of an addition of `q` to `R` into `D`, from those of the code
reading `q`. -/
theorem nafAdd_checks {q : Pt} (zeroQ : ScratchCT (.block (Jacobian.zeroTest nafK.M.n q.z)))
    (copyQ : ScratchCT (.block (copyPt nafK.M.n nafK.D q)))
    (head : ScratchCT (fprog p256Comb.SP (jacHead nafK.S nafK.R q)))
    (tail : ScratchCT (fprog p256Comb.SP (jacTail nafK.S nafK.R q nafK.D))) :
    JacAddChecks nafK p256Comb.SP nafK.R q nafK.D :=
  ⟨nafAddZeroP_ct, zeroQ, nafAddZeroH_ct, nafAddZeroR_ct, nafAddCopyP_ct, copyQ, head, tail,
    nafAddDouble_ct, nafAddInfinity_ct⟩

end VG.Proof.Ecdsa.Verify.X86
