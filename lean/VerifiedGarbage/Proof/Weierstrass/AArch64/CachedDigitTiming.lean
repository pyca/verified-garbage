module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedEntryTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedAddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

structure DigitChecks : Prop where
  entry : EntryChecks
  add : Checks
  copy : FieldCT (.block (copyPt K.M.n K.R K.D))
  digit : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
    (.block (Naf.digitRead K))

end VG.Proof.Weierstrass.AArch64.CachedField
