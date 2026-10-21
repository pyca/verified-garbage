module
public import VerifiedGarbage.Proof.Rsa.X86.CvRt.Load
public import VerifiedGarbage.Proof.Rsa.X86.CvPair

import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
public import VerifiedGarbage.Impl.Bignum.X86.ModulusCheck
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa

/-! # Loading and validating the public modulus preserves all call inputs -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem modulus_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : VG.Proof.Rsa.X86.CrtValuesRt.Lengths g) :
    WP isa (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 6)) (.block modulusCheck)) s fun t =>
      t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (inputBytes g s.mem 0)) (g.args 7).toNat) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide)
    (h.arguments 6 (by decide)).readSrc (h.arguments 7 (by decide)).readSrc)
    fun u ⟨p, c, m, k⟩ => ?_)
  refine WP.mono (modulusCheck_ok u len.lower len.upper (by rw [p]; exact h.inputFit 0)
    (by rw [p, k.2.1, k.2.2]; exact h.inputRead 0)
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using c)) fun t ⟨z, mt, kt⟩ => ?_
  rw [p, m] at z
  exact ⟨z, mt.trans m, (k.mono (by decide)).trans (kt.mono (by decide))⟩

theorem modulus_relCT (g : CallGeometry) :
    RelCT isa (Pair g) (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 6)) (.block modulusCheck))
      (fun _ _ => True) := by
  have check : RelCT isa (VG.X86.Taint.Agree loadTaint) (.block modulusCheck) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) loadTaint (fun _ _ h => h) (hc := .block [])
    rfl
  apply (VG.RelCT.seq (loadArguments_relCT 6 7 (g.args 6) (g.args 7)) check).mono
  · intro s t h
    exact ⟨h.agree, (h.left.arguments 6 (by decide)).readSrc, (h.right.arguments 6 (by decide)).readSrc,
      (h.left.arguments 7 (by decide)).readSrc, (h.right.arguments 7 (by decide)).readSrc⟩
  · exact fun _ _ h => h

end VG.Proof.Rsa.X86.CrtValues
