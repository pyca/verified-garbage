module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega

/-! Conversion out of Montgomery form produces exactly the ordinary public value. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem power_decode (M : Mont) {p : Parameters} {E : Nat} {s : State} (h : Power p E s) :
 WP isa (M.mm 6 6 7) s fun t =>
 ModState p t ∧ wv t.mem p.B (slot p.w 6) p.w=Spec.Rsa.powMod p.G E p.P ∧
 Arrays p.B p.w [2,3,6] s.mem t.mem ∧ Keep mmRegs s t := by
 have bound7 : wv s.mem p.B (slot p.w 7) p.w<p.P := by rw [h.one];exact p.modulusPositive
 refine WP.mono (crtMmN_ok M h.good p.room p.positive p.width (by decide : 6<8)
  (by decide : 6<8) (by decide : 7<8) (by decide) (by decide) (by decide) (by decide) (by decide)
  h.modulus h.inverse bound7) ?_
 rintro t ⟨goodT,modulusT,inverseT,boundT,productT,frame,rest⟩
 have modT := h.toModState.after_arrays goodT frame (by decide) (by decide) (by decide)
 have eq : wv t.mem p.B (slot p.w 6) p.w*2^(64*p.w)%p.P=
  Spec.Rsa.powMod p.G E p.P*2^(64*p.w)%p.P := by
  simpa only [h.one,h.value,Nat.mul_one,Nat.mod_mod] using productT
 have cancel := VG.Proof.Bignum.mont_cancel p.coprime eq
 rw [Nat.mod_eq_of_lt boundT] at cancel
 have decoded : wv t.mem p.B (slot p.w 6) p.w=Spec.Rsa.powMod p.G E p.P := by
  simpa only [VG.Proof.Bignum.powMod_eq,Nat.mod_mod] using cancel
 exact ⟨modT,decoded,frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached
