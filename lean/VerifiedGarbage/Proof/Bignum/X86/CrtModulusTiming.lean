module

public import VerifiedGarbage.Proof.Bignum.X86.CrtPair
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue

/-! # Loading and validating the public modulus preserves all call inputs -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem modulus_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (H : Inputs base bytes len args s) :
    WP isa (.seq (.block PublicFn.modulusArgs) (.block modulusCheck)) s fun t =>
      t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nf := H.fits 2 (by decide)
  have nr := H.readable 2 (by decide)
  change (args 2).toNat + (args 3).toNat ≤ 2 ^ 32 at nf
  change InRegions (s.rd ++ s.wr) (byteAddr (args 2)) (args 3).toNat at nr
  rw [H.modulus_length] at nf nr
  refine WP.seq (WP.mono (argumentPair_ok (c := BitVec.ofNat 32 len) (by decide) (by decide)
    (H.stack 2 (by decide)).readSrc (by rw [← H.nLen]; exact (H.stack 3 (by decide)).readSrc))
    fun u ⟨P, C, M, K⟩ => ?_)
  refine WP.mono (modulusCheck_ok u H.lower H.upper (by rw [P]; exact nf)
    (by rw [P, K.2.1, K.2.2]; exact nr) C) fun t ⟨Z, Mt, Kt⟩ => ?_
  rw [P, M] at Z
  exact ⟨Z, Mt.trans M, (K.mono (by decide)).trans (Kt.mono (by decide))⟩

theorem modulus_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (Pair base bytes len args) (.seq (.block PublicFn.modulusArgs) (.block modulusCheck))
      (fun _ _ => True) := by
  have Check : RelCT isa (VG.X86.Taint.Agree loadTaint) (.block modulusCheck) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) loadTaint (fun _ _ h => h) (hc := .block [])
    rfl
  apply (VG.RelCT.seq (loadArguments_relCT 2 3 (args 2) (args 3)) Check).mono
  · intro s t H
    exact ⟨H.agree, (H.left.stack 2 (by decide)).readSrc, (H.right.stack 2 (by decide)).readSrc,
      (H.left.stack 3 (by decide)).readSrc, (H.right.stack 3 (by decide)).readSrc⟩
  · exact fun _ _ h => h

end VG.Proof.Bignum.X86.Crt
