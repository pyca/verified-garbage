module
import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
import VerifiedGarbage.Proof.Framework.Omega

/-! Reuse RSA's array subtraction for the candidate's division remainder. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

theorem subtractRemainder_ok {s : State} {B : Addr} {Z w dst src rem : Nat}
    (h : Ws s B Z w) (hd : dst < 16) (hx : src < 16) (hr : rem < 16)
    (hdx : dst ≠ src) (hdr : dst ≠ rem)
    (hle : wv s.mem B (slot w rem) w ≤ wv s.mem B (slot w src) w) :
    WP isa (seqs (subA dst src rem)) s fun t =>
      wv t.mem B (slot w dst) w = wv s.mem B (slot w src) w - wv s.mem B (slot w rem) w ∧
      Outside B (slot w dst) (8 * w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (subA_ok h hd hx hr (.inr hdx) hdr) fun t ⟨hv, ho, _, _, _, hk⟩ => ?_
  refine ⟨?_, ho, hk.mono (by decide)⟩
  have hxlt := wv_lt s.mem B (slot w src) w
  have holt := wv_lt t.mem B (slot w dst) w
  cases hc : (!t.c) <;> rw [hc] at hv <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hv <;> omega

end VG.Proof.Dsa.AArch64.Generation
