module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextArgument
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEnvironment
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext

/-! # Establish the three runtime widths from the retained cdecl arguments -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.Rsa.X86.KeyRt (kw RtWs)
open VG.Proof.Bignum.X86 (CallArgument)
open VG.Proof.RsaKeyGen.X86.Key (Environment)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context)

theorem context_workspace {E : Environment} {p : BitVec 32} {s : State}
    (v : E.Valid) (C : Context E.base E.size p E.argument s)
    (old : VG.Proof.Rsa.X86.Keys.Ws s E.base E.size E.n 32) : Ws s E.base E.size E.n 32 := by
  obtain ⟨lo, hi, nk, kp, ke, plen⟩ := v.widths
  have width : E.n % 4 = 0 := by omega
  have resize (k : Nat) (positive : 0 < k) (small : k ≤ E.n) :
      VG.Proof.Rsa.X86.Keys.Ws s E.base E.size k 32 := by
    refine ⟨old.workspace, Nat.le_trans ?_ old.fits, positive, Nat.le_trans small old.wle⟩
    unfold VG.Proof.Rsa.X86.Keys.arr VG.Proof.Rsa.X86.Keys.S
    omega
  have wsValue : BitVec.ofNat 32 E.base.toNat = E.workspace := by
    apply BitVec.eq_of_toNat_eq
    simp only [Environment.base, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    have bound := E.workspace.isLt
    omega
  have wsArg : CallArgument s E.base E.size 20 (BitVec.ofNat 32 E.base.toNat) := by
    rw [wsValue]
    exact context_argument C (i := 16) (by decide)
  refine ⟨?_, ?_, ?_, width, lo, hi⟩
  · refine ⟨?_, ⟨2 * E.primeLength, by omega, ?_, context_argument C (i := 3) (by decide)⟩,
      wsArg, by omega, by decide⟩
    · simpa only [kw_full width] using old
    · change kw (2 * E.primeLength) = kw (4 * E.n)
      rw [plen]
      congr 1
      omega
  · refine ⟨?_, ⟨E.primeLength, by omega, ?_, context_argument C (i := 5) (by decide)⟩,
      wsArg, by omega, by decide⟩
    · simpa only [kw_prime width] using resize (E.n / 2) (by omega) (by omega)
    · change kw E.primeLength = kw (2 * E.n)
      rw [plen]
  · have kw8 : kw 8 = 2 := by decide
    refine ⟨?_, ⟨E.exponentLength, by have := v.exponentLength; omega, ?_,
      context_argument C (i := 15) (by decide)⟩, wsArg, by decide, by decide⟩
    · simpa only [kw8] using resize 2 (by decide) (by omega)
    · have bounds := v.exponentLength
      change kw E.exponentLength = kw 8
      simp only [kw, Spec.Rsa.modulusWords]
      omega

end VG.Proof.RsaKeyGen.X86.KeyRuntime
