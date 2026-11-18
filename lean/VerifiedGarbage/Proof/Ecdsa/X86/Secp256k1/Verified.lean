module

import VerifiedGarbage.Proof.Ecdsa.X86.Main
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
import VerifiedGarbage.Proof.Secp256k1.Point
import VerifiedGarbage.Proof.Weierstrass.X86.MontSecp256k1
import VerifiedGarbage.Proof.Secp256k1.Prime
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ecdsa.X86.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86.Layout
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
meta import VerifiedGarbage.Spec.Ecdsa.Secp256k1
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Secp256k1.Point
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontSecp256k1
meta import VerifiedGarbage.Proof.Secp256k1.Prime
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract

/-!
# ECDSA over secp256k1 on x86 (32-bit): the curve

secp256k1 is a curve the proofs support (`secp256k1_ok`), with the bits of its order;
and the hints of the constant-time checks of the functions over it (`weak`).
The signature, with the curve's comb, is `Proof/Ecdsa/X86/Secp256k1/Comb.lean`'s.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.Secp256k1

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem secp256k1_nBits : Spec.Ecdsa.nBits secp256k1.C = 256 := by
  show Spec.Secp256k1.curve.n.log2 + 1 = 256
  have h1 : 255 ≤ Spec.Secp256k1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.Secp256k1.curve.n.log2 < 256 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h1, h2]

/-- No bit of a hash of `32` bytes is dropped. -/
theorem secp256k1_sh : secp256k1.sh = 0 := by
  unfold Cfg.sh
  rw [secp256k1_nBits]
  rfl

theorem secp256k1_ok (hI : Inv.InvSounds) : CfgOk secp256k1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.Secp256k1.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by rw [secp256k1_sh]; decide

  inv_p _ := ⟨@hI _ secp256k1.C.p_ne_zero Proof.Secp256k1.p_prime,
    Inv.InvOk.ofMod (by decide +kernel) Mont.secp256k1p_ok rfl rfl⟩
  inv_n _ := ⟨@hI _ secp256k1.C.n_ne_zero Proof.Secp256k1.n_prime,
    Inv.InvOk.ofMod (by decide +kernel) Mont.secp256k1n_ok rfl rfl⟩
  fp := ⟨rfl, rfl, Mont.secp256k1p_ok⟩
  fn := ⟨rfl, rfl, Mont.secp256k1n_ok⟩

/-- The hints of the constant-time checks forget the words known to hold base
addresses (`native_taint_decide_weak`): no address depends on a value loaded from
the working space, and the kernel evaluates every instruction faster with
less to look through. They keep the public slots of memory, which the
inversions by divsteps read back (their batch counter). Inside the calls of
the field arithmetic (`τ.stk ≠ []`), they keep everything: the functions read
their pointers from the words of the call's frame. -/
def weak (τ : VG.X86.Taint.T) : VG.X86.Taint.T := if τ.stk = [] then { τ with wbases := [] } else τ

end VG.Proof.Ecdsa.X86.Secp256k1
