module

import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Ecdsa.X86.Main
import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Spec.Ecdsa.P256
import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ecdsa.X86.Lit
public import VerifiedGarbage.Impl.Ecdsa.P256.X86
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.P256.Prime
meta import VerifiedGarbage.Proof.Ecdsa.X86.Main
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
meta import VerifiedGarbage.Proof.Ecdsa.X86.Layout
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
meta import VerifiedGarbage.Spec.Ecdsa.P256
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.P256.Point
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdsa.X86.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P256.X86
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract

/-!
# ECDSA over P-256 on x86 (32-bit): `Verified`

P-256 is a curve the proof supports (`p256_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.P256.law`), so `sign_ok` gives
the contract's postcondition; `ebx`, `esi`, `edi` and `ebp` are restored,
`esp` kept, and the return address too, as every write is in the working
space or `out`. Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a
counter.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem p256_nBits : 64 * p256.n ≤ Spec.Ecdsa.nBits p256.C := by
  show 256 ≤ Spec.P256.curve.n.log2 + 1
  have : 255 ≤ Spec.P256.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `32` bytes is dropped. -/
theorem p256_sh : p256.sh = 0 := by
  have h : 64 * 4 ≤ Spec.Ecdsa.nBits p256.C := p256_nBits
  show 8 * 32 - Spec.Ecdsa.nBits p256.C = 0; omega

theorem p256_ok (hI : Weierstrass.X86.Inv.InvSounds) : CfgOk p256 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P256.onCurve_G
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
  sh := by rw [p256_sh]; decide
  inv_p _ := ⟨@hI _ p256.C.p_ne_zero Proof.P256.p_prime, Inv.InvOk.ofMod (by decide +kernel) Mont.p256p_ok rfl rfl⟩
  inv_n _ := ⟨@hI _ p256.C.n_ne_zero Proof.P256.n_prime, Inv.InvOk.ofMod (by decide +kernel) Mont.p256n_ok rfl rfl⟩
  fp := ⟨rfl, rfl, Mont.p256p_ok⟩
  fn := ⟨rfl, rfl, Mont.p256n_ok⟩

def signRd (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, 32⟩, ⟨(arg s 2).setWidth 64, 32⟩, ⟨(arg s 3).setWidth 64, 32⟩, ⟨argAddr s 0, 20⟩]
def signWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 64⟩, ⟨(arg s 4).setWidth 64, 8192⟩]

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0x4000, 0x8000` at
`0x20004`. -/
def satMem : Mem := fun a =>
  if a = 0x20005 then 0x10 else if a = 0x20009 then 0x20 else if a = 0x2000d then 0x30 else
  if a = 0x20011 then 0x40 else if a = 0x20015 then 0x80 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 20⟩]

end VG.Proof.Ecdsa.X86
