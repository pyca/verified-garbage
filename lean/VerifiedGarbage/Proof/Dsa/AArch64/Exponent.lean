module
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Impl.Rsa.AArch64.Crt
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFrame
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Bignum.CrtExp
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The shared fixed-window exponentiation against DSA's arithmetic

The existing RSA exponentiation uses a constant-size window and scans every
table entry when selecting a power. Its arithmetic proof only needs an odd
modulus, not a prime modulus. This bridge states its result in DSA's terms;
it retains the memory-frame and register-preservation facts for callers.
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- A suffix of the caller's scratch allocation is a valid exponent
source for a computation restricted to its prefix. This lets DSA use
computed exponents without changing the shared exponentiation proof. -/
theorem scratchSource {s : State} {B : Addr} {capacity active offset : Nat}
    {bytes : List Byte} (hs : Scr s B capacity) (hactive : active ≤ offset)
    (hfit : offset + bytes.length ≤ capacity)
    (hbytes : ∀ i (hi : i < bytes.length),
      s.mem (off B offset + BitVec.ofNat 64 i) = bytes[i]) :
    Src s B active (off B offset) bytes := by
  refine ⟨?_, hbytes, ?_⟩
  · intro i hi
    have hp : off B offset + BitVec.ofNat 64 i = off B (offset + i) :=
      Offset.add_add B offset i
    rw [hp]
    obtain ⟨r, hr, hc⟩ := hs.region (show offset + i + 1 ≤ capacity by omega) (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro i hi
    rw [ofs_off B (by have := hs.nowrap; omega)]
    omega

/-- DSA modular exponentiation in Montgomery representation. The exponent
is a nonempty byte string outside the scratch workspace; leading zeroes
are permitted. This lemma makes no primality or group-order assumption. -/
theorem expLoop_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat}
    {minv : BitVec 64} {m x : Nat}
    (hc : SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : m % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < m)
    (hxc : wv s.mem (off B o) (slot wx Crt.aXc) wx % m = x * 2 ^ (64 * wx) % m)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < m)
    (hyc : wv s.mem (off B o) (slot wx aY) wx % m = 2 ^ (64 * wx) % m)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (seqs (Crt.expLoop M.mm sp sl)) s fun t =>
      SubCtx t B Z o w wx minv ∧ wv t.mem (off B o) (slot wx aY) wx < m ∧
      wv t.mem (off B o) (slot wx aY) wx % m =
        Spec.Dsa.powMod x (Spec.Dsa.decodeBE eb) m * 2 ^ (64 * wx) % m ∧
      Frm (off B o) (crtExpRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (crtExpLoop_ok M (Q := True) hc hw2 hwx hw30 hn hinv hodd hxl
    (fun _ => hxc) hyl (fun _ => hyc) hsp hsl hep hel hL1 hL2 he) fun t ht => ?_
  obtain ⟨hctx, hlt, hval, hframe, hkeep⟩ := ht
  refine ⟨hctx, hlt, ?_, hframe, hkeep⟩
  rw [VG.Proof.Dsa.powMod_eq, VG.Proof.Dsa.decodeBE_os2ip, Nat.mod_mul_mod]
  exact hval True.intro

end VG.Proof.Dsa.AArch64
