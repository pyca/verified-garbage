module

public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Bound
public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Cut
public import VerifiedGarbage.Proof.Ffdh.AArch64.Out
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_ffdh_generate_key` on AArch64: a run's data up to the scalar

The public data (`GkP`) are the working space, the lengths, the pointers,
the domain, and whether the scalar is in range; the random octets are
secret. With the public data `p` and the octets `rb`, a run's data are
`p.D₀ rb` (the random octets an input) up to the scalar's octets in `x`
(`GkP.xo`), and `p.D₁ rb` (the scalar's octets an input) after them.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.GenerateKey

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Bignum.CrtWindowFive
open VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- The public data. -/
structure GkP where
  B : Addr
  Z : Nat
  k : Nat
  dl : Nat
  dp : Addr
  dom : List Byte
  xp : Addr
  yp : Addr
  rp : Addr
  /-- Whether the scalar is in range. -/
  pv : Bool
  sp : Addr

/-- The run's data, with the random octets an input. -/
def GkP.D₀ (p : GkP) (rb : List Byte) : FD :=
  ⟨p.B, p.Z, p.k, p.dl, p.dp, p.dom, [(sX, p.xp), (sY, p.yp), (sRand, p.rp)], [(p.rp, rb)]⟩

@[simp] theorem GkP.D₀_B (p : GkP) (rb : List Byte) : (p.D₀ rb).B = p.B := rfl
@[simp] theorem GkP.D₀_Z (p : GkP) (rb : List Byte) : (p.D₀ rb).Z = p.Z := rfl
@[simp] theorem GkP.D₀_k (p : GkP) (rb : List Byte) : (p.D₀ rb).k = p.k := rfl
@[simp] theorem GkP.D₀_dl (p : GkP) (rb : List Byte) : (p.D₀ rb).dl = p.dl := rfl
@[simp] theorem GkP.D₀_dp (p : GkP) (rb : List Byte) : (p.D₀ rb).dp = p.dp := rfl
@[simp] theorem GkP.D₀_dom (p : GkP) (rb : List Byte) : (p.D₀ rb).dom = p.dom := rfl

/-- The mask of the bound's first nonzero octet. -/
abbrev GkP.msk (p : GkP) (rb : List Byte) : BitVec 64 :=
  BitVec.ofNat 64 (KeyScalar.smearN (p.D₀ rb).bc.toNat)

/-- The scalar's octets. -/
def GkP.xo (p : GkP) (rb : List Byte) : List Byte := KeyScalar.cut rb (p.D₀ rb).bl ((p.msk rb).setWidth 8)

/-- The run's data, with the scalar's octets an input. -/
abbrev GkP.D₁ (p : GkP) (rb : List Byte) : FD := (p.D₀ rb).withSrcs [(p.xp, p.xo rb)]

/-- Bytes of regions apart are apart. -/
theorem ne_of_disj {a b : Addr} {n m i j : Nat} (hd : (⟨a, n⟩ : Region).Disjoint ⟨b, m⟩) (ha : a.toNat + n ≤ 2 ^ 64)
    (hb : b.toNat + m ≤ 2 ^ 64) (hi : i < n) (hj : j < m) : a + BitVec.ofNat 64 i ≠ b + BitVec.ofNat 64 j :=
  fun he => hd _ (contains_byte a hi (by omega_arith)) (he ▸ contains_byte b hj (by omega_arith))

/-! ## The scalar's octets -/

@[simp] theorem GkP.D₁_B (p : GkP) (rb : List Byte) : (p.D₁ rb).B = p.B := rfl
@[simp] theorem GkP.D₁_Z (p : GkP) (rb : List Byte) : (p.D₁ rb).Z = p.Z := rfl
@[simp] theorem GkP.D₁_k (p : GkP) (rb : List Byte) : (p.D₁ rb).k = p.k := rfl
@[simp] theorem GkP.D₁_dl (p : GkP) (rb : List Byte) : (p.D₁ rb).dl = p.dl := rfl
@[simp] theorem GkP.D₁_dp (p : GkP) (rb : List Byte) : (p.D₁ rb).dp = p.dp := rfl
@[simp] theorem GkP.D₁_dom (p : GkP) (rb : List Byte) : (p.D₁ rb).dom = p.dom := rfl

end VG.Proof.Ffdh.AArch64.GenerateKey
