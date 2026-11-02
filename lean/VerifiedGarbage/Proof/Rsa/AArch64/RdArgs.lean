module

public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Proof.Rsa.Ranges
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Rsa.AArch64.RecoverDet
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_recover_primes_det` on AArch64: the arguments

`RpArgs`: the arguments `Recover.entry` leaves in the header, kept by the
pieces; `RpIn`: the inputs, and `RpLens`: their lengths' bounds.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN)

/-- The inputs of `vg_rsa_recover_primes_det` and where they are. -/
structure RpIn where
  B : Addr
  Z : Nat
  k : Nat
  el : Nat
  dl : Nat
  pP : Addr
  pQ : Addr
  pN : Addr
  pE : Addr
  pD : Addr
  nb : List Byte
  eb : List Byte
  db : List Byte
  W : List Region

/-- The arguments in the header: the outputs' pointers, and `n`'s, `e`'s
and `d`'s pointers and lengths. -/
structure RpArgs (m : Mem) (B : Addr) (k el dl : Nat) (pP pQ pN pE pD : Addr) : Prop where
  p : word m B (8 * sP) = pP
  q : word m B (8 * sQ) = pQ
  n : word m B (8 * Public.sN) = pN
  k : word m B (8 * Public.sK) = BitVec.ofNat 64 k
  e : word m B (8 * Public.sE) = pE
  el : word m B (8 * Public.sElen) = BitVec.ofNat 64 el
  d : word m B (8 * sD) = pD
  dl : word m B (8 * sDl) = BitVec.ofNat 64 dl

/-- The header slots of `RpArgs`. -/
def rArg (i : Nat) : Prop := (16 ≤ i ∧ i < 22) ∨ i = 23 ∨ i = 24

theorem RpArgs.congr {m m' : Mem} {B : Addr} {k el dl : Nat} {pP pQ pN pE pD : Addr}
    (h : RpArgs m B k el dl pP pQ pN pE pD) (hm : ∀ i, rArg i → word m' B (8 * i) = word m B (8 * i)) :
    RpArgs m' B k el dl pP pQ pN pE pD :=
  ⟨(hm _ (by simp [rArg, sP, sFn])).trans h.p, (hm _ (by simp [rArg, sQ, sFn])).trans h.q,
    (hm _ (by simp [rArg, Public.sN, sFn])).trans h.n, (hm _ (by simp [rArg, Public.sK, sFn])).trans h.k,
    (hm _ (by simp [rArg, Public.sE, sFn])).trans h.e, (hm _ (by simp [rArg, Public.sElen, sFn])).trans h.el,
    (hm _ (by simp [rArg, sD, sFn])).trans h.d, (hm _ (by simp [rArg, sDl, sFn])).trans h.dl⟩

/-- The lengths, as `vg_rsa_recover_primes_det`'s contract bounds them. -/
structure RpLens (I : RpIn) : Prop where
  k1 : 64 ≤ I.k
  k2 : I.k ≤ 1024
  el1 : 1 ≤ I.el
  el2 : I.el ≤ I.k
  dl1 : 1 ≤ I.dl
  dl2 : I.dl ≤ I.k
  nbl : I.nb.length = I.k
  ebl : I.eb.length = I.el
  dbl : I.db.length = I.dl
  z : 128 * I.k ≤ I.Z

end VG.Proof.Rsa.AArch64
