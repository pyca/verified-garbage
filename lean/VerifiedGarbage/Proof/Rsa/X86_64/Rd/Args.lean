module

public import VerifiedGarbage.Proof.Rsa.Ranges
public import VerifiedGarbage.Proof.Rsa.X86_64.CvHead
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverDet
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Attr.Core

/-!
# `vg_rsa_recover_primes_det` on x86-64: the arguments

`RpArgs`: the arguments `Recover.entry` leaves in the header, kept by the
pieces; `RpIn`: the inputs, and `RpLens`: their lengths' bounds.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

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
  sv : Nat → BitVec 64
  nb : List Byte
  eb : List Byte
  db : List Byte
  W : List Region
  sp : BitVec 64

/-- The arguments in the header: the outputs' pointers, `n`'s, `e`'s and
`d`'s pointers and lengths, and the saved registers `sv`. -/
structure RpArgs (m : Mem) (B : Addr) (k el dl : Nat) (pP pQ pN pE pD : Addr) (sv : Nat → BitVec 64) : Prop where
  p : word m B (8 * sP) = pP
  q : word m B (8 * sQ) = pQ
  n : word m B (8 * Impl.Bignum.X86_64.Public.sN) = pN
  k : word m B (8 * Impl.Bignum.X86_64.Public.sK) = BitVec.ofNat 64 k
  e : word m B (8 * Impl.Bignum.X86_64.Public.sE) = pE
  el : word m B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el
  d : word m B (8 * sD) = pD
  dl : word m B (8 * sDl) = BitVec.ofNat 64 dl
  saved : ∀ i < 6, word m B (8 * i) = sv i

/-- The header slots of `RpArgs`. -/
def rArg (i : Nat) : Prop := i < 6 ∨ (16 ≤ i ∧ i < 22) ∨ i = 23 ∨ i = 24

theorem RpArgs.congr {m m' : Mem} {B : Addr} {k el dl : Nat} {pP pQ pN pE pD : Addr} {sv : Nat → BitVec 64}
    (h : RpArgs m B k el dl pP pQ pN pE pD sv) (hm : ∀ i, rArg i → word m' B (8 * i) = word m B (8 * i)) :
    RpArgs m' B k el dl pP pQ pN pE pD sv :=
  ⟨(hm _ (by simp [rArg, sP, Impl.Bignum.X86_64.Public.sOut, sFn])).trans h.p,
    (hm _ (by simp [rArg, sQ, Impl.Bignum.X86_64.Public.sIn, sFn])).trans h.q,
    (hm _ (by simp [rArg, Impl.Bignum.X86_64.Public.sN, sFn])).trans h.n,
    (hm _ (by simp [rArg, Impl.Bignum.X86_64.Public.sK, sFn])).trans h.k,
    (hm _ (by simp [rArg, Impl.Bignum.X86_64.Public.sE, sFn])).trans h.e,
    (hm _ (by simp [rArg, Impl.Bignum.X86_64.Public.sElen, sFn])).trans h.el,
    (hm _ (by simp [rArg, sD, Impl.Bignum.X86_64.Public.sI, sFn])).trans h.d,
    (hm _ (by simp [rArg, sDl, Impl.Bignum.X86_64.Public.sBit, sFn])).trans h.dl,
    fun i hi => (hm i (Or.inl hi)).trans (h.saved i hi)⟩

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

end VG.Proof.Rsa.X86_64
