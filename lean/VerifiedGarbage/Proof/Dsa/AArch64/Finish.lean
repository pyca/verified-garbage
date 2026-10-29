module
public import VerifiedGarbage.Impl.Dsa.AArch64.Core
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFrame
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.Operands

/-! # Returning an encoded DSA arithmetic result to the parent workspace -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- Internal DSA calls may use the arithmetic registers and temporarily
switch rdi to the child workspace. The enclosing entry point saves the ABI. -/
def coreRegs : List Reg := .x0 :: mmRegs

/-- Encode the arithmetic result, restore the parent workspace pointer,
and preserve every word in the active prefix. -/
theorem finish_ok {s : State} {B : Addr} {Z o w wx k : Nat} {minv parentMinv : BitVec 64}
    {out : Addr} (hc : SubCtx s B Z o w wx minv)
    (hpm : word s.mem B (8 * sMinv) = parentMinv)
    (hp : word s.mem B (8 * result) = out)
    (hl : word s.mem B (8 * resultLen) = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (out + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j)) :
    WP isa (seqs Core.finish) s fun t =>
      Good t B Z w parentMinv ∧
      Spec.Rsa.bytesAt t.mem out k = Spec.Dsa.encodeBE k (wv s.mem (off B o) (slot wx aY) wx) ∧
      (∀ d, d + 8 ≤ Z → word t.mem B d = word s.mem B d) ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧ Keep coreRegs s t := by
  unfold Core.finish seqs
  refine WP.seq (WP.mono (storeSuffix_ok hc (by decide) (by decide) (by decide)
    hp hl hk1 hk' hkw hout hprefix) fun u ⟨hcu, huout, hwrd, _, hfu, hku⟩ => ?_)
  have hpmu : word u.mem B (8 * sMinv) = parentMinv :=
    (hwrd _ (by have := hc.lo; have := hc.hi; have := hdr_lt_slot w 8 (show sMinv < 32 by decide); omega)).trans hpm
  refine WP.mono (leave_ok hcu hpmu) fun t ⟨hgt, hmem, hkt⟩ =>
    ⟨hgt, hmem ▸ huout, hmem ▸ hwrd, hmem ▸ hfu, (hku.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
