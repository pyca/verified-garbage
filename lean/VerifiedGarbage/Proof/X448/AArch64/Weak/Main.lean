module

import VerifiedGarbage.Proof.X448.AArch64.Weak.FinalSwap
import VerifiedGarbage.Proof.X448.AArch64.Weak.Inv
public import VerifiedGarbage.Proof.X448.AArch64.Main
public import VerifiedGarbage.Impl.X448.AArch64.Weak
public import VerifiedGarbage.Proof.X448.AArch64.Weak.Env
import VerifiedGarbage.Proof.X448.AArch64.Bits
import VerifiedGarbage.Proof.X448.AArch64.Weak.Setup
import VerifiedGarbage.Proof.X448.AArch64.Finish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X448.AArch64.Iter
import VerifiedGarbage.Spec.X25519
import VerifiedGarbage.Proof.X448.AArch64.Setup
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.X448.AArch64.Weak.Iter
import VerifiedGarbage.Proof.X448.Invert
import VerifiedGarbage.Proof.X448.AArch64.Env

@[expose] public section

namespace VG.Proof.X448.AArch64.Weak

open VG VG.AArch64 VG.Proof.X448
open VG.Impl.X448.AArch64 (ld st slot SWAP BITS)
open VG.Impl.X448.AArch64.Weak

theorem E_outside {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (i : Index)
    (hi : slot i.val + 128 ≤ o ∨ o + n ≤ slot i.val) : E m' base i = E m base i := by
  simp only [E, F]
  exact congrArg toFe (valN_congr (fun j hj => h.limbs hi
    (by have := i.isLt; simp only [slot]; omega) (by omega : j < 16)))

end VG.Proof.X448.AArch64.Weak
