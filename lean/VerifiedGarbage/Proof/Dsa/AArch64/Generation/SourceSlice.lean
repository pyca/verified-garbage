module
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup

import VerifiedGarbage.Proof.Dsa.AArch64.SourceSlices
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! Complete chunks of immutable generation tapes use the shared DSA slice proof. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem source_slice {s : State} {B ptr : Addr} {Z used width : Nat} {bytes : List Byte}
    (h : Src s B Z ptr bytes) (hroom : used + width ≤ bytes.length) :
    Src s B Z (off ptr used) ((bytes.drop used).take width) :=
  VG.Proof.Dsa.AArch64.source_slice h hroom

end VG.Proof.Dsa.AArch64.Generation
