module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVerify
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourContracts
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenPack
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackDispatch

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

theorem simple_verified : Verified AArch64.target simple (simpleBitPackContract AArch64.abi) :=
  simple_verified_of_wp (simple_wp_of_four simple_four_wp)

theorem signed_verified : Verified AArch64.target signed (bitPackContract AArch64.abi) :=
  signed_verified_of_wp (signed_wp_of_four signed_four_wp)

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
