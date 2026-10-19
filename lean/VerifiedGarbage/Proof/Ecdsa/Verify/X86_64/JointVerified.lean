module
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointLit
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitErase
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic

import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointAbi
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointCT
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Verified
import VerifiedGarbage.Impl.Ecdh.P256.X86_64
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.X86_64.Check
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Final
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointContract
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointInput
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTail
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFlags
import VerifiedGarbage.Proof.Ecdsa.X86_64.SharedSlots
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Mont.X86_64.Blocks
import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Mont.X86_64.Double4
import VerifiedGarbage.Proof.Mont.X86_64.Friendly
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Mont.X86_64.Round
import VerifiedGarbage.Proof.Mont.X86_64.Sparse
import VerifiedGarbage.Proof.Mont.X86_64.SparseX
import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfForward
import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfPublic
import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfWP
import VerifiedGarbage.Proof.P256.X86_64.HalfMemory
import VerifiedGarbage.Proof.P256.X86_64.JointLayout
import VerifiedGarbage.Proof.P256.X86_64.JointLoop
import VerifiedGarbage.Proof.P256.X86_64.JointWindowTiming
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.Window5
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacField
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacOps
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafChoose
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafOdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafPrep
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafSubtract
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardStores
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedAdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedLoad
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedPoint
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointMulTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointSeed
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointTables
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafAddress
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCache
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheEntryPoint
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafChoose
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafPoint
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafPrepTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTable
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableCopy
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableFields
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableIO
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableInit
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableStoreTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingStep
import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
import VerifiedGarbage.Proof.Weierstrass.X86_64.Words
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Spec.Ecdsa.Verify.P256

/-! The joint implementation satisfies the unchanged shared verification contract. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64

section
variable (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
include hL hT hI

theorem jointVerify_verified : Verified X86_64.target jointVerifyP256
    (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts) 8) :=
  Verified.of_inline (k₀ := verifyK₀) (by lit_decide) (fun s hs => jointVerify_x86 hL hT hI s (implies.pre _ hs))
    (jointVerify_ct hL hT hI) implies8 (fun _ h => Sig.clear_of_pre_consts h) (fun _ _ _ _ _ hp => hp)
    fun s₁ s₂ h₁ h₂ hp => (implies.pub s₁ s₂ (Sig.pre_stack0 h₁) (Sig.pre_stack0 h₂) hp).1

theorem jointVerify_verified_adx : Verified X86_64.target jointVerifyP256Adx
    (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts) 8) :=
  Verified.of_inline (k₀ := verifyK₀) (by lit_decide) (fun s hs => jointVerify_x86_adx hL hT hI s (implies.pre _ hs))
    (jointVerify_adx_ct hL hT hI) implies8 (fun _ h => Sig.clear_of_pre_consts h) (fun _ _ _ _ _ hp => hp)
    fun s₁ s₂ h₁ h₂ hp => (implies.pub s₁ s₂ (Sig.pre_stack0 h₁) (Sig.pre_stack0 h₂) hp).1

end
end VG.Proof.Ecdsa.Verify.X86_64
