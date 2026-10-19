module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
public import VerifiedGarbage.Proof.Rsa.AArch64.PublicImpl
import VerifiedGarbage.Proof.Rsa.AArch64.PubChecked
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivVerified
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdCT
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubCT
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.AArch64.ExpCheck
import VerifiedGarbage.Proof.Rsa.AArch64.PrivCT
import VerifiedGarbage.Proof.Rsa.AArch64.PrivCheckOk
import VerifiedGarbage.Proof.Rsa.AArch64.PrivCrt
import VerifiedGarbage.Proof.Rsa.AArch64.PrivRelease
import VerifiedGarbage.Proof.Rsa.Octets

/-!
# The RSA operations as the signatures' callees, on AArch64

`vg_rsa_public_checked` (`pubChecked`), each implementation of
`vg_rsa_public_precomputed_checked` (a variant of `RsaPublicPrecomputed`,
`pdOf`) and `vg_rsa_private_checked` calling each implementation of
`vg_rsa_private_crt` (a variant of `RsaPrivateCrt`, `privOf`) as `Callee`s.
The public operations make no calls and have no frame, so they are
`Verified` with no stack; the signatures reserve 16 bytes below their stack
pointer at the call (`Callee.pos`), and a contract with more stack implies one
with less (`pub_stack`, `pd_stack`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64

open VG VG.AArch64 VG.Proof.Rsa.AArch64

theorem pub_stack : (Spec.Rsa.publicCheckedContract abi).Implies (Spec.Rsa.publicCheckedContract abi 16) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicCheckedSig, abi, argRegs,
      Proof.Rsa.AArch64.stackArgs_two, List.append_eq] at h
    sig_pre [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicCheckedSig, abi, argRegs,
      Proof.Rsa.AArch64.stackArgs_two, List.append_eq] at h
    sig_pre [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicCheckedSig, abi, argRegs,
      Proof.Rsa.AArch64.stackArgs_two, List.append_eq]
    sig_pre [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicCheckedSig, abi, argRegs,
      Proof.Rsa.AArch64.stackArgs_two, List.append_eq]
    sig_split h
    sig_and_intros
    all_goals with_reducible assumption
  post := fun _ _ _ h => h
  pub := fun _ _ _ _ h => h
  sat := by sig_implies_sat [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicCheckedSig, abi, argRegs,
    Proof.Rsa.AArch64.stackArgs_two, List.append_eq] [pubSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using pubSatState

theorem pd_stack :
    (Spec.Rsa.publicPrecomputedCheckedContract abi).Implies (Spec.Rsa.publicPrecomputedCheckedContract abi 16) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
      Proof.Rsa.AArch64.stackArgs_two, List.append_eq] at h
    sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
      Proof.Rsa.AArch64.stackArgs_two, List.append_eq] at h
    sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
      Proof.Rsa.AArch64.stackArgs_two, List.append_eq]
    sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
      Proof.Rsa.AArch64.stackArgs_two, List.append_eq]
    sig_split h
    sig_and_intros
    all_goals with_reducible assumption
  post := fun _ _ _ h => h
  pub := fun _ _ _ _ h => h
  sat := by sig_implies_sat [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi,
    argRegs, Proof.Rsa.AArch64.stackArgs_two, List.append_eq] [pdSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using pdSatState

/-- `vg_rsa_public_checked`. -/
def pubChecked : PubChecked where
  name := Spec.Rsa.publicCheckedApi.name
  code := Impl.Rsa.AArch64.Checked.publicChecked
  stack := 16
  verified := publicChecked_verified.of_implies pub_stack
  depth := by decide +kernel
  pos := by decide
  le := by decide
  suffix := ""
  features := []

/-- The implementation `v` of `vg_rsa_public_precomputed_checked`. -/
def pdOf (v : PublicImpl) : PdChecked where
  name := v.name
  code := v.code
  stack := 16
  verified := (Verified.of_correct (k := pdChkContract) v.ok v.ct precomputedChecked_implies).of_implies pd_stack
  depth := by rw [v.depth]; decide
  pos := by decide
  le := by decide
  suffix := v.suffix
  features := v.features

/-- `vg_rsa_private_checked` calling the implementation `v` of
`vg_rsa_private_crt`, as `Generic/RsaPrivateCrt/AArch64/Rsa.lean` emits it. -/
def privOf (v : CrtImpl) : PrivChecked where
  name := privName v
  code := privCode v
  stack := stackBytes
  verified := code_verified v
  depth := by rw [privCode_depth]; decide
  pos := by decide
  le := by decide
  suffix := v.suffix
  features := v.features

end VG.Proof.RsaPkcs1Sig.AArch64
