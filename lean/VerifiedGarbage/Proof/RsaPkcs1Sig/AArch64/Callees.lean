module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
public import VerifiedGarbage.Proof.Rsa.AArch64.PublicImpl
public import VerifiedGarbage.Proof.Rsa.AArch64.PubChecked
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
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
public import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
public import VerifiedGarbage.Proof.Bignum.AArch64.Copy
public import VerifiedGarbage.Proof.Bignum.AArch64.Csub
public import VerifiedGarbage.Proof.Bignum.AArch64.Double
public import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
public import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
public import VerifiedGarbage.Proof.Bignum.AArch64.PdCT
public import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
public import VerifiedGarbage.Proof.Bignum.AArch64.PubCT
public import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
public import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
public import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
public import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
public import VerifiedGarbage.Proof.Bignum.AArch64.Row
public import VerifiedGarbage.Proof.Bignum.AArch64.Setup
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
public import VerifiedGarbage.Proof.Bignum.AArch64.Store
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Poly1305.Limbs64
public import VerifiedGarbage.Proof.Rsa.AArch64.ExpCheck
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivCT
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivCheckOk
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivCrt
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivRelease
public import VerifiedGarbage.Proof.Rsa.Octets

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
