module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
public import VerifiedGarbage.Proof.Rsa.AArch64.PublicImpl
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivVerified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Rsa.AArch64.PubChecked
public import VerifiedGarbage.Proof.Rsa.Contract

/-!
# The RSA operations as the signatures' callees, on AArch64

Each implementation of `vg_rsa_public_precomputed_checked` (a variant of
`RsaPublicPrecomputed`, `pdOf`) and `vg_rsa_private_checked` calling each
implementation of `vg_rsa_private_crt` (a variant of `RsaPrivateCrt`,
`privOf`) as `Callee`s. The public operation makes no calls and has no
frame, so it is `Verified` with no stack; the signatures reserve 16 bytes
below their stack pointer at the call (`Callee.pos`), and a contract with
more stack implies one with less (`pd_stack`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64

open VG VG.AArch64 VG.Proof.Rsa.AArch64

theorem pd_stack :
    (Proof.Rsa.publicPrecomputedCheckedContract abi).Implies (Proof.Rsa.publicPrecomputedCheckedContract abi 16) where
  pre := by
    intro s h
    sig_pre [Proof.Rsa.publicPrecomputedCheckedContract, Proof.Rsa.publicPrecomputedSig, abi, argRegs,
      Proof.Rsa.AArch64.stackArgs_two, List.append_eq] at h
    sig_pre [Proof.Rsa.publicPrecomputedCheckedContract, Proof.Rsa.publicPrecomputedSig, abi, argRegs,
      Proof.Rsa.AArch64.stackArgs_two, List.append_eq] at h
    sig_pre [Proof.Rsa.publicPrecomputedCheckedContract, Proof.Rsa.publicPrecomputedSig, abi, argRegs,
      Proof.Rsa.AArch64.stackArgs_two, List.append_eq]
    sig_pre [Proof.Rsa.publicPrecomputedCheckedContract, Proof.Rsa.publicPrecomputedSig, abi, argRegs,
      Proof.Rsa.AArch64.stackArgs_two, List.append_eq]
    sig_split h
    sig_and_intros
    all_goals with_reducible assumption
  post := fun _ _ _ h => h
  pub := fun _ _ _ _ h => h
  sat := by sig_implies_sat [Proof.Rsa.publicPrecomputedCheckedContract, Proof.Rsa.publicPrecomputedSig, abi,
    argRegs, Proof.Rsa.AArch64.stackArgs_two, List.append_eq] [pdSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using pdSatState

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
`vg_rsa_private_crt`, the internal function the padding functions call. -/
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
