import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
import VerifiedGarbage.Proof.Rsa.AArch64.PublicImpl
import VerifiedGarbage.Proof.Rsa.AArch64.PubChecked

/-!
# The RSA public operations as the signatures' callees, on AArch64

`vg_rsa_public_checked` (`pubChecked`) and each implementation of
`vg_rsa_public_precomputed_checked` (a variant of `RsaPublicPrecomputed`,
`pdOf`) as `Callee`s. Their code makes no calls and has no frame, so they are
`Verified` with no stack; the signatures reserve 16 bytes below their stack
pointer at the call (`Callee.pos`), and a contract with more stack implies one
with less (`pub_stack`, `pd_stack`).
-/

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

end VG.Proof.RsaPkcs1Sig.AArch64
