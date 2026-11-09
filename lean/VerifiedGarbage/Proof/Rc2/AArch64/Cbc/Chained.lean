module

public import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.CbcScratch
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Lit
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe

meta import VerifiedGarbage.Impl.Rc2.AArch64.Cbc
meta import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-! # RC2-CBC in place on AArch64, with wiped stack working space -/
-- separate module: exporting CBC does not rebuild its existing streaming callers.

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64

theorem encryptChained_ct : ConstantTime isa (contract .encrypt).pre (contract .encrypt).pub Impl.Rc2.AArch64.Cbc.encrypt := by
  refine VG.Taint.constantTime (A := taint)
    (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.1, fun r hr => h.2 r ?_⟩
  simpa only [Taint.mem_ofRegs] using hr

theorem encryptChained_verified :
    Verified AArch64.target Impl.Rc2.AArch64.Cbc.encrypt (Proof.Rc2.cbcEncChainedScratchContract abi 64) := by
  refine Verified.of_correct (k := contract .encrypt) encrypt_correct encryptChained_ct {
    pre := by sig_implies_pre [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, contract, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, PublicRegs]
    post := ?_
    pub := by sig_implies_pub [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, contract, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, PublicRegs]
    sat := AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial) }
  intro s s' _ h
  sig_post [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, contract, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, PublicRegs]
  exact Proof.Rc2.cbcEncChainedPost_of_blocks (r := 0) h.1 h.2

theorem encryptChained_framed :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped 512 .x4 64 Impl.Rc2.AArch64.Cbc.encrypt)
      (Spec.Rc2.cbcEncryptChainedContract abi 512) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 64) (post := Proof.Rc2.cbcEncChainedPost abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 512) encryptChained_verified (by decide) (by decide) (by decide)
    (Proof.Rc2.cbcEncChainedPostOut_local _) (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem decryptChained_ct : ConstantTime isa (contract .decrypt).pre (contract .decrypt).pub Impl.Rc2.AArch64.Cbc.decrypt := by
  refine VG.Taint.constantTime (A := taint)
    (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.1, fun r hr => h.2 r ?_⟩
  simpa only [Taint.mem_ofRegs] using hr

theorem decryptChained_verified :
    Verified AArch64.target Impl.Rc2.AArch64.Cbc.decrypt (Proof.Rc2.cbcDecChainedScratchContract abi 64) := by
  refine Verified.of_correct (k := contract .decrypt) decrypt_correct decryptChained_ct {
    pre := by sig_implies_pre [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, contract, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, PublicRegs]
    post := ?_
    pub := by sig_implies_pub [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, contract, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, PublicRegs]
    sat := AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial) }
  intro s s' _ h
  sig_post [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, contract, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, PublicRegs]
  exact Proof.Rc2.cbcDecChainedPost_of_blocks (r := 0) h.1 h.2

theorem decryptChained_framed :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped 512 .x4 64 Impl.Rc2.AArch64.Cbc.decrypt)
      (Spec.Rc2.cbcDecryptChainedContract abi 512) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 64) (post := Proof.Rc2.cbcDecChainedPost abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 512) decryptChained_verified (by decide) (by decide) (by decide)
    (Proof.Rc2.cbcDecChainedPostOut_local _) (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Rc2.AArch64.Cbc
