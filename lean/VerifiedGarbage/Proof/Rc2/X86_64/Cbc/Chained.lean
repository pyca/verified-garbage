module

public import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.CbcScratch
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Lit
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-! # RC2-CBC in place on x86-64, with wiped stack working space -/
-- separate module: exporting CBC does not rebuild its existing streaming callers.

@[expose] public section

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64

theorem encryptChained_verified :
    Verified X86_64.target Impl.Rc2.X86_64.Cbc.encrypt
      (Proof.Rc2.cbcEncChainedScratchContract abi 64 8) := by
  refine Verified.of_correct (k := contract .encrypt) encrypt_correct (encrypt_constantTime _) {
    pre := by sig_implies_pre [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, contract, abi, argRegs, PublicRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    post := ?_
    pub := by sig_implies_pub [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, contract, abi, argRegs, PublicRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    sat := X86_64.sat_regs (by decide) (by decide) (by decide +kernel)
      (by rw [Curry.apply_const]; trivial) }
  intro s s' _ h
  sig_post [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, contract, abi, argRegs, PublicRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact Proof.Rc2.cbcEncChainedPost_of_blocks (r := 0) h.1 h.2

theorem encryptChained_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratchWiped 520 .r8 64 Impl.Rc2.X86_64.Cbc.encrypt)
      (Spec.Rc2.cbcEncryptChainedContract abi 528) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 64) (post := Proof.Rc2.cbcEncChainedPost abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 520) encryptChained_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Rc2.cbcEncChainedPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel)
      (by rw [Curry.apply_const]; trivial))

theorem decryptChained_verified :
    Verified X86_64.target Impl.Rc2.X86_64.Cbc.decrypt
      (Proof.Rc2.cbcDecChainedScratchContract abi 64 8) := by
  refine Verified.of_correct (k := contract .decrypt) decrypt_correct (decrypt_constantTime _) {
    pre := by sig_implies_pre [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, contract, abi, argRegs, PublicRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    post := ?_
    pub := by sig_implies_pub [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, contract, abi, argRegs, PublicRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    sat := X86_64.sat_regs (by decide) (by decide) (by decide +kernel)
      (by rw [Curry.apply_const]; trivial) }
  intro s s' _ h
  sig_post [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, contract, abi, argRegs, PublicRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact Proof.Rc2.cbcDecChainedPost_of_blocks (r := 0) h.1 h.2

theorem decryptChained_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratchWiped 520 .r8 64 Impl.Rc2.X86_64.Cbc.decrypt)
      (Spec.Rc2.cbcDecryptChainedContract abi 528) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 64) (post := Proof.Rc2.cbcDecChainedPost abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 520) decryptChained_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Rc2.cbcDecChainedPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel)
      (by rw [Curry.apply_const]; trivial))

end VG.Proof.Rc2.X86_64.Cbc
