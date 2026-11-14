module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.CbcScratch
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe

meta import VerifiedGarbage.Impl.Rc2.PPC64LE.Cbc
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector

/-! # RC2-CBC in place on PPC64LE, with wiped stack working space -/
-- separate module: exporting CBC does not rebuild its existing streaming callers.

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE.Cbc

open VG VG.PPC64LE

theorem encryptChained_ct : ConstantTime isa (cbcC .encrypt).pre (cbcC .encrypt).pub Impl.Rc2.PPC64LE.Cbc.encrypt := by
  refine VG.Taint.constantTime (A := vectorTaint)
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  obtain ⟨h₀, h₁, h₂, h₃, h₄, hsp⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encryptChained_verified :
    Verified PPC64LE.target Impl.Rc2.PPC64LE.Cbc.encrypt (Proof.Rc2.cbcEncChainedScratchContract abi 64) := by
  refine Verified.of_correct (k := cbcC .encrypt) (cbc_ok .encrypt) encryptChained_ct {
    pre := by sig_implies_pre [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    post := ?_
    pub := by sig_implies_pub [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    sat := PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial) }
  intro s s' _ h
  sig_post [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact Proof.Rc2.cbcEncChainedPost_of_blocks (r := 0) h.1 h.2

theorem encryptChained_framed :
    Verified PPC64LE.target
      (Impl.StackScratch.PPC64LE.withStackScratchWiped 544 .r7 64 Impl.Rc2.PPC64LE.Cbc.encrypt)
      (Spec.Rc2.cbcEncryptChainedContract abi 544) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Rc2.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 64) (post := Proof.Rc2.cbcEncChainedPost abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 544) encryptChained_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Rc2.cbcEncChainedPost_local _)
    (Proof.Rc2.cbcEncChainedPostOut_local _) (PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem decryptChained_ct : ConstantTime isa (cbcC .decrypt).pre (cbcC .decrypt).pub Impl.Rc2.PPC64LE.Cbc.decrypt := by
  refine VG.Taint.constantTime (A := vectorTaint)
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  obtain ⟨h₀, h₁, h₂, h₃, h₄, hsp⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decryptChained_verified :
    Verified PPC64LE.target Impl.Rc2.PPC64LE.Cbc.decrypt (Proof.Rc2.cbcDecChainedScratchContract abi 64) := by
  refine Verified.of_correct (k := cbcC .decrypt) (cbc_ok .decrypt) decryptChained_ct {
    pre := by sig_implies_pre [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    post := ?_
    pub := by sig_implies_pub [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    sat := PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial) }
  intro s s' _ h
  sig_post [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact Proof.Rc2.cbcDecChainedPost_of_blocks (r := 0) h.1 h.2

theorem decryptChained_framed :
    Verified PPC64LE.target
      (Impl.StackScratch.PPC64LE.withStackScratchWiped 544 .r7 64 Impl.Rc2.PPC64LE.Cbc.decrypt)
      (Spec.Rc2.cbcDecryptChainedContract abi 544) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Rc2.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 64) (post := Proof.Rc2.cbcDecChainedPost abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 544) decryptChained_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Rc2.cbcDecChainedPost_local _)
    (Proof.Rc2.cbcDecChainedPostOut_local _) (PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Rc2.PPC64LE.Cbc
