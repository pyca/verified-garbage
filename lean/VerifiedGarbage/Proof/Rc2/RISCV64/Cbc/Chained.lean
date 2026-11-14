module

public import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.CbcScratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Contract

meta import VerifiedGarbage.Impl.Rc2.RISCV64.Cbc
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-! # RC2-CBC in place on RISCV64, with wiped stack working space -/
-- separate module: exporting CBC does not rebuild its existing streaming callers.

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64

def scratchSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 512⟩]

def frameSat : State := { scratchSat with wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩] }

theorem encryptChained_ct : ConstantTime isa (cbcC .encrypt).pre (cbcC .encrypt).pub Impl.Rc2.RISCV64.Cbc.encrypt := by
  refine VG.Taint.constantTime (A := taint)
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  obtain ⟨h₀, h₁, h₂, h₃, h₄, hsp⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encryptChained_verified :
    Verified RISCV64.target Impl.Rc2.RISCV64.Cbc.encrypt (Proof.Rc2.cbcEncChainedScratchContract abi 64) := by
  refine Verified.of_correct (k := cbcC .encrypt) (cbc_ok .encrypt) encryptChained_ct {
    pre := by sig_implies_pre [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    post := ?_
    pub := by sig_implies_pub [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    sat := by sig_implies_sat [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] [scratchSat] using scratchSat }
  intro s s' _ h
  sig_post [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact Proof.Rc2.cbcEncChainedPost_of_blocks (r := 0) h.1 h.2

theorem encryptChainedFrameSat : ∃ s, (Spec.Rc2.cbcEncryptChainedContract abi 512).pre s := by
  implies_sat [Spec.Rc2.cbcEncryptChainedContract, Spec.Rc2.cbcChainedSig, abi, argRegs]
    [frameSat, scratchSat] using frameSat

theorem encryptChained_framed :
    Verified RISCV64.target
      (Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a4 64 Impl.Rc2.RISCV64.Cbc.encrypt)
      (Spec.Rc2.cbcEncryptChainedContract abi 512) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 64) (post := Proof.Rc2.cbcEncChainedPost abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 512) encryptChained_verified (by decide) (by decide) (by decide)
    (Proof.Rc2.cbcEncChainedPostOut_local _) encryptChainedFrameSat

theorem decryptChained_ct : ConstantTime isa (cbcC .decrypt).pre (cbcC .decrypt).pub Impl.Rc2.RISCV64.Cbc.decrypt := by
  refine VG.Taint.constantTime (A := taint)
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  obtain ⟨h₀, h₁, h₂, h₃, h₄, hsp⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decryptChained_verified :
    Verified RISCV64.target Impl.Rc2.RISCV64.Cbc.decrypt (Proof.Rc2.cbcDecChainedScratchContract abi 64) := by
  refine Verified.of_correct (k := cbcC .decrypt) (cbc_ok .decrypt) decryptChained_ct {
    pre := by sig_implies_pre [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    post := ?_
    pub := by sig_implies_pub [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    sat := by sig_implies_sat [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] [scratchSat] using scratchSat }
  intro s s' _ h
  sig_post [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact Proof.Rc2.cbcDecChainedPost_of_blocks (r := 0) h.1 h.2

theorem decryptChainedFrameSat : ∃ s, (Spec.Rc2.cbcDecryptChainedContract abi 512).pre s := by
  implies_sat [Spec.Rc2.cbcDecryptChainedContract, Spec.Rc2.cbcChainedSig, abi, argRegs]
    [frameSat, scratchSat] using frameSat

theorem decryptChained_framed :
    Verified RISCV64.target
      (Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a4 64 Impl.Rc2.RISCV64.Cbc.decrypt)
      (Spec.Rc2.cbcDecryptChainedContract abi 512) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 64) (post := Proof.Rc2.cbcDecChainedPost abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 512) decryptChained_verified (by decide) (by decide) (by decide)
    (Proof.Rc2.cbcDecChainedPostOut_local _) decryptChainedFrameSat

end VG.Proof.Rc2.RISCV64.Cbc
