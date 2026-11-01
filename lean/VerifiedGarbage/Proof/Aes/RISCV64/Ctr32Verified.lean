module

public import VerifiedGarbage.Proof.Aes.RISCV64.Ctr32
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.Contract
meta import VerifiedGarbage.Proof.Gcm.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.RISCV64.Ctr32
meta import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Gcm.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.Aes.RISCV64.Ctr32

/-!
# AES counter mode on RISC-V: `Verified`

Correctness (`Ctr32.lean`), constant time (by taint tracking,
`taint_decide`: only the pointers, `rounds`, `n` and what is computed from
them reach addresses and branches), and a state satisfying the
precondition, against `Proof.Aes.ctr32RISCV64`, then moved to the shared
contract of `Spec/Gcm/Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.Proof.Aes

theorem ctr32_ct : ConstantTime isa Proof.Aes.ctr32RISCV64.pre Proof.Aes.ctr32RISCV64.pub
    Impl.Aes.RISCV64.ctr32 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5])
    ?_ (by taint_decide)
  rintro s₁ s₂ - - ⟨h0, h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5]

theorem ctr32_verified :
    Verified RISCV64.target Impl.Aes.RISCV64.ctr32 (Proof.Gcm.ctr32Contract RISCV64.abi) :=
  Verified.of_correct ctr32_correct ctr32_ct (by
    sig_implies [Proof.Gcm.ctr32Contract, Proof.Gcm.ctr32Sig, Proof.Aes.ctr32RISCV64, RISCV64.abi,
      RISCV64.argRegs] [Proof.Aes.RISCV64.satState] using Proof.Aes.RISCV64.satState)

end VG.Proof.Aes.RISCV64
