module

public import VerifiedGarbage.Proof.Aes.RISCV64.Ctr32
public import VerifiedGarbage.Proof.Aes.RISCV64.Ctr32Bs
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.Contract
meta import VerifiedGarbage.Proof.Gcm.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.RISCV64.Ctr32
meta import VerifiedGarbage.Proof.Aes.RISCV64.Ctr32Bs
meta import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
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
  refine VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5])
    ?_ (by taint_decide_sum [Impl.Aes.RISCV64.encrypt4Sum])
  rintro s₁ s₂ - - ⟨h0, h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5]

theorem ctr32To_ct : ConstantTime isa Proof.Aes.ctr32ToRISCV64.pre Proof.Aes.ctr32ToRISCV64.pub
    Impl.Aes.RISCV64.ctr32To := by
  refine VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6])
    ?_ (by taint_decide_sum [Impl.Aes.RISCV64.encrypt4Sum])
  rintro s₁ s₂ - - ⟨h0, h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5, h6]

theorem ctr32Bs_ct : ConstantTime isa Proof.Aes.ctr32BsRISCV64.pre Proof.Aes.ctr32BsRISCV64.pub
    Impl.Aes.RISCV64.ctr32Bs := by
  refine VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5])
    ?_ (by taint_decide_sum [Impl.Aes.RISCV64.encrypt4RaSum])
  rintro s₁ s₂ - - ⟨h0, h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5]

theorem ctr32BsTo_ct : ConstantTime isa Proof.Aes.ctr32BsToRISCV64.pre Proof.Aes.ctr32BsToRISCV64.pub
    Impl.Aes.RISCV64.ctr32BsTo := by
  refine VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6])
    ?_ (by taint_decide_sum [Impl.Aes.RISCV64.encrypt4RaSum])
  rintro s₁ s₂ - - ⟨h0, h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5, h6]

theorem ctr32Bs_noFrames : Impl.Aes.RISCV64.ctr32Bs.noFrames = true := by lit_decide

theorem ctr32BsTo_noFrames : Impl.Aes.RISCV64.ctr32BsTo.noFrames = true := by lit_decide

theorem ctr32To_noFrames : Impl.Aes.RISCV64.ctr32To.noFrames = true := by lit_decide

end VG.Proof.Aes.RISCV64
