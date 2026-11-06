module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Random
public import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Random
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # RSAES-PKCS1-v1_5 encryption from a random tape on x86: the pieces the taint analysis checks

Each straight-line piece, and the loops of zeros, from states in which only
the registers given are public.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Rnd

open VG VG.Impl.RsaPkcs1Enc.X86.Random
open VG.X86 hiding frameBytes

/-- The taint analysis proves `c` constant time from states that agree on `rs`. -/
abbrev TaintOk (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check VG.X86.taint (τr rs) c hc).isSome = true

theorem head_taint : TaintOk [.esp] (.block head) := ⟨_, by taint_decide⟩
theorem load_taint : TaintOk [.esi, .ecx] (.block load) := ⟨_, by taint_decide⟩
theorem keep_taint : TaintOk [.edi, .edx] (.block keep) := ⟨_, by taint_decide⟩
theorem cmpEdx_taint : TaintOk [.edx] (.block [.alu .cmp .edx (.imm 0)]) := ⟨_, by taint_decide⟩
theorem testEcx_taint : TaintOk [.ecx] (.block [.alu .test .ecx (.reg .ecx)]) := ⟨_, by taint_decide⟩
theorem tapePtr_taint : TaintOk [.esp] (.block tapePtr) := ⟨_, by taint_decide⟩
theorem tapeAcc_taint : TaintOk [.esp, .eax, .ecx] (.block tapeAcc) := ⟨_, by taint_decide⟩
theorem callArgs_taint : TaintOk [.esp] (.block callArgs) := ⟨_, by taint_decide⟩
theorem status_taint : TaintOk [.esp] (.block status) := ⟨_, by taint_decide⟩
theorem zeroLoop_taint : TaintOk [.esi, .ecx] zeroLoop := ⟨_, by taint_decide⟩
theorem ret_taint : TaintOk [.esp] (.block [.mov .eax (.reg .ebx)]) := ⟨_, by taint_decide⟩
theorem zeroOutArgs_taint : TaintOk [.esp] (.block zeroOutArgs) := ⟨_, by taint_decide⟩
theorem drawnArgs_taint : TaintOk [.esp, .edx] (.block drawnArgs) := ⟨_, by taint_decide⟩
theorem budget_taint : TaintOk [.esp] (.block budget) := ⟨_, by taint_decide⟩
theorem exhausted_taint : TaintOk [.esi] (.block exhausted) := ⟨_, by taint_decide⟩
theorem reqArgs_taint : TaintOk [] (.block reqArgs) := ⟨_, by taint_decide⟩
theorem movEb_taint : TaintOk [] (.block [.mov .eax (.reg .ebx)]) := ⟨_, by taint_decide⟩
theorem request_taint : TaintOk [.esi] (.block request) := ⟨_, by taint_decide⟩

end VG.Proof.RsaPkcs1Enc.X86.Rnd
