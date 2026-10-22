module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Precomputed
public import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Precomputed
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86: the pieces the taint analysis checks

Each straight-line piece of encryption, and the bodies of its loops, from
states in which only the registers given are public
(`Proof/RsaPkcs1Enc/X86/PcBody.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Pc

open VG VG.Impl.RsaPkcs1Enc.X86.Precomputed
open VG.X86 hiding frameBytes

/-- The taint analysis proves `c` constant time from states that agree on `rs`. -/
abbrev TaintOk (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check VG.X86.taint (τr rs) c hc).isSome = true

theorem head_taint : TaintOk [.esp] (.block head) := ⟨_, by taint_decide⟩
theorem psBody_taint : TaintOk [.esi, .edi, .ecx] (.block psBody) := ⟨_, by taint_decide⟩
theorem sep_taint : TaintOk [.esp, .edi] (.block sep) := ⟨_, by taint_decide⟩
theorem copy_taint : TaintOk [.esi, .ebx, .ecx] Impl.Bignum.X86.copyBytes := ⟨_, by taint_decide⟩
theorem callArgs_taint : TaintOk [.esp] (.block callArgs) := ⟨_, by taint_decide⟩
theorem maskArgs_taint : TaintOk [.esp] (.block maskArgs) := ⟨_, by taint_decide⟩
theorem maskBody_taint : TaintOk [.esi, .ecx] (.block maskBody) := ⟨_, by taint_decide⟩
theorem wipeArgs_taint : TaintOk [.esp] (.block wipeArgs) := ⟨_, by taint_decide⟩
theorem zeroLoop_taint : TaintOk [.esi, .ecx] zeroLoop := ⟨_, by taint_decide⟩
theorem ret_taint : TaintOk [.esp] (.block [.mov .eax (.reg .edi)]) := ⟨_, by taint_decide⟩

end VG.Proof.RsaPkcs1Enc.X86.Pc
