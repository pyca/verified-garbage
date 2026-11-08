module

public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenTo.Fn
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OpenTo.Fn
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Impl.AesGcm.X86_64.OpenTo
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Run
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse

/-!
# AES-GCM decryption out of place, x86-64: the frame's constant-time pieces

Untrusted: everything here is checked by Lean. What `OpenToSplit/CT.lean`
relates of two runs of `open_to`'s frame: the frame is pushed and popped at
`rsp`, the same in both runs (`rel_frame`); the test of the call's result,
`wipe`'s arguments, read at `rsp`, and its loop, on `dst` and `len`, are
constant time by the taint analysis from those registers (`test_taint`,
`wipeArgs_taint`, `zeroLoop_taint`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenTo

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Impl.AesGcm.X86_64.OpenTo (wipeArgs wipeBody)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (Eq2 TT rel_seq rel_regs rel_skip rel_ite ct_of)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width)
open VG.Proof.AesGcm (arg)

/-- A frame, from two runs of its body from the states its push leaves. -/
theorem rel_frame {rs : List Reg} {r : Reg} {k : Nat} {body : Prog isa} {σ₁ σ₂ : State}
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) (hb : RelCT isa (Eq2 (pushed rs σ₁) (pushed rs σ₂)) body TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.frame (.push rs) body (.pop r k)) TT :=
  RelCT.frame (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact hsp)
    (hb.mono (fun _ _ ⟨s₁, s₂, ⟨e₁, e₂⟩, hx, hy⟩ => by subst e₁ e₂; exact ⟨hx, hy⟩) fun _ _ h => h)

theorem test_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block [.alu32 .test .rax (.reg .rax)]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem wipeArgs_taint : ∃ h, (taint.check (Taint.ofRegs [.rsp]) (.block wipeArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem zeroLoop_taint : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rcx, .r10]) (.loop (.block wipeBody) .ne) h).isSome
    = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.X86_64.OpenTo
