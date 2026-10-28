module
public import VerifiedGarbage.Proof.RsaPss.X86_64.Checks
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.RsaPss.X86_64.Checks
meta import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-!
# EMSA-PSS's encoding and its check on x86-64: the taint checks of the
pieces that do not depend on the hash function
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64

/-- The checks of `encode`'s own pieces. -/
structure EFixed : Prop where
  pro : ∃ hc, (taint.check (pT 2 [] [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) (.block encPrologue) hc).isSome = true
  ret0 : ∃ hc, (taint.check (pT 2 [] []) ret0 hc).isSome = true
  copyOut : ∃ hc, (taint.check (pT 2 [16, 17, 21] []) copyOut hc).isSome = true
  ret1 : ∃ hc, (taint.check (pT 2 [] []) (.block [.mov32 .rax (.imm 1)]) hc).isSome = true

theorem eFixed : EFixed :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-- The checks of `checkEncoding`'s own pieces. -/
structure CFixed : Prop where
  pro : ∃ hc, (taint.check (pT 1 [] [.rdi, .rsi, .rdx, .rcx, .r8]) (.block chkPrologue) hc).isSome = true
  copyIn : ∃ hc, (taint.check (pT 1 [17, 21, 38] []) copyIn hc).isSome = true
  any1 : ∃ hc, (taint.check (pT 1 [] []) (.block [.mov32 .rax (.reg .r9), .alu .test .rax (.reg .rax)]) hc).isSome
    = true
  anyT : ∃ hc, (taint.check (pT 1 [] [])
    (.block [.mov32 .rax (.imm 0), .store (sp sAny) .rax, .mov .rdx (.mem (sp sSlen))]) hc).isSome = true
  anyE : ∃ hc, (taint.check (pT 1 [] [])
    (.block [.mov32 .rax (.imm 1), .store (sp sAny) .rax, .mov32 .rdx (.imm 0)]) hc).isSome = true
  ret0 : ∃ hc, (taint.check (pT 1 [] []) ret0 hc).isSome = true
  dbSlots : ∃ hc, (taint.check (pT 1 [26] [.rax]) (.block dbSlots) hc).isSome = true
  restore : ∃ hc, (taint.check (pT 1 [] []) (.block restoreRegs) hc).isSome = true

theorem cFixed : CFixed :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.RsaPss.X86_64
