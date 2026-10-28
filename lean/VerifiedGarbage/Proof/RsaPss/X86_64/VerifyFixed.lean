module
public import VerifiedGarbage.Proof.RsaPss.X86_64.Checks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.RsaPss.X86_64.Checks
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-!
# RSASSA-PSS verification on x86-64: the taint checks of the pieces that do
not depend on the hash function
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64

/-- The prologue of `shift`. -/
def shiftPro : List Instr :=
  [.mov .rax (.mem (sp sPos)), .alu .add .rax (.imm 1), .store (sp sA) .rax, .mov32 .rax (.imm 1),
    .store (sp sD) .rax, .mov32 .rax (.imm 10), .store (sp sJ) .rax]

theorem shift_eq (H : Impl.Pbkdf2.Md.X86_64.Hash) :
    shift H = .seq (.block shiftPro) (.loop (.seq (shiftPass H) (.block nextPass)) .ne) := rfl

/-- The checks. -/
structure VFixed : Prop where
  pro : ∃ hc, (taint.check (pT 1 [] [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) (.block (verifyPrologue ++ n0)) hc).isSome
    = true
  fail : ∃ hc, (taint.check (pT 1 [] []) verifyFail hc).isSome = true
  acc0 : ∃ hc, (taint.check (pT 1 [17, 21, 23, 25, 26] []) (.block acc0) hc).isSome = true
  clearTop : ∃ hc, (taint.check (pT 1 [23] []) (.block clearTop) hc).isSome = true
  posScan : ∃ hc, (taint.check (pT 1 [23, 24] []) posScan hc).isSome = true
  shiftPro : ∃ hc, (taint.check (pT 1 [] []) (.block shiftPro) hc).isSome = true
  nextPass : ∃ hc, (taint.check (pT 1 [] []) (.block nextPass) hc).isSome = true
  restore : ∃ hc, (taint.check (pT 1 [] []) (.block restoreRegs) hc).isSome = true
  scanAny : ∃ hc, (taint.check (pT 1 [35] [])
    (.block [.mov .rax (.mem (sp sAny)), .alu .test .rax (.reg .rax)]) hc).isSome = true
  scanLen : ∃ hc, (taint.check (pT 1 [24, 36] [])
    (.block [.mov .rax (.mem (sp sSlen)), .alu .cmp .rax (.mem (sp sDb))]) hc).isSome = true

theorem vFixed : VFixed :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.RsaPss.X86_64
