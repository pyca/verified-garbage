import VerifiedGarbage.Proof.RsaPss.X86_64.Checks

/-!
# RSASSA-PSS verification on x86-64: the taint checks of the pieces that do
not depend on the hash function
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64

/-- The first block of `anyArgs`. -/
def any1 : List Instr :=
  [.mov .rax (.mem (arg 1)), .store (sp sSlen) .rax, .mov32 .rax (.mem (arg 2)), .alu .test .rax (.reg .rax)]

/-- The prologue of `shift`. -/
def shiftPro : List Instr :=
  [.mov .rax (.mem (sp sPos)), .alu .add .rax (.imm 1), .store (sp sA) .rax, .mov32 .rax (.imm 1),
    .store (sp sD) .rax, .mov32 .rax (.imm 10), .store (sp sJ) .rax]

theorem anyArgs_eq : anyArgs = .seq (.block any1)
    (.ite .e (.block [.mov32 .rax (.imm 0), .store (sp sAny) .rax, .mov .rdx (.mem (sp sSlen))])
      (.block [.mov32 .rax (.imm 1), .store (sp sAny) .rax, .mov32 .rdx (.imm 0)])) := rfl

theorem shift_eq (H : Impl.Pbkdf2.Md.X86_64.Hash) :
    shift H = .seq (.block shiftPro) (.loop (.seq (shiftPass H) (.block nextPass)) .ne) := rfl

/-- The checks. -/
structure VFixed : Prop where
  pro : ∃ hc, (taint.check (pT 1 [] [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) (.block (verifyPrologue ++ n0)) hc).isSome
    = true
  fail : ∃ hc, (taint.check (pT 1 [] []) verifyFail hc).isSome = true
  any1 : ∃ hc, (taint.check (pT 1 [] []) (.block any1) hc).isSome = true
  anyT : ∃ hc, (taint.check (pT 1 [] [])
    (.block [.mov32 .rax (.imm 0), .store (sp sAny) .rax, .mov .rdx (.mem (sp sSlen))]) hc).isSome = true
  anyE : ∃ hc, (taint.check (pT 1 [] [])
    (.block [.mov32 .rax (.imm 1), .store (sp sAny) .rax, .mov32 .rdx (.imm 0)]) hc).isSome = true
  dbPub : ∃ hc, (taint.check (pT 1 [17, 18, 19, 20, 21, 22, 26, 38] [.rax])
    (.seq (.block dbSlots) (.block pubArgs)) hc).isSome = true
  acc0 : ∃ hc, (taint.check (pT 1 [17, 21, 23, 25, 26] []) (.block acc0) hc).isSome = true
  clearTop : ∃ hc, (taint.check (pT 1 [23] []) (.block clearTop) hc).isSome = true
  posScan : ∃ hc, (taint.check (pT 1 [23, 24] []) posScan hc).isSome = true
  shiftPro : ∃ hc, (taint.check (pT 1 [] []) (.block shiftPro) hc).isSome = true
  nextPass : ∃ hc, (taint.check (pT 1 [] []) (.block nextPass) hc).isSome = true
  restore : ∃ hc, (taint.check (pT 1 [] []) (.block restoreRegs) hc).isSome = true

theorem vFixed : VFixed :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.RsaPss.X86_64
