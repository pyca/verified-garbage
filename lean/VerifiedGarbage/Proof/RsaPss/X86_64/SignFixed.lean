import VerifiedGarbage.Proof.RsaPss.X86_64.Checks

/-!
# RSASSA-PSS signing on x86-64: the taint checks of the pieces that do not
depend on the hash function
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64

/-- `putH`'s last block: `0xbc` at `EM`'s last byte. -/
def putHTail : List Instr :=
  scr .rdi oEm ++ [.mov .rax (.mem (sp sK)), .alu .add .rdi (.reg .rax), .alu .sub .rdi (.imm 1),
    .mov32 .rax (.imm 0xbc), .store8 (at_ .rdi) .rax]

theorem putH_eq (H : Impl.Pbkdf2.Md.X86_64.Hash) : putH H =
    .seq (.block ([.mov .rdi (.mem (sp sEb)), .mov .rax (.mem (sp sDb)), .alu .add .rdi (.reg .rax)] ++
      scr .rsi oDig ++ [.mov32 .r8 (.imm 0)]))
    (.seq (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rdi .r8) .rax] (.imm (BitVec.ofNat 32 H.D)))
      (.block putHTail)) := rfl

/-- The checks. -/
structure SFixed : Prop where
  pro : ∃ hc, (taint.check (pT 2 [] [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) (.block (signPrologue ++ n0)) hc).isSome
    = true
  fail : ∃ hc, (taint.check (pT 2 [16, 17] []) signFail hc).isSome = true
  dbSlots : ∃ hc, (taint.check (pT 2 [26] [.rax]) (.block dbSlots) hc).isSome = true
  clearEm : ∃ hc, (taint.check (pT 2 [17, 21] []) clearEm hc).isSome = true
  putSalt : ∃ hc, (taint.check (pT 2 [23, 24, 39, 40] []) putSalt hc).isSome = true
  putHTail : ∃ hc, (taint.check (pT 2 [17, 21] []) (.block putHTail) hc).isSome = true
  clearTop : ∃ hc, (taint.check (pT 2 [23] []) (.block clearTop) hc).isSome = true
  privArgs : ∃ hc, (taint.check (pT 2 [] []) (.block privArgs) hc).isSome = true
  restore : ∃ hc, (taint.check (pT 2 [] []) (.block restoreRegs) hc).isSome = true

theorem sFixed : SFixed :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.RsaPss.X86_64
