module

public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Proof.Framework.Semantics

/-! # Indirect calls (x86-64): the instructions that stand for them

For the analyses that read the instructions of code (`instrs`), an indirect
call (`Code.icall`) is instructions that write every general-purpose
register but the callee-saved ones (`calleeSaved`, `rsp` among them), which
the function restores (`ISA.callOk`), and MXCSR: an analysis that one of
those registers or MXCSR keeps its value says nothing of code with an
indirect call, nor does one that every instruction leaves the vector
registers alone (`ldmxcsr` is not among the instructions such analyses
cover). -/

@[expose] public section

namespace VG.X86_64

instance : IcallInstrs Instr where
  icallInstrs := .ldmxcsr { base := .rsp } ::
    [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11].map fun r => .mov r (.imm 0)

/-- `ldmxcsr` stands for an indirect call: no analysis that MXCSR is kept
covers one. -/
theorem ldmxcsr_mem_icall {n : Nat} :
    Instr.ldmxcsr { base := .rsp } ∈ instrs (Code.icall n : Prog isa) := by
  simp [instrs, icallInstrs]

/-- A write of each general-purpose register that is not callee-saved stands
for an indirect call: no analysis that such a register is kept covers one. -/
theorem mov_mem_icall {n : Nat} {r : Reg} (hr : r ∉ calleeSaved) :
    Instr.mov r (.imm 0) ∈ instrs (Code.icall n : Prog isa) := by
  cases r <;> simp_all [instrs, icallInstrs, calleeSaved]

/-! ## What a function called indirectly changes

Only the registers, flags, MXCSR and memory (`State.withArch`). -/

theorem fn_withArch {s s₁ s₂ : State} {a : Addr} {f : State → Option (State × List Leak)}
    {t : List Leak} (hf : fnAt s a = some f) (h : f s₁ = some (s₂, t)) :
    ∃ r : Arch, s₂ = s₁.withArch r := by
  simp only [fnAt, Option.map_eq_some_iff] at hf
  obtain ⟨g, -, rfl⟩ := hf
  obtain ⟨r, -, hr⟩ := Option.map_eq_some_iff.mp h
  cases hr; exact ⟨r.1, rfl⟩

@[simp] theorem withArch_rd (s : State) (r : Arch) : (s.withArch r).rd = s.rd := rfl
@[simp] theorem withArch_wr (s : State) (r : Arch) : (s.withArch r).wr = s.wr := rfl
@[simp] theorem withArch_unknowns (s : State) (r : Arch) : (s.withArch r).unknowns = s.unknowns := rfl
@[simp] theorem withArch_syms (s : State) (r : Arch) : (s.withArch r).syms = s.syms := rfl
@[simp] theorem withArch_funs (s : State) (r : Arch) : (s.withArch r).funs = s.funs := rfl

end VG.X86_64
