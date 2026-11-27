module

public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Calling a function by the address in memory (x86-64)

`call qword ptr [m]` (`Instr.callm`) calls the address in the 8 bytes at
`m`. As the instruction of an indirect call of one function `n`, whose code
is `c` (`Code.icalls (.callm m) [(n, c)]`), it runs as the call of `c`
wherever those bytes hold `n`'s address (`callm_ok`). Two runs of it are two
runs of the call wherever both read the same address `m` and it holds `n`'s
address, the same in both (`callm_ct`): the address it reads and the address
it calls are all it observes beyond the call's trace.

Code that shares one body between the variants of its callees calls them
this way: each variant's entry leaves its callees' addresses in words the
body reads but never writes.
-/

@[expose] public section

namespace VG.X86_64

/-- An indirect call through the address in memory at `m` runs as the call
of the one function `n` it may reach, where `m` holds `n`'s address. -/
theorem callm_ok {m : MemOp} {n : String} {c : Prog isa} {s : State}
    (hw : s.load64 (s.ea m) = some (s.syms n)) {Q : State → Prop} (h : WP isa (.call n c) s Q) :
    WP isa (Code.icalls (.callm m) [(n, c)]) s Q :=
  WP.icalls_of_call (i := (Instr.callm m : Instr)) (a := s.syms n) hw
    (by simp [icallTarget, isa]) h

/-- Two runs of the indirect call through `m`, which reads the same address
in both and finds `n`'s address there, the same in both, are two runs of the
call of `n`, with the address added to both traces. -/
theorem callm_ct {m : MemOp} {n : String} {c : Prog isa} {P Q : State → State → Prop}
    (hs : ∀ s₁ s₂, P s₁ s₂ → s₁.ea m = s₂.ea m ∧ s₁.load64 (s₁.ea m) = some (s₁.syms n) ∧
      s₂.load64 (s₂.ea m) = some (s₂.syms n) ∧ s₁.syms n = s₂.syms n)
    (h : RelCT isa P (.call n c) Q) :
    RelCT isa P (Code.icalls (.callm m) [(n, c)]) Q :=
  RelCT.icalls_of_call h fun s₁ s₂ hp => by
    obtain ⟨he, h₁, h₂, hy⟩ := hs s₁ s₂ hp
    refine ⟨s₁.syms n, h₁, hy ▸ h₂, by simp [icallTarget, isa], by simp [icallTarget, isa, hy], ?_⟩
    show [s₁.ea m] = [s₂.ea m]
    rw [he]

end VG.X86_64
