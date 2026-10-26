module

public import VerifiedGarbage.Proof.Framework.Fence
public import VerifiedGarbage.TCB.X86_64.Target

/-!
# Fencing x86-64 code with `lfence`

`lfence` is the speculation barrier: "LFENCE does not execute until all
prior instructions have completed locally, and no later instruction begins
execution until LFENCE completes" (Intel SDM Vol. 2A, "LFENCE"), and Intel
recommends it against bounds check bypass ("Speculative Execution Side
Channel Mitigations", rev. 3.0, §2.1). On AMD processors it is
dispatch-serializing with `MSR C001_1029[1]` set (AMD, "Software Techniques
for Managing Speculation on AMD Processors"), the default on Family 17h and
later. A transient semantics `S` models it as a barrier by
`S.fence .lfence = true`.

Sequentially it does nothing and accesses no memory (`Nop`), and every x86-64
instruction, call and return makes the same number of observations whatever
the state (`leakShape`, which the model states as a design rule in
`TCB/X86_64/Isa.lean`). So every verified x86-64 artifact, fenced, is
verified and speculatively constant time (`verified_fence`), for every
transient semantics in which `lfence` is a barrier.
-/

@[expose] public section

namespace VG.X86_64

theorem lfence_nop : Nop isa .lfence := ⟨fun _ => rfl, fun _ => rfl⟩

theorem leakShape : LeakShape isa where
  addrs i s s' := by
    cases i
    case mov _ src | alu _ _ src | mov32 _ src | alu32 _ _ src | mulx _ _ src | adcx _ src
      | adox _ src | cmov _ _ src => cases src <;> rfl
    case push | pop => simp only [addrs, List.length_map]
    all_goals rfl
  callAddrs _ _ := rfl
  retAddrs _ _ := rfl

/-- **Every verified x86-64 artifact, with `lfence` at its entry and every
branch target, is verified and speculatively constant time.** -/
theorem verified_fence {c : Prog isa} {k : Contract isa} (h : Verified target c k)
    {S : Spectre isa} (hf : S.fence .lfence = true) :
    Verified target (c.fenceFn .lfence) k ∧ SpecConstantTime S k.pre k.pub (c.fenceFn .lfence) :=
  h.fence_spec leakShape lfence_nop hf

end VG.X86_64
