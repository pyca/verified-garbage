import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Md5.X86_64.Lit
import VerifiedGarbage.Proof.Md5.X86_64.Shared

/-! Local prototype (not for a PR): "no residue", the dead-stack guarantee,
on x86-64, and the generic lemmas that discharge it. -/

namespace VG.Proto
open VG X86_64

/-- TCB-shaped definition. Two runs from `Pre`-states that agree on public
data (`Pub`) and on the caller's context (`Ctx`: everything but the secret
arguments and the buffers' contents) end with the same memory at every
address outside the function's buffers (`vis`): whatever the function left
there, at any depth below the stack pointer, depends on nothing secret. -/
def NoResidue (M : ISA) (Pre : M.State → Prop) (Pub Ctx : M.State → M.State → Prop)
    (vis : M.State → List Region) (mem : M.State → Mem) (c : Prog M) : Prop :=
  ∀ s₁ s₂ t₁ t₂ s₁' s₂', Pre s₁ → Pre s₂ → Pub s₁ s₂ → Ctx s₁ s₂ →
    Exec M c s₁ t₁ s₁' → Exec M c s₂ t₂ s₂' →
    ∀ a, (∀ r ∈ vis s₁, ¬ r.Contains a 1) → mem s₁' a = mem s₂' a

/-- x86-64: the buffers are the regions the entry state may access. -/
def vis (s : State) : List Region := s.rd ++ s.wr

/-- The caller's context (simplified for the prototype: the full version
says all registers but the secret arguments agree). -/
def Ctx (s₁ s₂ : State) : Prop :=
  s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.wr = s₂.wr ∧ s₁.rd = s₂.rd ∧
  ∀ a, (∀ r ∈ vis s₁, ¬ r.Contains a 1) → s₁.mem a = s₂.mem a

/-- The reduction every proof starts from: code that only moves `rsp` by
frames and calls (`spSafe`, which every artifact proves) leaves residue only
in the `x86_64Depth` bytes below `rsp`. So no residue follows from the two
runs agreeing there at the end. -/
theorem noResidue_of_below {c : Prog isa} (hc : SpSafe c) (hd : c.x86_64Depth < 2 ^ 64)
    {Pre : State → Prop} {Pub : State → State → Prop}
    (hbelow : ∀ s₁ s₂ t₁ t₂ s₁' s₂', Pre s₁ → Pre s₂ → Pub s₁ s₂ → Ctx s₁ s₂ →
      Exec isa c s₁ t₁ s₁' → Exec isa c s₂ t₂ s₂' →
      ∀ a, (below (s₁.gpr .rsp) c.x86_64Depth).Contains a 1 → s₁'.mem a = s₂'.mem a) :
    NoResidue isa Pre Pub Ctx vis (·.mem) c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hx e₁ e₂ a ha
  by_cases hb : (below (s₁.gpr .rsp) c.x86_64Depth).Contains a 1
  · exact hbelow _ _ _ _ _ _ h₁ h₂ hp hx e₁ e₂ a hb
  have hout : ∀ (s s' : State) (t : List Leak), Exec isa c s t s' → s.wr = s₁.wr →
      s.gpr .rsp = s₁.gpr .rsp → s'.mem a = s.mem a := by
    intro s s' t e hw hr
    refine Exec.stackFrame hc e hd a fun r hr' => ?_
    rcases List.mem_append.mp hr' with hr' | hr'
    · rw [hw] at hr'; exact ha r (List.mem_append_right _ hr')
    · rw [List.mem_singleton.mp hr', hr]; exact hb
  obtain ⟨hsp, hw, -, hm⟩ := hx
  show s₁'.mem a = s₂'.mem a
  rw [hout _ _ _ e₁ rfl rfl, hout _ _ _ e₂ hw.symm hsp.symm]
  exact hm a ha

/-- Automatic case: code without frames or calls leaves no residue. -/
theorem noResidue_of_depth_zero {c : Prog isa} (hc : SpSafe c) (hd : c.x86_64Depth = 0)
    {Pre : State → Prop} {Pub : State → State → Prop} :
    NoResidue isa Pre Pub Ctx vis (·.mem) c :=
  noResidue_of_below hc (by omega) fun _ _ _ _ _ _ _ _ _ _ _ _ a ha => by
    simp only [Region.Contains, hd] at ha; omega

/-- Example: MD5's compression function, registered with `stack := 0`. -/
theorem md5_compress_noResidue {Pre : State → Prop} {Pub : State → State → Prop} :
    NoResidue isa Pre Pub Ctx vis (·.mem) Impl.Md5.X86_64.compress :=
  have hs : Impl.Md5.X86_64.compress.all (fun i => !isa.writesSp i) = true :=
    Code.all_of_allInstrs (by lit_decide)
  noResidue_of_depth_zero (fun i hi => by simpa using Code.all_instrs hs i hi) (by lit_decide)

/-- Wiped scratch: a frame of `bytes` bytes around frame-free code that, by
its correctness proof, leaves the frame zero leaves no residue. The
hypothesis is about one run, so it comes from the functional proof (the
wipe's `wipeAt_run`), not from a second, relational one. -/
theorem noResidue_wipedFrame {body : Prog isa} {bytes : Nat}
    (hc : SpSafe (.frame (.alloc bytes) body (.free bytes))) (hd : body.x86_64Depth = 0)
    (hb : bytes < 2 ^ 64) {Pre : State → Prop} {Pub : State → State → Prop}
    (hz : ∀ s t s', Pre s → Exec isa (.frame (.alloc bytes) body (.free bytes)) s t s' →
      ∀ a, (below (s.gpr .rsp) bytes).Contains a 1 → s'.mem a = 0) :
    NoResidue isa Pre Pub Ctx vis (·.mem) (.frame (.alloc bytes) body (.free bytes)) := by
  have hdep : (Code.frame (.alloc bytes) body (.free bytes) : Prog isa).x86_64Depth = bytes := by
    simp only [Code.x86_64Depth, hd, Instr.frameBytes, Nat.zero_add]
  refine noResidue_of_below hc (by omega) fun s₁ s₂ _ _ _ _ h₁ h₂ _ hx e₁ e₂ a ha => ?_
  rw [hdep] at ha
  rw [hz _ _ _ h₁ e₁ a ha, hz _ _ _ h₂ e₂ a (hx.1 ▸ ha)]

end VG.Proto
