module

public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.Registration
public meta import VerifiedGarbage.Proof.Framework.Registration

/-!
# No residue (x86-64)

`NoResidue` for code on x86-64, from its contract's `ctx`: the two entry
states are the same but for their memory and the secret argument registers
(`sameBut`), so they agree on `rsp`, the regions and the memory outside the
regions. Code that moves `rsp` only by frames and calls (`SpSafe`) changes
memory only in its writable regions and its `x86_64Depth` bytes below `rsp`
(`Exec.stackFrame`), so it leaves no residue if the two runs agree there
(`noResidue_of_below`), and code without frames or calls leaves none at all
(`noResidue_of_depth_zero`, which `residue_auto` applies).
-/

@[expose] public section

namespace VG.X86_64

/-- The memory an artifact's caller gives it, under the calling convention
`abi.withConsts cs`. -/
abbrev vis (cs : List (String × List (BitVec 64))) (s : State) : List Region :=
  (abi.withConsts cs).rd s ++ (abi.withConsts cs).wr s

theorem withConsts_ctx (cs : List (String × List (BitVec 64))) :
    (abi.withConsts cs).ctx = abi.ctx ∧ (abi.withConsts cs).mem = abi.mem ∧
      (abi.withConsts cs).wr = abi.wr := by
  cases cs <;> exact ⟨rfl, rfl, rfl⟩

theorem secretRegs_rsp (ws : List Nat) (pubs : List Bool) : Reg.rsp ∉ secretRegs ws pubs := by
  intro h
  simp only [secretRegs, List.mem_filterMap] at h
  obtain ⟨⟨r, p⟩, hm, he⟩ := h
  have hr := (List.of_mem_zip hm).1
  cases p <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, reduceCtorEq] at he
  subst he
  have := List.mem_of_mem_take hr
  simp [argRegs] at this

/-- What a contract's `ctx` says of the two entry states. -/
theorem ctx_facts {sig : Sig} {cs : List (String × List (BitVec 64))} {pre post wa st leak}
    {s₁ s₂ : State} (h : (sig.contract (abi.withConsts cs) pre post wa st leak).ctx s₁ s₂) :
    s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.wr = s₂.wr ∧ s₁.rd = s₂.rd ∧
      ∀ a, (∀ r ∈ vis cs s₁, ¬ r.Contains a 1) → s₁.mem a = s₂.mem a := by
  obtain ⟨hc, hm, -⟩ := withConsts_ctx cs
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  obtain ⟨-, hs, -, -, hout⟩ := h
  rw [hc] at hs
  rw [hm] at hout
  have hs' : s₂ = { s₁ with mem := s₂.mem, gpr := _ } := hs
  refine ⟨?_, by rw [hs'], by rw [hs'], hout⟩
  rw [hs']
  simp only [secretRegs_rsp, ↓reduceIte]

/-- Residue only in the `x86_64Depth` bytes below `rsp`: no residue, if the
two runs agree there. -/
theorem noResidue_of_below {sig : Sig} {cs : List (String × List (BitVec 64))} {pre post wa st leak}
    {c : Prog isa} (hc : SpSafe c) (hd : c.x86_64Depth < 2 ^ 64)
    (hbelow : ∀ s₁ s₂ t₁ t₂ s₁' s₂',
      (sig.contract (abi.withConsts cs) pre post wa st leak).pre s₁ →
      (sig.contract (abi.withConsts cs) pre post wa st leak).pre s₂ →
      (sig.contract (abi.withConsts cs) pre post wa st leak).ctx s₁ s₂ →
      Exec isa c s₁ t₁ s₁' → Exec isa c s₂ t₂ s₂' →
      ∀ a, (below (s₁.gpr .rsp) c.x86_64Depth).Contains a 1 → s₁'.mem a = s₂'.mem a) :
    NoResidue isa (sig.contract (abi.withConsts cs) pre post wa st leak).pre
      (sig.contract (abi.withConsts cs) pre post wa st leak).ctx (vis cs)
      (abi.withConsts cs).mem c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hx e₁ e₂ a ha
  rw [(withConsts_ctx cs).2.1]
  show s₁'.mem a = s₂'.mem a
  by_cases hb : (below (s₁.gpr .rsp) c.x86_64Depth).Contains a 1
  · exact hbelow _ _ _ _ _ _ h₁ h₂ hx e₁ e₂ a hb
  obtain ⟨hsp, hw, -, hm⟩ := ctx_facts hx
  have hwr : (abi.withConsts cs).wr s₁ = s₁.wr := by rw [(withConsts_ctx cs).2.2]; rfl
  have hout : ∀ (s s' : State) (t : List Leak), Exec isa c s t s' → s.wr = s₁.wr →
      s.gpr .rsp = s₁.gpr .rsp → s'.mem a = s.mem a := by
    intro s s' t e hw' hr
    refine Exec.stackFrame hc e hd a fun r hr' => ?_
    rcases List.mem_append.mp hr' with hr' | hr'
    · rw [hw', ← hwr] at hr'; exact ha r (List.mem_append_right _ hr')
    · rw [List.mem_singleton.mp hr', hr]; exact hb
  rw [hout _ _ _ e₁ rfl rfl, hout _ _ _ e₂ hw.symm hsp.symm]
  exact hm a ha

/-- Code without frames or calls leaves no residue. -/
theorem noResidue_of_depth_zero {sig : Sig} {cs : List (String × List (BitVec 64))}
    {pre post wa st leak} {c : Prog isa} (hc : c.all (fun i => !isa.writesSp i) = true)
    (hd : c.x86_64Depth = 0) :
    NoResidue isa (sig.contract (abi.withConsts cs) pre post wa st leak).pre
      (sig.contract (abi.withConsts cs) pre post wa st leak).ctx (vis cs)
      (abi.withConsts cs).mem c :=
  noResidue_of_below (fun i hi => by simpa using Code.all_instrs hc i hi) (by omega)
    fun _ _ _ _ _ _ _ _ _ _ _ a ha => by simp only [Region.Contains, hd] at ha; omega

/-- `noResidue_of_depth_zero` for an artifact's contract, given `ofSig`. -/
theorem noResidue_of_depth_zero' {sig : Sig} {cs : List (String × List (BitVec 64))} {wa st}
    {k : Contract isa} (hk : ∃ pre post leak, k = sig.contract (abi.withConsts cs) pre post wa st leak)
    {c : Prog isa} (hc : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth = 0) :
    NoResidue isa k.pre k.ctx (vis cs) (abi.withConsts cs).mem c := by
  obtain ⟨_, _, _, rfl⟩ := hk
  exact noResidue_of_depth_zero hc hd

end VG.X86_64

namespace VG.X86_64

/-- `residue_auto` on x86-64: code without frames or calls, from the
registration's `ofSig` and `spSafe`. -/
macro_rules
  | `(tactic| residue_auto) =>
    `(tactic| exact VG.X86_64.noResidue_of_depth_zero' (by of_sig) ‹_› (by lit_decide))

end VG.X86_64
