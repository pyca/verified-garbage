module

public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Inlining verified code that calls functions (x86-64)

`WP.inline` (`Inline.lean`) inlines verified code that calls no function:
such code changes memory only within the regions it may write. Code that
calls functions also stores their return addresses below the stack pointer,
within `8 * depth` bytes of it if it never writes `rsp` itself
(`Exec.frameSp`): `WP.inlineSp` inlines it with that frame. Code that writes
`rsp` only in the pushes and pops of its frames (`SpSafe`) changes memory
below `rsp` only within its `c.x86_64Depth` bytes (`Exec.stackFrame`):
`WP.inlineF` inlines it with those. `relCT_inline`
gives two runs of inlined verified code the same trace, from its
constant-time proof, as `relCT_call` does for a call.
-/

@[expose] public section

namespace VG.X86_64

/-- Inlining verified code that may call functions: from a state `s` in
which the code's precondition holds once its permissions are narrowed to
`rd` and `wr`, the code terminates in a state satisfying its postcondition
and calling-convention obligations (both on the narrowed states), which has
the permissions of `s`, differs from it in memory only within `wr` and the
`8 * depth` bytes below `rsp`, and keeps every register that no instruction
writes. -/
theorem WP.inlineSp {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : 8 * c.depth + 8 < 2 ^ 64)
    {s : State} {rd wr : List Region} (hpre : k.pre (s.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → abiPreserved s s' →
      Frame (wr ++ [below (s.gpr .rsp) (8 * c.depth)]) s.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = s.gpr r) →
      k.post (s.withRegions rd wr) (s'.withRegions rd wr) → Q s') : WP isa c s Q := by
  obtain ⟨t, s₁, he, ha, hp⟩ := hv _ hpre
  obtain ⟨he', e⟩ := regionModel.inline he hc hw
  have f := Exec.frameSp he hsp hd
  refine ⟨t, _, he', hQ _ (Exec.rdwr he').1 (Exec.rdwr he').2 ha f (fun _ h => Exec.gpr h he') ?_⟩
  rw [show State.withRegions (regionModel.withRegions s₁ (regionModel.rd s) (regionModel.wr s)) rd wr = s₁
    from e]
  exact hp

/-- `WP.inlineSp`, for code that writes `rsp` only in the pushes and pops
of its frames: memory changes within `wr` and the `c.x86_64Depth` bytes
below `rsp`. -/
theorem WP.inlineF {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : SpSafe c) (hd : c.x86_64Depth < 2 ^ 64)
    {s : State} {rd wr : List Region} (hpre : k.pre (s.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → abiPreserved s s' →
      Frame (wr ++ [below (s.gpr .rsp) c.x86_64Depth]) s.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = s.gpr r) →
      k.post (s.withRegions rd wr) (s'.withRegions rd wr) → Q s') : WP isa c s Q := by
  obtain ⟨t, s₁, he, ha, hp⟩ := hv _ hpre
  obtain ⟨he', e⟩ := regionModel.inline he hc hw
  have f := Exec.stackFrame hsp he hd
  refine ⟨t, _, he', hQ _ (Exec.rdwr he').1 (Exec.rdwr he').2 ha f (fun _ h => Exec.gpr h he') ?_⟩
  rw [show State.withRegions (regionModel.withRegions s₁ (regionModel.rd s) (regionModel.wr s)) rd wr = s₁
    from e]
  exact hp

end VG.X86_64

namespace VG.RegionModel

variable {M : ISA} (R : RegionModel M)

/-- Two runs of inlined verified code leak the same trace when its
contract holds in both, narrowed to regions their states' regions cover, and
its public data agrees. -/
theorem relCT_inline {c : Prog M} {Pre : M.State → Prop} {Post : M.State → M.State → Prop}
    {Pub : M.State → M.State → Prop}
    (hv : ∀ s, Pre s → ∃ t s', Exec M c s t s' ∧ Post s s')
    (hct : ConstantTime M Pre Pub c) {P : M.State → M.State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ →
      ∃ r₁ w₁ r₂ w₂ : List Region,
        Pre (R.withRegions s₁ r₁ w₁) ∧ Pre (R.withRegions s₂ r₂ w₂) ∧
        Pub (R.withRegions s₁ r₁ w₁) (R.withRegions s₂ r₂ w₂) ∧
        Covers (r₁ ++ w₁) (R.rd s₁ ++ R.wr s₁) ∧ Covers w₁ (R.wr s₁) ∧
        Covers (r₂ ++ w₂) (R.rd s₂ ++ R.wr s₂) ∧ Covers w₂ (R.wr s₂)) :
    RelCT M P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨_, _, _, _, p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  obtain ⟨_, n₁⟩ := R.trace_narrow hv p₁ c₁ w₁ e₁
  obtain ⟨_, n₂⟩ := R.trace_narrow hv p₂ c₂ w₂ e₂
  exact ⟨hct _ _ _ _ _ _ p₁ p₂ hpub n₁ n₂, trivial⟩

end VG.RegionModel
