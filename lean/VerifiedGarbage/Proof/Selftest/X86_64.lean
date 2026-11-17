module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Impl.Selftest.X86_64
import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Selftest.Contract
public import VerifiedGarbage.Impl.Scrub.X86_64
public import VerifiedGarbage.TCB.X86_64.Residue
import VerifiedGarbage.Proof.Framework.X86_64.ScrubPart
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-! # Pipeline self-test: x86-64 proof -/

@[expose] public section

namespace VG.Proof.Selftest

open Spec.Selftest

open X86_64 in
/-- The x86-64 contract the proof is written against (the artifact's is the
shared contract of `Spec/`, which implies it), for
`vg_selftest_add(a: u64, b: u64) -> u64`: returns
`add a b` and does not modify memory. Both arguments are secret. -/
def addX86_64 : Contract X86_64.isa where
  pre _ := True
  post s s' := s'.gpr .rax = add (s.gpr .rdi) (s.gpr .rsi) ∧ s'.mem = s.mem
  pub _ _ := True

end VG.Proof.Selftest

namespace VG.Proof.Selftest.X86_64

open VG.X86_64

/-- A state satisfying the precondition. -/
def sat : State where
  gpr _ := 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := []

/-! ## Without secret residue

`add` writes only `rax`, the result, and the flags, which depend on the
arguments; the clearing that follows it (`Impl.Scrub.X86_64.scrub`) is one
`xor r11d, r11d`, whose flags are known. It writes no memory: the
postcondition says the memory is unchanged, so `X86_64.Scrub.scrubReg`,
which needs it to read only the buffers (`PostOut`), does not apply, and
the proof is direct. -/

/-- `add`, then the clearing. -/
def addScrubbed : Prog isa := Impl.Scrub.X86_64.scrub .sse 64 [] [] [.r11] [] [] Impl.Selftest.X86_64.add

theorem addScrubbed_run (s : State) : ∃ s', Exec isa addScrubbed s [] s' ∧
    (∀ r, s'.gpr r = if r = .r11 then 0 else if r = .rax then s.gpr .rdi + s.gpr .rsi else s.gpr r) ∧
    s'.cf = some false ∧ s'.zf = some true ∧ s'.sf = some false ∧ s'.of = some false ∧
    s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧
    s'.zmmHi = s.zmmHi ∧ s'.ymmH = s.ymmH ∧ s'.zmmHiH = s.zmmHiH ∧ s'.mxcsr = s.mxcsr := by
  have e : Exec isa addScrubbed s ([] ++ ([] ++ ([] ++ ([] ++ [])))) _ :=
    .seq (.block rfl) (.seq (.block rfl) (.seq (.block rfl) (.seq (.block rfl) (.block rfl))))
  refine ⟨_, e, fun r => ?_, ?_⟩
  · cases r <;> simp [State.setReg, State.setReg32, arithFlags, State.setFlags]
  · simp [State.setReg, State.setReg32, arithFlags, State.setFlags]

theorem addScrubbed_correct (s : State) (_ : Proof.Selftest.addX86_64.pre s) :
    ∃ t s', Exec isa addScrubbed s t s' ∧ abiPreserved s s' ∧ Proof.Selftest.addX86_64.post s s' := by
  obtain ⟨s', e, hg, -, -, -, -, hm, -, -, -, -, -, -, -, hmx⟩ := addScrubbed_run s
  refine ⟨_, s', e, ⟨fun r hr => ?_, by rw [hm], by rw [hmx]⟩, by rw [hg]; rfl, hm⟩
  rw [hg]
  have : r ≠ .r11 ∧ r ≠ .rax := by revert hr; revert r; decide
  simp [this.1, this.2]

theorem addScrubbed_ct :
    ConstantTime isa Proof.Selftest.addX86_64.pre Proof.Selftest.addX86_64.pub addScrubbed :=
  ConstantTime.of_silent fun s _ _ _ h => (Exec.det h (addScrubbed_run s).choose_spec.1).1

theorem addScrubbed_verified :
    Verified X86_64.target addScrubbed (Spec.Selftest.addContract X86_64.abi) :=
  Verified.of_correct addScrubbed_correct addScrubbed_ct (by
    sig_implies [Spec.Selftest.addContract, Spec.Selftest.addSig, Proof.Selftest.addX86_64,
      X86_64.abi, X86_64.argRegs] [sat] using sat)

/-- Two runs that agree outside the buffers (there are none) agree at the
end, but on the result. -/
theorem addScrubbed_noResidue :
    NoResidue addScrubbed (Spec.Selftest.addContract X86_64.abi) 64 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ _ ho _ e₁ e₂
  obtain ⟨u₁, a₁, g₁, c₁, z₁, f₁, o₁, m₁, r₁, w₁, x₁, y₁, h₁, yH₁, zH₁, mx₁⟩ := addScrubbed_run s₁
  obtain ⟨u₂, a₂, g₂, c₂, z₂, f₂, o₂, m₂, r₂, w₂, x₂, y₂, h₂, yH₂, zH₂, mx₂⟩ := addScrubbed_run s₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ a₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ a₂
  obtain ⟨hrd, hwr, hg, hax, -, -, -, -, hx, hy, hz, hyH, hzH, hmx, hm⟩ := ho
  have hdi := hg .rdi (by decide)
  have hsi := hg .rsi (by decide)
  refine ⟨⟨by rw [r₁, r₂, hrd], by rw [w₁, w₂, hwr], fun r hr => ?_, ?_, by rw [c₁, c₂], by rw [z₁, z₂],
    by rw [f₁, f₂], by rw [o₁, o₂], by rw [x₁, x₂, hx], by rw [y₁, y₂, hy], by rw [h₁, h₂, hz],
    by rw [yH₁, yH₂, hyH], by rw [zH₁, zH₂, hzH], by rw [mx₁, mx₂, hmx], fun x hx' => ?_⟩,
    by rw [c₁]; exact Option.some_ne_none _, by rw [z₁]; exact Option.some_ne_none _,
    by rw [f₁]; exact Option.some_ne_none _, by rw [o₁]; exact Option.some_ne_none _⟩
  · rw [g₁, g₂, hdi, hsi, hg r hr]
  · have hax' : s₁.gpr .rax = s₂.gpr .rax := by simpa using hax
    rw [g₁, g₂, hdi, hsi, hax']
  · rw [m₁, m₂]
    exact hm x (by rw [← r₁, ← w₁]; exact hx')


/-! ## Clearing only the registers that may hold secrets

`leakAdd` returns `a + b` too, but first puts the secret `a` in `rcx` and
`xmm1`, and clears both itself. The clearing that `Verified.scrub` derives
from its instructions clears all sixteen SSE registers and `rcx`
(`hall`); `Verified.scrubPart` clears only `r11`, for the flags, since two
runs end agreeing on every other register (`RegsOk`, from what each run
leaves in them, `regsOk_of_leaves`). -/

/-- `rax := rdi + rsi`, through `rcx` and `xmm1`, which it then clears. -/
def leakAdd : Prog isa := .block [
  .mov .rcx (.reg .rdi),
  .xop (.movq .xmm1 .rcx),
  .xop (.bin .pxor .xmm1 .xmm1),
  .alu32 .xor .rcx (.reg .rcx),
  .mov .rax (.reg .rdi),
  .alu .add .rax (.reg .rsi)]

/-- `vg_selftest_add`'s signature, with a postcondition of the result alone,
which `Verified.scrub` needs (`PostOut`): the clearing may write the stack. -/
def addRetContract : Contract isa :=
  Spec.Selftest.addSig.contract X86_64.abi (post := fun a b _ _ r => r = Spec.Selftest.add a b)

/-- What the proof of `leakAdd` is written against. -/
def leakX86_64 : Contract isa where
  pre _ := True
  post s s' := s'.gpr .rax = Spec.Selftest.add (s.gpr .rdi) (s.gpr .rsi)
  pub _ _ := True

theorem leakAdd_run (s : State) : ∃ s', Exec isa leakAdd s [] s' ∧
    (∀ r, s'.gpr r = if r = .rcx then 0 else if r = .rax then s.gpr .rdi + s.gpr .rsi else s.gpr r) ∧
    s'.xmm = (fun x => if x = .xmm1 then 0 else s.xmm x) ∧ s'.ymmHi = s.ymmHi ∧ s'.zmmHi = s.zmmHi ∧
    s'.mxcsr = s.mxcsr ∧ s'.mem = s.mem := by
  refine ⟨_, .block rfl, fun r => ?_, ?_⟩
  · cases r <;> simp [State.setReg, State.setReg32, arithFlags, State.setFlags, XOp.exec, State.setXmm]
  · refine ⟨funext fun x => ?_, ?_⟩
    · cases x <;> simp [State.setReg, State.setReg32, arithFlags, State.setFlags, XOp.exec, State.setXmm,
        reduceXBinOpEval]
    · simp [State.setReg, State.setReg32, arithFlags, State.setFlags, XOp.exec, State.setXmm]

theorem leakAdd_verified : Verified X86_64.target leakAdd addRetContract := by
  refine Verified.of_correct (k := leakX86_64) (fun s _ => ?_)
    (ConstantTime.of_silent fun s _ _ _ h => (Exec.det h (leakAdd_run s).choose_spec.1).1) (by
    sig_implies [addRetContract, Spec.Selftest.addSig, leakX86_64, X86_64.abi, X86_64.argRegs] [sat] using sat)
  obtain ⟨s', e, hg, -, -, -, hmx, hm⟩ := leakAdd_run s
  refine ⟨_, s', e, ⟨fun r hr => ?_, by rw [hm], by rw [hmx]⟩, by simp only [leakX86_64]; rw [hg]; rfl⟩
  rw [hg]
  have : r ≠ .rcx ∧ r ≠ .rax := by revert hr; revert r; decide
  simp [this.1, this.2]

/-- `leakAdd` with the clearing `Verified.scrub` derives from its
instructions: every SSE register, `rcx` and `r11`. -/
theorem leakAdd_all :
    Verified X86_64.target (Impl.Scrub.X86_64.scrub .sse 64 Impl.Scrub.X86_64.xregs [] [.rcx, .r11] [] [] leakAdd)
        addRetContract ∧
      NoResidue (Impl.Scrub.X86_64.scrub .sse 64 Impl.Scrub.X86_64.xregs [] [.rcx, .r11] [] [] leakAdd)
        addRetContract 64 :=
  Scrub.Verified.scrub (A := X86_64.abi) Scrub.ScrubAbi.plain leakAdd_verified (SpSafe.of_all (by decide))
    (by decide) rfl (by decide) (by simp) (by decide) (by decide)
    (fun s u u' hs hq _ hr => by
      revert hq; simp only [Sig.contract, X86_64.abi] at hr ⊢; rw [hr]; exact id)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x hx _ => absurd hx (by simp [Region.Contains]))
    ⟨fun h => absurd rfl h, fun h => absurd rfl h, by simp, by decide, by simp⟩
    (.inl Scrub.mem_xregs) (fun _ => Scrub.mem_xregs) (fun _ _ e => nomatch e) (by decide)

/-- `leakAdd`, then the clearing of `r11` alone. -/
def leakAddScrubbed : Prog isa := Impl.Scrub.X86_64.scrub .sse 64 [] [] [.r11] [] [] leakAdd

theorem leakAddScrubbed_ok :
    Verified X86_64.target leakAddScrubbed addRetContract ∧ NoResidue leakAddScrubbed addRetContract 64 :=
  Scrub.Verified.scrubPart (A := X86_64.abi) Scrub.ScrubAbi.plain leakAdd_verified (Nat.le_refl _) (by simp)
    (fun _ _ e => nomatch e) (Nat.le_refl _) (by simp) (fun _ _ e => nomatch e) (.inl rfl) ⟨fun h => absurd rfl h, fun h => absurd rfl h, by simp, by decide, by simp⟩
    ⟨fun h => absurd rfl h, fun h => absurd rfl h, by simp, by decide, by simp⟩
    (Scrub.regsOk_of_leaves leakAdd_verified.2.1 (G := fun _ _ r => if r = .rcx then some 0 else none)
      (X := fun _ _ x => if x = .xmm1 then some 0 else none) (Y := fun _ _ _ => none)
      (fun s t u _ e => by
        obtain ⟨s', e', hg, hx, hy, hz, -⟩ := leakAdd_run s
        obtain ⟨-, rfl⟩ := Exec.det e e'
        refine ⟨fun r hr _ _ => ?_, fun x _ => ⟨?_, ?_⟩⟩
        · rw [hg]
          have : r ≠ .rax := Scrub.ne_rax_of_scratch r hr
          by_cases h : r = .rcx <;> simp [h, this]
        · rw [hx]; by_cases h : x = .xmm1 <;> simp [h]
        · rw [hy, hz]; rfl)
      (fun _ _ _ _ _ _ _ _ => ⟨rfl, rfl, rfl⟩))
    leakAdd_all

end VG.Proof.Selftest.X86_64
