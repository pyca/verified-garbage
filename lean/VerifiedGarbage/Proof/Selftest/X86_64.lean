module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Impl.Selftest.X86_64
import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Selftest.Contract
public import VerifiedGarbage.Impl.Scrub.X86_64
public import VerifiedGarbage.TCB.X86_64.Residue

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

theorem add_correct (s : State) (_ : Proof.Selftest.addX86_64.pre s) :
    ∃ t s', Exec isa Impl.Selftest.X86_64.add s t s' ∧ abiPreserved s s' ∧
      Proof.Selftest.addX86_64.post s s' := by
  refine ⟨[], _, .block rfl, ?_, ?_, ?_⟩
  · simp [abiPreserved, calleeSaved, State.setReg, arithFlags, State.setFlags]
  · simp [State.setReg, arithFlags, State.setFlags, Spec.Selftest.add]
  · rfl

theorem add_ct : ConstantTime isa Proof.Selftest.addX86_64.pre Proof.Selftest.addX86_64.pub
    Impl.Selftest.X86_64.add := by
  refine ConstantTime.of_silent fun s t s' _ h => ?_
  rw [Impl.Selftest.X86_64.add, Exec.block_iff] at h
  cases h
  rfl

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

theorem add_verified :
    Verified X86_64.target Impl.Selftest.X86_64.add (Spec.Selftest.addContract X86_64.abi) :=
  Verified.of_correct add_correct add_ct (by
    sig_implies [Spec.Selftest.addContract, Spec.Selftest.addSig, Proof.Selftest.addX86_64,
      X86_64.abi, X86_64.argRegs] [sat] using sat)

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
  refine ⟨by rw [r₁, r₂, hrd], by rw [w₁, w₂, hwr], fun r hr => ?_, ?_, by rw [c₁, c₂], by rw [z₁, z₂],
    by rw [f₁, f₂], by rw [o₁, o₂], by rw [x₁, x₂, hx], by rw [y₁, y₂, hy], by rw [h₁, h₂, hz],
    by rw [yH₁, yH₂, hyH], by rw [zH₁, zH₂, hzH], by rw [mx₁, mx₂, hmx], fun x hx' => ?_⟩
  · rw [g₁, g₂, hdi, hsi, hg r hr]
  · have hax' : s₁.gpr .rax = s₂.gpr .rax := by simpa using hax
    rw [g₁, g₂, hdi, hsi, hax']
  · rw [m₁, m₂]
    exact hm x (by rw [← r₁, ← w₁]; exact hx')

end VG.Proof.Selftest.X86_64
