module

public import VerifiedGarbage.Proof.Rsa.X86.KcTimeCheck
public import VerifiedGarbage.Proof.Rsa.X86.KcCT
import VerifiedGarbage.Proof.Rsa.X86.KcSized
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeExp
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Rsa.X86.KcInputs
public import VerifiedGarbage.Impl.Rsa.X86.KeyCheckRt
public import VerifiedGarbage.Proof.Rsa.X86.KcInputs
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.Framework.Slots
public import VerifiedGarbage.TCB.X86.Isa

/-! # The trace of the key checks at a run-time width, once the modulus and exponent are accepted

The width is read from the arguments on the stack, so the taint analysis
takes them public with `edi` and `esp` (`τV`, `sizedCheck`), from states whose
permissions are narrowed to the working space, apart from the arguments
(`ArgsOk`); runs of `sized` from the states themselves leak the same traces
(`sizedNarrow_relCT`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.KeyCheckRt (sized)
open VG.Proof.Bignum.X86.PublicRt (Both relCT_narrow)

/-- What the runs of `sized` from the states themselves need: the inputs, `esp`, and the arguments apart
from what the body writes. -/
def SizedAt (g : CallGeometry) (sp : BitVec 32) (s : State) : Prop :=
  Inputs g s ∧ s.gpr .esp = sp ∧ sp.toNat + argSpan g.full ≤ 2 ^ 32 ∧
    ∀ r ∈ g.writes, Region.Disjoint ⟨sp.setWidth 64, argSpan g.full⟩ r

theorem narrow_inputs {g : CallGeometry} {s : State} (h : Inputs g s) :
    Inputs g (s.withRegions (s.rd ++ s.wr) g.writes) := by
  refine ⟨⟨⟨h.ws.workspace.edi, by simp [State.withRegions, CallGeometry.writes], h.ws.workspace.nowrap,
      h.ws.workspace.stk⟩, h.ws.fits, h.ws.wpos, h.ws.wle⟩, h.lower, h.upper,
    fun i hi => ⟨⟨?_, (h.arguments i hi).stack.apart⟩, (h.arguments i hi).value⟩, h.stackApart, h.inputPositive,
    h.inputBound, h.inputFit, fun j hj => ?_, h.inputApart⟩
  · obtain ⟨r, hr, hc⟩ := (h.arguments i hi).stack.read
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := h.inputRead j hj
    exact ⟨r, List.mem_append_left _ hr, hc⟩

theorem narrow_run {g : CallGeometry} {sp : BitVec 32} {s : State} (S : SizedAt g sp s) :
    Run g sp (s.withRegions (s.rd ++ s.wr) g.writes) := by
  obtain ⟨h, esp, fit, apart⟩ := S
  refine ⟨narrow_inputs h, ⟨?_, fun r hr => ?_⟩, esp⟩
  · show (s.gpr .esp).toNat + argSpan g.full ≤ _; rw [esp]; exact fit
  · show Region.Disjoint ⟨(s.gpr .esp).setWidth 64, argSpan g.full⟩ r; rw [esp]; exact apart r hr

theorem sizedNarrow_relCT (g : CallGeometry) (len : Lengths g) (sp : BitVec 32) :
    RelCT isa (fun s₁ s₂ => Both (SizedAt g sp) s₁ s₂ ∧ inputBytes g s₁.mem 0 = inputBytes g s₂.mem 0)
      (sized g.full) fun _ _ => True := by
  refine relCT_narrow (Pn := fun s₁ s₂ => (Run g sp s₁ ∧ Run g sp s₂) ∧ inputBytes g s₁.mem 0 = inputBytes g s₂.mem 0)
    (fun s => s.rd ++ s.wr) (fun _ => g.writes) (fun s₁ s₂ ⟨⟨S₁, S₂⟩, hn⟩ => ?_) (sized_relCT g len sp)
  have cov : ∀ {s : State}, SizedAt g sp s → Covers g.writes s.wr := by
    intro s S
    apply Covers.of_forall
    intro r hr
    simp only [CallGeometry.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact Covers.of_mem (by simpa using S.1.ws.workspace.wr)
  have wp : ∀ {s : State}, SizedAt g sp s →
      ∃ F, WP isa (sized g.full) (s.withRegions (s.rd ++ s.wr) g.writes) F :=
    fun S => ⟨_, sized_wp (narrow_inputs S.1) len⟩
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right (cov S₁)), cov S₁,
    Covers.append_left (Covers.refl _) (Covers.right (cov S₂)), cov S₂, wp S₁, wp S₂,
    ⟨narrow_run S₁, narrow_run S₂⟩, hn⟩

end VG.Proof.Rsa.X86.KeyCheck
