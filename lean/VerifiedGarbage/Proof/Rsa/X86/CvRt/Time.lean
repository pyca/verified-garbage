module

public import VerifiedGarbage.Proof.Rsa.X86.CvRt.TimeCheck
public import VerifiedGarbage.Proof.Rsa.X86.CvRt.Sized
public import VerifiedGarbage.Proof.Rsa.X86.CvPair
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeBase
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeExp
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega

/-! # The trace of CRT parameter calculation at a run-time width, once the modulus is accepted

The width is read from the arguments on the stack, so the taint analysis
takes them public with `edi` and `esp` (`τV`, `sizedCheck`), from states whose
permissions are narrowed to the outputs and the working space, apart from the
arguments (`ArgsOk`); runs of `sized` from the states themselves leak the
same traces (`sizedNarrow_relCT`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.CrtValuesRt
open VG.Proof.Rsa.X86.CrtValues (CallGeometry Inputs bodyWrites)
open VG.Proof.Bignum.X86.PublicRt (Both relCT_narrow)

/-- The return address and the arguments lie apart from every writable region. -/
def ArgsOk (s : State) : Prop :=
  (s.gpr .esp).toNat + 68 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 68⟩ r

theorem τV_wf {s : State} (A : ArgsOk s) : VG.X86.Taint.Wf τV s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => A, fun _ h => (List.not_mem_nil h).elim⟩

theorem agreeV {g : CallGeometry} {s₁ s₂ : State} (h₁ : Inputs g s₁) (h₂ : Inputs g s₂)
    (A₁ : ArgsOk s₁) (A₂ : ArgsOk s₂) (sp : s₁.gpr .esp = s₂.gpr .esp) : VG.X86.Taint.Agree τV s₁ s₂ := by
  have f₁ := A₁.1
  have f₂ := A₂.1
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τV_wf A₁, τV_wf A₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τV, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (h₁.ws.workspace.edi_toNat.trans h₂.ws.workspace.edi_toNat.symm)
    · exact sp
  · simp only [τV] at hk
    rw [show VG.X86.Taint.depth τV.stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (show arg s₁ _ = arg s₂ _ from
      (h₁.arguments _ (by omega)).value.trans (h₂.arguments _ (by omega)).value.symm)

/-- What a narrowed run of `sized` keeps: the inputs, the arguments apart and `esp`. -/
def Run (g : CallGeometry) (sp : BitVec 32) (s : State) : Prop :=
  Inputs g s ∧ ArgsOk s ∧ s.gpr .esp = sp

theorem sized_relCT (g : CallGeometry) (sp : BitVec 32) :
    RelCT isa (Both (Run g sp)) sized fun _ _ => True :=
  RelCT.taint (A := taint) τV (fun _ _ h => agreeV h.1.1 h.2.1 h.1.2.1 h.2.2.1 (h.1.2.2.trans h.2.2.2.symm))
    sizedCheck

/-- What the runs of `sized` from the states themselves need: the inputs, `esp`, and the arguments apart
from what the body writes. -/
def SizedAt (g : CallGeometry) (sp : BitVec 32) (s : State) : Prop :=
  Inputs g s ∧ s.gpr .esp = sp ∧ sp.toNat + 68 ≤ 2 ^ 32 ∧
    ∀ r ∈ g.writes, Region.Disjoint ⟨sp.setWidth 64, 68⟩ r

theorem narrow_inputs {g : CallGeometry} {s : State} (h : Inputs g s) :
    Inputs g (s.withRegions (s.rd ++ s.wr) g.writes) := by
  refine ⟨⟨⟨h.ws.workspace.edi, by simp [State.withRegions, CallGeometry.writes], h.ws.workspace.nowrap,
      h.ws.workspace.stk⟩, h.ws.fits, h.ws.wpos, h.ws.wle⟩, h.lower, h.upper,
    fun i hi => ⟨⟨?_, (h.arguments i hi).stack.apart⟩, (h.arguments i hi).value⟩, h.stackApart, h.inputPositive,
    h.inputBound, h.inputFit, fun j => ?_, h.inputApart, h.outputPositive, h.outputBound, h.outputFit, fun j => ?_,
    h.outputScratch, h.outputSeparate⟩
  · obtain ⟨r, hr, hc⟩ := (h.arguments i hi).stack.read
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := h.inputRead j
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · refine ⟨g.buffer (2 * j.val), ?_, Region.contains_self _ _⟩
    have cases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
    rcases cases with e | e | e <;> simp [State.withRegions, CallGeometry.writes, e]

theorem narrow_run {g : CallGeometry} {sp : BitVec 32} {s : State} (S : SizedAt g sp s) :
    Run g sp (s.withRegions (s.rd ++ s.wr) g.writes) := by
  obtain ⟨h, esp, fit, apart⟩ := S
  refine ⟨narrow_inputs h, ⟨?_, fun r hr => ?_⟩, esp⟩
  · show (s.gpr .esp).toNat + 68 ≤ _; rw [esp]; exact fit
  · show Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 68⟩ r; rw [esp]; exact apart r hr

theorem sizedNarrow_relCT (g : CallGeometry) (len : Lengths g) (sp : BitVec 32) :
    RelCT isa (Both (SizedAt g sp)) sized fun _ _ => True := by
  refine relCT_narrow (Pn := Both (Run g sp)) (fun s => s.rd ++ s.wr)
    (fun _ => g.writes) (fun s₁ s₂ ⟨S₁, S₂⟩ => ?_) (sized_relCT g sp)
  have cov : ∀ {s : State}, SizedAt g sp s → Covers g.writes s.wr := by
    intro s S
    apply Covers.of_forall
    intro r hr
    simp only [CallGeometry.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Covers.of_mem (by simpa using S.1.ws.workspace.wr)
    · exact Covers.one (S.1.outputWrite 0)
    · exact Covers.one (S.1.outputWrite 1)
    · exact Covers.one (S.1.outputWrite 2)
  have wp : ∀ {s : State}, SizedAt g sp s →
      ∃ F, WP isa sized (s.withRegions (s.rd ++ s.wr) g.writes) F :=
    fun S => ⟨_, sized_ok (narrow_inputs S.1) len⟩
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right (cov S₁)), cov S₁,
    Covers.append_left (Covers.refl _) (Covers.right (cov S₂)), cov S₂, wp S₁, wp S₂,
    narrow_run S₁, narrow_run S₂⟩

end VG.Proof.Rsa.X86.CrtValuesRt
