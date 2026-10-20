module

import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Ffdh.Arm.SamplePowerLaw
import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailInstance
import VerifiedGarbage.Proof.Ffdh.Arm.SamplePowerArgs
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Impl.Ffdh.Arm.KeyPower
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend

/-! # Shared exponentiation consumes the selected public scalar layout -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SampleKeyGenerate
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt)

def power (b : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.KeyPower.powerAt
    (VG.Impl.Ffdh.Arm.KeyPower.twoPhase (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul))
    (VG.Impl.Bignum.Arm.SharedWindow.phase (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul)) 56 16 20

private theorem significant_below {p : Inputs} {l : ScalarLayout p} {s : State}
    (h : KeyCallMemory p s) :
    Region.Disjoint ⟨State.addr l.start, l.width⟩ (belowA s.sp 48) := by
  have fit := h.privateFits
  have lead := l.lead_lt
  rw [ScalarLayout.start, VG.Arm.addr_add (by omega)]
  exact h.privateValue.sub_left (Offset.sub_base _ (by unfold ScalarLayout.width; omega))

theorem powerLaw (b : MontBackend) : SamplePowerLaw (power b) := by
  constructor
  · intro s p l slots eb context calls stable h56 h32 ready modulus odd r2 exponent size
    let A := KeyGenerate.arithmetic b p.base s.sp p.len p.w
    let F := KeyGenerate.fallback A (KeyGenerate.timing b p.base s.sp p.len p.w) p.width.2.2.1
    have separate : ∀ r ∈ [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48],
        Region.Disjoint ⟨State.addr l.start, eb.length⟩ r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact exponent.separate
      · rw [size]; exact significant_below calls
    change WP isa (VG.Impl.Ffdh.Arm.KeyPower.powerAt A.phase F.code 56 16 20) s _
    rw [VG.Impl.Ffdh.Arm.KeyPower.powerAt, WP.seq_iff]
    refine WP.mono (samplePowerArgs_input s A stable h56 h32 context ready modulus odd r2 exponent size
      ⟨calls.stack, rfl⟩ separate) ?_
    rintro u ⟨input, memU, restU⟩
    refine WP.mono (KeyPower.power_ok A F u input) ?_
    rintro t ⟨rd, value, m, rr, one, _, frameT, restT⟩
    have frame : Frame [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] s.mem t.mem := by
      rw [memU] at frameT; exact frameT
    have rest := restU.trans restT
    exact ⟨context.toContext.after_call calls frame rest rd.ptr (fun d hd => (stableSlots_at stable hd).1),
      rd, value, m, rr, one, frame, rest⟩
  · intro p l slots eb1 eb2 stable h56 h32 size1 size2 odd s t tr1 tr2 u v h e1 e2
    let A := KeyGenerate.arithmetic b p.base s.sp p.len p.w
    let F := KeyGenerate.fallback A (KeyGenerate.timing b p.base s.sp p.len p.w) p.width.2.2.1
    have separate (z : State) (eb : List Byte) (hz : SamplePowerInput p l slots eb z)
        (calls : KeyCallMemory p z) (sp : z.sp = s.sp) (size : eb.length = l.width) :
        ∀ r ∈ [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48],
          Region.Disjoint ⟨State.addr l.start, eb.length⟩ r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hz.exponent.separate
      · rw [size, ← sp]; exact significant_below calls
    have args (z : State) (eb : List Byte) (hz : SamplePowerInput p l slots eb z)
        (calls : KeyCallMemory p z) (sp : z.sp = s.sp) (size : eb.length = l.width) :=
      samplePowerArgs_input z A stable h56 h32 hz.context hz.ready hz.modulus odd hz.r2 hz.exponent size
        ⟨calls.stack, sp⟩ (separate z eb hz calls sp size)
    have fit : arrAt p.w 3 + 32 ≤ 8 * p.len := by
      have f := p.width.2.2.1
      simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at *
      omega
    have hn : 0 < 2 * p.w := by have := p.width.1; omega
    have initial : RelCT isa (fun z z' =>
        (SamplePowerInput p l slots eb1 z ∧ KeyCallMemory p z ∧ z.sp = s.sp) ∧
        (SamplePowerInput p l slots eb2 z' ∧ KeyCallMemory p z' ∧ z'.sp = s.sp) ∧ z.sp = z'.sp)
        (VG.Impl.Ffdh.Arm.KeyPower.powerAt A.phase F.code 56 16 20) (fun _ _ => True) := by
      unfold VG.Impl.Ffdh.Arm.KeyPower.powerAt
      exact relCT_chain
        ((powerArgs_ct 56 16 20).mono (fun _ _ k => k.2.2) (fun _ _ _ => trivial))
        (fun z k => WP.mono (args z eb1 k.1 k.2.1 k.2.2 size1) fun _ a => a.1)
        (fun z k => WP.mono (args z eb2 k.1 k.2.1 k.2.2 size2) fun _ a => a.1)
        (KeyPower.power_ct A (KeyGenerate.timing b p.base s.sp p.len p.w) F fit hn
          (by rw [size1]; exact l.width_bounds.1) (size1.trans size2.symm))
    exact initial s t tr1 tr2 u v ⟨⟨h.1.1, h.1.2, rfl⟩, ⟨h.2.1.1, h.2.1.2, h.2.2.symm⟩, h.2.2⟩ e1 e2

end VG.Proof.Ffdh.Arm.SampleKeyGenerate
