module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTState
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.ArgumentContext
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Arguments
public import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallGeometry

/-! The two candidate calls share the same public search point and native argument snapshot. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Pins)

def ReadyCT (q : SearchPoint) (s : State) : Prop :=
  LiveCT q s ∧ q.used + q.inputs.c.length ≤ q.inputs.c.bytes.length

def AllocatedCT (q : SearchPoint) (s : State) : Prop :=
  ∃ original, ReadyCT q original ∧ s = allocated 24 original

def CallCT (q : SearchPoint) (s : State) : Prop :=
  ∃ original, LiveCT q original ∧ q.used + q.inputs.c.length ≤ q.inputs.c.bytes.length ∧
    ArgumentContext q.inputs q.used s ∧
    s.mem = callMem q.inputs q.used original.mem (original.sp - 24#32) ∧
    Rest [.r0, .r1, .r2, .r3, .r9, .r12] (allocated 24 original) s

theorem allocated_pins : Pins AllocatedCT [.r4] := by
  rintro q s t ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ r hr
  exact live_pins q a b ha.1 hb.1 r hr

end VG.Proof.Ffdh.Arm.ParameterSearch
