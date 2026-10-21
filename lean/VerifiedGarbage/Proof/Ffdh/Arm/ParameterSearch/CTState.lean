module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Params

/-! Native parameter timing depends on the shared public tape, consumed offset and u64 budget. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins)

structure SearchPoint where
  inputs : SearchParams
  used : Nat
  remaining : Nat

def LiveCT (q : SearchPoint) (s : State) : Prop := SearchLive q.inputs q.used q.remaining s

def AnyCT (p : SearchParams) (s : State) : Prop := ∃ used remaining, SearchLive p used remaining s

def DoneCT (p : SearchParams) (s : State) : Prop := ∃ result, SearchDone p result s

theorem live_pins : Pins LiveCT [.r4] := by
  intro q s t hs ht r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.buffers.controller.ptr.trans ht.buffers.controller.ptr.symm

theorem any_pins : Pins AnyCT [.r4] := by
  intro p s t ⟨_, _, hs⟩ ⟨_, _, ht⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.buffers.controller.ptr.trans ht.buffers.controller.ptr.symm

theorem done_pins : Pins DoneCT [.r4] := by
  intro p s t ⟨_, hs⟩ ⟨_, ht⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.buffers.controller.ptr.trans ht.buffers.controller.ptr.symm

end VG.Proof.Ffdh.Arm.ParameterSearch
