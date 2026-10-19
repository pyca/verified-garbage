module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands

import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
import VerifiedGarbage.Proof.Dsa.Encoding

/-! # Public state and secret operand availability for complete schedules -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure SchedulePublic where
  layout : ExecutionLayout
  digestLen : Nat
  pGreater : 1 < layout.modulus
  qGreater : 255 < layout.subgroup
  pOdd : layout.modulus % 2 = 1
  qOdd : layout.subgroup % 2 = 1
  pFits : layout.modulus ≤ 256 ^ layout.pLen
  qFits : layout.subgroup ≤ 256 ^ layout.qLen
  digestBound : digestLen < 2 ^ 64

def Available (L : ExecutionLayout) (a : Operand) (n : Nat) (s : State) : Prop :=
  ∃ bs : List Byte, OperandBytes s L.base activeBytes a bs ∧ bs.length = n

def ExternalAvailable (L : ExecutionLayout) (a : Operand) (n : Nat) (s : State) : Prop :=
  ∃ bs : List Byte, OperandBytes s L.base usedBytes a bs ∧ bs.length = n

def ScheduleState (inputs : SchedulePublic → List (Operand × Nat)) (p : SchedulePublic) (s : State) : Prop :=
  Ready p.layout s ∧ (∀ a ∈ inputs p, ExternalAvailable p.layout a.1 a.2 s) ∧
    ∃ valid : Bool, word s.mem p.layout.base Field.mask.offset = mask valid

theorem ExternalAvailable.active {L : ExecutionLayout} {a : Operand} {n : Nat} {s : State}
    (h : ExternalAvailable L a n s) : Available L a n s := by
  obtain ⟨bs, hb, hl⟩ := h
  exact ⟨bs, hb.active, hl⟩

theorem Ready.availableLocal {L : ExecutionLayout} {s : State} (h : Ready L s)
    (side : ModulusSide) (d : Nat) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes) :
    Available L ⟨.local d, side.lengthField⟩ (side.length L) s :=
  ⟨_, h.readLocal side d hd hend, by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]⟩

theorem CallResult.schedule {inputs : SchedulePublic → List (Operand × Nat)} {p : SchedulePublic}
    {side : ModulusSide} {d value : Nat} {s t : State}
    (h : CallResult p.layout side d value s t) (hs : ScheduleState inputs p s)
    (hd : activeBytes ≤ d) (hend : d + side.length p.layout ≤ usedBytes)
    (stable : ∀ a ∈ inputs p, a.1.length ≠ .mask ∧ stablePointer a.1.pointer) : ScheduleState inputs p t := by
  refine ⟨h.ready, ?_, ?_⟩
  · intro a ha
    obtain ⟨bs, hb, hlen⟩ := hs.2.1 a ha
    obtain ⟨hf, hp⟩ := stable a ha
    exact ⟨bs, hs.1.preserveExternal h.ready (h.scheduleFrame hd hend) h.keep hf hp hb, hlen⟩
  · obtain ⟨valid, hm⟩ := hs.2.2
    exact ⟨valid, (h.fields hd hend .mask).trans hm⟩

def LocalReduced (L : ExecutionLayout) (side : ModulusSide) (d : Nat) (s : State) : Prop :=
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off L.base d) (side.length L)) < side.value L

theorem CallResult.reduced {L : ExecutionLayout} {side : ModulusSide} {d value : Nat} {s t : State}
    (h : CallResult L side d value s t) (hv : value < side.value L)
    (hf : side.value L ≤ 256 ^ side.length L) : LocalReduced L side d t := by
  unfold LocalReduced
  rw [h.bytes, decodeBE_encodeBE (Nat.lt_of_lt_of_le hv hf)]
  exact hv

theorem SchedulePublic.greater (p : SchedulePublic) (side : ModulusSide) : 1 < side.value p.layout := by
  cases side
  · exact p.pGreater
  · change 1 < p.layout.subgroup
    have := p.qGreater
    omega

theorem SchedulePublic.odd (p : SchedulePublic) (side : ModulusSide) : side.value p.layout % 2 = 1 := by
  cases side
  · exact p.pOdd
  · exact p.qOdd

theorem SchedulePublic.fits (p : SchedulePublic) (side : ModulusSide) :
    side.value p.layout ≤ 256 ^ side.length p.layout := by
  cases side
  · exact p.pFits
  · exact p.qFits

theorem scalar_space {d : Nat} (hd : d + 32 ≤ usedBytes) (p : SchedulePublic) :
    d + p.layout.qLen ≤ usedBytes := by
  have := p.layout.widths.2.1
  omega

theorem element_space {d : Nat} (hd : d + 384 ≤ usedBytes) (p : SchedulePublic) :
    d + p.layout.pLen ≤ usedBytes := by
  have := p.layout.widths.2.2.2
  omega

end VG.Proof.Dsa.X86_64
