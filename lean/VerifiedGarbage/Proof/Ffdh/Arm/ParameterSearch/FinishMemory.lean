module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Offset
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Arm.Isa

/-! The final u64 consumption store preserves the prime, controller and saved registers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont

def savedSlots : List (Reg × Nat) := [(.r4, 0), (.r9, 4), (.r10, 8), (.r11, 12), (.r12, 16), (.lr, 20)]

structure ResultPost (p : SearchParams) (result : Spec.Ffdh.ParameterSearchResult) (s : State) : Prop where
  status : s.gpr .r0 = BitVec.ofNat 32 result.status
  output : searchOutput p result s.mem
  used : Spec.Rsa.wordsAt s.mem (State.addr p.c.usedPtr) 1 = [BitVec.ofNat 64 result.used]
  policy : Spec.Rsa.wordsAt s.mem (State.addr p.control) 4 = searchPolicy p result

structure FinishInput (p : SearchParams) (original : State) (result : Spec.Ffdh.ParameterSearchResult)
    (s : State) : Prop extends SearchDone p result s where
  saved : Spill.Saved s.mem (State.addr s.sp) original.gpr savedSlots
  sp : s.sp = original.sp - 24#32
  stackFits : 24 ≤ original.sp.toNat
  kept : ∀ r ∈ [.r5, .r6, .r7, .r8], s.gpr r = original.gpr r

theorem SearchDone.used_buffer {p : SearchParams} {result : Spec.Ffdh.ParameterSearchResult}
    {s : State} (h : SearchDone p result s) : VG.Proof.Ffdh.Arm.OutputBuffer p.c.usedPtr 8 s :=
  ⟨p.c.usedFits, ⟨_, h.buffers.used.2, Region.contains_self _ _⟩⟩

theorem SearchDone.output_after_used {p : SearchParams} {result : Spec.Ffdh.ParameterSearchResult}
    {s : State} {m : Mem} (h : SearchDone p result s)
    (frame : Frame [⟨State.addr p.c.usedPtr, 8⟩] s.mem m) : searchOutput p result m := by
  unfold searchOutput at *
  have fit : p.c.out.toNat + p.c.length ≤ 2 ^ 32 := p.c.outputFits
  exact (VG.Proof.Bignum.Arm.rsa_bytes_frame frame (by omega)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact p.c.outputUsed)).trans h.output

theorem SearchDone.policy_after_used {p : SearchParams} {result : Spec.Ffdh.ParameterSearchResult}
    {s : State} {m : Mem} (h : SearchDone p result s)
    (frame : Frame [⟨State.addr p.c.usedPtr, 8⟩] s.mem m) :
    Spec.Rsa.wordsAt m (State.addr p.control) 4 = searchPolicy p result := by
  have same : Spec.Rsa.wordsAt m (State.addr p.control) 4 =
      Spec.Rsa.wordsAt s.mem (State.addr p.control) 4 := by
    unfold Spec.Rsa.wordsAt
    apply List.map_congr_left
    intro j hj
    have bound : j < 4 := List.mem_range.mp hj
    exact frame.readW (r := ⟨State.addr p.control, 128⟩)
      (Offset.contains_base _ (by omega) (by omega))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact p.controlUsed) (by decide)
  exact same.trans h.policy

end VG.Proof.Ffdh.Arm.ParameterSearch
