module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTState
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.RequestBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Select
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Live
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Both request comparisons depend only on public bounded lengths, even with arbitrary scratch contents. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins two_piece two_taint)

def available (q : SearchPoint) := q.inputs.c.bytes.length - q.used
def requestFloor (q : SearchPoint) := 256 * q.inputs.c.length
def requestPeak (q : SearchPoint) := max (available q) (requestFloor q)
def requestDouble (q : SearchPoint) := 2 * requestPeak q
def requestCap (q : SearchPoint) := Spec.Ffdh.parameterEntropy q.inputs.c.bits

def PairCT (x y : SearchPoint → Nat) (q : SearchPoint) (s : State) : Prop :=
  LiveCT q s ∧ s.gpr .r9 = BitVec.ofNat 32 (x q) ∧ s.gpr .r10 = BitVec.ofNat 32 (y q)

def ValueCT (x : SearchPoint → Nat) (q : SearchPoint) (s : State) : Prop :=
  LiveCT q s ∧ s.gpr .r9 = BitVec.ofNat 32 (x q)

private theorem pair_pins (x y : SearchPoint → Nat) : Pins (PairCT x y) [.r9, .r10] := by
  intro q s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.2.2.trans ht.2.2.symm

private theorem value_pins (x : SearchPoint → Nat) : Pins (ValueCT x) [.r4, .r9] := by
  intro q s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.1.buffers.controller.ptr.trans ht.1.buffers.controller.ptr.symm
  · exact hs.2.trans ht.2.symm

private theorem head_ready (q : SearchPoint) (s : State) (h : LiveCT q s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 10,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 1, .mov .r10 (.shifted .r10 .lsl 8)]) s
      (PairCT available requestFloor q) := by
  have tape := h.saved 10 (by simp [searchSlots])
  have width := h.saved 1 (by simp [searchSlots])
  simp only [searchValues] at tape width
  refine WP.mono (requestHead_ok s h.buffers.controller tape width) ?_
  rintro t ⟨⟨left, right, mem⟩, rest⟩
  exact ⟨h.after_read (by decide) mem rest, left, right⟩

private theorem max_ready (q : SearchPoint) (s : State) (h : PairCT available requestFloor q s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.select true) s (ValueCT requestPeak q) := by
  refine WP.mono (selectNat_ok true s (by have := q.inputs.c.tapeCount; unfold available; omega)
    (by have := q.inputs.width_bounds; unfold requestFloor; omega) h.2.1 h.2.2) ?_
  rintro t ⟨⟨value, mem⟩, rest⟩
  exact ⟨h.1.after_read (by decide) mem rest, value⟩

private theorem double_ready (q : SearchPoint) (s : State) (h : ValueCT requestPeak q s) :
    WP isa (.block [.dp .add .r9 .r9 (.reg .r9), VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 2]) s
      (PairCT requestDouble requestCap q) := by
  have cap := h.1.saved 2 (by simp [searchSlots])
  simp only [searchValues] at cap
  refine WP.mono (requestDouble_ok s h.1.buffers.controller h.2 cap) ?_
  rintro t ⟨⟨left, right, mem⟩, rest⟩
  exact ⟨h.1.after_read (by decide) mem rest, left, right⟩

private theorem min_ready (q : SearchPoint) (s : State) (h : PairCT requestDouble requestCap q s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.select false) s
      (ValueCT (fun q => min (requestDouble q) (requestCap q)) q) := by
  have tapeBound : q.inputs.c.bytes.length ≤ Spec.Ffdh.parameterEntropy q.inputs.c.bits := q.inputs.tapeBound
  have doubleFits : requestDouble q < 2 ^ 32 := q.inputs.policy.double_fits (by unfold available; omega)
  refine WP.mono (selectNat_ok false s doubleFits q.inputs.entropy_fits h.2.1 h.2.2) ?_
  rintro t ⟨⟨value, mem⟩, rest⟩
  exact ⟨h.1.after_read (by decide) mem rest, value⟩

theorem request_ct : RelCT isa (Two LiveCT) VG.Impl.Ffdh.Arm.ParameterSearch.request (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.request
  refine RelCT.seq (two_piece [.r4] live_pins (by taint_decide) head_ready) ?_
  refine RelCT.seq (two_piece [.r9, .r10] (pair_pins _ _) (by taint_decide) max_ready) ?_
  refine RelCT.seq (two_piece [.r4, .r9] (value_pins _) (by taint_decide) double_ready) ?_
  refine RelCT.seq (two_piece [.r9, .r10] (pair_pins _ _) (by taint_decide) min_ready) ?_
  exact two_taint [.r4] (fun _ _ _ hs ht r hr => live_pins _ _ _ hs.1 ht.1 r hr) (by taint_decide)

end VG.Proof.Ffdh.Arm.ParameterSearch
