module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Framework.Offset

/-! The three public table-building counters are outside all persistent cells. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem Memory.after_control {p : Inputs} {sp : BitVec 32} {s t : State} {d : Nat}
    (h : Memory p sp s) (hd : d ∈ [36,40,68])
    (frame : Frame [⟨off (State.addr s.sp) d,4⟩] s.mem t.mem)
    (rest : Rest roundClobbers s t) (ptr : t.gpr .r0 = p.base) :
    Memory p sp t ∧ WorkspaceEq (State.addr p.base) (8*p.len) s.mem t.mem := by
  have choices : d = 36 ∨ d = 40 ∨ d = 68 := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hd
  have fit : d+4 ≤ 72 := by omega
  have sub := Offset.sub_base (State.addr s.sp) (d := d) (n := 4) (k := 72) fit
  have workspaceSep : ∀ r ∈ [⟨off (State.addr s.sp) d,4⟩],
      (⟨State.addr p.base,8*p.len⟩ : Region).Disjoint r := by
    intro r hr
    have eq := List.mem_singleton.mp hr
    subst r
    exact h.context.locals.separate.symm.sub_right sub
  have baseSep : ∀ r ∈ [⟨off (State.addr s.sp) d,4⟩],
      (⟨State.addr s.sp,4⟩ : Region).Disjoint r := by
    intro r hr
    have eq := List.mem_singleton.mp hr
    subst r
    exact Offset.base_disjoint (State.addr s.sp) (by omega) (by omega)
  obtain ⟨ready,workspace⟩ := h.ready.after_external frame workspaceSep baseSep rest ptr
  have context := h.context.after_local fit frame rest ptr
    (by intro e he; simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at he; omega)
    (by intro e he; simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at he; omega)
  refine ⟨⟨context,ready,h.calls.after rest,rest.sp.trans h.fixed,h.output.after rest,
    h.workspaceSeparate,h.domainSeparate,h.localSeparate,h.callSeparate,?_,?_⟩,workspace⟩
  · have word := frame.readW (w := 32) (r := ⟨off (State.addr s.sp) 16,4⟩) (Region.contains_self _ _)
      (by
        intro r hr
        have eq := List.mem_singleton.mp hr
        subst r
        exact Offset.disjoint (State.addr s.sp) (d := 16) (n := 4) (e := d) (k := 4)
          (Or.inl (by omega)) (by decide) (by omega)) (by decide)
    rw [h.fixed] at word
    exact word.trans h.bitsSaved
  · have word := frame.readW (w := 32) (r := ⟨off (State.addr s.sp) 44,4⟩) (Region.contains_self _ _)
      (by
        intro r hr
        have eq := List.mem_singleton.mp hr
        subst r
        exact Offset.disjoint (State.addr s.sp) (d := 44) (n := 4) (e := d) (k := 4)
          (by omega) (by decide) (by omega)) (by decide)
    rw [h.fixed] at word
    exact word.trans h.rowsSaved

end VG.Proof.Ffdh.Arm.CombBuilder
