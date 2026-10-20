module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout

/-! # Preserve the search invariant across native controller updates -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh.X86_64

theorem SearchLive.control_update {p : SearchPublic} {original s t : State} {used remaining u r : Nat}
    (h : SearchLive p original used remaining s) (hu : u ≤ p.c.rand.length) (hr : r ≤ p.remaining)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 16)
    (h4 : ∀ e ∈ values, 4 ≠ e.1)
    (hm : t.mem = writeController s.mem p.control values)
    (hread : t.rd = s.rd) (hwrite : t.wr = s.wr)
    (hg : ∀ reg ∈ calleeSaved, t.gpr reg = s.gpr reg)
    (hh : Slots t.mem p.control (p.headers u r)) : SearchLive p original u r t := by
  refine ⟨h.input, hu, hr, hread.trans h.rd, hwrite.trans h.wr,
    (hg .rsp (by decide)).trans h.rsp, (hg .r12 (by decide)).trans h.r12,
    fun reg hreg hne => (hg reg hreg).trans (h.saved reg hreg hne), ?_, ?_, hh⟩
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 4) = _
    rw [writeController_word _ _ _ hb 4 (by decide), controllerValue_unchanged _ _ _ h4]
    exact h.savedR12
  · have hf : Frame (original.wr ++ [below (original.gpr .rsp) 160]) s.mem t.mem := by
      rw [hm]
      apply (writeController_frame s.mem p.control values hb).sub
      intro region hregion
      obtain rfl := List.mem_singleton.mp hregion
      refine ⟨inputControl original, List.mem_append_left _ ?_, ?_⟩
      · rw [h.input.1.2.2.2.1]
        simp
      · cases h.input.2
        exact fun _ hi => hi
    exact (h.input.random_frame hf).trans h.random

end VG.Proof.Ffdh.X86_64.Generation
