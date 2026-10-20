module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCallPre

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCallLayout
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # A candidate call preserves the controller and unconsumed input tape -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem call_frame {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) {m m' : Mem}
    (hf : Frame (callWrites p ++ [below (p.c.sp - 32) 128]) m m') :
    Frame (inputBuffers original ++ [below (original.gpr .rsp) 160]) m m' := by
  apply hf.sub
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [callWrites_eq h.input] at hr
    exact ⟨r, List.mem_append_left _ hr, fun _ hi => hi⟩
  · obtain rfl := List.mem_singleton.mp hr
    refine ⟨below (original.gpr .rsp) 160, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    cases h.input.2
    exact below_below (original.gpr .rsp) 32 128

theorem arguments_frame {p : SearchPublic} {original s t : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s)
    (hm : t.mem = writeController s.mem (s.gpr .rsp - 32) (searchCallValues p used)) :
    Frame (inputBuffers original ++ [below (original.gpr .rsp) 160]) s.mem t.mem := by
  apply (search_arguments_frame hm).sub
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨below (original.gpr .rsp) 160, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
  have hsp : s.gpr .rsp = original.gpr .rsp := by cases h.input.2; exact h.rsp
  rw [hsp]
  exact Offset.below_mono _ (by decide) (by decide)

theorem SearchLive.restore {p : SearchPublic} {original s t : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (hg : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r)
    (hf : Frame (inputBuffers original ++ [below (original.gpr .rsp) 160]) s.mem t.mem) :
    SearchLive p original used remaining t := by
  have hc := h.input.control_frame hf
  refine ⟨h.input, h.used_le, h.remaining_le, hr.trans h.rd, hw.trans h.wr,
    (hg .rsp (by decide)).trans h.rsp, (hg .r12 (by decide)).trans h.r12,
    fun r hr hn => (hg r hr).trans (h.saved r hr hn), ?_, ?_, ?_⟩
  · exact (hc 4 (by decide)).trans h.savedR12
  · have hf' : Frame (original.wr ++ [below (original.gpr .rsp) 160]) s.mem t.mem :=
      hf.sub fun r hr => ⟨r, List.mem_append.mpr ((List.mem_append.mp hr).elim
        (fun hi => Or.inl (by rw [h.input.1.2.2.2.1]; exact List.mem_append_left _ hi)) Or.inr), fun _ hi => hi⟩
    exact (h.input.random_frame hf').trans h.random
  · intro e he
    have hj : e.1 < 16 := by
      simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        dsimp only <;> decide
    exact (hc e.1 hj).trans (h.headers e he)

theorem SearchLive.keep {p : SearchPublic} {original s t : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) {rs : List Reg}
    (k : VG.Proof.MlKem.X86_64.Keep rs s t) (hm : t.mem = s.mem)
    (hregs : ∀ reg ∈ calleeSaved, reg ∉ rs) : SearchLive p original used remaining t := by
  apply h.restore k.2.1 k.2.2 (fun reg hr => k.gpr (hregs reg hr))
  rw [hm]
  exact Frame.refl _ _

end VG.Proof.Ffdh.X86_64.Generation
