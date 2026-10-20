module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Layout

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Start

/-! # What keeps the key-generation controller's loop state -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64 (Slots)
open VG.Proof.Ffdh.X86_64.Generation (writeController writeController_frame writeController_word
  controllerValue controllerValue_unchanged)

theorem KeyPublic.headers_index {p : KeyPublic} {used keys scalars : Nat} {e : Nat × BitVec 64}
    (he : e ∈ p.headers used keys scalars) : e.1 < 16 := p.headers_bound used keys scalars e he

theorem frame_of_callChanges (s : State) {m m' : Mem} (hf : Frame (KeyInput.callChanges s) m m') :
    Frame (KeyInput.changes s) m m' := hf.sub (KeyInput.callChanges_sub s)

namespace KeyLive

variable {p : KeyPublic} {original s t : State} {used keys scalars : Nat}

/-- Through code that keeps r12, the stack pointer, the regions, the
controller's words, and writes only the outputs, `used`, the working space
and the stack. -/
theorem restore (h : KeyLive p original used keys scalars s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (hg : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r)
    (hf : Frame (KeyInput.callChanges original) s.mem t.mem) :
    KeyLive p original used keys scalars t := by
  have hc := h.input.control_frame hf
  have hf' := frame_of_callChanges original hf
  refine ⟨h.input, h.used_le, h.keys_le, h.scalars_le, hr.trans h.rd, hw.trans h.wr,
    (hg .rsp (by decide)).trans h.rsp, (hg .r12 (by decide)).trans h.r12,
    fun r hr hn => (hg r hr).trans (h.saved r hr hn), ?_, ?_, ?_, ?_⟩
  · exact (hc 4 (by decide)).trans h.savedR12
  · exact (h.input.random_frame hf').trans h.random
  · exact (h.input.domain_frame hf').trans h.domain
  · intro e he
    exact (hc e.1 (KeyPublic.headers_index he)).trans (h.headers e he)

theorem keep (h : KeyLive p original used keys scalars s) {rs : List Reg}
    (k : Keep rs s t) (hm : t.mem = s.mem) (hregs : ∀ reg ∈ calleeSaved, reg ∉ rs) :
    KeyLive p original used keys scalars t := by
  apply h.restore k.2.1 k.2.2 (fun reg hr => k.gpr (hregs reg hr))
  rw [hm]
  exact Frame.refl _ _

/-- Through writes of the controller's words but the saved r12, to the
counters `u`, `k` and `c`. -/
theorem update (h : KeyLive p original used keys scalars s) {u k c : Nat}
    (hu : u ≤ p.randLen) (hk : k ≤ 128) (hc : c ≤ 128)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 16)
    (h4 : ∀ e ∈ values, 4 ≠ e.1)
    (hm : t.mem = writeController s.mem p.control values)
    (hread : t.rd = s.rd) (hwrite : t.wr = s.wr)
    (hg : ∀ reg ∈ calleeSaved, t.gpr reg = s.gpr reg)
    (hh : Slots t.mem p.control (p.headers u k c)) : KeyLive p original u k c t := by
  have hf : Frame (KeyInput.changes original) s.mem t.mem := by
    rw [hm]
    apply (writeController_frame s.mem p.control values hb).sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    refine ⟨inCtl original, by simp [KeyInput.changes, inWrites], ?_⟩
    rw [← h.input.2]
    exact fun _ hi => hi
  refine ⟨h.input, hu, hk, hc, hread.trans h.rd, hwrite.trans h.wr,
    (hg .rsp (by decide)).trans h.rsp, (hg .r12 (by decide)).trans h.r12,
    fun reg hreg hne => (hg reg hreg).trans (h.saved reg hreg hne), ?_, ?_, ?_, hh⟩
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 4) = _
    rw [writeController_word _ _ _ hb 4 (by decide), controllerValue_unchanged _ _ _ h4]
    exact h.savedR12
  · exact (h.input.random_frame hf).trans h.random
  · exact (h.input.domain_frame hf).trans h.domain

theorem header (h : KeyLive p original used keys scalars s) {j : Nat} {v : BitVec 64}
    (hj : (j, v) ∈ p.headers used keys scalars) : word s.mem p.control (8 * j) = v :=
  h.headers (j, v) hj

end KeyLive

theorem KeyDone.keep {p : KeyPublic} {original s t : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) {rs : List Reg} (k : Keep rs s t) (hm : t.mem = s.mem)
    (hregs : ∀ reg ∈ calleeSaved, reg ∉ rs) : KeyDone p original result t := by
  refine ⟨h.input, k.2.1.trans h.rd, k.2.2.trans h.wr,
    (k.gpr (hregs .rsp (by decide))).trans h.rsp, (k.gpr (hregs .r12 (by decide))).trans h.r12,
    fun reg hr hn => (k.gpr (hregs reg hr)).trans (h.saved reg hr hn), ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  · exact h.savedR12
  · exact h.usedPtr
  · exact h.used
  · exact h.status
  · exact h.policy
  · exact h.output

end VG.Proof.Ffdh.X86_64.KeyGeneration
