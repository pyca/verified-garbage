module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Data
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Live
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
import VerifiedGarbage.Proof.Framework.Omega

/-! # What keeps the key-generation controller's loop state (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.KeyGeneration

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Proof.Ffdh.PPC64LE.Generation (Slots CtlAccess)
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  controllerValue controllerValue_unchanged)

theorem frame_of_callChanges (s : State) {m m' : Mem} (hf : Frame (KeyInput.callChanges s) m m') :
    Frame (KeyInput.changes s) m m' := hf.sub (KeyInput.callChanges_sub s)

namespace KeyLive

variable {p : KeyPublic} {original s t : State} {used keys scalars : Nat}

theorem access (h : KeyLive p original used keys scalars s) : CtlAccess s p.control :=
  CtlAccess.of_scr (h.input.control_scr (t := s) h.wr)

/-- Through code that keeps `r31`, the stack pointer, the regions, the
controller's words, and writes only the outputs, `used`, the working space
and the stack. -/
theorem restore (h : KeyLive p original used keys scalars s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ preserved, t.gpr r = s.gpr r)
    (hf : Frame (KeyInput.callChanges original) s.mem t.mem) :
    KeyLive p original used keys scalars t := by
  have hc := h.input.control_frame hf
  have hf' := frame_of_callChanges original hf
  refine ⟨h.input, h.used_le, h.keys_le, h.scalars_le, hr.trans h.rd, hw.trans h.wr,
    hsp.trans h.sp, (hg .r31 (by decide)).trans h.r31,
    fun r hr h31 => (hg r hr).trans (h.saved r hr h31), ?_, ?_, ?_, ?_⟩
  · exact (hc 4 (by decide)).trans h.savedR31
  · exact (h.input.random_frame hf').trans h.random
  · exact (h.input.domain_frame hf').trans h.domain
  · intro e he
    exact (hc e.1 (KeyPublic.headers_index he)).trans (h.headers e he)

theorem keep (h : KeyLive p original used keys scalars s) {rs : List Reg}
    (k : Keep rs s t) (hm : t.mem = s.mem) (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) :
    KeyLive p original used keys scalars t := by
  apply h.restore k.rd k.wr k.sp (fun reg hr => k.gpr reg (hregs reg hr))
  rw [hm]
  exact Frame.refl _ _

/-- Through writes of the controller's words but the saved `r31`, to the
counters `u`, `k` and `c`. -/
theorem update (h : KeyLive p original used keys scalars s) {u k c : Nat}
    (hu : u ≤ p.randLen) (hk : k ≤ 128) (hc : c ≤ 128)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 16)
    (h4 : ∀ e ∈ values, 4 ≠ e.1)
    (hm : t.mem = writeController s.mem p.control values)
    (kp : Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] s t)
    (hh : Slots t.mem p.control (p.headers u k c)) : KeyLive p original u k c t := by
  have hf : Frame (KeyInput.changes original) s.mem t.mem := by
    rw [hm]
    apply (writeController_frame s.mem p.control values hb).sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    refine ⟨inCtl original, by simp [KeyInput.changes, inWrites], ?_⟩
    rw [← h.input.2]
    exact fun _ hi => hi
  have hg : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => kp.gpr r (by revert r hr; decide)
  refine ⟨h.input, hu, hk, hc, kp.rd.trans h.rd, kp.wr.trans h.wr,
    kp.sp.trans h.sp, (hg .r31 (by decide)).trans h.r31,
    fun reg hreg h31 => (hg reg hreg).trans (h.saved reg hreg h31), ?_, ?_, ?_, hh⟩
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 4) = _
    rw [writeController_word _ _ _ hb 4 (by decide), controllerValue_unchanged _ _ _ h4]
    exact h.savedR31
  · exact (h.input.random_frame hf).trans h.random
  · exact (h.input.domain_frame hf).trans h.domain

theorem header (h : KeyLive p original used keys scalars s) {j : Nat} {v : BitVec 64}
    (hj : (j, v) ∈ p.headers used keys scalars) : word s.mem p.control (8 * j) = v :=
  h.headers (j, v) hj

/-- A finished search's state, from a loop state with its words written. -/
theorem done (h : KeyLive p original used keys scalars s) {r : Spec.Ffdh.KeySearchResult}
    (hu : r.used = used)
    (hs : word s.mem p.control 112 = BitVec.ofNat 64 r.status)
    (hp : Spec.Rsa.wordsAt s.mem p.control 4 = p.policy r)
    (ho : KeyOutput p r s.mem) : KeyDone p original r s :=
  ⟨h.input, h.rd, h.wr, h.r31, h.saved, h.savedR31,
    h.header (j := 15) (by simp [KeyPublic.headers]),
    by rw [hu]; exact h.header (j := 11) (by simp [KeyPublic.headers]), hs, hp, ho⟩

end KeyLive

theorem KeyDone.keep {p : KeyPublic} {original s t : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) {rs : List Reg} (k : Keep rs s t) (hm : t.mem = s.mem)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) : KeyDone p original result t := by
  refine ⟨h.input, k.rd.trans h.rd, k.wr.trans h.wr, (k.gpr _ (hregs .r31 (by decide))).trans h.r31,
    fun reg hr h31 => (k.gpr reg (hregs reg hr)).trans (h.saved reg hr h31), ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  · exact h.savedR31
  · exact h.usedPtr
  · exact h.used
  · exact h.status
  · exact h.policy
  · exact h.output

/-- A finished search's state depends on its result's outcome and octets
consumed, not on its statuses. -/
theorem KeyDone.congr {p : KeyPublic} {original s : State} {r r' : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original r s) (ho : r.outcome = r'.outcome) (hu : r.used = r'.used) :
    KeyDone p original r' s := by
  have hs : r.status = r'.status := by unfold Spec.Ffdh.KeySearchResult.status; rw [ho]
  have hr : r.retries = r'.retries := by unfold Spec.Ffdh.KeySearchResult.retries; rw [ho]
  refine ⟨h.input, h.rd, h.wr, h.r31, h.saved, h.savedR31, h.usedPtr,
    by rw [← hu]; exact h.used, by rw [← hs]; exact h.status, ?_, ?_⟩
  · rw [h.policy]; unfold KeyPublic.policy; rw [hs, hr]
  · have ho' := h.output; unfold KeyOutput at ho' ⊢; rw [← ho]; exact ho'

end VG.Proof.Ffdh.PPC64LE.KeyGeneration
