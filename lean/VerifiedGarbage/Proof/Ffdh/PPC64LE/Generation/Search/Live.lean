module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Data
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.GenerationBounds
import VerifiedGarbage.Proof.Ffdh.GenerationTape

/-! # What keeps the parameter search's loop state (PPC64LE), and where the search goes -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  controllerValue controllerValue_unchanged)

/-- The loads and stores of a controller's block, at its words. -/
structure CtlAccess (s : State) (B : Addr) : Prop where
  ld : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8
  st : ∀ d, d + 8 ≤ 128 → InRegions s.wr (B + BitVec.ofNat 64 d) 8
  ld0 : InRegions (s.rd ++ s.wr) B 8
  st0 : InRegions s.wr B 8

theorem CtlAccess.of_scr {s : State} {B : Addr} (scr : Scr s B 128) : CtlAccess s B :=
  ⟨fun _ hd => scr.ld hd, fun _ hd => scr.st hd,
    by simpa only [off, BitVec.add_zero] using scr.ld (d := 0) (by decide),
    by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)⟩

/-- The controller's words after writes of `values`. -/
theorem headers_after {p : SPub} {s t : State} (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 16) (hm : t.mem = writeController s.mem p.control values)
    {used k : Nat}
    (hv : ∀ e ∈ p.headers used k, controllerValue values e.1 (word s.mem p.control (8 * e.1)) = e.2) :
    Slots t.mem p.control (p.headers used k) := by
  intro e he
  rw [hm, writeController_word _ _ _ hb e.1 (SPub.headers_index he)]
  exact hv e he

namespace SLive

variable {p : SPub} {original s t : State} {used k : Nat}

theorem access (h : SLive p original used k s) : CtlAccess s p.control :=
  CtlAccess.of_scr (h.input.control_scr (t := s) h.wr)

theorem header (h : SLive p original used k s) {j : Nat} {v : BitVec 64}
    (hj : (j, v) ∈ p.headers used k) : word s.mem p.control (8 * j) = v :=
  h.headers (j, v) hj

theorem rand_length (h : SLive p original used k s) : p.rand.length = p.randLen := h.input.rand_length

/-- Through code that keeps `r31`, the stack pointer, the regions, the
controller's words, and writes only the output, `used`, the working space
and the stack. -/
theorem restore (h : SLive p original used k s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ preserved, t.gpr r = s.gpr r)
    (hf : Frame (SInput.callChanges original) s.mem t.mem) :
    SLive p original used k t := by
  have hc := h.input.control_frame hf
  have hf' := frame_of_callChanges original hf
  refine ⟨h.input, h.used_le, h.k_le, hr.trans h.rd, hw.trans h.wr,
    hsp.trans h.sp, (hg .r31 (by decide)).trans h.r31,
    fun r hr h31 => (hg r hr).trans (h.saved r hr h31), ?_, ?_, ?_⟩
  · exact (hc 4 (by decide)).trans h.savedR31
  · exact (h.input.random_frame hf').trans h.random
  · intro e he
    exact (hc e.1 (SPub.headers_index he)).trans (h.headers e he)

theorem keep (h : SLive p original used k s) {rs : List Reg}
    (kp : Keep rs s t) (hm : t.mem = s.mem) (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) :
    SLive p original used k t := by
  apply h.restore kp.rd kp.wr kp.sp (fun reg hr => kp.gpr reg (hregs reg hr))
  rw [hm]
  exact Frame.refl _ _

/-- Through writes of the controller's words but the saved `r31`. -/
theorem update (h : SLive p original used k s) {u k' : Nat}
    (hu : u ≤ p.randLen) (hk : k' ≤ p.attempts)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 16)
    (h4 : ∀ e ∈ values, 4 ≠ e.1)
    (hm : t.mem = writeController s.mem p.control values)
    (kp : Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] s t)
    (hh : Slots t.mem p.control (p.headers u k')) : SLive p original u k' t := by
  have hf : Frame (SInput.changes original) s.mem t.mem := by
    rw [hm]
    apply (writeController_frame s.mem p.control values hb).sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    refine ⟨inCtl original, by simp [SInput.changes, inWrites], ?_⟩
    rw [h.input.ctl_eq]
    exact fun _ hi => hi
  have hg : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => kp.gpr r (by revert r hr; decide)
  refine ⟨h.input, hu, hk, kp.rd.trans h.rd, kp.wr.trans h.wr,
    kp.sp.trans h.sp, (hg .r31 (by decide)).trans h.r31,
    fun reg hreg h31 => (hg reg hreg).trans (h.saved reg hreg h31), ?_, ?_, hh⟩
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 4) = _
    rw [writeController_word _ _ _ hb 4 (by decide), controllerValue_unchanged _ _ _ h4]
    exact h.savedR31
  · exact (h.input.random_frame hf).trans h.random

/-- A finished search's state, from a loop state with its words written. -/
theorem done (h : SLive p original used k s) {r : ParameterSearchResult}
    (hu : r.used = used)
    (hs : word s.mem p.control 112 = BitVec.ofNat 64 r.status)
    (hp : Spec.Rsa.wordsAt s.mem p.control 4 = p.policy r)
    (ho : SOutput p r s.mem) : SDone p original r s :=
  ⟨h.input, h.rd, h.wr, h.r31, h.saved, h.savedR31,
    h.header (j := 7) (by simp [SPub.headers]),
    by rw [hu]; exact h.header (j := 12) (by simp [SPub.headers]), hs, hp, ho⟩

end SLive

theorem SDone.keep {p : SPub} {original s t : State} {result : ParameterSearchResult}
    (h : SDone p original result s) {rs : List Reg} (k : Keep rs s t) (hm : t.mem = s.mem)
    (hregs : ∀ reg ∈ preserved, reg ∉ rs := by decide) : SDone p original result t := by
  refine ⟨h.input, k.rd.trans h.rd, k.wr.trans h.wr, (k.gpr _ (hregs .r31 (by decide))).trans h.r31,
    fun reg hr h31 => (k.gpr reg (hregs reg hr)).trans (h.saved reg hr h31), ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  · exact h.savedR31
  · exact h.usedPtr
  · exact h.used
  · exact h.status
  · exact h.policy
  · exact h.output

/-! ## Where the search goes from a loop state -/

theorem SPub.tail_zero (p : SPub) (used : Nat) : p.tail used 0 = .exhausted used := by
  simp only [SPub.tail, parameterSearch, ParameterSearchResult.consume, Nat.add_zero]

theorem SPub.tail_short {p : SPub} {used k : Nat} (hk : k ≠ 0) (hl : p.rand.length = p.randLen)
    (hc : parameterCandidate p.bits p.gen (p.rand.drop used) = none) :
    p.tail used k = if parameterEntropy p.bits ≤ p.randLen - used then .exhausted used
      else .entropy k (parameterRequest p.bits (p.randLen - used)) used := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simp only [SPub.tail, parameterSearch, hc, List.length_drop, hl]
  split <;> simp only [ParameterSearchResult.consume, Nat.add_zero]

theorem SPub.tail_accept {p : SPub} {used k q : Nat} {rest : List Byte} (hk : k ≠ 0)
    (hl : p.rand.length = p.randLen)
    (hc : parameterCandidate p.bits p.gen (p.rand.drop used) = some (some q, rest)) :
    p.tail used k = .accepted q (used + ((p.randLen - used) - rest.length)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simp only [SPub.tail, parameterSearch, hc, List.length_drop, hl, ParameterSearchResult.consume]

theorem SPub.tail_reject {p : SPub} {used k : Nat} {rest : List Byte} (hk : k ≠ 0)
    (hl : p.rand.length = p.randLen)
    (hc : parameterCandidate p.bits p.gen (p.rand.drop used) = some (none, rest)) :
    p.tail used k = p.tail (used + ((p.randLen - used) - rest.length)) (k - 1) := by
  have := Proof.Ffdh.Generation.search_reject (Nat.pos_of_ne_zero hk) hc
  simp only [List.length_drop, hl] at this
  exact this

/-- The octets a candidate reads are in the tape. -/
theorem candidate_used_le {p : SPub} {used : Nat} {value : Option Nat} {rest : List Byte}
    (hl : p.rand.length = p.randLen)
    (hc : parameterCandidate p.bits p.gen (p.rand.drop used) = some (value, rest)) :
    rest.length ≤ p.randLen - used := by
  obtain ⟨n, _, hr⟩ := Proof.Ffdh.Generation.candidate_suffix hc
  rw [hr]
  simp only [List.length_drop, hl]
  omega

end VG.Proof.Ffdh.PPC64LE.Generation
