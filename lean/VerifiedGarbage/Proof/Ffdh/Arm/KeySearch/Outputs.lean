module

import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ffdh.Arm.ZeroBuffer
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Live
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Packed
import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts

/-! ### `Ffdh.Arm.KeySearch.CallPreserves`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeySearch.Memory`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeySearch.ConstantMemory`, which this module and modules that import it used -/

section

/-! Constant-table reads survive the controller's disjoint writes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeyConstants
open VG VG.Arm VG.Impl.Ffdh.Arm.VettedGroups

theorem tablePtr_of_syms {sampling : GenerationPolicy} {s t : State}
    (syms : t.syms = s.syms) : tablePtr sampling t = tablePtr sampling s := by
  cases sampling with
  | full | cached => rfl
  | vetted => exact congrFun syms tableSym

 theorem held_of_consts {sampling : GenerationPolicy} {stack : Nat} {s : State}
    (hc : ConstsOk (consts sampling) stack s) : held sampling (tablePtr sampling s) s.mem := by
  intro c member i hi
  have original := hc.2.1 c member i hi
  cases sampling with
  | full | cached => exact False.elim (List.not_mem_nil member)
  | vetted =>
    simp only [consts, tableConsts, List.mem_singleton] at member
    subst c
    exact original

private theorem singleton_held_after_frame {name : String} {words : List (BitVec 64)}
    {ptr : BitVec 32} {m m' : Mem} {changes : List Region}
    (size : words.length < 2 ^ 60)
    (h : Abi.constsHeld m (fun _ => State.addr ptr) [(name, words)])
    (frame : Frame changes m m')
    (safe : ∀ table ∈ [(⟨State.addr ptr, 8 * words.length⟩ : Region)], ∀ r ∈ changes, table.Disjoint r) :
    Abi.constsHeld m' (fun _ => State.addr ptr) [(name, words)] := by
  intro c member i hi
  simp only [List.mem_singleton] at member
  subst c
  dsimp only [Prod.snd] at hi
  rw [frame.readW (r := ⟨State.addr ptr, 8 * words.length⟩)
    (Offset.contains_base _ (by omega_using [hi]) (by omega_using [size, hi]))
    (fun r hr => safe _ List.mem_cons_self r hr) (by decide)]
  exact h _ List.mem_cons_self i hi

 theorem held_after_frame {sampling : GenerationPolicy} {ptr : BitVec 32}
    {m m' : Mem} {changes : List Region} (h : held sampling ptr m)
    (frame : Frame changes m m')
    (safe : ∀ table ∈ regions sampling ptr, ∀ r ∈ changes, table.Disjoint r) :
    held sampling ptr m' := by
  cases sampling with
  | full | cached =>
    intro c member
    exact False.elim (List.not_mem_nil member)
  | vetted =>
    exact singleton_held_after_frame (name := tableSym) (words := tableWords)
      (by rw [VG.Proof.Ffdh.Arm.VettedGroups.tableWords_length]; decide) h frame safe

end VG.Proof.Ffdh.Arm.KeyConstants

end

end

/-! Controller writes preserve the entropy tape, domain and saved AAPCS registers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem KeyInput.domain_control {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    (⟨State.addr p.dp, p.dlen⟩ : Region).Disjoint ⟨State.addr p.control, 128⟩ := by
  rw [← h.2.1]
  exact (h.layout.separate (inControl s) (by simp [writes]) (inDomain s) (by simp [reads])).symm

theorem KeyInput.random_control {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    (⟨State.addr p.rp, p.randLen⟩ : Region).Disjoint ⟨State.addr p.control, 128⟩ := by
  rw [← h.2.1]
  exact (h.layout.separate (inControl s) (by simp [writes]) (inRand s) (by simp [reads])).symm

theorem KeyInput.saved_control {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    (⟨State.addr (p.sp - BitVec.ofNat 32 24), 24⟩ : Region).Disjoint ⟨State.addr p.control, 128⟩ := by
  have fit := h.bounds.stackFits
  rw [← h.2.1] at fit ⊢
  change (stackUse sampling) ≤ s.sp.toNat at fit
  have sep := h.layout.stack (inControl s) (List.mem_append_left _ (by simp [writes]))
  rw [← FrameStack.addr_sub' fit] at sep
  exact sep.sub_left (FrameStack.belowA_sub (by cases sampling <;> decide : 24 ≤ (stackUse sampling)) fit)

theorem bytesAt_frame {r : Region} {m m' : Mem} {changes : List Region}
    (frame : Frame changes m m') (sep : ∀ w ∈ changes, r.Disjoint w)
    (fit : r.len ≤ 2 ^ 64) : Spec.Rsa.bytesAt m' r.base r.len = Spec.Rsa.bytesAt m r.base r.len := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro j hj
  exact frame.bytes sep fit (List.mem_range.mp hj)

theorem KeyLive.after_control {p : KeyPublic sampling} {original s t : State} {used keys scalars : Nat}
    {newUsed newKeys newScalars : Nat} {rs : List Reg}
    (h : KeyLive p original used keys scalars s) (rest : Rest rs s t) (syms : t.syms = s.syms)
    (kept : ∀ r ∈ keptRegisters, r ∉ rs)
    (frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem)
    (usedBound : newUsed ≤ p.randLen) (keysBound : newKeys ≤ 128) (scalarsBound : newScalars ≤ 128)
    (headers : Slots t.mem p.control (p.headers newUsed newKeys newScalars))
    (high : ∀ j < 3, t.mem.readW (off (State.addr p.control) (8 * j + 4)) 32 = 0)
    (cacheSlots : CachedSlots p t.mem) :
    KeyLive p original newUsed newKeys newScalars t := by
  refine ⟨h.input, usedBound, keysBound, scalarsBound, rest.rd.trans h.rd, rest.wr.trans h.wr,
    rest.sp.trans h.sp, (rest.gpr .r4 (kept .r4 (by decide))).trans h.pointer,
    fun r hr => (rest.gpr r (kept r (List.mem_cons_of_mem _ hr))).trans (h.kept r hr),
    ?_, ?_, ?_, headers, high, ?_, ?_, ?_, cacheSlots⟩
  · apply h.saved.frame (lo := 0) (hi := 24) (by decide) frame
    simpa using h.input.saved_control
  · exact (bytesAt_frame (r := ⟨State.addr p.rp, p.randLen⟩) frame (by simpa using h.input.random_control)
      (by change p.randLen ≤ 2 ^ 64; have := h.input.bounds.randomFits; omega_using [this])).trans h.random
  · exact (bytesAt_frame (r := ⟨State.addr p.dp, p.dlen⟩) frame (by simpa using h.input.domain_control)
      (by change p.dlen ≤ 2 ^ 64; have := h.input.bounds.domainFit; omega_using [this])).trans h.domain
  · cases sampling <;> simpa only [KeyConstants.tablePtr, syms] using h.tablePtr
  · exact KeyConstants.held_after_frame h.held frame (by
      intro table ht r hr
      have er := List.mem_singleton.mp hr
      subst r
      exact h.input.constants_control table ht)

  · apply h.cachedHeld.after_frame frame
    · intro cached
      have fit := h.input.context_fit cached
      omega_using [fit]
    · intro cached r member
      have same := List.mem_singleton.mp member
      subst r
      exact h.input.context_control cached

theorem KeyLive.update {p : KeyPublic sampling} {original s t : State} {used keys scalars : Nat}
    {newUsed newKeys newScalars : Nat} {rs : List Reg}
    (h : KeyLive p original used keys scalars s) (rest : Rest rs s t) (syms : t.syms = s.syms)
    (kept : ∀ r ∈ keptRegisters, r ∉ rs)
    (values : List (Nat × BitVec 32)) (bounds : ∀ e ∈ values, e.1 < 16)
    (absent4 : ∀ e ∈ values, 4 ≠ e.1)
    (mem : t.mem = writeLow s.mem p.control values)
    (usedBound : newUsed ≤ p.randLen) (keysBound : newKeys ≤ 128) (scalarsBound : newScalars ≤ 128)
    (headers : Slots t.mem p.control (p.headers newUsed newKeys newScalars)) :
    KeyLive p original newUsed newKeys newScalars t := by
  apply h.after_control rest syms kept (by rw [mem]; exact writeLow_frame _ _ _ bounds)
    usedBound keysBound scalarsBound headers
  · intro j hj
    rw [mem, highWord_writeLow _ _ _ bounds j (by omega_using [hj])]
    exact h.high j hj
  · intro cached
    obtain ⟨ptr, words⟩ := h.cachedSlots cached
    constructor
    · change lowWord t.mem p.control 4 = p.context
      rw [mem, lowWord_writeLow _ _ _ bounds 4 (by decide), lowValue_unchanged _ _ _ absent4]
      exact ptr
    · change t.mem.readW (off (State.addr p.control) (8 * 4 + 4)) 32 = _
      rw [mem, highWord_writeLow _ _ _ bounds 4 (by decide)]
      exact words

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! A nested key-generation attempt changes its outputs, workspace and its
own stack, preserving the retry sampling and saved controller frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont

namespace KeyInput
variable {p : KeyPublic sampling} {s : State}

theorem call_control (h : KeyInput p s) : ∀ r ∈ callChanges p, (rControl p).Disjoint r := by
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  have sep := h.output_regions_disjoint
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact sep.2.2.2.1
  · exact sep.2.2.2.2.1
  · exact sep.2.2.2.2.2
  · apply Region.Disjoint.symm
    apply (h.stack_separate (r := rControl p) (by rw [h.write_regions]; simp)).sub_left
    exact arguments_sub h.bounds.stackFits
  · apply Region.Disjoint.symm
    apply (h.stack_separate (r := rControl p) (by rw [h.write_regions]; simp)).sub_left
    exact callStack_sub h.bounds.stackFits

theorem call_read (h : KeyInput p s) {r : Region} (read : r ∈ s.rd) :
    ∀ w ∈ callChanges p, r.Disjoint w := by
  intro w hw
  have sep (q : Region) (hq : q ∈ s.wr) : r.Disjoint q := by
    apply Region.Disjoint.symm
    apply h.layout.separate q (by rw [← h.layout.wr]; exact hq) r
    rw [← h.layout.rd]; exact read
  have saved := h.stack_separate (List.mem_append_right s.wr read)
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact sep _ (by rw [h.write_regions]; simp)
  · exact sep _ (by rw [h.write_regions]; simp)
  · exact sep _ (by rw [h.write_regions]; simp)
  · exact (saved.sub_left (arguments_sub h.bounds.stackFits)).symm
  · exact (saved.sub_left (callStack_sub h.bounds.stackFits)).symm

theorem call_saved (h : KeyInput p s) : ∀ r ∈ callChanges p, (rSaved p).Disjoint r := by
  intro r hr
  have below : (rSaved p).Sub (FrameStack.belowA p.sp (stackUse sampling)) :=
    FrameStack.belowA_sub (by cases sampling <;> decide : 24 ≤ (stackUse sampling)) h.bounds.stackFits
  have sep (q : Region) (hq : q ∈ s.wr) : (rSaved p).Disjoint q :=
    (h.stack_separate (List.mem_append_left _ hq)).sub_left below
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact sep _ (by rw [h.write_regions]; simp)
  · exact sep _ (by rw [h.write_regions]; simp)
  · exact sep _ (by rw [h.write_regions]; simp)
  · exact saved_arguments_separate h.bounds.stackFits
  · exact saved_callStack_separate h.bounds.stackFits

theorem call_domain_frame (h : KeyInput p s) {m m' : Mem} (frame : Frame (callChanges p) m m') :
    Spec.Rsa.bytesAt m' (State.addr p.dp) p.dlen = Spec.Rsa.bytesAt m (State.addr p.dp) p.dlen :=
  bytesAt_frame (r := rDomain p) frame (h.call_read (by rw [h.read_regions]; simp))
    (by change p.dlen ≤ 2 ^ 64; have := h.bounds.domainFit; omega_using [this])

theorem call_random_frame (h : KeyInput p s) {m m' : Mem} (frame : Frame (callChanges p) m m') :
    Spec.Rsa.bytesAt m' (State.addr p.rp) p.randLen = Spec.Rsa.bytesAt m (State.addr p.rp) p.randLen :=
  bytesAt_frame (r := rRandom p) frame (h.call_read (by rw [h.read_regions]; simp))
    (by change p.randLen ≤ 2 ^ 64; have := h.bounds.randomFits; omega_using [this])

end KeyInput

theorem KeyLive.restore {p : KeyPublic sampling} {original s t : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp)
    (kept : ∀ r ∈ keptRegisters, t.gpr r = s.gpr r)
    (syms : t.syms = s.syms)
    (frame : Frame (callChanges p) s.mem t.mem) : KeyLive p original used keys scalars t := by
  refine ⟨h.input, h.used_le, h.keys_le, h.scalars_le, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
    (kept .r4 (by decide)).trans h.pointer,
    fun r hr => (kept r (List.mem_cons_of_mem _ hr)).trans (h.kept r hr),
    ?_, (h.input.call_random_frame frame).trans h.random,
    (h.input.call_domain_frame frame).trans h.domain, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply h.saved.frame (lo := 0) (hi := 24) (by decide) frame
    simpa using h.input.call_saved
  · intro e he
    have index : e.1 < 16 := by
      simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals dsimp only; decide
    exact (frame.readW (r := rControl p) (Offset.contains_base _ (by omega_using [index]) (by omega_using [index]))
      h.input.call_control (by decide)).trans (h.headers e he)
  · intro j hj
    exact (frame.readW (r := rControl p) (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
      h.input.call_control (by decide)).trans (h.high j hj)
  · exact (KeyConstants.tablePtr_of_syms syms).trans h.tablePtr
  · exact KeyConstants.held_after_frame h.held frame (fun table member r hr =>
      h.input.call_read (h.input.constants_read member) r hr)

  · apply h.cachedHeld.after_frame frame
    · intro active
      have := h.input.context_fit active
      omega_using [this]
    · intro active
      exact h.input.call_read (by rw [h.input.read_regions]; simp [contextRegions, active])
  · intro active
    obtain ⟨ptr, len⟩ := h.cachedSlots active
    constructor
    · exact (frame.readW (r := rControl p) (Offset.contains_base _ (by decide : 32 + 4 ≤ 128) (by decide))
        h.input.call_control (by decide)).trans ptr
    · exact (frame.readW (r := rControl p) (Offset.contains_base _ (by decide : 36 + 4 ≤ 128) (by decide))
        h.input.call_control (by decide)).trans len

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.ZeroOutput`, which this module and modules that import it used -/

section

/-! The native retry controller clears rejected or incomplete outputs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem zeroOutputArgs_ok (s : State) {base dst : BitVec 32} {j n : Nat}
    (h : Controller base s) (slot : j < 16)
    (pointer : lowWord s.mem base j = dst) (length : lowWord s.mem base 2 = BitVec.ofNat 32 n) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 j,
      VG.Impl.Ffdh.Arm.KeySearch.ldf .lr 2, .mov .r2 (.imm 0)]) s fun t =>
      (t.gpr .r0 = dst ∧ t.gpr .lr = BitVec.ofNat 32 n ∧ t.gpr .r2 = 0 ∧ t.mem = s.mem) ∧
      Rest [.r0, .r2, .lr] s t := by
  refine withRest_all [.r0, .r2, .lr] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.KeySearch.ldf lowWord at *
  ffrun [(by omega_using [slot] : 8 * j < 4096), h.addr slot, h.read slot,
    h.addr (by decide : 2 < 16), h.read (by decide : 2 < 16), pointer, length]

theorem zeroOutput_ok (s : State) {base dst : BitVec 32} {j n : Nat}
    (h : Controller base s) (slot : j < 16) (positive : 0 < n) (fits : n < 2 ^ 32)
    (pointer : lowWord s.mem base j = dst) (length : lowWord s.mem base 2 = BitVec.ofNat 32 n)
    (output : VG.Proof.Ffdh.Arm.OutputBuffer dst n s) :
    WP isa (VG.Impl.Ffdh.Arm.KeySearch.zeroOutput j) s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = List.replicate n 0 ∧
      Frame [⟨State.addr dst, n⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  rw [VG.Impl.Ffdh.Arm.KeySearch.zeroOutput, WP.seq_iff]
  refine WP.mono (zeroOutputArgs_ok s h slot pointer length) ?_
  rintro u ⟨⟨ptr, count, zero, mem⟩, restU⟩
  refine WP.mono (zeroBuffer_ok false u positive fits output.fits
    (by rw [restU.wr]; exact output.writable) zero (src := u.gpr .r1) rfl ptr count) ?_
  rintro t ⟨bytes, _, _, frame, rest⟩
  exact ⟨bytes, by rw [mem] at frame; exact frame,
    (restU.mono (by simp)).trans (rest.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! Clearing both outputs preserves the controller and all loop invariants. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem KeyLive.x_buffer {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) : OutputBuffer p.xp p.len s := by
  refine ⟨h.input.bounds.xFit, ⟨rX p, ?_, Region.contains_self _ _⟩⟩
  rw [h.wr, h.input.write_regions]
  simp

theorem KeyLive.y_buffer {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) : OutputBuffer p.yp p.len s := by
  refine ⟨h.input.bounds.yFit, ⟨rY p, ?_, Region.contains_self _ _⟩⟩
  rw [h.wr, h.input.write_regions]
  simp

theorem KeyInput.outputs_control {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    ∀ r ∈ [rX p, rY p], (rControl p).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.output_regions_disjoint.2.2.2.1
  · exact h.output_regions_disjoint.2.2.2.2.1

theorem KeyLive.zero_outputs {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa VG.Impl.Ffdh.Arm.KeySearch.zeroOutputs s fun t =>
      KeyLive p original used keys scalars t ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.xp) p.len = List.replicate p.len 0 ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.yp) p.len = List.replicate p.len 0 ∧
      Frame [rX p, rY p] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  have positive : 0 < p.len := by have := h.input.bounds.minLength; omega_using [this]
  have fits : p.len < 2 ^ 32 := by have := h.input.bounds.maxLength; omega_using [this]
  rw [VG.Impl.Ffdh.Arm.KeySearch.zeroOutputs, WP.seq_iff]
  refine WP.mono_syms (zeroOutput_ok s h.controller (by decide : 5 < 16) positive fits
    (h.header (by simp [KeyPublic.headers])) (h.header (by simp [KeyPublic.headers])) h.x_buffer) ?_
  rintro u ⟨xzero, xframe, xrest⟩ xsyms
  have live : KeyLive p original used keys scalars u :=
    h.restore xrest.rd xrest.wr xrest.sp (fun r hr => xrest.gpr r (by revert r hr; decide)) xsyms
      (xframe.mono (by simp [callChanges]))
  refine WP.mono_syms (zeroOutput_ok u live.controller (by decide : 6 < 16) positive fits
    (live.header (by simp [KeyPublic.headers])) (live.header (by simp [KeyPublic.headers])) live.y_buffer) ?_
  rintro t ⟨yzero, yframe, yrest⟩ ysyms
  have finished : KeyLive p original used keys scalars t :=
    live.restore yrest.rd yrest.wr yrest.sp (fun r hr => yrest.gpr r (by revert r hr; decide)) ysyms
      (yframe.mono (by simp [callChanges]))
  refine ⟨finished, ?_, yzero,
    (xframe.mono (by simp)).trans (yframe.mono (by simp)), xrest.trans yrest⟩
  exact (bytesAt_frame (r := rX p) yframe
    (by simpa using h.input.output_regions_disjoint.1)
    (by change p.len ≤ 2 ^ 64; have := h.input.bounds.maxLength; omega_using [fits])).trans xzero

theorem KeyOutput.control_frame {p : KeyPublic sampling} {original : State} {result : Spec.Ffdh.KeySearchResult}
    {m m' : Mem} (h : KeyInput p original) (before : KeyOutput p result m)
    (frame : Frame [rControl p] m m') : KeyOutput p result m' := by
  have xeq := bytesAt_frame (r := rX p) frame
    (by simpa using h.output_regions_disjoint.2.2.2.1.symm)
    (by change p.len ≤ 2 ^ 64; have := h.bounds.maxLength; omega_using [this])
  have yeq := bytesAt_frame (r := rY p) frame
    (by simpa using h.output_regions_disjoint.2.2.2.2.1.symm)
    (by change p.len ≤ 2 ^ 64; have := h.bounds.maxLength; omega_using [this])
  cases outcome : result.outcome <;> simp only [KeyOutput, outcome] at before ⊢ <;>
    exact ⟨xeq.trans before.1, yeq.trans before.2⟩

theorem KeyLive.done {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    {result : Spec.Ffdh.KeySearchResult} (h : KeyLive p original used keys scalars s)
    (count : result.used = used) (status : lowWord s.mem p.control 14 = BitVec.ofNat 32 result.status)
    (policy : Spec.Rsa.wordsAt s.mem (State.addr p.control) 4 =
      [BitVec.ofNat 64 result.retries.keys, BitVec.ofNat 64 result.retries.scalars,
        BitVec.ofNat 64 p.len, BitVec.ofNat 64 (if result.status = 0 then p.len else 0)])
    (output : KeyOutput p result s.mem) : KeyDone p original result s :=
  ⟨h.input, by rw [count]; exact h.used_le, h.rd, h.wr, h.sp, h.pointer, h.kept, h.saved,
    h.header (by simp [KeyPublic.headers]), by rw [count]; exact h.header (by simp [KeyPublic.headers]),
    status, policy, output⟩

end VG.Proof.Ffdh.Arm.KeySearch
