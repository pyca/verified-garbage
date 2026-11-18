module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Live
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Packed
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts

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
