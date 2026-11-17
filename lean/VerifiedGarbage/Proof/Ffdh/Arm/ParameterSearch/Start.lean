module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Params
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Memory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.FieldMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Packed
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
public import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord

/-! ### `Ffdh.Arm.ParameterSearch.Incoming`, which this module and modules that import it used -/

section

/-! Incoming ARM stack words remain readable while the controller retains
its arguments in separate packed-u64 workspace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm.KeySearch (Controller)

def incomingValue (p : SearchParams) (i : Nat) : BitVec 32 :=
  match i with
  | 0 => BitVec.ofNat 32 p.c.generator
  | 1 => p.c.tape
  | 2 => BitVec.ofNat 32 p.c.bytes.length
  | 3 => p.c.base
  | 4 => BitVec.ofNat 32 p.c.capacity
  | _ => p.control

structure EntryArguments (p : SearchParams) (s : State) : Prop where
  incoming : ∀ i < 6, IncomingWord (incomingValue p i) (24 + 4 * i) s
  separate : ∀ i < 6, (⟨off (State.addr s.sp) (24 + 4 * i), 4⟩ : Region).Disjoint
    ⟨State.addr p.control, 128⟩

structure EntryContext (p : SearchParams) (s : State) : Prop extends EntryArguments p s where
  controller : Controller p.control s

theorem EntryArguments.after {p : SearchParams} {s t : State} {rs : List Reg}
    (h : EntryArguments p s) (rest : Rest rs s t)
    (frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem) : EntryArguments p t := by
  refine ⟨?_, ?_⟩
  · intro i hi
    have old := h.incoming i hi
    refine ⟨by rw [rest.sp]; exact old.fits,
      by rw [rest.rd, rest.wr, rest.sp]; exact old.readable, ?_⟩
    rw [rest.sp]
    exact (frame.readW (r := ⟨off (State.addr s.sp) (24 + 4 * i), 4⟩) (Region.contains_self _ _)
      (by simpa using h.separate i hi) (by decide)).trans old.word
  · intro i hi
    rw [rest.sp]
    exact h.separate i hi

theorem EntryContext.after {p : SearchParams} {s t : State} {rs : List Reg}
    (h : EntryContext p s) (rest : Rest rs s t)
    (kept : .r4 ∉ rs) (frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem) : EntryContext p t :=
  ⟨h.toEntryArguments.after rest frame,
    ⟨h.controller.space.congr rest.wr, (rest.gpr .r4 kept).trans h.controller.ptr⟩⟩

theorem entryCopy_ok (s : State) {p : SearchParams} {i j : Nat}
    (h : EntryContext p s) (incoming : i < 6) (slot : j < 16) :
    WP isa (.block [.ldrSp .r3 (24 + 4 * i), VG.Impl.Ffdh.Arm.ParameterSearch.stf .r3 j]) s fun t =>
      t.mem = s.mem.writeW (off (State.addr p.control) (8 * j)) (incomingValue p i) ∧ Rest [.r3] s t := by
  refine withRest_all [.r3] ?_ (by rfl) (by rfl)
  have arg := h.incoming i incoming
  have address : State.addr (s.sp + BitVec.ofNat 32 (24 + 4 * i)) =
      off (State.addr s.sp) (24 + 4 * i) := VG.Arm.addr_add (by have := arg.fits; omega_using [this])
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.stf
  ffrun [(by omega_using [incoming] : 24 + 4 * i < 4096), (by omega_using [slot] : 8 * j < 4096),
    address, arg.readable, arg.word, h.controller.addr slot, h.controller.write slot]

theorem wp_entryCopy {p : SearchParams} {s : State} {i j : Nat} {is : List Instr} {Q : State → Prop}
    (h : EntryContext p s) (incoming : i < 6) (slot : j < 16)
    (next : ∀ t, EntryContext p t →
      t.mem = s.mem.writeW (off (State.addr p.control) (8 * j)) (incomingValue p i) →
      Rest [.r3] s t → WP isa (.block is) t Q) :
    WP isa (.block (.ldrSp .r3 (24 + 4 * i) :: VG.Impl.Ffdh.Arm.ParameterSearch.stf .r3 j :: is)) s Q := by
  change WP isa (.block ([.ldrSp .r3 (24 + 4 * i), VG.Impl.Ffdh.Arm.ParameterSearch.stf .r3 j] ++ is)) s Q
  rw [WP.block_append_iff]
  refine WP.mono (entryCopy_ok s h incoming slot) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (r := ⟨State.addr p.control, 128⟩) (by simp) (incomingValue p i)
      (Offset.contains_base _ (by omega_using [slot]) (by omega_using [slot]))
  exact next t (h.after rest (by simp) frame) mem rest

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! ### `Ffdh.Arm.ParameterSearch.Entry`, which only this module used -/

section

/-! Exact argument snapshot made before entering the key-search loop. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/EntryBlocks.lean`, which only this module imported.
section

/-! Save the register arguments before reading and retaining the incoming stack arguments. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.Ffdh.Arm.KeySearch (writeLow)
open VG.Proof.X25519.Arm (Rest)

theorem entryHead_ok (s : State) {p : SearchParams} (h : EntryArguments p s)
    (space : Workspace s p.control 128) (out : s.gpr .r0 = p.c.out) (used : s.gpr .r2 = p.c.usedPtr)
    (bits : s.gpr .r3 = BitVec.ofNat 32 p.c.bits) :
    WP isa (.block [.ldrSp .r4 44, VG.Impl.Ffdh.Arm.ParameterSearch.stf .r0 5,
      VG.Impl.Ffdh.Arm.ParameterSearch.stf .r2 6, VG.Impl.Ffdh.Arm.ParameterSearch.stf .r3 7]) s fun t =>
      (t.gpr .r4 = p.control ∧ t.mem = writeLow s.mem p.control
        [(5, p.c.out), (6, p.c.usedPtr), (7, BitVec.ofNat 32 p.c.bits)]) ∧ Rest [.r4] s t := by
  refine withRest_all [.r4] ?_ (by rfl) (by rfl)
  have arg := h.incoming 5 (by decide)
  have addr44 : State.addr (s.sp + 44#32) = off (State.addr s.sp) 44 :=
    VG.Arm.addr_add (by have := arg.fits; omega)
  have addr40 : State.addr (p.control + 40#32) = off (State.addr p.control) 40 :=
    VG.Arm.addr_add (by have := space.nowrap; omega)
  have addr48 : State.addr (p.control + 48#32) = off (State.addr p.control) 48 :=
    VG.Arm.addr_add (by have := space.nowrap; omega)
  have addr56 : State.addr (p.control + 56#32) = off (State.addr p.control) 56 :=
    VG.Arm.addr_add (by have := space.nowrap; omega)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.stf writeLow
  simp only [List.foldl_cons, List.foldl_nil]
  ffrun [addr44, arg.readable, arg.word, incomingValue, addr40, addr48, addr56,
    space.write (off := 40) (by decide), space.write (off := 48) (by decide),
    space.write (off := 56) (by decide), out, used, bits]

theorem entryZero_ok (s : State) {p : SearchParams} (h : EntryContext p s) :
    WP isa (.block [.mov .r3 (.imm 0), VG.Impl.Ffdh.Arm.ParameterSearch.stf .r3 4]) s fun t =>
      t.mem = s.mem.writeW (off (State.addr p.control) 32) (0#32) ∧ Rest [.r3] s t := by
  refine withRest_all [.r3] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.stf
  ffrun [h.controller.addr (by decide : 4 < 16), h.controller.write (by decide : 4 < 16)]
  rfl

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm.KeySearch (lowWord writeLow writeLow_frame lowWord_writeLow lowValue)

def entryValues (p : SearchParams) : List (Nat × BitVec 32) :=
  [(5, p.c.out), (6, p.c.usedPtr), (7, BitVec.ofNat 32 p.c.bits),
    (8, BitVec.ofNat 32 p.c.generator), (9, p.c.tape), (10, BitVec.ofNat 32 p.c.bytes.length),
    (11, p.c.base), (12, BitVec.ofNat 32 p.c.capacity), (4, 0)]

theorem entryValues_bound (p : SearchParams) : ∀ e ∈ entryValues p, e.1 < 16 := by
  simp only [entryValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem entry_ok (s : State) {p : SearchParams} (h : EntryArguments p s)
    (space : Workspace s p.control 128) (out : s.gpr .r0 = p.c.out) (used : s.gpr .r2 = p.c.usedPtr)
    (bits : s.gpr .r3 = BitVec.ofNat 32 p.c.bits) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.entry) s fun t =>
      (EntryContext p t ∧ t.mem = writeLow s.mem p.control (entryValues p)) ∧ Rest [.r3, .r4] s t := by
  refine withRest_all [.r3, .r4] ?_ (by rfl) (by rfl)
  change WP isa (.block ([.ldrSp .r4 44, VG.Impl.Ffdh.Arm.ParameterSearch.stf .r0 5,
    VG.Impl.Ffdh.Arm.ParameterSearch.stf .r2 6, VG.Impl.Ffdh.Arm.ParameterSearch.stf .r3 7] ++ _)) s _
  rw [WP.block_append_iff]
  refine WP.mono (entryHead_ok s h space out used bits) ?_
  rintro u ⟨⟨pointer, mem⟩, rest⟩
  have frame : Frame [⟨State.addr p.control, 128⟩] s.mem u.mem := by
    rw [mem]; exact writeLow_frame _ _ _ (by simp)
  have context : EntryContext p u :=
    ⟨h.after rest frame, ⟨space.congr rest.wr, pointer⟩⟩
  refine wp_entryCopy (i := 0) (j := 8) context (by decide) (by decide) fun s1 c1 m1 _ => ?_
  refine wp_entryCopy (i := 1) (j := 9) c1 (by decide) (by decide) fun s2 c2 m2 _ => ?_
  refine wp_entryCopy (i := 2) (j := 10) c2 (by decide) (by decide) fun s3 c3 m3 _ => ?_
  refine wp_entryCopy (i := 3) (j := 11) c3 (by decide) (by decide) fun s4 c4 m4 _ => ?_
  refine wp_entryCopy (i := 4) (j := 12) c4 (by decide) (by decide) fun s5 c5 m5 _ => ?_
  refine WP.mono (entryZero_ok s5 c5) ?_
  rintro t ⟨m6, r6⟩
  have frame6 : Frame [⟨State.addr p.control, 128⟩] s5.mem t.mem := by
    rw [m6]
    exact (Frame.refl _ _).writeW (r := ⟨State.addr p.control, 128⟩) (by simp) (0#32)
      (Offset.contains_base _ (by decide : 32 + 4 ≤ 128) (by decide))
  refine ⟨c5.after r6 (by simp) frame6, ?_⟩
  rw [m6, m5, m4, m3, m2, m1, mem]
  rfl

theorem entry_fields (p : SearchParams) (m : Mem)
    (width : lowWord m p.control 1 = BitVec.ofNat 32 p.c.length)
    (entropy : lowWord m p.control 2 = BitVec.ofNat 32 (Spec.Ffdh.parameterEntropy p.c.bits)) :
    ∀ j ∈ searchSlots, lowWord (writeLow m p.control (entryValues p)) p.control j = searchValues p 0 j := by
  intro j member
  have bound : j < 16 := by
    simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at member
    omega_using [member]
  rw [lowWord_writeLow _ _ _ (entryValues_bound p) j bound]
  simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [entryValues, lowValue, searchValues, width, entropy]

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end


/-! Argument capture establishes the native search invariant from the persistent public policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (lowWord)

structure SearchStart (p : SearchParams) (s : State) : Prop where
  storage : SearchBuffers p (s.setReg .r4 p.control)
  incoming : EntryArguments p s
  out : s.gpr .r0 = p.c.out
  used : s.gpr .r2 = p.c.usedPtr
  bits : s.gpr .r3 = BitVec.ofNat 32 p.c.bits
  counter : s.mem.readW (State.addr p.control) 64 = BitVec.ofNat 64 p.attempts
  width : s.mem.readW (off (State.addr p.control) 8) 64 = BitVec.ofNat 64 p.c.length
  entropy : s.mem.readW (off (State.addr p.control) 16) 64 = BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)

theorem SearchStart.entry {p : SearchParams} {s : State} (h : SearchStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.entry) s fun t =>
      SearchLive p 0 p.attempts t ∧ Rest [.r3, .r4] s t := by
  refine WP.mono (entry_ok s h.incoming (h.storage.controller.space.congr rfl) h.out h.used h.bits) ?_
  rintro t ⟨⟨context, mem⟩, rest⟩
  have frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem := by
    rw [mem]; exact VG.Proof.Ffdh.Arm.KeySearch.writeLow_frame _ _ _ (entryValues_bound p)
  have fakeRest : Rest [.r3] (s.setReg .r4 p.control) t := by
    refine ⟨?_, rest.rd, rest.wr, rest.sp⟩
    intro r hr
    by_cases four : r = .r4
    · subst r
      simpa only [State.setReg, ite_true] using context.controller.ptr
    · rw [rest.gpr r (by simp_all), State.setReg]
      simp only [four, ite_false]
  have buffers : SearchBuffers p t := h.storage.after_frame (by decide)
    (frame.mono (by simp [searchRegions])) fakeRest
  have widthLow := packedLow s.mem p.control 1 p.c.length
    (by have := p.width_bounds; omega_using [this]) h.width
  have entropyLow := packedLow s.mem p.control 2 (Spec.Ffdh.parameterEntropy p.c.bits)
    (by have := p.entropy_bound; omega_using [this]) h.entropy
  refine ⟨⟨buffers, Nat.zero_le _, Nat.le_refl _, ?_, ?_, ?_, ?_⟩, rest⟩
  · have word := fields_word s.mem p.control (entryValues p) (entryValues_bound p)
      (j := 0) (by decide) (by simp [entryValues])
    have address : off (State.addr p.control) 0 = State.addr p.control := by simp [off]
    rw [show 8 * 0 = 0 from rfl, address] at word
    rw [mem, word]
    exact h.counter
  · rw [mem, fields_word _ _ _ (entryValues_bound p) (j := 1) (by decide) (by simp [entryValues])]
    exact h.width
  · rw [mem, fields_word _ _ _ (entryValues_bound p) (j := 2) (by decide) (by simp [entryValues])]
    exact h.entropy
  · rw [mem]
    exact entry_fields p s.mem widthLow entropyLow

end VG.Proof.Ffdh.Arm.ParameterSearch
