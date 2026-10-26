module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import Mathlib.Util.CompileInductive

/-! Incoming ARM stack words remain readable while the controller retains
its arguments in separate packed-u64 workspace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def entryWords (sampling : VG.Proof.Ffdh.GenerationPolicy) : Nat :=
  if sampling.cachedContext then 11 else 9

theorem entryWords_min (sampling : VG.Proof.Ffdh.GenerationPolicy) : 9 ≤ entryWords sampling := by
  cases sampling <;> decide

theorem entryWords_max (sampling : VG.Proof.Ffdh.GenerationPolicy) : entryWords sampling ≤ 11 := by
  cases sampling <;> decide

theorem entryWords_bytes (sampling : VG.Proof.Ffdh.GenerationPolicy) : 4*entryWords sampling=argsBytes sampling := by
  cases sampling <;> decide

def incomingValue (p : KeyPublic sampling) (i : Nat) : BitVec 32 :=
  match i with
  | 0 => p.up
  | 1 => p.dp
  | 2 => BitVec.ofNat 32 p.dlen
  | 3 => BitVec.ofNat 32 p.len
  | 4 => p.rp
  | 5 => BitVec.ofNat 32 p.randLen
  | 6 => p.scratch
  | 7 => BitVec.ofNat 32 p.capacity
  | 9 => p.context
  | 10 => BitVec.ofNat 32 p.contextWords
  | _ => p.control

structure EntryArguments (p : KeyPublic sampling) (s : State) : Prop where
  incoming : ∀ i < entryWords sampling, IncomingWord (incomingValue p i) (24 + 4 * i) s
  separate : ∀ i < entryWords sampling, (⟨off (State.addr s.sp) (24 + 4 * i), 4⟩ : Region).Disjoint
    ⟨State.addr p.control, 128⟩

structure EntryContext (p : KeyPublic sampling) (s : State) : Prop extends EntryArguments p s where
  controller : Controller p.control s

theorem EntryArguments.after {p : KeyPublic sampling} {s t : State} {rs : List Reg}
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

theorem EntryContext.after {p : KeyPublic sampling} {s t : State} {rs : List Reg}
    (h : EntryContext p s) (rest : Rest rs s t)
    (kept : .r4 ∉ rs) (frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem) : EntryContext p t :=
  ⟨h.toEntryArguments.after rest frame,
    ⟨h.controller.space.congr rest.wr, (rest.gpr .r4 kept).trans h.controller.ptr⟩⟩

theorem entryCopy_ok (s : State) {p : KeyPublic sampling} {i j : Nat}
    (h : EntryContext p s) (incoming : i < entryWords sampling) (slot : j < 16) :
    WP isa (.block [.ldrSp .r3 (24 + 4 * i), VG.Impl.Ffdh.Arm.KeySearch.stf .r3 j]) s fun t =>
      t.mem = s.mem.writeW (off (State.addr p.control) (8 * j)) (incomingValue p i) ∧ Rest [.r3] s t := by
  refine withRest_all [.r3] ?_ (by rfl) (by rfl)
  have bound := entryWords_max sampling
  have arg := h.incoming i incoming
  have address : State.addr (s.sp + BitVec.ofNat 32 (24 + 4 * i)) =
      off (State.addr s.sp) (24 + 4 * i) := VG.Arm.addr_add (by have := arg.fits; omega)
  unfold VG.Impl.Ffdh.Arm.KeySearch.stf
  ffrun [(by omega : 24 + 4 * i < 4096), (by omega : 8 * j < 4096),
    address, arg.readable, arg.word, h.controller.addr slot, h.controller.write slot]

theorem wp_entryCopy {p : KeyPublic sampling} {s : State} {i j : Nat} {is : List Instr} {Q : State → Prop}
    (h : EntryContext p s) (incoming : i < entryWords sampling) (slot : j < 16)
    (next : ∀ t, EntryContext p t →
      t.mem = s.mem.writeW (off (State.addr p.control) (8 * j)) (incomingValue p i) →
      Rest [.r3] s t → WP isa (.block is) t Q) :
    WP isa (.block (.ldrSp .r3 (24 + 4 * i) :: VG.Impl.Ffdh.Arm.KeySearch.stf .r3 j :: is)) s Q := by
  change WP isa (.block ([.ldrSp .r3 (24 + 4 * i), VG.Impl.Ffdh.Arm.KeySearch.stf .r3 j] ++ is)) s Q
  rw [WP.block_append_iff]
  refine WP.mono (entryCopy_ok s h incoming slot) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (r := ⟨State.addr p.control, 128⟩) (by simp) (incomingValue p i)
      (Offset.contains_base _ (by omega) (by omega))
  exact next t (h.after rest (by simp) frame) mem rest

end VG.Proof.Ffdh.Arm.KeySearch
