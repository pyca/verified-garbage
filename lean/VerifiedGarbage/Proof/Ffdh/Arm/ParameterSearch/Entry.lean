module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.EntryBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Incoming
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Params

/-! Exact argument snapshot made before entering the key-search loop. -/

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
  refine withRest [.r3, .r4] ?_ (by
    intro r hr instr hi
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterSearch.entry : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked instr hi
    cases hc : clobbers instr r <;> simp_all) (by rfl)
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
    omega
  rw [lowWord_writeLow _ _ _ (entryValues_bound p) j bound]
  simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [entryValues, lowValue, searchValues, width, entropy]

end VG.Proof.Ffdh.Arm.ParameterSearch
