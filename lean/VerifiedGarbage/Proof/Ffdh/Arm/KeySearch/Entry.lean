module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.EntryBlocks
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Fields
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Incoming
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.Block

/-! Exact argument snapshot made before entering the key-search loop. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

def entryValues (p : KeyPublic sampling) : List (Nat × BitVec 32) :=
  [(5, p.xp), (6, p.yp), (15, p.up), (7, p.dp), (8, BitVec.ofNat 32 p.dlen),
    (9, p.rp), (10, BitVec.ofNat 32 p.randLen), (12, p.scratch),
    (13, BitVec.ofNat 32 p.capacity), (11, 0)]

theorem entryValues_bound (p : KeyPublic sampling) : ∀ e ∈ entryValues p, e.1 < 16 := by
  simp only [entryValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem entry_base_ok (s : State) {p : KeyPublic sampling} (h : EntryArguments p s)
    (space : Workspace s p.control 128) (x : s.gpr .r0 = p.xp) (y : s.gpr .r2 = p.yp) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.entry) s fun t =>
      (EntryContext p t ∧ t.mem = writeLow s.mem p.control (entryValues p)) ∧ Rest [.r3, .r4] s t := by
  refine withRest_all [.r3, .r4] ?_ (by rfl) (by rfl)
  change WP isa (.block ([.ldrSp .r4 56, VG.Impl.Ffdh.Arm.KeySearch.stf .r0 5,
    VG.Impl.Ffdh.Arm.KeySearch.stf .r2 6] ++ _)) s _
  rw [WP.block_append_iff]
  refine WP.mono (entryHead_ok s h space x y) ?_
  rintro u ⟨⟨pointer, mem⟩, rest⟩
  have frame : Frame [⟨State.addr p.control, 128⟩] s.mem u.mem := by
    rw [mem]; exact writeLow_frame _ _ _ (by simp)
  have context : EntryContext p u :=
    ⟨h.after rest frame, ⟨space.congr rest.wr, pointer⟩⟩
  refine wp_entryCopy (i := 0) (j := 15) context (by have := entryWords_min sampling; omega) (by decide) fun s1 c1 m1 _ => ?_
  refine wp_entryCopy (i := 1) (j := 7) c1 (by have := entryWords_min sampling; omega) (by decide) fun s2 c2 m2 _ => ?_
  refine wp_entryCopy (i := 2) (j := 8) c2 (by have := entryWords_min sampling; omega) (by decide) fun s3 c3 m3 _ => ?_
  refine wp_entryCopy (i := 4) (j := 9) c3 (by have := entryWords_min sampling; omega) (by decide) fun s4 c4 m4 _ => ?_
  refine wp_entryCopy (i := 5) (j := 10) c4 (by have := entryWords_min sampling; omega) (by decide) fun s5 c5 m5 _ => ?_
  refine wp_entryCopy (i := 6) (j := 12) c5 (by have := entryWords_min sampling; omega) (by decide) fun s6 c6 m6 _ => ?_
  refine wp_entryCopy (i := 7) (j := 13) c6 (by have := entryWords_min sampling; omega) (by decide) fun s7 c7 m7 _ => ?_
  refine WP.mono (entryZero_ok s7 c7) ?_
  rintro t ⟨m8, r8⟩
  have frame8 : Frame [⟨State.addr p.control, 128⟩] s7.mem t.mem := by
    rw [m8]
    exact (Frame.refl _ _).writeW (r := ⟨State.addr p.control, 128⟩) (by simp) (0#32)
      (Offset.contains_base _ (by decide : 88 + 4 ≤ 128) (by decide))
  refine ⟨c7.after r8 (by simp) frame8, ?_⟩
  rw [m8, m7, m6, m5, m4, m3, m2, m1, mem]
  rfl

theorem entry_fields (p : KeyPublic sampling) (m : Mem)
    (keys : lowWord m p.control 0 = BitVec.ofNat 32 p.keys)
    (scalars : lowWord m p.control 1 = BitVec.ofNat 32 p.scalars)
    (width : lowWord m p.control 2 = BitVec.ofNat 32 p.len) :
    Slots (writeLow m p.control (entryValues p)) p.control (p.headers 0 p.keys p.scalars) := by
  apply (slots_fields _ _ _ _ _ _).mpr
  intro j hj
  rw [lowWord_writeLow _ _ _ (entryValues_bound p) j (headerIndices_bound hj)]
  simp only [headerIndices, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [entryValues, lowValue, KeyPublic.field, keys, scalars, width]

end VG.Proof.Ffdh.Arm.KeySearch
