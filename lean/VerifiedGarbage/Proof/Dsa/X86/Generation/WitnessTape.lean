module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleRoundFrame
public import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers

/-! Exact readable tape suffixes, including a cursor that wraps only after its last byte. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86

structure WitnessTape (base : Addr) (bytes : Nat) (sp src : BitVec 32) (r : List Byte) (s : State) : Prop where
  fit : src.toNat + r.length ≤ 2 ^ 32
  data : Spec.Rsa.bytesAt s.mem (byteAddr src) r.length = r
  read : r ≠ [] → InRegions (s.rd ++ s.wr) (byteAddr src) r.length
  workspace : Region.Disjoint ⟨byteAddr src, r.length⟩ ⟨base, bytes⟩
  stack : Region.Disjoint ⟨byteAddr src, r.length⟩ (below sp 1184)

theorem WitnessTape.of_keeps {s t : State} {base : Addr} {bytes : Nat} {sp src : BitVec 32} {r : List Byte}
    (T : WitnessTape base bytes sp src r s) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (memory : t.mem = s.mem) : WitnessTape base bytes sp src r t :=
  ⟨T.fit, by rw [memory]; exact T.data, by rw [rd, wr]; exact T.read, T.workspace, T.stack⟩

private theorem zero_disjoint (p : Addr) (r : Region) : Region.Disjoint ⟨p, 0⟩ r := by
  intro x hx _
  change (x - p).toNat + 1 ≤ 0 at hx
  omega

theorem WitnessTape.prefix {s : State} {base : Addr} {bytes count : Nat} {sp src : BitVec 32} {r : List Byte}
    (T : WitnessTape base bytes sp src r s) (positive : 0 < count) (fit : count ≤ r.length) :
    InRegions (s.rd ++ s.wr) (byteAddr src) count ∧
      Region.Disjoint ⟨byteAddr src, count⟩ ⟨base, bytes⟩ := by
  have source := T.read (by intro h; rw [h] at fit; simp only [List.length_nil] at fit; omega)
  refine ⟨?_, T.workspace.sub_left (Region.sub_prefix fit)⟩
  apply Covers.one source
  exact ⟨_, List.mem_singleton_self _, by
    simpa only [BitVec.add_zero] using Offset.contains_base (byteAddr src) (d := 0) (n := count)
      (k := r.length) (by omega) (by decide)⟩

theorem sample_round_enclose {s t : State} {base : Addr} {sp : BitVec 32} {bytes len : Nat}
    (F : SampleRoundFrame base sp len s t) (capacity : 40960 ≤ bytes) (length : len ≤ 384) :
    Frame [⟨base, bytes⟩, below sp 1184] s.mem t.mem := by
  apply F.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨base, bytes⟩, by simp, Region.sub_prefix (by unfold montgomeryBytes; omega)⟩
  · exact ⟨⟨base, bytes⟩, by simp, Offset.sub_base base (by unfold Layout.arithmetic; omega)⟩
  · exact ⟨⟨base, bytes⟩, by simp, Offset.sub_base base (by unfold Layout.witness; omega)⟩
  · exact ⟨⟨base, bytes⟩, by simp, Offset.sub_base base (by unfold Layout.control; omega)⟩
  · exact ⟨below sp 1184, by simp, fun _ h => h⟩

theorem WitnessTape.keep_enclosed {s t : State} {base : Addr} {bytes : Nat} {sp src : BitVec 32} {r : List Byte}
    (T : WitnessTape base bytes sp src r s) (F : Frame [⟨base, bytes⟩, below sp 1184] s.mem t.mem)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) : WitnessTape base bytes sp src r t := by
  refine ⟨T.fit, ?_, ?_, T.workspace, T.stack⟩
  · rw [VG.Proof.Dsa.Generation.frame_bytesAt F (by
      intro region hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact T.workspace
      · exact T.stack) (by have := T.fit; omega), T.data]
  · rw [rd, wr]; exact T.read

theorem WitnessTape.keep {s t : State} {base : Addr} {bytes len : Nat} {sp src : BitVec 32} {r : List Byte}
    (T : WitnessTape base bytes sp src r s) (F : SampleRoundFrame base sp len s t)
    (capacity : 40960 ≤ bytes) (length : len ≤ 384) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    WitnessTape base bytes sp src r t :=
  T.keep_enclosed (sample_round_enclose F capacity length) rd wr

theorem WitnessTape.advance {s : State} {base : Addr} {bytes count : Nat} {sp src : BitVec 32} {r : List Byte}
    (T : WitnessTape base bytes sp src r s) (countFit : count ≤ r.length) :
    WitnessTape base bytes sp (src + BitVec.ofNat 32 count) (r.drop count) s := by
  by_cases empty : r.drop count = []
  · rw [empty]
    refine ⟨by simp only [List.length_nil, Nat.add_zero]; exact Nat.le_of_lt (BitVec.isLt _),
      by simp only [List.length_nil, Spec.Rsa.bytesAt, List.range_zero, List.map_nil],
      by intro h; exact False.elim (h rfl), zero_disjoint _ _, zero_disjoint _ _⟩
  · have left : count < r.length := by
      have := List.length_pos_iff.mpr empty
      rw [List.length_drop] at this
      omega
    have strict : src.toNat + count < 2 ^ 32 := by have := T.fit; omega
    have address := byteAddr_add (a := src) (k := count) strict
    have value : (src + BitVec.ofNat 32 count).toNat = src.toNat + count := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := count) (by omega), Nat.mod_eq_of_lt strict]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [value, List.length_drop]; have := T.fit; omega
    · have slice := VG.Proof.Dsa.bytesAt_slice s.mem (byteAddr src) (total := r.length)
        (offset := count) (len := r.length - count) (by omega)
      rw [T.data] at slice
      rw [← List.length_drop, List.take_length] at slice
      rw [address]
      exact slice.symm
    · intro _
      rw [address, List.length_drop]
      apply Covers.one (T.read (by intro h; rw [h] at left; simp only [List.length_nil] at left; omega))
      exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [address, List.length_drop]
      exact T.workspace.sub_left (Offset.sub_base _ (by omega))
    · rw [address, List.length_drop]
      exact T.stack.sub_left (Offset.sub_base _ (by omega))

end VG.Proof.Dsa.X86.Generation
