module

import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Copy
public import VerifiedGarbage.Proof.TripleDes.KeyMemory
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Load
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Component
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Lit

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Key

open VG VG.PPC64LE
open VG.Proof.TripleDes (componentKeys componentOffset)

abbrev keyR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev outputR (s : State) : Region := ⟨s.gpr .r5, 384⟩

def slot (base : Addr) (c j : Nat) : Addr := base + BitVec.ofNat 64 (128 * c + 8 * j)

structure Components (origin s : State) (done : Nat) : Prop where
  keys : ∀ c < done, ∀ j < 16, s.mem.readW (slot (origin.gpr .r5) c j) 64 =
    ((componentKeys origin.mem (origin.gpr .r3) (origin.gpr .r4).toNat c).getD j 0).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  reg : ∀ r ∈ keyKept, s.gpr r = origin.gpr r
  frame : Frame [outputR origin] origin.mem s.mem

structure Permissions (s : State) : Prop where
  reads : ∀ offset, offset + 8 ≤ (s.gpr .r4).toNat →
    InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 offset) 8
  writes : ∀ offset, offset + 8 ≤ 384 → InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 offset) 8
  keyOutput : (keyR s).Disjoint (outputR s)
  valid : Spec.TripleDes.validKey (s.gpr .r4).toNat

theorem componentStep_ok (origin s : State) (c : Nat) (hc : c < 3)
    (hp : Permissions origin) (hs : Components origin s c)
    (hoff : componentOffset (origin.gpr .r4).toNat c = 8 * c) :
    WP isa (Impl.TripleDes.PPC64LE.Key.component (8 * c) c) s
      (Components origin · (c + 1)) := by
  have offsetBound := VG.Proof.TripleDes.componentOffset_bound _ c hp.valid hc
  rw [hoff] at offsetBound
  have read : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (8 * c)) 8 := by
    rw [hs.rd, hs.wr, hs.reg .r3 (by decide)]
    exact hp.reads _ offsetBound
  have write : ∀ j < 16, InRegions s.wr
      (s.gpr .r5 + BitVec.ofNat 64 (128 * c) + BitVec.ofNat 64 (8 * j)) 8 := by
    intro j hj
    rw [hs.wr, hs.reg .r5 (by decide), Offset.add_ofNat_add_ofNat]
    exact hp.writes _ (by omega_using [hc, hj])
  apply WP.mono (component_ok s (8 * c) c hc (by omega) read write)
  intro t ht
  have frame : Frame [⟨origin.gpr .r5 + BitVec.ofNat 64 (128 * c), 128⟩] s.mem t.mem := by
    have hf := ht.frame
    rw [hs.reg .r5 (by decide)] at hf
    exact hf
  have key : Spec.TripleDes.blockAt s.mem (s.gpr .r3 + BitVec.ofNat 64 (8 * c)) =
      Spec.TripleDes.blockAt origin.mem (origin.gpr .r3 + BitVec.ofNat 64 (8 * c)) := by
    rw [hs.reg .r3 (by decide)]
    apply VG.Proof.TripleDes.blockAt_eq_of_frame _ hs.frame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hp.keyOutput.sub_left (Offset.sub_base _ offsetBound)
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun r hr => (ht.reg r hr).trans (hs.reg r hr), hs.frame.trans (frame.sub ?_)⟩
  · intro k hk j hj
    by_cases he : k = c
    · subst k
      have h := ht.keys j hj
      rw [key, hs.reg .r5 (by decide), Offset.add_ofNat_add_ofNat] at h
      unfold componentKeys
      rw [hoff]
      exact h
    · have before : k < c := by omega_using [hk, he]
      have sep : (Region.mk (slot (origin.gpr .r5) k j) 8).Disjoint
          ⟨origin.gpr .r5 + BitVec.ofNat 64 (128 * c), 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [hk, hc, hj]) (by omega_using [hc])
      have hmem := frame.readW (a := slot (origin.gpr .r5) k j) (w := 64) (r := ⟨slot (origin.gpr .r5) k j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys k before j hj)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by omega_using [hc])⟩

theorem copyThird_ok (origin s : State) (hp : Permissions origin)
    (hs : Components origin s 2) (hn : (origin.gpr .r4).toNat = 16) :
    WP isa (.block Impl.TripleDes.PPC64LE.Key.copyThird) s (Components origin · 3) := by
  have reads : ∀ i < 16, InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hs.rd, hs.wr, hs.reg .r5 (by decide)]
    obtain ⟨r, hr, hc⟩ := hp.writes (8 * i) (by omega_using [hi])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writes : ∀ i < 16, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (256 + 8 * i)) 8 := by
    intro i hi
    rw [hs.wr, hs.reg .r5 (by decide)]
    exact hp.writes _ (by omega_using [hi])
  apply WP.mono (copy_ok s 16 (by decide) reads writes)
  intro t ht
  have frame : Frame [⟨origin.gpr .r5 + BitVec.ofNat 64 256, 128⟩] s.mem t.mem := by
    have h := ht.frame
    rw [hs.reg .r5 (by decide)] at h
    exact h
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr, ?_, hs.frame.trans (frame.sub ?_)⟩
  · intro c hc j hj
    by_cases he : c = 2
    · subst c
      have hRepeat : componentKeys origin.mem (origin.gpr .r3) (origin.gpr .r4).toNat 2 =
          componentKeys origin.mem (origin.gpr .r3) (origin.gpr .r4).toNat 0 := by
        rw [hn]; rfl
      have h := ht.keys j hj
      rw [hs.reg .r5 (by decide)] at h
      change t.mem.readW (origin.gpr .r5 + BitVec.ofNat 64 (256 + 8 * j)) 64 = _
      rw [hRepeat]
      have first := hs.keys 0 (by decide) j hj
      simp only [slot, Nat.mul_zero, Nat.zero_add] at first
      exact h.trans first
    · have before : c < 2 := by omega_using [hc, he]
      have sep : (Region.mk (slot (origin.gpr .r5) c j) 8).Disjoint
          ⟨origin.gpr .r5 + BitVec.ofNat 64 256, 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [before, hj]) (by decide)
      have hmem := frame.readW (a := slot (origin.gpr .r5) c j) (w := 64) (r := ⟨slot (origin.gpr .r5) c j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys c before j hj)
  · intro r hr
    have unused : ∀ r ∈ keyKept, r ≠ .r8 := by decide
    exact (ht.reg r (unused r hr)).trans (hs.reg r hr)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by decide)⟩

def componentIndex (i : Nat) : Nat := if i < 16 then 0 else if i < 32 then 1 else 2

theorem index_partition : ∀ i < 48, componentIndex i < 3 ∧ i % 16 < 16 ∧
    8 * i = 128 * componentIndex i + 8 * (i % 16) := by decide

theorem Components.schedule {origin s : State} (h : Components origin s 3) :
    Spec.TripleDes.scheduleAt s.mem (origin.gpr .r5) =
      VG.Proof.TripleDes.expandedMemory origin.mem (origin.gpr .r3) (origin.gpr .r4).toNat := by
  apply Vector.ext
  intro i hi
  have fact := index_partition i hi
  have keys := h.keys (componentIndex i) fact.1 (i % 16) fact.2.1
  rw [slot, ← fact.2.2] at keys
  rw [VG.Proof.TripleDes.scheduleAt_readW s.mem (origin.gpr .r5) i hi]
  simp only [VG.Proof.TripleDes.expandedMemory, Vector.getElem_ofFn]
  by_cases h16 : i < 16
  · simpa only [componentIndex, h16, ite_true] using keys
  · by_cases h32 : i < 32
    · simpa only [componentIndex, h16, h32, ite_false, ite_true] using keys
    · simpa only [componentIndex, h16, h32, ite_false] using keys


end VG.Proof.TripleDes.PPC64LE.Key
