module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Entry
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.EntryCache
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Packed
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! The same entry snapshot optionally retains the two cached-context arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

def entryMem (p : KeyPublic sampling) (m : Mem) : Mem :=
  if sampling.cachedContext then entryCacheMem p (writeLow m p.control (entryValues p))
  else writeLow m p.control (entryValues p)

theorem entryMem_frame (p : KeyPublic sampling) (m : Mem) :
    Frame [⟨State.addr p.control,128⟩] m (entryMem p m) := by
  unfold entryMem
  split
  · exact (writeLow_frame _ _ _ (entryValues_bound p)).trans (entryCache_frame _ _)
  · exact writeLow_frame _ _ _ (entryValues_bound p)

theorem entry_ok (s : State) {p : KeyPublic sampling} (h : EntryArguments p s)
    (space : Workspace s p.control 128) (x : s.gpr .r0=p.xp) (y : s.gpr .r2=p.yp) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.entryFor sampling.cachedContext)) s fun t =>
      (EntryContext p t ∧ t.mem=entryMem p s.mem) ∧ Rest [.r3,.r4] s t := by
  rw [VG.Impl.Ffdh.Arm.KeySearch.entryFor,WP.block_append_iff]
  refine WP.mono (entry_base_ok s h space x y) ?_
  rintro u ⟨⟨context,mem⟩,rest⟩
  by_cases cached : sampling.cachedContext=true
  · simp only [cached,ite_true]
    refine WP.mono (entryCache_ok u context cached) ?_
    rintro t ⟨⟨ct,memT⟩,restT⟩
    refine ⟨⟨ct,?_⟩,rest.trans (restT.mono (by simp))⟩
    rw [memT,mem,entryMem,ite_eq_left cached]
  · simp only [cached]
    exact WP.block_nil ⟨⟨context,by rw [entryMem,ite_eq_right cached]; exact mem⟩,rest⟩

theorem entryCache_read (p : KeyPublic sampling) (m : Mem) {d : Nat}
    (bound : d+4≤128) (sep : d+4≤32 ∨ 40≤d) :
    (entryCacheMem p m).readW (off (State.addr p.control) d) 32 =
      m.readW (off (State.addr p.control) d) 32 := by
  unfold entryCacheMem
  rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]

theorem entryMem_fields (p : KeyPublic sampling) (m : Mem)
    (keys : lowWord m p.control 0=BitVec.ofNat 32 p.keys)
    (scalars : lowWord m p.control 1=BitVec.ofNat 32 p.scalars)
    (width : lowWord m p.control 2=BitVec.ofNat 32 p.len) :
    Slots (entryMem p m) p.control (p.headers 0 p.keys p.scalars) := by
  have old := entry_fields p m keys scalars width
  unfold entryMem
  split
  · apply (slots_fields _ _ _ _ _ _).mpr
    intro j hj
    change (entryCacheMem p _).readW _ 32 = _
    rw [entryCache_read _ _ (by have := headerIndices_bound hj; omega) (by
      simp only [headerIndices,List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
    exact (slots_fields _ _ _ _ _ _).mp old j hj
  · exact old

theorem entryMem_high (p : KeyPublic sampling) (m : Mem) {j : Nat} (hj : j<3) :
    (entryMem p m).readW (off (State.addr p.control) (8*j+4)) 32 =
      m.readW (off (State.addr p.control) (8*j+4)) 32 := by
  unfold entryMem
  split
  · rw [entryCache_read _ _ (by omega) (by omega)]
    exact highWord_writeLow _ _ _ (entryValues_bound p) j (by omega)
  · exact highWord_writeLow _ _ _ (entryValues_bound p) j (by omega)

theorem entryMem_cached (p : KeyPublic sampling) (m : Mem) : CachedSlots p (entryMem p m) := by
  intro cached
  rw [entryMem,ite_eq_left cached]
  unfold entryCacheMem
  constructor
  · rw [Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · exact Mem.readW_writeW_self32 _ _ _

end VG.Proof.Ffdh.Arm.KeySearch
