module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Spills
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Block
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Saving and restoring `r14`–`r28` in slots 0–14 of the scratch buffer
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

def savedReg (i : Nat) : Reg := savedRegs.getD i .r14

theorem blockSave_eq : blockSave = Spill.saveCode .r5 (Spill.slots savedReg 15) := by
  decide +kernel

theorem blockRestore_eq : blockRestore = Spill.restoreCode .r5 (Spill.slots savedReg 15) := by
  decide +kernel

def Saved (original current : State) : Prop :=
  ∀ i < 15, current.mem.readW (current.gpr .r5 + BitVec.ofNat 64 (8 * i)) 64 =
    original.gpr (savedReg i)

structure SavePost (original current : State) : Prop where
  gpr : current.gpr = original.gpr
  rd : current.rd = original.rd
  wr : current.wr = original.wr
  saved : Saved original current
  frame : Frame [⟨original.gpr .r5, 120⟩] original.mem current.mem

theorem blockSave_ok (s : State)
    (hw : ∀ i < 15, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block blockSave) s (SavePost s) := by
  rw [blockSave_eq]
  refine WP.mono (Spill.save_wp (by decide) (by decide) (Spill.forall_slots hw)) fun s' h =>
    ⟨h.gpr, h.rd, h.wr, fun i hi => ?_, ?_⟩
  · rw [h.gpr, h.mem]
    exact Spill.saveMem_saved (l := Spill.slots savedReg 15) (by decide) s.mem (s.gpr .r5) s.gpr
      (savedReg i, 8 * i) (Spill.mem_slots hi)
  · rw [h.mem]; exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _

structure RestorePost (original origin current : State) : Prop where
  saved : ∀ r ∈ savedRegs, current.gpr r = original.gpr r
  keep : Keep savedRegs origin current
  mem : current.mem = origin.mem

theorem blockRestore_ok (original s : State) (hsaved : Saved original s)
    (hread : ∀ i < 15, InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block blockRestore) s (RestorePost original s) := by
  rw [blockRestore_eq]
  have hregs : (Spill.slots savedReg 15).map Prod.fst = savedRegs := by decide +kernel
  exact WP.mono (Spill.restore_wp (by decide) rfl (by decide) (by decide) (Spill.forall_slots hread)
    (Spill.forall_slots hsaved)) fun s' h =>
    ⟨fun r hr => h.gpr_of (.inl (hregs ▸ hr)), ⟨fun r hr => h.other r (hregs ▸ hr), h.rd, h.wr⟩,
      h.mem⟩

theorem savedSlot_spill_disjoint (s : State) (i : Nat) (hi : i < 15) :
    (⟨s.gpr .r5 + BitVec.ofNat 64 (8 * i), 8⟩ : Region).Disjoint (spillRegion s) :=
  Offset.disjoint (s.gpr .r5) (by omega) (by omega) (by decide)

theorem Saved.congr {original s t : State} (hs : Saved original s)
    (hbase : t.gpr .r5 = s.gpr .r5) (hf : Frame [spillRegion s] s.mem t.mem) :
    Saved original t := by
  intro i hi
  have hmem := hf.readW (a := s.gpr .r5 + BitVec.ofNat 64 (8 * i)) (w := 64)
    (r := ⟨s.gpr .r5 + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
    (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact savedSlot_spill_disjoint s i hi)
    (by decide)
  rw [hbase]
  exact hmem.trans (hs i hi)

end VG.Proof.TripleDes.PPC64LE
