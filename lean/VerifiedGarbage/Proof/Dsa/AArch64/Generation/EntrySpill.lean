module

public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Store the AAPCS64 preserved registers outside the generation frame words. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

def vectorSlots : List (Reg × Nat) :=
  [⟨.x0, 384⟩, ⟨.x1, 392⟩, ⟨.x2, 400⟩, ⟨.x3, 408⟩,
   ⟨.x4, 416⟩, ⟨.x5, 424⟩, ⟨.x6, 432⟩, ⟨.x7, 440⟩]

def vectorValues (s : State) : Reg → BitVec 64
  | .x0 => laneOf s .v8 0 | .x1 => laneOf s .v9 0
  | .x2 => laneOf s .v10 0 | .x3 => laneOf s .v11 0
  | .x4 => laneOf s .v12 0 | .x5 => laneOf s .v13 0
  | .x6 => laneOf s .v14 0 | _ => laneOf s .v15 0

def savedAbiMem (s : State) : Mem :=
  Spill.saveMem (Spill.saveMem s.mem (generationBase s) s.gpr abiGprs)
    (generationBase s) (vectorValues s) vectorSlots

def linkRegion (s : State) : Region := ⟨off (generationBase s) 296, 152⟩

def linkState (s : State) : State :=
  { allocState 448 s with
    gpr := fun r => if r = .x9 then laneOf s .v15 0 else s.gpr r
    mem := (savedAbiMem s).writeW (linkRegion s).base (s.gpr .x30) }

theorem entrySave_ok (s : State) :
    WP isa (.block entrySave) (allocState 448 s) (fun t => t = linkState s) := by
  have hw (d : Nat) (hd : d + 8 ≤ 448) :
      InRegions (allocState 448 s).wr ((allocState 448 s).sp + BitVec.ofNat 64 d) 8 :=
    ⟨⟨generationBase s, 448⟩, List.mem_cons_self .., Offset.contains_base _ hd (by omega)⟩
  simp only [entrySave, abiGprs, abiVectors, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append]
  brun [exec_storeSp (off := 304) (by decide), exec_storeSp (off := 312) (by decide), exec_storeSp (off := 320) (by decide), exec_storeSp (off := 328) (by decide), exec_storeSp (off := 336) (by decide), exec_storeSp (off := 344) (by decide), exec_storeSp (off := 352) (by decide), exec_storeSp (off := 360) (by decide), exec_storeSp (off := 368) (by decide), exec_storeSp (off := 376) (by decide), exec_storeSp (off := 384) (by decide), exec_storeSp (off := 392) (by decide), exec_storeSp (off := 400) (by decide), exec_storeSp (off := 408) (by decide), exec_storeSp (off := 416) (by decide), exec_storeSp (off := 424) (by decide), exec_storeSp (off := 432) (by decide), exec_storeSp (off := 440) (by decide), exec_storeSp (off := 296) (by decide), hw 304 (by decide), hw 312 (by decide), hw 320 (by decide), hw 328 (by decide), hw 336 (by decide), hw 344 (by decide), hw 352 (by decide), hw 360 (by decide), hw 368 (by decide), hw 376 (by decide), hw 384 (by decide), hw 392 (by decide), hw 400 (by decide), hw 408 (by decide), hw 416 (by decide), hw 424 (by decide), hw 432 (by decide), hw 440 (by decide), hw 296 (by decide), exec_umov (by decide : 0 < 2), savedAbiMem, Spill.saveMem,
    abiGprs, vectorSlots, vectorValues, linkState, linkRegion, laneOf, State.write]
  congr 1
  funext r
  by_cases h : r = .x9 <;> simp only [h, ite_true, ite_false] <;> rfl

end VG.Proof.Dsa.AArch64.Generation
