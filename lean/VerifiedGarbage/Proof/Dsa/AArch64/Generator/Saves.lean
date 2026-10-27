module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generator
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp -- shake: keep (the statements need `WP` and `preserved`; narrowing it does not build)
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep (brun's simp set reads its lemmas)
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Offset

/-! # The stage saves the callee-saved registers in the working space, and restores them

`str`/`ldr` of each register at its slot of the control area, the low halves
of v8–v15 through `x9` and `x10`. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Impl.Dsa.AArch64.Generator

/-- The slots of the vector registers' low halves, keyed by `x0`–`x7` as
`Spill`'s lists of registers are. -/
def vectorKeys : List (Reg × Nat) :=
  [(.x0, spill + 88), (.x1, spill + 96), (.x2, spill + 104), (.x3, spill + 112), (.x4, spill + 120),
   (.x5, spill + 128), (.x6, spill + 136), (.x7, spill + 144)]

/-- The low halves of v8–v15, keyed by `x0`–`x7`. -/
def laneValues (s : State) : Reg → BitVec 64
  | .x0 => laneOf s .v8 0 | .x1 => laneOf s .v9 0
  | .x2 => laneOf s .v10 0 | .x3 => laneOf s .v11 0
  | .x4 => laneOf s .v12 0 | .x5 => laneOf s .v13 0
  | .x6 => laneOf s .v14 0 | _ => laneOf s .v15 0

def savedMem (s : State) : Mem :=
  Spill.saveMem (Spill.saveMem s.mem (s.gpr .x0) s.gpr gprSlots) (s.gpr .x0) (laneValues s) vectorKeys

/-- The state after the saves. -/
def savedState (s : State) : State :=
  { s with gpr := fun r => if r = .x9 then laneOf s .v15 0 else s.gpr r, mem := savedMem s }

theorem save_ok {s : State}
    (hw : ∀ d, spill ≤ d → d + 8 ≤ spill + spillBytes → InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 d) 8) :
    WP isa (.block save) s (· = savedState s) := by
  simp only [save, gprSlots, vectorSlots, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, spill, VG.Impl.Dsa.Generation.Layout.control]
  have w (d : Nat) (h₁ : 27840 ≤ d) (h₂ : d + 8 ≤ 27992) := hw d (by unfold spill VG.Impl.Dsa.Generation.Layout.control; omega)
    (by unfold spill spillBytes VG.Impl.Dsa.Generation.Layout.control; omega)
  brun [exec_str_x (off := 27840) (by decide), exec_str_x (off := 27848) (by decide),
    exec_str_x (off := 27856) (by decide), exec_str_x (off := 27864) (by decide),
    exec_str_x (off := 27872) (by decide), exec_str_x (off := 27880) (by decide),
    exec_str_x (off := 27888) (by decide), exec_str_x (off := 27896) (by decide),
    exec_str_x (off := 27904) (by decide), exec_str_x (off := 27912) (by decide),
    exec_str_x (off := 27920) (by decide), exec_str_x (off := 27928) (by decide),
    exec_str_x (off := 27936) (by decide), exec_str_x (off := 27944) (by decide),
    exec_str_x (off := 27952) (by decide), exec_str_x (off := 27960) (by decide),
    exec_str_x (off := 27968) (by decide), exec_str_x (off := 27976) (by decide),
    exec_str_x (off := 27984) (by decide),
    w 27840 (by decide) (by decide), w 27848 (by decide) (by decide), w 27856 (by decide) (by decide),
    w 27864 (by decide) (by decide), w 27872 (by decide) (by decide), w 27880 (by decide) (by decide),
    w 27888 (by decide) (by decide), w 27896 (by decide) (by decide), w 27904 (by decide) (by decide),
    w 27912 (by decide) (by decide), w 27920 (by decide) (by decide), w 27928 (by decide) (by decide),
    w 27936 (by decide) (by decide), w 27944 (by decide) (by decide), w 27952 (by decide) (by decide),
    w 27960 (by decide) (by decide), w 27968 (by decide) (by decide), w 27976 (by decide) (by decide),
    w 27984 (by decide) (by decide),
    exec_umov (by decide : 0 < 2), savedMem, Spill.saveMem, gprSlots, vectorKeys, laneValues, savedState,
    laneOf, State.write, spill, VG.Impl.Dsa.Generation.Layout.control]
  congr 1
  funext r
  by_cases h : r = .x9 <;> simp only [h, ite_true, ite_false] <;> rfl

/-- What the restores leave. -/
structure Restored (s t u : State) : Prop where
  gprs : ∀ r ∈ preserved, u.gpr r = s.gpr r
  vectors : ∀ v ∈ preservedV, (u.v v).extractLsb' 0 64 = (s.v v).extractLsb' 0 64
  memory : u.mem = t.mem
  stack : u.sp = t.sp
  read : u.rd = t.rd
  write : u.wr = t.wr
  result : u.gpr .x0 = t.gpr .x0

theorem restore_ok {s t : State} {B : Addr}
    (hB : t.mem.readW (t.sp + BitVec.ofNat 64 40) 64 = B)
    (r40 : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 40) 8)
    (read : ∀ d, spill ≤ d → d + 8 ≤ spill + spillBytes → InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 d) 8)
    (g : Spill.Saved B s.gpr gprSlots t.mem) (v : Spill.Saved B (laneValues s) vectorKeys t.mem) :
    WP isa (.block restore) t (Restored s t) := by
  simp only [restore, gprSlots, vectorSlots, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, spill, VG.Impl.Dsa.Generation.Layout.control]
  have r (d : Nat) (h₁ : 27840 ≤ d) (h₂ : d + 8 ≤ 27992) := read d (by unfold spill VG.Impl.Dsa.Generation.Layout.control; omega)
    (by unfold spill spillBytes VG.Impl.Dsa.Generation.Layout.control; omega)
  simp only [Spill.Saved, gprSlots, vectorKeys, spill, VG.Impl.Dsa.Generation.Layout.control, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Nat.reduceAdd] at g v
  obtain ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g30⟩ := g
  obtain ⟨v8, v9, v10, v11, v12, v13, v14, v15⟩ := v
  brun [exec_ldrSp (off := 40) (by decide),
    exec_ldr_x (off := 27840) (by decide), exec_ldr_x (off := 27848) (by decide),
    exec_ldr_x (off := 27856) (by decide), exec_ldr_x (off := 27864) (by decide),
    exec_ldr_x (off := 27872) (by decide), exec_ldr_x (off := 27880) (by decide),
    exec_ldr_x (off := 27888) (by decide), exec_ldr_x (off := 27896) (by decide),
    exec_ldr_x (off := 27904) (by decide), exec_ldr_x (off := 27912) (by decide),
    exec_ldr_x (off := 27920) (by decide), exec_ldr_x (off := 27928) (by decide),
    exec_ldr_x (off := 27936) (by decide), exec_ldr_x (off := 27944) (by decide),
    exec_ldr_x (off := 27952) (by decide), exec_ldr_x (off := 27960) (by decide),
    exec_ldr_x (off := 27968) (by decide), exec_ldr_x (off := 27976) (by decide),
    exec_ldr_x (off := 27984) (by decide),
    exec_ins (by decide : 0 < 2), hB, r40,
    r 27840 (by decide) (by decide), r 27848 (by decide) (by decide), r 27856 (by decide) (by decide),
    r 27864 (by decide) (by decide), r 27872 (by decide) (by decide), r 27880 (by decide) (by decide),
    r 27888 (by decide) (by decide), r 27896 (by decide) (by decide), r 27904 (by decide) (by decide),
    r 27912 (by decide) (by decide), r 27920 (by decide) (by decide), r 27928 (by decide) (by decide),
    r 27936 (by decide) (by decide), r 27944 (by decide) (by decide), r 27952 (by decide) (by decide),
    r 27960 (by decide) (by decide), r 27968 (by decide) (by decide), r 27976 (by decide) (by decide),
    r 27984 (by decide) (by decide),
    g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g30, v8, v9, v10, v11, v12, v13, v14, v15,
    laneValues, laneOf, State.write, State.setV]
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro r hr
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    all_goals exact extract_setLane64 _ _ (i := 0) (j := 0) (by decide) (by decide)

theorem saved_gprs (s : State) : Spill.Saved (s.gpr .x0) s.gpr gprSlots (savedState s).mem := by
  have g := Spill.saveMem_saved (l := gprSlots) (by decide) s.mem (s.gpr .x0) s.gpr
  have vf := Spill.saveMem_frame (l := vectorKeys) (lo := spill + 88) (n := 64) (by decide) (by decide)
    (Spill.saveMem s.mem (s.gpr .x0) s.gpr gprSlots) (s.gpr .x0) (laneValues s)
  exact g.frame_in (lo := spill) (n := 88) (by decide) vf (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint (s.gpr .x0) (by decide) (by decide) (by decide))

theorem saved_vectors (s : State) : Spill.Saved (s.gpr .x0) (laneValues s) vectorKeys (savedState s).mem :=
  Spill.saveMem_saved (l := vectorKeys) (by decide) _ (s.gpr .x0) (laneValues s)

theorem save_frame (s : State) :
    Frame [⟨s.gpr .x0 + BitVec.ofNat 64 spill, spillBytes⟩] s.mem (savedState s).mem := by
  have gp := Spill.saveMem_frame (l := gprSlots) (lo := spill) (n := spillBytes) (by decide) (by decide)
    s.mem (s.gpr .x0) s.gpr
  have vp := Spill.saveMem_frame (l := vectorKeys) (lo := spill) (n := spillBytes) (by decide) (by decide)
    (Spill.saveMem s.mem (s.gpr .x0) s.gpr gprSlots) (s.gpr .x0) (laneValues s)
  exact gp.trans vp

end VG.Proof.Dsa.AArch64.Generator
