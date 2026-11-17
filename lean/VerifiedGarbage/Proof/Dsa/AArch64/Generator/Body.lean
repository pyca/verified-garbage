module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Finish
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep (brun's simp set reads its lemmas)
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.AArch64.Generator
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp -- shake: keep (the statements need `WP` and `preserved`; narrowing it does not build)
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! ### `Dsa.AArch64.Generator.Saves`, which this module and modules that import it used -/

section

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
  have w (d : Nat) (h₁ : 27840 ≤ d) (h₂ : d + 8 ≤ 27992) := hw d (by unfold spill VG.Impl.Dsa.Generation.Layout.control; omega_using [h₁])
    (by unfold spill spillBytes VG.Impl.Dsa.Generation.Layout.control; omega_using [h₂])
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
  have r (d : Nat) (h₁ : 27840 ≤ d) (h₂ : d + 8 ≤ 27992) := read d (by unfold spill VG.Impl.Dsa.Generation.Layout.control; omega_using [h₁])
    (by unfold spill spillBytes VG.Impl.Dsa.Generation.Layout.control; omega_using [h₂])
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

end

end

/-! # The stage's body, between its frame's push and pop

The body saves the callee-saved registers in the working space's control
area, fills the frame words, runs the stage, returns its status as 1 or 0,
and restores the registers. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout VG.Impl.Dsa.AArch64.Generator
open VG.Proof.Dsa.AArch64.Generation (allocState)
open VG.Proof.RsaOaep.AArch64 (Lay Rep)

/-- The body of the function, inside its frame. -/
abbrev body (mul : Nat → Nat → Nat → Prog isa) (pLen : Nat) : Prog isa :=
  Impl.Bignum.AArch64.seqs [.block save, .block entry, stage mul pLen, .block exit, .block restore]

variable {pLen : Nat} {s : State}

/-- The saved registers' region. -/
abbrev spillRegion (s : State) : Region := ⟨off (s.gpr .x0) spill, spillBytes⟩

/-- What the body leaves: the stage's status as 1 or 0, the packed domain,
the memory changed only in the stage's regions, the frame and the saved
registers' slots, and the callee-saved registers. -/
structure BodyPost (pLen : Nat) (s t : State) : Prop where
  status : t.gpr .x0 = BitVec.ofNat 64 (endCode pLen s + 4 * (pLen * readCount pLen s))
  packed : ∀ a, result pLen s = some a →
    Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) packed) (2 * pLen + qLen pLen) = Spec.Dsa.encodeParams pLen (qLen pLen) a
  frame : Frame (stageChanged pLen s ++ [⟨frameBase s, 272⟩, spillRegion s]) s.mem t.mem
  regs : ∀ r ∈ preserved, t.gpr r = s.gpr r
  vectors : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  sp : t.sp = (allocState 272 s).sp
  wr : t.wr = (allocState 272 s).wr
  rd : t.rd = s.rd

theorem exit_ok {t : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t F S) (R : Rep t.mem F S V W) :
    WP isa (.block exit) t fun t' => t'.mem = t.mem ∧ t'.gpr .x0 = W 19 + (W 20 <<< 2) ∧
      Keep [.x0, .x3, .x4] t t' := by
  have hw : t.mem.readW (t.sp + BitVec.ofNat 64 152) 64 = W 19 := by rw [L.sp]; exact R.fr 19 (by decide)
  have hw' : t.mem.readW (t.sp + BitVec.ofNat 64 160) 64 = W 20 := by rw [L.sp]; exact R.fr 20 (by decide)
  have hl : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 152) 8 := by rw [L.sp]; exact L.ld (d := 152) (by decide)
  have hl' : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 160) 8 := by rw [L.sp]; exact L.ld (d := 160) (by decide)
  have run : WP isa (.block exit) t fun t' => t'.mem = t.mem ∧ t'.gpr .x0 = W 19 + (W 20 <<< 2) := by
    unfold exit
    brun [State.write, exec_ldrSp (off := 152) (by decide), exec_ldrSp (off := 160) (by decide),
      exec_lsl_x (by decide : 2 < 64), hw, hl, hw', hl']
  exact WP.mono (WP.keep [.x0, .x3, .x4] run (by decide)) fun t' ⟨⟨hm, hx⟩, k⟩ => ⟨hm, hx, k⟩

theorem savedState_gpr (s : State) {r : Reg} (h : r ≠ .x9) : (savedState s).gpr r = s.gpr r := by
  simp [savedState, h]

theorem StageABI.spill_in (hb : Supported pLen) (A : StageABI pLen s) :
    ∀ d, spill ≤ d → d + 8 ≤ spill + spillBytes → InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 d) 8 := by
  intro d h₁ h₂
  have := spill_used hb
  have := A.size
  have := A.wsBound
  exact ⟨wsRegion s, by rw [A.wr]; exact List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- The saves, from the frame's allocation. -/
theorem save_saved (hb : Supported pLen) (A : StageABI pLen s) :
    WP isa (.block save) (allocState 272 s) (· = savedState (allocState 272 s)) :=
  save_ok fun d h₁ h₂ => by
    obtain ⟨r, hr, hc⟩ := A.spill_in hb d h₁ h₂
    exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩

/-- The entry, from the saves' state, fills the frame words. -/
theorem entry_entered (s : State) :
    WP isa (.block entry) (savedState (allocState 272 s)) fun u => Entered pLen s u ∧
      Frame [⟨frameBase s, 272⟩] (savedState (allocState 272 s)).mem u.mem := by
  have hF : ∀ {d n : Nat}, d + n ≤ 272 → Region.Contains ⟨frameBase s, 272⟩ (off (frameBase s) d) n :=
    fun h => Offset.contains_base _ h (by omega_using [h])
  refine WP.mono (entry_ok (s := savedState (allocState 272 s)) (F := frameBase s) rfl
    (fun d hd => ⟨_, List.mem_cons_self, hF hd⟩)) fun u ⟨hmu, ku⟩ => ?_
  have g0 : (savedState (allocState 272 s)).gpr .x0 = s.gpr .x0 := savedState_gpr _ (by decide)
  have g2 : (savedState (allocState 272 s)).gpr .x2 = s.gpr .x2 := savedState_gpr _ (by decide)
  have g3 : (savedState (allocState 272 s)).gpr .x3 = s.gpr .x3 := savedState_gpr _ (by decide)
  have fl : Frame [spillRegion s] s.mem (savedState (allocState 272 s)).mem := save_frame (allocState 272 s)
  have fe : Frame [⟨frameBase s, 272⟩] (savedState (allocState 272 s)).mem u.mem := hmu ▸ entryMem_frame _ _
  refine ⟨{
    sp := ku.sp
    rd := ku.rd
    wr := ku.wr
    frame := (fl.mono (by simp)).trans (fe.mono (by simp))
    words := fun k hk => by rw [hmu, entryMem_word _ _ hk, g0, g2, g3] }, fe⟩

theorem body_ok (M : Mont) (hb : Supported pLen) (A : StageABI pLen s) :
    WP isa (body M.mm pLen) (allocState 272 s) (BodyPost pLen s) := by
  simp only [body, Impl.Bignum.AArch64.seqs]
  refine WP.seq (WP.mono (save_saved hb A) fun l hl => ?_)
  subst hl
  refine WP.seq (WP.mono (entry_entered (pLen := pLen) s) fun u ⟨E, fe⟩ => ?_)
  refine WP.seq (WP.mono (stage_ok M hb A E) fun t T => ?_)
  obtain ⟨V, W, R, h5, h19, h20⟩ := T.rep
  refine WP.seq (WP.mono (exit_ok T.lay R) fun t' ⟨hm', hx, k'⟩ => ?_)
  -- The saved registers, which nothing but the saves wrote.
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have qn := hb.q_le
  have hs := spill_used hb
  have sep : ∀ r ∈ [(⟨frameBase s, 272⟩ : Region)] ++ stageChanged pLen s,
      Region.Disjoint ⟨s.gpr .x0 + BitVec.ofNat 64 spill, spillBytes⟩ r := by
    intro r hr
    simp only [stageChanged, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have c : spill = 27840 := rfl
    have c1 : packed = 27008 := rfl
    have c2 : g = 26240 := rfl
    have c5 : arithmetic = 28672 := rfl
    have c6 : domainCheck = 40960 := rfl
    have sp : ∀ {d n : Nat}, d + n ≤ usedBytes pLen → (d + n ≤ spill ∨ spill + spillBytes ≤ d) →
        Region.Disjoint ⟨s.gpr .x0 + BitVec.ofNat 64 spill, spillBytes⟩ ⟨off (s.gpr .x0) d, n⟩ := fun h h' =>
      A.parts hb hs h (h'.symm)
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ((A.stackWs.sub_left (frame_sub0 s (Nat.le_refl _))).sub_right (A.part_sub hs)).symm
    · exact sp (used_small hb (by decide) (by rfl)) (Or.inr (by decide))
    · have := sp (used_parent hb) (Or.inl (by decide)); simpa [off] using this
    · exact sp (used_small hb (by decide) (by unfold arithmeticBytes; omega_using [pn])) (Or.inl (by omega_using [pn, c, c2]))
    · exact sp (used_small hb (by decide) (by unfold arithmeticBytes; omega_using [pn, qn])) (Or.inl (by omega_using [pn, qn, c, c1]))
    · exact sp (StageABI.domainCheck_room hb) (Or.inr (by decide))
    · exact ((A.stackWs.sub_left (frame_sub0 s (by unfold frameBytes; omega_using []))).sub_right (A.part_sub hs)).symm
  have fmid : Frame ([⟨frameBase s, 272⟩] ++ stageChanged pLen s) (savedState (allocState 272 s)).mem t'.mem := by
    rw [hm']
    exact (fe.mono (by simp)).trans (T.frame.mono (by intro r hr; simp [hr]))
  have saved_g := (saved_gprs (allocState 272 s)).frame_in (lo := spill) (n := spillBytes) (by decide) fmid sep
  have saved_v := (saved_vectors (allocState 272 s)).frame_in (lo := spill) (n := spillBytes) (by decide) fmid sep
  have sp' : t'.sp = frameBase s := k'.sp.trans T.lay.sp
  have wr' : t'.wr = (allocState 272 s).wr := k'.wr.trans (T.wr.trans E.wr)
  have hB : t'.mem.readW (t'.sp + BitVec.ofNat 64 40) 64 = s.gpr .x0 := by
    rw [sp', hm']; exact (R.fr 5 (by decide)).trans h5
  have r40 : InRegions (t'.rd ++ t'.wr) (t'.sp + BitVec.ofNat 64 40) 8 := by
    rw [k'.rd, k'.wr, sp']; exact T.lay.ld (d := 40) (by decide)
  have rd : ∀ d, spill ≤ d → d + 8 ≤ spill + spillBytes →
      InRegions (t'.rd ++ t'.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ => by
    obtain ⟨r, hr, hc⟩ := A.spill_in hb d h₁ h₂
    exact ⟨r, List.mem_append_right _ (by rw [wr']; exact List.mem_cons_of_mem _ hr), hc⟩
  refine WP.mono (restore_ok (s := allocState 272 s) hB r40 rd saved_g saved_v) fun t'' Rs => ?_
  refine ⟨?_, fun a ha => ?_, ?_, Rs.gprs, Rs.vectors, Rs.stack.trans sp', Rs.write.trans wr',
    Rs.read.trans (k'.rd.trans (T.rd.trans E.rd))⟩
  · rw [Rs.result, hx, h19, h20]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    omega_using []
  · rw [Rs.memory, hm']; exact T.packed a ha
  · rw [Rs.memory, hm']
    exact (E.frame.mono (by simp)).trans (T.frame.mono (by intro r hr; simp [hr]))

end VG.Proof.Dsa.AArch64.Generator
