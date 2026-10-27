module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Finish
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Saves
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep (brun's simp set reads its lemmas)
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

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
  status : t.gpr .x0 = BitVec.ofNat 64 (if (result pLen s).isSome then 1 else 0)
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
    WP isa (.block exit) t fun t' => t'.mem = t.mem ∧ t'.gpr .x0 = (3 - W 19) >>> 1 ∧ Keep [.x0, .x3] t t' := by
  have hw : t.mem.readW (t.sp + BitVec.ofNat 64 152) 64 = W 19 := by rw [L.sp]; exact R.fr 19 (by decide)
  have hl : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 152) 8 := by rw [L.sp]; exact L.ld (d := 152) (by decide)
  have h3 : BitVec.setWidth 64 (BitVec.ofNat 16 3) = (3 : BitVec 64) := by decide
  have run : WP isa (.block exit) t fun t' => t'.mem = t.mem ∧ t'.gpr .x0 = (3 - W 19) >>> 1 := by
    unfold exit
    brun [State.write, exec_ldrSp (off := 152) (by decide), exec_lsr_x (by decide : 1 < 64), hw, hl, h3]
  exact WP.mono (WP.keep [.x0, .x3] run (by decide)) fun t' ⟨⟨hm, hx⟩, k⟩ => ⟨hm, hx, k⟩

theorem savedState_gpr (s : State) {r : Reg} (h : r ≠ .x9) : (savedState s).gpr r = s.gpr r := by
  simp [savedState, h]

theorem StageABI.spill_in (hb : Supported pLen) (A : StageABI pLen s) :
    ∀ d, spill ≤ d → d + 8 ≤ spill + spillBytes → InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 d) 8 := by
  intro d h₁ h₂
  have := spill_used hb
  have := A.size
  have := A.wsBound
  exact ⟨wsRegion s, by rw [A.wr]; exact List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩

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
    fun h => Offset.contains_base _ h (by omega)
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
  obtain ⟨V, W, R, h5, h19⟩ := T.rep
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
    · exact sp (used_small hb (by decide) (by unfold arithmeticBytes; omega)) (Or.inl (by omega))
    · exact sp (used_small hb (by decide) (by unfold arithmeticBytes; omega)) (Or.inl (by omega))
    · exact sp (StageABI.domainCheck_room hb) (Or.inr (by decide))
    · exact ((A.stackWs.sub_left (frame_sub0 s (by unfold frameBytes; omega))).sub_right (A.part_sub hs)).symm
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
  · rw [Rs.result, hx, h19]
    cases (result pLen s).isSome <;> decide
  · rw [Rs.memory, hm']; exact T.packed a ha
  · rw [Rs.memory, hm']
    exact (E.frame.mono (by simp)).trans (T.frame.mono (by intro r hr; simp [hr]))

end VG.Proof.Dsa.AArch64.Generator
