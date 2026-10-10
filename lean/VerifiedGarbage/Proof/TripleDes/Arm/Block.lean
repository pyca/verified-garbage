import VerifiedGarbage.Proof.TripleDes.Arm.Head
import VerifiedGarbage.Proof.TripleDes.Arm.WordStore
import VerifiedGarbage.Proof.TripleDes.Word

/-! ## `Store` -/

section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction)

def storeTail (d : Direction) : List Instr :=
  [.rev .r4 .r4, .rev .r5 .r5, .str .r4 .r1 0, .str .r5 .r1 4,
    .dp (if d = .encrypt then .sub else .add) .r0 .r0
      (.imm (if d = .encrypt then 384 else 8))]

theorem storeTail_ok (d : Direction) (s : State)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (hw : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4) :
    ∃ s', runBlock isa (storeTail d) s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (s.gpr .r1))
        (byteRev64 (s.gpr .r4 ++ s.gpr .r5)) ∧
      s'.gpr .r0 = (if d = .encrypt then s.gpr .r0 - 384 else s.gpr .r0 + 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r0 → r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) := by
  have h0 : InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 0)) 4 := by
    simpa only [Nat.mul_zero] using hw 0 (by decide)
  have h1 : InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 4)) 4 := by
    simpa only [Nat.mul_one] using hw 1 (by decide)
  cases d <;> refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, storeTail, 
      runBlock_cons, runStep_some, exec, State.store32, h0, h1,
      Op2.eval, gpr_setReg, mem_setReg, wr_setReg]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false,
    rd_setReg, wr_setReg, sp_setReg]
  all_goals try
    simp only [mem_setReg, BitVec.add_zero]
    rw [addr_add (by omega_using [fit])]
    exact (writeW_pair s.mem _ _ _).trans (congrArg (s.mem.writeW _) (revPair _ _))
  all_goals
    intro r h0 h4 h5
    simp only [h0, h4, h5, ite_false]

theorem blockStore_ok (d : Direction) (s : State) (l r : BitVec 32)
    (hl : s.gpr .r10 = l) (hr : s.gpr .r11 = r)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (hw : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4) :
    ∃ s', runBlock isa (blockStore d) s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (s.gpr .r1))
        (byteRev64 (Spec.TripleDes.permute Spec.TripleDes.fp (l ++ r))) ∧
      s'.gpr .r0 = (if d = .encrypt then s.gpr .r0 - 384 else s.gpr .r0 + 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ loadKept, q ≠ .r0 → s'.gpr q = s.gpr q) := by
  obtain ⟨s₁, run₁, lo₁, hi₁, rd₁, wr₁, sp₁, mem₁, reg₁⟩ := final_raw_ok s
  rw [hl, hr] at lo₁ hi₁
  have keeps : ∀ q ∈ loadKept, s₁.gpr q = s.gpr q := by
    intro q hq
    have checks : ∀ q ∈ loadKept,
        ((instrs finalPermutation.lit).all fun op => dstOf op != some q) = true := by decide +kernel
    exact reg₁ q (checks q hq)
  have fit₁ : (s₁.gpr .r1).toNat + 8 ≤ 2 ^ 32 := by rw [keeps .r1 (by decide)]; exact fit
  have hw₁ : ∀ t < 2, InRegions s₁.wr (State.addr (s₁.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [wr₁, keeps .r1 (by decide)]; exact hw
  obtain ⟨s₂, run₂, mem₂, ptr₂, rd₂, wr₂, sp₂, reg₂⟩ := storeTail_ok d s₁ fit₁ hw₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
  · rw [blockStore, ← storeTail, runBoxes_append, run₁, Option.bind_some, run₂]
  · rw [mem₂, mem₁, keeps .r1 (by decide), hi₁, lo₁, VG.Proof.TripleDes.halves_append]
  · rw [ptr₂, keeps .r0 (by decide)]
  · intro q hq h0
    have unused : ∀ q ∈ loadKept, q ≠ .r4 ∧ q ≠ .r5 := by decide
    exact (reg₂ q h0 (unused q hq).1 (unused q hq).2).trans (keeps q hq)

end VG.Proof.TripleDes.Arm

end

/-! ## `Tail` -/

section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction)

structure TailPost (original origin : State) (d : Direction) (x : BitVec 64) (s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (State.addr (origin.gpr .r1)) =
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp x)
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  pointer : s.gpr .r0 = (if d = .encrypt then origin.gpr .r0 - 384 else origin.gpr .r0 + 8)
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [⟨State.addr (origin.gpr .r1), 8⟩] origin.mem s.mem

theorem blockTail_ok (original s : State) (d : Direction) (x : BitVec 64)
    (hword : WordState x s) (hsaved : Saved original s)
    (scratchFit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32)
    (dataFit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (hsavedRead : ∀ i < 9, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4)
    (hwrite : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4)
    (hsep : (⟨State.addr (s.gpr .r1), 8⟩ : Region).Disjoint (saveRegion s)) :
    WP isa (.block (blockStore d ++ blockRestore)) s (TailPost original s d x) := by
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, mem₁, ptr₁, rd₁, wr₁, sp₁, reg₁⟩ := blockStore_ok d s
    ((x >>> 32).setWidth 32) (x.setWidth 32) hword.left hword.right dataFit hwrite
  rw [VG.Proof.TripleDes.halves_append] at mem₁
  have regs₁ : ∀ q ∈ roundStepKept, s₁.gpr q = s.gpr q := by
    intro q hq
    have incl : ∀ q ∈ roundStepKept, q ∈ loadKept ∧ q ≠ .r0 := by decide
    exact reg₁ q (incl q hq).1 (incl q hq).2
  have frame₁ : Frame [⟨State.addr (s.gpr .r1), 8⟩] s.mem s₁.mem := by
    rw [mem₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have saved₁ : Saved original s₁ := by
    unfold Saved; rw [regs₁ .r2 (by decide)]
    exact Spill.Saved.frame hsaved slots_ok frame₁ fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hsep.sub_right (Offset.sub_base _ (by decide))).symm
  have reads₁ : ∀ i < 9, InRegions (s₁.rd ++ s₁.wr)
      (State.addr (s₁.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [rd₁, wr₁, regs₁ .r2 (by decide)]; exact hsavedRead
  apply WP.of_runBlock
  refine ⟨s₁, run₁, ?_⟩
  apply WP.mono (blockRestore_ok original s₁ saved₁
    (by rw [regs₁ .r2 (by decide)]; exact scratchFit) reads₁)
  intro s₂ hs₂
  refine ⟨?_, hs₂.saved, ?_, hs₂.keep.rd.trans rd₁, hs₂.keep.wr.trans wr₁,
    hs₂.sp.trans sp₁, ?_, ?_⟩
  · rw [hs₂.keep.mem, mem₁]
    exact blockAt_writeW s.mem _ _
  · exact (hs₂.keep.reg .r0 (by decide)).trans ptr₁
  · intro q hq
    have unused : ∀ q ∈ roundStepKept, q ∉ savedRegs := by decide
    exact (hs₂.keep.reg q (unused q hq)).trans (regs₁ q hq)
  · rw [hs₂.keep.mem]; exact frame₁

end VG.Proof.TripleDes.Arm

end

/-! ## `Block` -/

section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction Schedule)

def blockResult (keys : Schedule) (direction : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.Block :=
  match direction with
  | .encrypt => Spec.TripleDes.encryptBlock keys b
  | .decrypt => Spec.TripleDes.decryptBlock keys b

theorem blockResult_core (keys : Schedule) (direction : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp
      (blockCore (Spec.TripleDes.componentSchedule keys) direction
        (Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock b)))) =
      blockResult keys direction b := by
  cases direction
  · exact (VG.Proof.TripleDes.encryptBlock_eq_cores keys b).symm
  · exact (VG.Proof.TripleDes.decryptBlock_eq_cores keys b).symm

def blockRegions (s : State) : List Region := [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩]

structure BlockPost (keys : Schedule) (direction : Direction) (original s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (State.addr (original.gpr .r1)) =
    blockResult keys direction (Spec.TripleDes.blockAt original.mem (State.addr (original.gpr .r1)))
  pointer : s.gpr .r0 = original.gpr .r0
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = original.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = original.gpr q
  frame : Frame (blockRegions original) original.mem s.mem

theorem block_ok (keys : Schedule) (base : BitVec 32) (direction : Direction) (s : State)
    (hp : HeadPre (Spec.TripleDes.componentSchedule keys) base s)
    (hwrite : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4) :
    WP isa (block direction) s (BlockPost keys direction s) := by
  apply WP.seq
  apply WP.mono (blockHead_ok (Spec.TripleDes.componentSchedule keys) base s hp)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (blockBody_ok (Spec.TripleDes.componentSchedule keys) base s₁ _ direction ((hs₁.regs .r0 (by decide)).trans hp.pointer) hs₁.ready hs₁.word)
  intro s₂ hs₂
  have hregs₂ : ∀ q ∈ roundStepKept, s₂.gpr q = s.gpr q := by
    intro q hq
    have hkeep : ∀ r ∈ roundStepKept, r ∈ loadKept := by decide
    exact (hs₂.2.2.1.regs q hq).trans (hs₁.regs q (hkeep q hq))
  have saved₂ := hs₁.saved.congr (hs₂.2.2.1.regs .r2 (by decide)) hs₂.2.2.1.frame
  have savedRead₂ : ∀ i < 9, InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [hs₂.2.2.1.rd, hs₂.2.2.1.wr, hs₁.rd, hs₁.wr, hregs₂ .r2 (by decide)]
    exact hp.saveRead
  have hwrite₂ : ∀ t < 2, InRegions s₂.wr (State.addr (s₂.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [hs₂.2.2.1.wr, hs₁.wr, hregs₂ .r1 (by decide)]
    exact hwrite
  apply WP.mono (blockTail_ok s s₂ direction _ hs₂.1 saved₂
    (by rw [hregs₂ .r2 (by decide)]; exact hp.scratchFit)
    (by rw [hregs₂ .r1 (by decide)]; exact hp.dataFit) savedRead₂ hwrite₂
    (by rw [saveRegion, hregs₂ .r1 (by decide), hregs₂ .r2 (by decide)]; exact hp.dataSeparate))
  intro s₃ hs₃
  refine ⟨?_, ?_, hs₃.saved, hs₃.rd.trans (hs₂.2.2.1.rd.trans hs₁.rd),
    hs₃.wr.trans (hs₂.2.2.1.wr.trans hs₁.wr),
    hs₃.sp.trans (hs₂.2.2.1.sp.trans hs₁.sp),
    fun q hq => (hs₃.regs q hq).trans (hregs₂ q hq), ?_⟩
  · have hresult := hs₃.result
    rw [hregs₂ .r1 (by decide)] at hresult
    exact hresult.trans (blockResult_core keys direction _)
  · rw [hs₃.pointer, hs₂.2.2.2, hp.pointer]
    cases direction <;> simp only [reduceCtorEq, ite_true, ite_false,
      BitVec.add_sub_cancel, BitVec.sub_add_cancel]
  · have hf₁ : Frame (blockRegions s) s.mem s₁.mem := hs₁.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨State.addr (s.gpr .r2), 512⟩, by simp [blockRegions], Region.sub_prefix (by decide)⟩)
    have hf₂ : Frame (blockRegions s) s₁.mem s₂.mem := hs₂.2.2.1.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨⟨State.addr (s.gpr .r2), 512⟩, by simp [blockRegions], ?_⟩
      have hbase := hs₁.regs .r2 (by decide)
      change Region.Sub ⟨State.addr (s₁.gpr .r2) + BitVec.ofNat 64 60, 388⟩ ⟨State.addr (s.gpr .r2), 512⟩
      rw [hbase]
      exact Offset.sub_base _ (by decide))
    have hf₃ : Frame (blockRegions s) s₂.mem s₃.mem := hs₃.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      rw [hregs₂ .r1 (by decide)]
      exact ⟨⟨State.addr (s.gpr .r1), 8⟩, by simp [blockRegions], fun _ h => h⟩)
    exact hf₁.trans (hf₂.trans hf₃)

end VG.Proof.TripleDes.Arm

end
