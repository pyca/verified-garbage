import VerifiedGarbage.Proof.TripleDes.Arm.Bytes
import VerifiedGarbage.Proof.TripleDes.Arm.Initial
import VerifiedGarbage.Proof.TripleDes.Arm.Body
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rc2.Arm.Save

/-! ## `BlockIO` -/

section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm

def loadKept : List Reg := [.r0, .r1, .r2, .r3]

theorem readDataWords_ok (s : State) (offset : Nat) (ho : offset + 4 < 4096)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r1 + BitVec.ofNat 32 (offset + 4 * t))) 4) :
    ∃ s', runBlock isa [.ldr .r4 .r1 offset, .ldr .r5 .r1 (offset + 4),
        .rev .r4 .r4, .rev .r5 .r5] s = some s' ∧
      s'.gpr .r4 = rev (s.mem.readW (State.addr (s.gpr .r1 + BitVec.ofNat 32 offset)) 32) ∧
      s'.gpr .r5 = rev (s.mem.readW (State.addr (s.gpr .r1 + BitVec.ofNat 32 (offset + 4))) 32) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) := by
  have h0 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 offset)) 4 := by
    simpa only [Nat.mul_zero, Nat.add_zero] using hr 0 (by decide)
  have h1 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (offset + 4))) 4 := by
    simpa only [Nat.mul_one] using hr 1 (by decide)
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show offset < 4096 from by omega, h0, show offset + 4 < 4096 from ho, ite_true, State.load32,
      gpr_setReg, reduceCtorEq, ite_false, rd_setReg, wr_setReg, h1,
      Option.map_some, mem_setReg, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · simp only [sp_setReg]
  · intro r h4 h5; simp only [gpr_setReg, h4, h5, ite_false]


theorem blockLoad_ok (s : State)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (hread : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4) :
    ∃ s', runBlock isa blockLoad s = some s' ∧
      s'.gpr .r10 = ((Spec.TripleDes.permute Spec.TripleDes.ip
        (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1))))) >>> 32).setWidth 32 ∧
      s'.gpr .r11 = (Spec.TripleDes.permute Spec.TripleDes.ip
        (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1))))).setWidth 32 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ loadKept, s'.gpr r = s.gpr r) := by
  obtain ⟨s₁, run₁, hi₁, lo₁, mem₁, rd₁, wr₁, sp₁, reg₁⟩ := readDataWords_ok s 0 (by decide)
    (by simpa only [Nat.zero_add] using hread)
  obtain ⟨s₂, run₂, lo₂, hi₂, rd₂, wr₂, sp₂, mem₂, reg₂⟩ := initial_raw_ok s₁
  have input : s₁.gpr .r4 ++ s₁.gpr .r5 =
      Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1))) := by
    rw [hi₁, lo₁, decodeBlock_readW]
    simp only [BitVec.add_zero, Nat.zero_add]
    rw [addr_add (by omega_using [fit])]
    rfl
  rw [input] at lo₂ hi₂
  refine ⟨s₂, ?_, hi₂, lo₂, mem₂.trans mem₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_, ?_⟩
  · rw [blockLoad, runBoxes_append, run₁, Option.bind_some, run₂]
  · exact sp₂.trans sp₁
  · intro r hr
    have checks : ∀ r ∈ loadKept,
        ((instrs initialPermutation.lit).all fun op => dstOf op != some r) = true := by decide +kernel
    have unused : ∀ r ∈ loadKept, r ≠ .r4 ∧ r ≠ .r5 := by decide
    exact (reg₂ r (checks r hr)).trans (reg₁ r (unused r hr).1 (unused r hr).2)

end VG.Proof.TripleDes.Arm

end

/-! ## `Save` -/

section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (slotsOf)

theorem blockSave_eq : blockSave = (slotsOf savedRegs).map (fun p => Instr.str p.1 .r2 p.2) := by
  rw [blockSave, slotsOf, List.map_map]; rfl

theorem blockRestore_eq : blockRestore = (slotsOf savedRegs).map (fun p => Instr.ldr p.1 .r2 p.2) := by
  rw [blockRestore, slotsOf, List.map_map]; rfl

theorem slots_ok : Spill.Slots 0 36 (slotsOf savedRegs) := by decide

theorem slot_index : ∀ p ∈ slotsOf savedRegs, ∃ i < 9, p.2 = 4 * i := by decide

def Saved (original current : State) : Prop :=
  Spill.Saved current.mem (State.addr (current.gpr .r2)) original.gpr (slotsOf savedRegs)

structure SavePost (original current : State) : Prop where
  gpr : current.gpr = original.gpr
  rd : current.rd = original.rd
  wr : current.wr = original.wr
  sp : current.sp = original.sp
  saved : Saved original current
  frame : Frame [⟨State.addr (original.gpr .r2), 36⟩] original.mem current.mem

theorem blockSave_ok (s : State)
    (fit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32)
    (hw : ∀ i < 9, InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block blockSave) s (SavePost s) := by
  rw [blockSave_eq, ← List.append_nil (List.map _ _)]
  refine Spill.save_ok _ s _ (fun p hp => ?_) (WP.block_nil ⟨rfl, rfl, rfl, rfl,
    Spill.saveMem_saved _ _ _ _ slots_ok, Spill.saveMem_frame _ _ _ (by decide) _ (by decide)⟩)
  obtain ⟨i, hi, he⟩ := slot_index p hp
  exact ⟨by omega, by omega, he ▸ hw i hi⟩

structure RestorePost (original origin current : State) : Prop where
  saved : ∀ r ∈ savedRegs, current.gpr r = original.gpr r
  keep : VG.Proof.Rc2.Arm.Keep savedRegs origin current
  sp : current.sp = origin.sp

theorem blockRestore_ok (original s : State) (hsaved : Saved original s)
    (fit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32)
    (hread : ∀ i < 9, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block blockRestore) s (RestorePost original s) := by
  rw [blockRestore_eq, ← List.append_nil (List.map _ _)]
  have hregs : (slotsOf savedRegs).map Prod.fst = savedRegs := by decide
  refine Spill.restoreList_ok _ s _ (by decide) (fun p hp => ?_)
    fun s' hl ho hm hrd hwr hsp => WP.block_nil ⟨?_, ⟨fun r hr => ho r (hregs ▸ hr), hm, hrd, hwr⟩, hsp⟩
  · obtain ⟨i, hi, he⟩ := slot_index p hp
    have hne : ∀ p ∈ slotsOf savedRegs, p.1 ≠ .r2 := by decide
    exact ⟨hne p hp, by omega, by omega, he ▸ hread i hi⟩
  · exact Spill.restored_of (hsaved.restored hl) fun r hr => hregs ▸ hr

theorem Saved.congr {original s t : State} (hs : Saved original s)
    (hbase : t.gpr .r2 = s.gpr .r2) (hf : Frame [spillRegion s] s.mem t.mem) :
    Saved original t := by
  unfold Saved; rw [hbase]
  exact Spill.Saved.frame hs slots_ok hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)

end VG.Proof.TripleDes.Arm

end

/-! ## `Head` -/

section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def saveRegion (s : State) : Region := ⟨State.addr (s.gpr .r2), 36⟩

structure HeadPre (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) : Prop where
  spills : Ok sboxCfg s
  scratchFit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32
  dataFit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32
  pointer : s.gpr .r0 = base
  saveRead : ∀ i < 9, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4
  saveWrite : ∀ i < 9, InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4
  dataRead : ∀ t < 2, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4
  dataSeparate : (⟨State.addr (s.gpr .r1), 8⟩ : Region).Disjoint (saveRegion s)
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    InRegions (s.rd ++ s.wr) (wordAddr (keyAddr (componentBase base c) d j) t) 4
  separateWork : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (keyAddr (componentBase base c) d j) t, 4⟩ : Region).Disjoint (spillRegion s)
  separateSave : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (keyAddr (componentBase base c) d j) t, 4⟩ : Region).Disjoint (saveRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (readKey s.mem (keyAddr (componentBase base c) d j)).setWidth 48 = roundKey (keys c) d j

structure HeadPost (keys : Nat → DesSchedule) (base : BitVec 32) (original s : State) : Prop where
  word : WordState (Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt original.mem (State.addr (original.gpr .r1))))) s
  ready : Ready keys base s
  saved : Saved original s
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = original.sp
  regs : ∀ q ∈ loadKept, s.gpr q = original.gpr q
  frame : Frame [saveRegion original] original.mem s.mem

theorem ready_afterSave {keys : Nat → DesSchedule} {base : BitVec 32} {s t : State}
    (hp : HeadPre keys base s) (hg : t.gpr = s.gpr) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hf : Frame [saveRegion s] s.mem t.mem) : Ready keys base t := by
  have hbase : t.gpr .r2 = s.gpr .r2 := congrFun hg .r2
  refine ⟨hp.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_⟩
  · rw [hrd, hwr]; exact hp.read
  · rw [show spillRegion t = spillRegion s from
      congrArg (fun p => (⟨State.addr p + BitVec.ofNat 64 60, 388⟩ : Region)) hbase]
    exact hp.separateWork
  · intro c hc d j hj
    have hm := readKey_frame hf (ptr := keyAddr (componentBase base c) d j)
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.separateSave c hc d j hj t ht)
    exact (congrArg (BitVec.setWidth 48) hm).trans (hp.values c hc d j hj)

theorem blockHead_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State)
    (hp : HeadPre keys base s) : WP isa (.block (blockSave ++ blockLoad)) s (HeadPost keys base s) := by
  apply WP.block_append
  apply WP.mono (blockSave_ok s hp.scratchFit hp.saveWrite)
  intro s₁ hs₁
  have hready := ready_afterSave hp hs₁.gpr hs₁.rd hs₁.wr hs₁.frame
  have hread₁ : ∀ t < 2, InRegions (s₁.rd ++ s₁.wr)
      (State.addr (s₁.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [hs₁.rd, hs₁.wr, hs₁.gpr]; exact hp.dataRead
  have hdata : Spec.TripleDes.blockAt s₁.mem (State.addr (s₁.gpr .r1)) =
      Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1)) := by
    rw [hs₁.gpr]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ hs₁.frame
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.dataSeparate)
  obtain ⟨s₂, run₂, left₂, right₂, mem₂, rd₂, wr₂, sp₂, regs₂⟩ :=
    blockLoad_ok s₁ (by rw [hs₁.gpr]; exact hp.dataFit) hread₁
  have hframe : Frame [spillRegion s₁] s₁.mem s₂.mem := by
    rw [mem₂]; exact Frame.refl _ _
  have hinput := congrArg (fun b => Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock b)) hdata
  apply WP.of_runBlock
  refine ⟨s₂, run₂, ?_, hready.congr (regs₂ .r2 (by decide)) rd₂ wr₂ hframe,
    hs₁.saved.congr (regs₂ .r2 (by decide)) hframe,
    rd₂.trans hs₁.rd, wr₂.trans hs₁.wr, sp₂.trans hs₁.sp, ?_, ?_⟩
  · exact ⟨left₂.trans (congrArg (fun x : BitVec 64 => (x >>> 32).setWidth 32) hinput),
      right₂.trans (congrArg (fun x : BitVec 64 => x.setWidth 32) hinput)⟩
  · intro q hq
    exact (regs₂ q hq).trans (congrFun hs₁.gpr q)
  · rw [mem₂]; exact hs₁.frame

end VG.Proof.TripleDes.Arm

end
