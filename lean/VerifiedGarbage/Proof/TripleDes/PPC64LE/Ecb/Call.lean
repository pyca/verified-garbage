module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Ecb
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.Schedule
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ConstantTime
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.TripleDes.PPC64LE.RoundLit
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.PPC64LE.MovImm
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Word
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bytes
import VerifiedGarbage.Proof.TripleDes.Word
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Lit
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Pass
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Spills
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Block
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Permutation
import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep

/-! ### `TripleDes.PPC64LE.Block`, which this module and modules that import it used -/

section

/-! ### `TripleDes.PPC64LE.Ready`, which only this module used -/

section

/-! ### `TripleDes.PPC64LE.WordState`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE
open VG.Proof.TripleDes (desCore roundPrefix)

/-- A DES word held as two zero-extended 32-bit Feistel registers. -/
structure WordState (x : BitVec 64) (s : State) : Prop where
  left : s.gpr .r14 = ((x >>> 32).setWidth 32).setWidth 64
  right : s.gpr .r15 = (x.setWidth 32).setWidth 64

theorem PassPost.wordState {keys : Spec.TripleDes.DesSchedule}
    {direction : Spec.TripleDes.Direction} {origin s : State} {x : BitVec 64} {n : Nat}
    (hs : PassPost keys direction origin ((x >>> 32).setWidth 32, x.setWidth 32) n s) :
    WordState (desCore keys direction x) s := by
  have hcore := VG.Proof.TripleDes.desCore_roundPrefix keys direction x
  let halves := roundPrefix keys direction 16 ((x >>> 32).setWidth 32, x.setWidth 32)
  have hleft : ((desCore keys direction x >>> 32).setWidth 32).setWidth 64 = halves.2.setWidth 64 :=
    (congrArg (fun v : BitVec 64 => ((v >>> 32).setWidth 32).setWidth 64) hcore).trans
      (congrArg (BitVec.setWidth 64) (VG.Proof.TripleDes.appended_left halves.2 halves.1))
  have hright : ((desCore keys direction x).setWidth 32).setWidth 64 = halves.1.setWidth 64 :=
    (congrArg (fun v : BitVec 64 => (v.setWidth 32).setWidth 64) hcore).trans
      (congrArg (BitVec.setWidth 64) (VG.Proof.TripleDes.appended_right halves.2 halves.1))
  exact ⟨hs.left.trans hleft.symm, hs.right.trans hright.symm⟩

end VG.Proof.TripleDes.PPC64LE

end

end

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def componentBase (base : Addr) (component : Nat) : Addr :=
  base + BitVec.ofNat 64 (128 * component)

structure Ready (keys : Nat → DesSchedule) (base : Addr) (s : State) : Prop where
  scratch : Ok scratchCfg s
  consts : ConstsAt s
  baseReg : s.gpr .r3 = base
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    InRegions (s.rd ++ s.wr) (keyAddr (componentBase base c) d j) 8
  separate : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (spillRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (s.mem.readW (keyAddr (componentBase base c) d j) 64).setWidth 48 = roundKey (keys c) d j

theorem Ready.congr {keys : Nat → DesSchedule} {base : Addr} {s t : State}
    (hs : Ready keys base s) (hbase : t.gpr .r5 = s.gpr .r5)
    (hkey : t.gpr .r3 = s.gpr .r3) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame [spillRegion s] s.mem t.mem) : Ready keys base t := by
  have hwork : spillRegion t = spillRegion s :=
    congrArg (fun p => (⟨p + BitVec.ofNat 64 496, 16⟩ : Region)) hbase
  refine ⟨hs.scratch.congr hbase hbase hrd hwr, hs.consts.of_frame hbase hf, hkey.trans hs.baseReg,
    ?_, ?_, ?_⟩
  · rw [hrd, hwr]; exact hs.read
  · rw [hwork]; exact hs.separate
  · intro c hc d j hj
    have hmem := hf.readW (a := keyAddr (componentBase base c) d j) (w := 64)
      (r := ⟨keyAddr (componentBase base c) d j, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hs.separate c hc d j hj) (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hs.values c hc d j hj)

theorem passPointer (base : Addr) (c : Nat) (d : Direction) :
    base + BitVec.ofNat 64 (passOffset c d) = keyAddr (componentBase base c) d 0 := by
  cases d
  · change base + BitVec.ofNat 64 (128 * c + 0) = base + BitVec.ofNat 64 (128 * c) + (0 : BitVec 64)
    exact (congrArg (fun n => base + BitVec.ofNat 64 n) (Nat.add_zero (128 * c))).trans
      (BitVec.add_zero (base + BitVec.ofNat 64 (128 * c))).symm
  · simp only [passOffset, keyAddr, componentBase, reduceCtorEq, ite_false]
    rw [Offset.add_ofNat_add_ofNat]


structure Stable (origin s : State) : Prop where
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ passKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

theorem Stable.trans {s t u : State} (hs : Stable s t) (ht : Stable t u) : Stable s u := by
  have hwork : spillRegion t = spillRegion s :=
    congrArg (fun p => (⟨p + BitVec.ofNat 64 496, 16⟩ : Region)) (hs.regs .r5 (by decide))
  have hf := ht.frame
  rw [hwork] at hf
  exact ⟨ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun q hq => (ht.regs q hq).trans (hs.regs q hq), hs.frame.trans hf⟩

theorem pass_word_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3)
    (hready : Ready keys base s) (hword : WordState x s)
    (hpasses : s.gpr .r19 = BitVec.ofNat 64 p) :
    WP isa (pass d) s (fun t =>
      WordState (VG.Proof.TripleDes.desCore (keys (passOf d p).1) (passOf d p).2 x) t ∧
      Ready keys base t ∧ Stable s t ∧
      t.gpr .r19 = BitVec.ofNat 64 (p - 1) ∧
      isa.eval (.nonzero .d .r19) t = some (decide (p ≠ 1))) := by
  have hc := passOf_lt d p
  have hptr : s.gpr .r3 + BitVec.ofNat 64 (passOffset (passOf d p).1 (passOf d p).2) =
      keyAddr (componentBase base (passOf d p).1) (passOf d p).2 0 := by
    rw [hready.baseReg]
    exact passPointer base _ _
  apply WP.mono (pass_ok d hp (keys (passOf d p).1) (componentBase base (passOf d p).1) s
    ((x >>> 32).setWidth 32, x.setWidth 32) hready.scratch hready.consts hword.left hword.right
    hpasses hptr (hready.read _ hc _) (hready.separate _ hc _) (hready.values _ hc _))
  intro t ht
  exact ⟨ht.wordState,
    hready.congr (ht.regs .r5 (by decide)) (ht.regs .r3 (by decide)) ht.rd ht.wr ht.frame,
    ⟨ht.rd, ht.wr, ht.regs, ht.frame⟩, ht.passes, ht.zf⟩

end VG.Proof.TripleDes.PPC64LE

end

end

/-! ### `TripleDes.PPC64LE.Save`, which only this module used -/

section

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
  Offset.disjoint (s.gpr .r5) (by omega_using [hi]) (by omega_using [hi]) (by decide)

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

end

end

/-! ### `TripleDes.PPC64LE.BlockIO`, which only this module used -/

section

/-! ### `TripleDes.PPC64LE.Initial`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE
open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

theorem initial_ok (s : State) :
    ∃ s', runBlock isa (instrs initialPermutation.lit) s = some s' ∧
      s'.gpr .r8 = (Spec.TripleDes.permute Spec.TripleDes.ip
        ((s.gpr .r7).setWidth 64)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) :=
  fixedPermutation_ok Spec.TripleDes.ip (by decide) (by decide)
    VG.Proof.TripleDes.ip_bounds .r7 .r8 (instrs initialPermutation.lit) initialPermutation_check s
end VG.Proof.TripleDes.PPC64LE
namespace VG.Proof.TripleDes.PPC64LE
open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

theorem initial_raw_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.ip 64 .r8 .r7 .r9 .r10) s = some s' ∧
      s'.gpr .r8 = Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .r7) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, mem, regs⟩ := initial_ok s
  have hcode : permuteCode Spec.TripleDes.ip 64 .r8 .r7 .r9 .r10 =
      instrs initialPermutation.lit := congrArg instrs initialPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, mem, regs⟩
  exact word.trans ((BitVec.setWidth_eq _).trans
    (congrArg (Spec.TripleDes.permute Spec.TripleDes.ip) (BitVec.setWidth_eq _)))
end VG.Proof.TripleDes.PPC64LE

namespace VG.Proof.TripleDes.PPC64LE
open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE
theorem final_ok (s : State) :
    ∃ s', runBlock isa (instrs finalPermutation.lit) s = some s' ∧
      s'.gpr .r8 = (Spec.TripleDes.permute Spec.TripleDes.fp
        ((s.gpr .r6).setWidth 64)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) :=
  fixedPermutation_ok Spec.TripleDes.fp (by decide) (by decide)
    VG.Proof.TripleDes.fp_bounds .r6 .r8 (instrs finalPermutation.lit) finalPermutation_check s

theorem final_raw_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.fp 64 .r8 .r6 .r9 .r10) s = some s' ∧
      s'.gpr .r8 = Spec.TripleDes.permute Spec.TripleDes.fp (s.gpr .r6) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, mem, regs⟩ := final_ok s
  have hcode : permuteCode Spec.TripleDes.fp 64 .r8 .r6 .r9 .r10 =
      instrs finalPermutation.lit := congrArg instrs finalPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, mem, regs⟩
  exact word.trans ((BitVec.setWidth_eq _).trans
    (congrArg (Spec.TripleDes.permute Spec.TripleDes.fp) (BitVec.setWidth_eq _)))

end VG.Proof.TripleDes.PPC64LE

end

end

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

/-- The registers the block's load and store keep. -/
def loadKept : List Reg := passKept

theorem readData_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .r4) 8) :
    ∃ s', runBlock isa [.li .r6 0, .loadRev .d .r7 .r4 .r6] s = some s' ∧
      s'.gpr .r7 = Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .r4)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r6 → r ≠ .r7 → s'.gpr r = s.gpr r) := by
  let s₁ := s.write .r6 (BitVec.ofNat 64 0)
  have ha : s₁.gpr .r4 + s₁.gpr .r6 = s.gpr .r4 := by
    simp only [s₁, gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.add_zero]
  have hload := exec_loadRev_d (s := s₁) (t := .r7) (a := .r4) (b := .r6) (by decide)
    (by rw [ha]; exact hread)
  rw [ha] at hload
  let s₂ := s₁.write .r7 (rev64 (s₁.mem.readW (s.gpr .r4) 64))
  refine ⟨s₂, by
    rw [runBlock_cons, exec_li (by decide), runStep_some, runBlock_cons, hload, runStep_some,
      runBlock_nil], ?_, rfl, rfl, rfl, ?_⟩
  · rw [gpr_write_self]
    exact (decodeBlock_readW s.mem (s.gpr .r4)).symm
  · intro r h6 h7
    simp only [s₂, s₁, gpr_write, h6, h7, ite_false]

theorem rotateRight_zero32 (x : BitVec 32) : x.rotateRight 0 = x := by
  simp [BitVec.rotateRight, BitVec.rotateRightAux]

def splitHalves : List Instr := [.lsr .d .r14 .r8 32, .rotr .w .r15 .r8 0]

theorem splitHalves_ok (s : State) :
    ∃ s', runBlock isa splitHalves s = some s' ∧
      s'.gpr .r14 = s.gpr .r8 >>> 32 ∧
      s'.gpr .r15 = ((s.gpr .r8).setWidth 32).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) := by
  let s₁ := s.write .r14 (s.gpr .r8 >>> 32)
  let s₂ := s₁.write .r15 (((s₁.gpr .r8).setWidth 32).rotateRight 0 |>.setWidth 64)
  refine ⟨s₂, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · rw [splitHalves, runBlock_cons, exec_lsr_d (by decide), runStep_some, runBlock_cons,
      exec_rotr_w (by decide), runStep_some, runBlock_nil]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false, rotateRight_zero32]
  · intro r h14 h15
    simp only [s₂, s₁, gpr_write, h14, h15, ite_false]

theorem upperHalf_extend (x : BitVec 64) :
    x >>> 32 = ((x >>> 32).setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h : j < 32
  · simp only [h, hj, decide_true, Bool.true_and]
  · have hz : x.getLsbD (32 + j) = false := BitVec.getLsbD_of_ge _ _ (by omega_using [h])
    simp only [h, hj, decide_false, decide_true, Bool.false_and, Bool.true_and, hz]

theorem runAppend_some (xs ys : List Instr) (s t u : State)
    (hx : runBlock isa xs s = some t) (hy : runBlock isa ys t = some u) :
    runBlock isa (xs ++ ys) s = some u := by
  calc
    runBlock isa (xs ++ ys) s = (runBlock isa xs s).bind (runBlock isa ys) :=
      runBoxes_append xs ys s
    _ = (some t).bind (runBlock isa ys) := congrArg (fun v => v.bind (runBlock isa ys)) hx
    _ = runBlock isa ys t := Option.bind_some t (runBlock isa ys)
    _ = some u := hy

theorem initial_preserves : loadKept.all (fun r =>
    (instrs initialPermutation.lit).all (fun op => dstOf op != some r)) = true := by
  decide +kernel

theorem blockLoad_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .r4) 8) :
    ∃ s', runBlock isa blockLoad s = some s' ∧
      s'.gpr .r14 =
        (((Spec.TripleDes.permute Spec.TripleDes.ip
          (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .r4)))) >>> 32).setWidth 32).setWidth 64 ∧
      s'.gpr .r15 =
        ((Spec.TripleDes.permute Spec.TripleDes.ip
          (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .r4)))).setWidth 32).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ loadKept, s'.gpr r = s.gpr r) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, regs₁⟩ := readData_ok s hread
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, mem₂, regs₂⟩ := initial_raw_ok s₁
  obtain ⟨s₃, run₃, left₃, right₃, mem₃, rd₃, wr₃, regs₃⟩ := splitHalves_ok s₂
  have hword : s₂.gpr .r8 = Spec.TripleDes.permute Spec.TripleDes.ip
      (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .r4))) :=
    word₂.trans (congrArg (Spec.TripleDes.permute Spec.TripleDes.ip) word₁)
  have hhead := runAppend_some _ _ _ _ _ run₁ run₂
  have htail := runAppend_some _ _ _ _ _ hhead run₃
  have hcode : blockLoad =
      (([.li .r6 0, .loadRev .d .r7 .r4 .r6] : List Instr) ++
        permuteCode Spec.TripleDes.ip 64 .r8 .r7 .r9 .r10) ++ splitHalves := by
    simp only [blockLoad, splitHalves, List.append_assoc]
  refine ⟨s₃, (congrArg (fun is => runBlock isa is s) hcode).trans htail, ?_, ?_,
    mem₃.trans (mem₂.trans mem₁), rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), ?_⟩
  · exact left₃.trans ((congrArg (fun x : BitVec 64 => x >>> 32) hword).trans (upperHalf_extend _))
  · exact right₃.trans (congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) hword)
  · intro r hr
    have hno := List.all_eq_true.mp initial_preserves r hr
    have hne : r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r14 ∧ r ≠ .r15 := by
      clear hno; revert hr; cases r <;> decide
    exact (regs₃ r hne.2.2.1 hne.2.2.2).trans ((regs₂ r hno).trans (regs₁ r hne.1 hne.2.1))

end VG.Proof.TripleDes.PPC64LE

end

end

/-! ### `TripleDes.PPC64LE.Head`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

/-- Slots 0–61 of the scratch buffer: the saved registers and the constants. -/
def saveRegion (s : State) : Region := ⟨s.gpr .r5, 496⟩

structure HeadPre (keys : Nat → DesSchedule) (base : Addr) (s : State) : Prop where
  scratch : Ok scratchCfg s
  pointer : s.gpr .r3 = base
  saveRead : ∀ i < 15, InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8
  saveWrite : ∀ i < 62, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8
  dataRead : InRegions (s.rd ++ s.wr) (s.gpr .r4) 8
  dataSeparate : (⟨s.gpr .r4, 8⟩ : Region).Disjoint (saveRegion s)
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    InRegions (s.rd ++ s.wr) (keyAddr (componentBase base c) d j) 8
  separateWork : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (spillRegion s)
  separateSave : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (saveRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (s.mem.readW (keyAddr (componentBase base c) d j) 64).setWidth 48 = roundKey (keys c) d j

structure HeadPost (keys : Nat → DesSchedule) (base : Addr) (original s : State) : Prop where
  word : WordState (Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt original.mem (original.gpr .r4)))) s
  ready : Ready keys base s
  saved : Saved original s
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  regs : ∀ q ∈ loadKept, s.gpr q = original.gpr q
  frame : Frame [saveRegion original] original.mem s.mem

/-! ## The constants -/

theorem movImm64_ok (d : Reg) (v : BitVec 64) (s : State) :
    ∃ s', runBlock isa (movImm64 d v) s = some s' ∧ s'.gpr d = v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [movImm64, runBlock_cons, exec_lis, runStep_some, runBlock_cons, exec_ori, runStep_some,
    runBlock_cons, exec_lsl (by decide), runStep_some, runBlock_cons, exec_oris, runStep_some,
    runBlock_cons, exec_ori, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [gpr_write_self]
    exact movImm64_eq v
  · simp [gpr_write, hr]

/-- The memory `m` with the words `vs` written at `B + off` on. -/
def constMem (m : Mem) (B : Addr) : List (BitVec 64) → Nat → Mem
  | [], _ => m
  | v :: vs, off => constMem (m.writeW (B + BitVec.ofNat 64 off) v) B vs (off + 8)

theorem constMem_frame (B : Addr) (vs : List (BitVec 64)) :
    ∀ (m : Mem) (off : Nat), off + 8 * vs.length ≤ 2048 →
      Frame [⟨B + BitVec.ofNat 64 off, 8 * vs.length⟩] m (constMem m B vs off) := by
  induction vs with
  | nil => intro m off _; exact Frame.refl _ _
  | cons v vs ih =>
    intro m off h
    simp only [List.length_cons] at h
    have h1 : Frame [⟨B + BitVec.ofNat 64 off, 8 * (vs.length + 1)⟩] m
        (m.writeW (B + BitVec.ofNat 64 off) v) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) v (by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [])
    have h2 := ih (m.writeW (B + BitVec.ofNat 64 off) v) (off + 8) (by omega_using [h])
    refine h1.trans (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.sub B (by omega_using []) (by omega_using [])

theorem constMem_read (B : Addr) (vs : List (BitVec 64)) :
    ∀ (m : Mem) (off : Nat), off + 8 * vs.length ≤ 2048 → ∀ c < vs.length,
      (constMem m B vs off).readW (B + BitVec.ofNat 64 (off + 8 * c)) 64 = vs.getD c 0 := by
  induction vs with
  | nil => intro _ _ _ c hc; simp at hc
  | cons v vs ih =>
    intro m off h c hc
    simp only [List.length_cons] at h hc
    rcases c with _ | c
    · have hf := constMem_frame B vs (m.writeW (B + BitVec.ofNat 64 off) v) (off + 8) (by omega_using [h])
      simp only [constMem, Nat.mul_zero, Nat.add_zero, List.getD_cons_zero]
      rw [hf.readW (r := ⟨B + BitVec.ofNat 64 off, 8⟩) (Region.contains_self _ _) (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact Offset.disjoint B (Or.inl (Nat.le_refl _)) (by omega_using [h]) (by omega_using [h])) (by decide),
        Mem.readW_writeW_self64]
    · simp only [constMem, List.getD_cons_succ]
      rw [show off + 8 * (c + 1) = off + 8 + 8 * c by omega_using []]
      exact ih _ (off + 8) (by omega_using [h]) c (by omega_using [hc])

theorem storeConsts_wp (vs : List (BitVec 64)) :
    ∀ (off : Nat) (s : State) (Q : State → Prop), off % 8 = 0 → off + 8 * vs.length ≤ 2048 →
      (∀ c < vs.length, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (off + 8 * c)) 8) →
      (∀ t : State, t.mem = constMem s.mem (s.gpr .r5) vs off → t.rd = s.rd → t.wr = s.wr →
        (∀ r, r ≠ .r6 → t.gpr r = s.gpr r) → Q t) →
      WP isa (.block (storeConsts vs off)) s Q := by
  induction vs with
  | nil =>
    intro off s Q _ _ _ hQ
    exact WP.block_nil (hQ s rfl rfl rfl fun _ _ => rfl)
  | cons v vs ih =>
    intro off s Q hoff hlim hin hQ
    simp only [List.length_cons] at hlim
    rw [storeConsts, WP.block_append_iff, WP.block_append_iff]
    obtain ⟨s₁, run₁, d₁, o₁, m₁, rd₁, wr₁⟩ := movImm64_ok t0 v s
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have hb₁ : s₁.gpr .r5 = s.gpr .r5 := o₁ _ (by decide)
    let s₂ : State := { s₁ with mem := s₁.mem.writeW (s₁.gpr .r5 + BitVec.ofNat 64 off) (s₁.gpr t0) }
    refine WP.of_runBlock ⟨s₂, ?_, ?_⟩
    · have h0 := hin 0 (by simp)
      simp only [Nat.mul_zero, Nat.add_zero] at h0
      show runBlock isa [.store .d t0 .r5 off] s₁ = some s₂
      rw [runBlock_cons, exec_store_d (by decide) ⟨by omega_using [hlim], by omega_using [hoff]⟩ (by rw [hb₁, wr₁]; exact h0),
        runStep_some, runBlock_nil]
    · have hb₂ : s₂.gpr .r5 = s.gpr .r5 := hb₁
      refine ih (off + 8) s₂ Q (by omega_using [hoff]) (by omega_using [hlim]) (fun c hc => ?_)
        fun t hm hrd hwr hg => hQ t ?_ (hrd.trans rd₁) (hwr.trans wr₁) fun r h0 => ?_
      · rw [hb₂, show off + 8 + 8 * c = off + 8 * (c + 1) by omega_using []]
        exact wr₁ ▸ hin (c + 1) (by simp only [List.length_cons]; omega_using [hc])
      · rw [hm, hb₂]
        show constMem (s₁.mem.writeW (s₁.gpr .r5 + BitVec.ofNat 64 off) (s₁.gpr t0)) _ vs (off + 8) = _
        rw [hb₁, d₁, m₁]; rfl
      · exact (hg r h0).trans (o₁ r h0)

/-! ## The head -/

theorem roundConsts_length : roundConsts.length = 47 := by
  rw [roundConsts.lit_eq]; decide +kernel

/-- The constants fit the scratch buffer, by their number: `decide` on it would evaluate them. -/
theorem consts_fit : constOff + 8 * roundConsts.length ≤ 2048 := by
  rw [roundConsts_length]; decide

theorem consts_ready {s t : State} (hb : t.gpr .r5 = s.gpr .r5)
    (hm : t.mem = constMem s.mem (s.gpr .r5) roundConsts constOff) : ConstsAt t := by
  intro c hc
  rw [hm, hb, wordAddr, show 8 * (15 + c) = constOff + 8 * c by unfold constOff; omega_using []]
  exact constMem_read _ _ _ _ consts_fit c (by rw [roundConsts_length]; exact hc)

theorem consts_frame (s : State) :
    Frame [saveRegion s] s.mem (constMem s.mem (s.gpr .r5) roundConsts constOff) :=
  (constMem_frame _ _ _ _ consts_fit).sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, by
      rw [roundConsts_length]; exact Offset.sub_base _ (by decide)⟩

theorem consts_saved {original s t : State} (hs : Saved original s) (hb : t.gpr .r5 = s.gpr .r5)
    (hm : t.mem = constMem s.mem (s.gpr .r5) roundConsts constOff) : Saved original t := by
  intro i hi
  rw [hm, hb, ← hs i hi]
  exact (constMem_frame _ _ _ _ consts_fit).readW (r := ⟨s.gpr .r5 + BitVec.ofNat 64 (8 * i), 8⟩)
    (Region.contains_self _ _) (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq
      rw [roundConsts_length]
      exact Offset.disjoint _ (Or.inl (by unfold constOff; omega_using [hi])) (by omega_using [hi]) (by decide)) (by decide)

theorem ready_afterSave {keys : Nat → DesSchedule} {base : Addr} {s t : State}
    (hp : HeadPre keys base s) (hb : t.gpr .r5 = s.gpr .r5) (hkey : t.gpr .r3 = s.gpr .r3)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hc : ConstsAt t) (hf : Frame [saveRegion s] s.mem t.mem) :
    Ready keys base t := by
  refine ⟨hp.scratch.congr hb hb hrd hwr, hc, hkey.trans hp.pointer, ?_, ?_, ?_⟩
  · rw [hrd, hwr]; exact hp.read
  · rw [show spillRegion t = spillRegion s from
      congrArg (fun p => (⟨p + BitVec.ofNat 64 496, 16⟩ : Region)) hb]
    exact hp.separateWork
  · intro c hc d j hj
    have hmem := hf.readW (a := keyAddr (componentBase base c) d j) (w := 64)
      (r := ⟨keyAddr (componentBase base c) d j, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.separateSave c hc d j hj)
      (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hp.values c hc d j hj)

theorem blockHead_ok (keys : Nat → DesSchedule) (base : Addr) (s : State)
    (hp : HeadPre keys base s) :
    WP isa (.block (blockSave ++ storeConsts roundConsts constOff ++ blockLoad)) s
      (HeadPost keys base s) := by
  rw [WP.block_append_iff, WP.block_append_iff]
  apply WP.mono (blockSave_ok s fun i hi => hp.saveWrite i (by omega_using [hi]))
  intro s₁ hs₁
  have hb₁ : s₁.gpr .r5 = s.gpr .r5 := congrFun hs₁.gpr .r5
  refine storeConsts_wp roundConsts constOff s₁ _ (by decide) (by rw [roundConsts_length]; decide)
    (fun c hc => by
      rw [hs₁.wr, hb₁, show constOff + 8 * c = 8 * (15 + c) by unfold constOff; omega_using []]
      exact hp.saveWrite _ (by rw [roundConsts_length] at hc; omega_using [hc])) ?_
  intro s₂ m₂ rd₂ wr₂ g₂
  have hb₂ : s₂.gpr .r5 = s₁.gpr .r5 := g₂ _ (by decide)
  have hframe₂ : Frame [saveRegion s] s.mem s₂.mem := by
    refine hs₁.frame.sub (fun r hr => ?_) |>.trans ?_
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · rw [m₂, show saveRegion s = saveRegion s₁ by simp only [saveRegion, hb₁]]
      exact consts_frame s₁
  have hready := ready_afterSave hp (hb₂.trans hb₁) ((g₂ _ (by decide)).trans (congrFun hs₁.gpr .r3))
    (rd₂.trans hs₁.rd) (wr₂.trans hs₁.wr) (consts_ready hb₂ m₂) hframe₂
  have hsaved₂ := consts_saved hs₁.saved hb₂ m₂
  have hread₂ : InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .r4) 8 := by
    rw [rd₂, wr₂, hs₁.rd, hs₁.wr, g₂ _ (by decide), hs₁.gpr]; exact hp.dataRead
  have hdata : Spec.TripleDes.blockAt s₂.mem (s₂.gpr .r4) =
      Spec.TripleDes.blockAt s.mem (s.gpr .r4) := by
    rw [g₂ _ (by decide), hs₁.gpr]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ hframe₂
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.dataSeparate)
  obtain ⟨s₃, run₃, left₃, right₃, mem₃, rd₃, wr₃, regs₃⟩ := blockLoad_ok s₂ hread₂
  have hframe : Frame [spillRegion s₂] s₂.mem s₃.mem := by
    rw [mem₃]; exact Frame.refl _ _
  have hinput := congrArg (fun b => Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock b)) hdata
  apply WP.of_runBlock
  refine ⟨s₃, run₃, ?_, hready.congr (regs₃ .r5 (by decide)) (regs₃ .r3 (by decide)) rd₃ wr₃ hframe,
    ?_, rd₃.trans (rd₂.trans hs₁.rd), wr₃.trans (wr₂.trans hs₁.wr), ?_, ?_⟩
  · exact ⟨left₃.trans (congrArg (fun x : BitVec 64 => ((x >>> 32).setWidth 32).setWidth 64) hinput),
      right₃.trans (congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) hinput)⟩
  · intro i hi
    rw [regs₃ .r5 (by decide), mem₃]
    exact hsaved₂ i hi
  · intro q hq
    have hne : q ≠ .r6 := by revert hq; decide +revert
    exact (regs₃ q hq).trans ((g₂ q hne).trans (congrFun hs₁.gpr q))
  · rw [mem₃]; exact hframe₂

end VG.Proof.TripleDes.PPC64LE

end

end

/-! ### `TripleDes.PPC64LE.Body`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (desCore)

/-- The word after the first `k` passes of the block. -/
def passesDone (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) :
    Nat → BitVec 64
  | 0 => x
  | k + 1 => desCore (keys (passOf direction (3 - k)).1) (passOf direction (3 - k)).2
      (passesDone keys direction x k)

def blockCore (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) : BitVec 64 :=
  match direction with
  | .encrypt => desCore (keys 2) .encrypt (desCore (keys 1) .decrypt (desCore (keys 0) .encrypt x))
  | .decrypt => desCore (keys 0) .decrypt (desCore (keys 1) .encrypt (desCore (keys 2) .decrypt x))

theorem blockCore_passesDone (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) :
    blockCore keys direction x = passesDone keys direction x 3 := by
  cases direction <;> rfl

/-- The loop's invariant, with `m` passes left. -/
structure BodyInv (keys : Nat → DesSchedule) (base : Addr) (direction : Direction)
    (x : BitVec 64) (origin : State) (m : Nat) (s : State) : Prop where
  pos : 1 ≤ m
  le : m ≤ 3
  passes : s.gpr .r19 = BitVec.ofNat 64 m
  word : WordState (passesDone keys direction x (3 - m)) s
  ready : Ready keys base s
  stable : Stable origin s

theorem blockBody_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (direction : Direction) (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (blockBody direction) s
      (fun t => WordState (blockCore keys direction x) t ∧ Ready keys base t ∧ Stable s t) := by
  let s₁ := s.write .r19 (BitVec.ofNat 64 3)
  have hregs : ∀ r, r ≠ .r19 → s₁.gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ h
  have hframe : Frame [spillRegion s] s.mem s₁.mem := Frame.refl _ _
  have hstable : Stable s s₁ := ⟨rfl, rfl,
    fun q hq => hregs q (by revert hq; cases q <;> decide), hframe⟩
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · rw [runBlock_cons, imm, exec_li (by decide), runStep_some, runBlock_nil]
  refine WP.loop (M := isa) (BodyInv keys base direction x s) ?_ 3 s₁
    ⟨by decide, by decide, gpr_write_self _ _ _, ?_,
      hready.congr (hregs .r5 (by decide)) (hregs .r3 (by decide)) rfl rfl hframe, hstable⟩
  · rintro m t ⟨hpos, hle, hpasses, hw, hr, hst⟩
    refine WP.mono (pass_word_ok keys base t _ direction ⟨hpos, hle⟩ hr hw hpasses)
      fun u ⟨hwu, hru, hsu, hpu, hzu⟩ => ?_
    have hdone : desCore (keys (passOf direction m).1) (passOf direction m).2
        (passesDone keys direction x (3 - m)) = passesDone keys direction x (3 - (m - 1)) := by
      rw [show 3 - (m - 1) = 3 - m + 1 by omega_using [hpos, hle], passesDone, show 3 - (3 - m) = m by omega_using [hle]]
    rw [hdone] at hwu
    by_cases hlast : m = 1
    · subst m
      refine Or.inl ⟨by rw [hzu]; rfl, ?_, hru, hst.trans hsu⟩
      rw [blockCore_passesDone]
      exact hwu
    · refine Or.inr ⟨by rw [hzu]; simp [hlast], m - 1, by omega_using [hpos],
        ⟨by omega_using [hpos, hlast], by omega_using [hle], hpu, hwu, hru, hst.trans hsu⟩⟩
  · exact ⟨(hregs .r14 (by decide)).trans hword.left, (hregs .r15 (by decide)).trans hword.right⟩

end VG.Proof.TripleDes.PPC64LE

end

end

/-! ### `TripleDes.PPC64LE.Tail`, which only this module used -/

section

/-! ### `TripleDes.PPC64LE.Store`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

def packHalves : List Instr := [.rotr .d .r6 .r14 32, .logic .xor .r6 .r6 .r15]

theorem rotateRight_extend (l : BitVec 32) :
    (l.setWidth 64).rotateRight 32 = l.setWidth 64 <<< 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j < 32
  · simp [h, hj]
  · simp [h, hj]

theorem packHalves_ok (s : State) (l r : BitVec 32)
    (hl : s.gpr .r14 = l.setWidth 64) (hr : s.gpr .r15 = r.setWidth 64) :
    ∃ s', runBlock isa packHalves s = some s' ∧
      s'.gpr .r6 = l ++ r ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q, q ≠ .r6 → s'.gpr q = s.gpr q) := by
  let s₁ := s.write .r6 ((s.gpr .r14).rotateRight 32)
  let s₂ := s₁.write .r6 (s₁.gpr .r6 ^^^ s₁.gpr .r15)
  refine ⟨s₂, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · rw [packHalves, runBlock_cons, exec_rotr_d (by decide), runStep_some, runBlock_cons,
      exec_logic, runStep_some, runBlock_nil]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false, hl, hr,
      rotateRight_extend]
    exact packHalves_shift l r
  · intro q hq
    simp only [s₂, s₁, gpr_write, hq, ite_false]

theorem final_preserves : loadKept.all (fun r =>
    (instrs finalPermutation.lit).all (fun op => dstOf op != some r)) = true := by
  decide +kernel

theorem writeData_ok (s : State) (hwrite : InRegions s.wr (s.gpr .r4) 8) :
    ∃ s', runBlock isa [.li .r7 0, .storeRev .d .r8 .r4 .r7] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r4) (rev64 (s.gpr .r8)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q, q ≠ .r7 → s'.gpr q = s.gpr q) := by
  let s₁ := s.write .r7 (BitVec.ofNat 64 0)
  have ha : s₁.gpr .r4 + s₁.gpr .r7 = s.gpr .r4 := by
    simp only [s₁, gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.add_zero]
  have hstore := exec_storeRev_d (s := s₁) (t := .r8) (a := .r4) (b := .r7) (by decide)
    (by rw [ha]; exact hwrite)
  rw [ha] at hstore
  refine ⟨{ s₁ with mem := s₁.mem.writeW (s.gpr .r4) (rev64 (s₁.gpr .r8)) }, by
    rw [runBlock_cons, exec_li (by decide), runStep_some, runBlock_cons, hstore, runStep_some,
      runBlock_nil], ?_, rfl, rfl, ?_⟩
  · change s.mem.writeW (s.gpr .r4) (rev64 (s₁.gpr .r8)) = _
    rw [show s₁.gpr .r8 = s.gpr .r8 from gpr_write_of_ne _ _ (by decide)]
  · intro q hq
    exact gpr_write_of_ne _ _ hq

theorem blockStore_ok (s : State) (l r : BitVec 32)
    (hl : s.gpr .r14 = l.setWidth 64) (hr : s.gpr .r15 = r.setWidth 64)
    (hwrite : InRegions s.wr (s.gpr .r4) 8) :
    ∃ s', runBlock isa blockStore s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r4)
        (rev64 (Spec.TripleDes.permute Spec.TripleDes.fp (l ++ r))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ loadKept, s'.gpr q = s.gpr q) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, regs₁⟩ := packHalves_ok s l r hl hr
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, mem₂, regs₂⟩ := final_raw_ok s₁
  have r4₁ : s₁.gpr .r4 = s.gpr .r4 := regs₁ .r4 (by decide)
  have r4₂ : s₂.gpr .r4 = s.gpr .r4 :=
    (regs₂ .r4 (List.all_eq_true.mp final_preserves .r4 (by decide))).trans r4₁
  obtain ⟨s₃, run₃, mem₃, rd₃, wr₃, regs₃⟩ := writeData_ok s₂ (by
    rw [r4₂, wr₂, wr₁]; exact hwrite)
  have hhead := runAppend_some _ _ _ _ _ run₁ run₂
  have htail := runAppend_some _ _ _ _ _ hhead run₃
  have hcode : blockStore =
      (packHalves ++ permuteCode Spec.TripleDes.fp 64 .r8 .r6 .r9 .r10) ++
      ([.li .r7 0, .storeRev .d .r8 .r4 .r7] : List Instr) := rfl
  refine ⟨s₃, (congrArg (fun is => runBlock isa is s) hcode).trans htail, ?_,
    rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_⟩
  · rw [mem₃, mem₂, mem₁, r4₂, word₂, word₁]
  · intro q hq
    have hno := List.all_eq_true.mp final_preserves q hq
    have hne : q ≠ .r6 ∧ q ≠ .r7 := by clear hno; revert hq; cases q <;> decide
    exact (regs₃ q hne.2).trans ((regs₂ q hno).trans (regs₁ q hne.1))

end VG.Proof.TripleDes.PPC64LE

end

end


@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

structure TailPost (original origin : State) (x : BitVec 64) (s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (origin.gpr .r4) =
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp x)
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ loadKept, s.gpr q = origin.gpr q
  frame : Frame [⟨origin.gpr .r4, 8⟩] origin.mem s.mem

theorem blockTail_ok (original s : State) (x : BitVec 64)
    (hword : WordState x s) (hsaved : Saved original s)
    (hsavedRead : ∀ i < 15, InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8)
    (hwrite : InRegions s.wr (s.gpr .r4) 8)
    (hsep : (⟨s.gpr .r4, 8⟩ : Region).Disjoint ⟨s.gpr .r5, 120⟩) :
    WP isa (.block (blockStore ++ blockRestore)) s (TailPost original s x) := by
  obtain ⟨s₁, run₁, mem₁, rd₁, wr₁, regs₁⟩ :=
    blockStore_ok s ((x >>> 32).setWidth 32) (x.setWidth 32) hword.left hword.right hwrite
  have hframe₁ : Frame [⟨s.gpr .r4, 8⟩] s.mem s₁.mem := by
    rw [mem₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have saved₁ : Saved original s₁ := by
    intro i hi
    rw [regs₁ .r5 (by decide)]
    refine (hframe₁.readW (r := ⟨s.gpr .r5 + BitVec.ofNat 64 (8 * i), 8⟩)
      (Region.contains_self _ _) (fun q hq => ?_) (by decide)).trans (hsaved i hi)
    obtain rfl := List.mem_singleton.mp hq
    exact (hsep.sub_right (Offset.sub_base _ (by omega_using [hi]))).symm
  have savedRead₁ : ∀ i < 15, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [rd₁, wr₁, regs₁ .r5 (by decide)]
    exact hsavedRead
  apply WP.block_append
  apply WP.of_runBlock
  refine ⟨s₁, run₁, ?_⟩
  apply WP.mono (blockRestore_ok original s₁ saved₁ savedRead₁)
  intro s₂ hs₂
  have hregs₂ : ∀ q ∈ loadKept, s₂.gpr q = s.gpr q := by
    intro q hq
    have hn : q ∉ savedRegs := by revert hq; cases q <;> decide
    exact (hs₂.keep.gpr hn).trans (regs₁ q hq)
  refine ⟨?_, hs₂.saved, hs₂.keep.2.1.trans rd₁, hs₂.keep.2.2.trans wr₁, hregs₂, ?_⟩
  · rw [hs₂.mem, mem₁, VG.Proof.TripleDes.halves_append x]
    exact blockAt_writeW s.mem (s.gpr .r4) (Spec.TripleDes.permute Spec.TripleDes.fp x)
  · rw [hs₂.mem]; exact hframe₁

end VG.Proof.TripleDes.PPC64LE

end

end


@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE
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

def blockRegions (s : State) : List Region := [⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩]

structure BlockPost (keys : Schedule) (direction : Direction) (original s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (original.gpr .r4) =
    blockResult keys direction (Spec.TripleDes.blockAt original.mem (original.gpr .r4))
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  regs : ∀ q ∈ loadKept, s.gpr q = original.gpr q
  frame : Frame (blockRegions original) original.mem s.mem

theorem block_ok (keys : Schedule) (base : Addr) (direction : Direction) (s : State)
    (hp : HeadPre (Spec.TripleDes.componentSchedule keys) base s)
    (hwrite : InRegions s.wr (s.gpr .r4) 8) :
    WP isa (block direction) s (BlockPost keys direction s) := by
  apply WP.seq
  apply WP.mono (blockHead_ok (Spec.TripleDes.componentSchedule keys) base s hp)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (blockBody_ok (Spec.TripleDes.componentSchedule keys) base s₁ _ direction hs₁.ready hs₁.word)
  intro s₂ hs₂
  have hregs₂ : ∀ q ∈ loadKept, s₂.gpr q = s.gpr q := by
    intro q hq
    exact (hs₂.2.2.regs q hq).trans (hs₁.regs q hq)
  have saved₂ := hs₁.saved.congr (hs₂.2.2.regs .r5 (by decide)) hs₂.2.2.frame
  have savedRead₂ : ∀ i < 15, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [hs₂.2.2.rd, hs₂.2.2.wr, hs₁.rd, hs₁.wr, hregs₂ .r5 (by decide)]
    exact hp.saveRead
  have hwrite₂ : InRegions s₂.wr (s₂.gpr .r4) 8 := by
    rw [hs₂.2.2.wr, hs₁.wr, hregs₂ .r4 (by decide)]
    exact hwrite
  have hsep₂ : (⟨s₂.gpr .r4, 8⟩ : Region).Disjoint ⟨s₂.gpr .r5, 120⟩ := by
    rw [hregs₂ .r4 (by decide), hregs₂ .r5 (by decide)]
    exact hp.dataSeparate.sub_right (Region.sub_prefix (by decide))
  apply WP.mono (blockTail_ok s s₂ _ hs₂.1 saved₂ savedRead₂ hwrite₂ hsep₂)
  intro s₃ hs₃
  refine ⟨?_, hs₃.saved, hs₃.rd.trans (hs₂.2.2.rd.trans hs₁.rd),
    hs₃.wr.trans (hs₂.2.2.wr.trans hs₁.wr),
    fun q hq => (hs₃.regs q hq).trans (hregs₂ q hq), ?_⟩
  · have hresult := hs₃.result
    rw [hregs₂ .r4 (by decide)] at hresult
    exact hresult.trans (blockResult_core keys direction _)
  · have hf₁ : Frame (blockRegions s) s.mem s₁.mem := hs₁.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨s.gpr .r5, 512⟩, by simp [blockRegions], Region.sub_prefix (by decide)⟩)
    have hf₂ : Frame (blockRegions s) s₁.mem s₂.mem := hs₂.2.2.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨⟨s.gpr .r5, 512⟩, by simp [blockRegions], ?_⟩
      have hbase := hs₁.regs .r5 (by decide)
      change Region.Sub ⟨s₁.gpr .r5 + BitVec.ofNat 64 496, 16⟩ ⟨s.gpr .r5, 512⟩
      rw [hbase]
      exact Offset.sub_base _ (by decide))
    have hf₃ : Frame (blockRegions s) s₂.mem s₃.mem := hs₃.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      rw [hregs₂ .r4 (by decide)]
      exact ⟨⟨s.gpr .r4, 8⟩, by simp [blockRegions], fun _ h => h⟩)
    exact hf₁.trans (hf₂.trans hf₃)

end VG.Proof.TripleDes.PPC64LE

end

end

/-! ### `TripleDes.PPC64LE.Pre`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction)

def blockContract (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 384⟩
    let data : Region := ⟨s.gpr .r4, 8⟩
    let scratch : Region := ⟨s.gpr .r5, 512⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch
  post s s' := Spec.TripleDes.blockAt s'.mem (s.gpr .r4) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)) d (Spec.TripleDes.blockAt s.mem (s.gpr .r4))
  pub := PublicRegs [.r3, .r4, .r5]

def selectedRound (d : Direction) (j : Nat) : Nat := if d = .encrypt then j else 15 - j

theorem selectedRound_bound (d : Direction) (j : Nat) (hj : j < 16) : selectedRound d j < 16 := by
  cases d <;> simp only [selectedRound, reduceCtorEq, ite_true, ite_false] <;> omega_arith

theorem keyAddr_component (base : Addr) (c : Nat) (d : Direction) (j : Nat) :
    keyAddr (componentBase base c) d j = base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j)) := by
  unfold keyAddr componentBase selectedRound
  rw [Offset.add_ofNat_add_ofNat]
  exact congrArg (fun n => base + BitVec.ofNat 64 n) (by omega_using [])

/-- The block function's precondition, from its 512 bytes of scratch at
`x2` writable, the schedule at `x0` readable and the block at `x1`
writable, neither in the scratch. -/
theorem headPre_of (s : State)
    (scratchWrites : ∀ i < 64, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8)
    (keyReads : ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (8 * i)) 8)
    (dataWrite : InRegions s.wr (s.gpr .r4) 8)
    (keySep : Region.Disjoint ⟨s.gpr .r3, 384⟩ ⟨s.gpr .r5, 512⟩)
    (dataSep : Region.Disjoint ⟨s.gpr .r4, 8⟩ ⟨s.gpr .r5, 512⟩) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)))
      (s.gpr .r3) s := by
  have inRd : ∀ {a n}, InRegions s.wr a n → InRegions (s.rd ++ s.wr) a n := fun ⟨r, h1, h2⟩ =>
    ⟨r, List.mem_append_right _ h1, h2⟩
  have scratch : Ok scratchCfg s := by
    refine ⟨scratchWrites, ?_, by decide, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · intro k hk j hj; change j < 0 at hj; omega
  have keySub : ∀ c < 3, ∀ direction : Direction, ∀ j < 16,
      Region.Sub ⟨keyAddr (componentBase (s.gpr .r3) c) direction j, 8⟩ ⟨s.gpr .r3, 384⟩ := by
    intro c hc direction j hj
    rw [keyAddr_component]
    have hindex := selectedRound_bound direction j hj
    exact Offset.sub_base _ (by omega_using [hc, hindex])
  have workSub : Region.Sub (spillRegion s) ⟨s.gpr .r5, 512⟩ := Offset.sub_base _ (by decide)
  have saveSub : Region.Sub (saveRegion s) ⟨s.gpr .r5, 512⟩ := Region.sub_prefix (by decide)
  refine ⟨scratch, rfl, (fun i hi => inRd (scratchWrites i (by omega_using [hi]))),
    (fun i hi => scratchWrites i (by omega_using [hi])), inRd dataWrite, dataSep.sub_right saveSub, ?_, ?_, ?_, ?_⟩
  · intro c hc direction j hj
    rw [keyAddr_component]
    exact keyReads _ (by have := selectedRound_bound direction j hj; omega_using [hc, this])
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right workSub
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right saveSub
  · intro c hc direction j hj
    rw [keyAddr_component]
    exact (VG.Proof.TripleDes.componentSchedule_readW s.mem (s.gpr .r3) c
      (selectedRound direction j) hc (selectedRound_bound direction j hj)).symm

theorem headPre_of_contract (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)))
      (s.gpr .r3) s := by
  obtain ⟨hrd, hwr, keySep, dataSep⟩ := hs
  refine headPre_of s (fun i hi => ?_) (fun i hi => ?_) ?_ keySep dataSep
  · rw [hwr]
    exact ⟨⟨s.gpr .r5, 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [hrd, hwr]
    exact ⟨⟨s.gpr .r3, 384⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [hwr]
    exact ⟨⟨s.gpr .r4, 8⟩, by simp, Region.contains_self _ _⟩


end VG.Proof.TripleDes.PPC64LE

end

end


/-! # A call of the block function from the modes and CMAC on PPC64LE -/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Ecb

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

/-- The argument registers the block functions keep. -/
def kept : List Reg := [.r3, .r4, .r5]

def callContract (d : Spec.TripleDes.Direction) : Contract isa :=
  { blockContract d with
    post := fun s s' => (blockContract d).post s s' ∧ ∀ r ∈ kept, s'.gpr r = s.gpr r }

theorem block_correct' (d : Spec.TripleDes.Direction) (s : State) (hs : (callContract d).pre s) :
    ∃ t s', Exec isa (block d) s t s' ∧ abiPreserved s s' ∧ (callContract d).post s s' := by
  have hp := headPre_of_contract d s hs
  have hwrite : InRegions s.wr (s.gpr .r4) 8 := by
    rw [hs.2.1]
    exact ⟨⟨s.gpr .r4, 8⟩, by simp, Region.contains_self _ _⟩
  obtain ⟨t, s', he, post⟩ := block_ok (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3))
    (s.gpr .r3) d s hp hwrite
  have hlr : s'.lr = s.lr := by
    cases d
    · exact Exec.lr (c := encryptBlock) he (by lit_decide) (by lit_decide)
    · exact Exec.lr (c := decryptBlock) he (by lit_decide) (by lit_decide)
  refine ⟨t, s', he, ⟨?_, Exec.sp he, hlr⟩, post.result, ?_⟩
  · intro r hr
    have hkeep : ∀ q ∈ preserved, q ∈ savedRegs ∨ q ∈ loadKept := by decide
    rcases hkeep r hr with h | h
    · exact post.saved r h
    · exact post.regs r h
  · intro r hr
    exact post.regs r (by revert hr; decide +revert)

/-- The name of the block function of the direction `d`. -/
def blockName : Spec.TripleDes.Direction → String
  | .encrypt => "vg_triple_des_encrypt_block"
  | .decrypt => "vg_triple_des_decrypt_block"

theorem blockCall_eq (d : Spec.TripleDes.Direction) :
    Impl.TripleDes.PPC64LE.Ecb.blockCall d = .call (blockName d) (block d) := by cases d <;> rfl

structure CallPre (s : State) : Prop where
  reads : Covers [⟨s.gpr .r3, 384⟩, ⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩] (s.rd ++ s.wr)
  writes : Covers [⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩] s.wr
  keyScratch : (Region.mk (s.gpr .r3) 384).Disjoint ⟨s.gpr .r5, 512⟩
  dataScratch : (Region.mk (s.gpr .r4) 8).Disjoint ⟨s.gpr .r5, 512⟩

structure CallPost (d : Spec.TripleDes.Direction) (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩] s.mem s'.mem
  output : Spec.TripleDes.blockAt s'.mem (s.gpr .r4) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)) d
      (Spec.TripleDes.blockAt s.mem (s.gpr .r4))

theorem call_ok (d : Spec.TripleDes.Direction) (s : State) (hp : CallPre s) :
    WP isa (Impl.TripleDes.PPC64LE.Ecb.blockCall d) s (CallPost d s) := by
  rw [blockCall_eq]
  have c3 := State.callEntry_gpr s (r := .r3) (by decide)
  have c4 := State.callEntry_gpr s (r := .r4) (by decide)
  have c5 := State.callEntry_gpr s (r := .r5) (by decide)
  refine WP.call (k := callContract d) (block_correct' d)
    (rd := [⟨s.gpr .r3, 384⟩])
    (wr := [⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩])
    ?_ hp.reads hp.writes ?_ (by cases d <;> rfl)
  · simp only [callContract, blockContract, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c3, c4, c5]
    exact ⟨trivial, trivial, hp.keyScratch, hp.dataScratch⟩
  · intro s' rd wr _ frame callee _ out
    refine ⟨?_, callee, rd, wr, frame, ?_⟩
    · intro r hr
      have h := out.2 r hr
      have hl : ∀ r ∈ kept, r ∉ linkRegs := by decide
      have hl := hl r hr
      simp only [State.withRegions_gpr, State.callEntry_gpr _ hl] at h
      exact h
    · have h := out.1
      change Spec.TripleDes.blockAt s'.mem _ = blockResult _ d _ at h
      simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4] at h
      exact h

end VG.Proof.TripleDes.PPC64LE.Ecb
