module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Body
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.TripleDes.RISCV64.Bytes
import VerifiedGarbage.Proof.TripleDes.RISCV64.Permutation
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd

/-!
# A block

`block_ok`: `block d dp doff` replaces the block at `doff(dp)` with its
encryption (or decryption) under the schedules' copy in the frame at `sb`,
writing only the block and the frame's slots 7–30, and keeps the registers
a caller expects preserved, `a0` and `ra`.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.RegUpd VG.RISCV64.ByteLoad
open VG.Impl.TripleDes.RISCV64
open VG.Impl.Words.RISCV64 (loadBE64 storeBE)
open VG.Spec.TripleDes (Direction Schedule Block)
open VG.Proof.TripleDes (desCore)

def blockResult (keys : Schedule) (direction : Direction) (b : Block) : Block :=
  match direction with
  | .encrypt => Spec.TripleDes.encryptBlock keys b
  | .decrypt => Spec.TripleDes.decryptBlock keys b

theorem blockResult_core (keys : Schedule) (direction : Direction) (b : Block) :
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp
      (blockCore (Spec.TripleDes.componentSchedule keys) direction
        (Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock b)))) =
      blockResult keys direction b := by
  cases direction
  · exact (VG.Proof.TripleDes.encryptBlock_eq_cores keys b).symm
  · exact (VG.Proof.TripleDes.decryptBlock_eq_cores keys b).symm

/-- The frame's slots 7–30: the saved registers and the spills. -/
def workRegion (s : State) : Region := ⟨s.gpr sb + BitVec.ofNat 64 56, 192⟩

/-- What the block needs: the block at `doff(dp)` and the frame of 80
slots at `sb`, with the schedules' copy from byte `keyOff` on. -/
structure BlockPre (k : Schedule) (dp : Reg) (doff : Nat) (s : State) : Prop where
  dpKept : dp ∈ passKept
  doffLt : doff + 8 ≤ 2048
  al : (s.gpr sb).toNat % 8 = 0
  wr : ∀ o < 80, InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * o)) 8
  keys : Spec.TripleDes.scheduleAt s.mem (s.gpr sb + BitVec.ofNat 64 keyOff) = k
  data : InRegions s.wr (s.gpr dp + BitVec.ofNat 64 doff) 8
  sep : (⟨s.gpr dp + BitVec.ofNat 64 doff, 8⟩ : Region).Disjoint (workRegion s)

/-- The registers the block keeps: those a caller expects preserved, `a0`
and `ra`. -/
def blockKept : List Reg :=
  [.ra, .s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11, .a0]

structure BlockPost (k : Schedule) (d : Direction) (dp : Reg) (doff : Nat) (s t : State) :
    Prop where
  result : Spec.TripleDes.blockAt t.mem (s.gpr dp + BitVec.ofNat 64 doff) =
    blockResult k d (Spec.TripleDes.blockAt s.mem (s.gpr dp + BitVec.ofNat 64 doff))
  regs : ∀ r ∈ blockKept, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr dp + BitVec.ofNat 64 doff, 8⟩, workRegion s] s.mem t.mem

theorem savedSlots_fits : Spill.Fits savedSlots := by decide
theorem savedSlots_restorable : Spill.Restorable sb savedSlots := by decide

theorem savedSlots_in : ∀ p ∈ savedSlots, 56 ≤ p.2 ∧ p.2 + 8 ≤ 56 + 64 := by decide

/-- A word of the frame, `8 o` bytes on. -/
theorem slot_eq (B : Addr) (o : Nat) : B + BitVec.ofNat 64 (8 * o) = wordAddr B o := rfl

/-- The schedules' copy, for the rounds. -/
theorem keysAt_of {k : Schedule} {s : State} (hal : (s.gpr sb).toNat % 8 = 0)
    (hwr : ∀ o < 80, InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * o)) 8)
    (hk : Spec.TripleDes.scheduleAt s.mem (s.gpr sb + BitVec.ofNat 64 keyOff) = k)
    (c : Nat) (hc : c < 3) (d : Direction) :
    KeysAt (Spec.TripleDes.componentSchedule k c) d
      (componentBase (s.gpr sb + BitVec.ofNat 64 keyOff) c) s := by
  have haddr : ∀ j < 16, keyAddr (componentBase (s.gpr sb + BitVec.ofNat 64 keyOff) c) d j =
      s.gpr sb + BitVec.ofNat 64 (8 * (32 + 16 * c + (if d = .encrypt then j else 15 - j))) := by
    intro j hj
    simp only [keyAddr, componentBase, keyOff, Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => s.gpr sb + BitVec.ofNat 64 n) (by split <;> omega)
  have hj' : ∀ j < 16, (if d = .encrypt then j else 15 - j) < 16 := fun j hj => by split <;> omega
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [haddr j hj]
    have := hj' j hj
    obtain ⟨r, hr, hc'⟩ := hwr (32 + 16 * c + (if d = .encrypt then j else 15 - j)) (by omega)
    exact ⟨r, List.mem_append_right _ hr, hc'⟩
  · rw [haddr j hj]; exact Spill.al8 hal (by omega)
  · rw [haddr j hj]
    have := hj' j hj
    exact Offset.disjoint _ (Or.inr (by omega)) (by omega) (by omega)
  · rw [haddr j hj]
    have h := VG.Proof.TripleDes.componentSchedule_readW s.mem
      (s.gpr sb + BitVec.ofNat 64 keyOff) c (if d = .encrypt then j else 15 - j) hc (hj' j hj)
    rw [hk, Offset.add_ofNat_add_ofNat] at h
    simp only [VG.Proof.TripleDes.roundKey]
    rw [h]
    exact congrArg (fun n => (s.mem.readW (s.gpr sb + BitVec.ofNat 64 n) 64).setWidth 48)
      (by simp only [keyOff]; omega)

theorem sboxCfg_ok {s : State} (hal : (s.gpr sb).toNat % 8 = 0)
    (hwr : ∀ o < 80, InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * o)) 8) : Ok sboxCfg s where
  slotIn k hk := hwr k (by simp only [sboxCfg] at hk; omega)
  extIn k hk := by simp [sboxCfg] at hk
  baseAl _ := hal
  extAl h := by simp [sboxCfg] at h
  slots := by decide
  sep k _ j hj := by simp [sboxCfg] at hj

theorem ready_of {k : Schedule} {s : State} (hal : (s.gpr sb).toNat % 8 = 0)
    (hwr : ∀ o < 80, InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * o)) 8)
    (hk : Spec.TripleDes.scheduleAt s.mem (s.gpr sb + BitVec.ofNat 64 keyOff) = k) :
    Ready (Spec.TripleDes.componentSchedule k) (s.gpr sb + BitVec.ofNat 64 keyOff) s :=
  ⟨sboxCfg_ok hal hwr, rfl, fun c hc d => keysAt_of hal hwr hk c hc d⟩

/-- IP of the block at `doff(dp)` in the halves. -/
theorem blockLoad_ok (dp : Reg) (doff : Nat) (hdp : dp ∈ passKept) (ho : doff + 8 ≤ 2048)
    (u : State) (hin : InRegions (u.rd ++ u.wr) (u.gpr dp + BitVec.ofNat 64 doff) 8) :
    WP isa (.block (blockLoad dp doff)) u fun t =>
      WordState (Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt u.mem (u.gpr dp + BitVec.ofNat 64 doff)))) t ∧
      t.mem = u.mem ∧ t.rd = u.rd ∧ t.wr = u.wr ∧ t.sp = u.sp ∧
      ∀ r ∈ blockKept, t.gpr r = u.gpr r := by
  have hne : Reg.t0 ≠ dp ∧ Reg.t1 ≠ dp := by revert hdp; cases dp <;> decide
  unfold blockLoad
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (loadBE64_ok (d := .t0) (tmp := .t1) (n := dp) hne.1 hne.2 (by decide)
    (by omega) hin) fun u₁ e₁ => ?_
  subst e₁
  have hcode : permuteCode Spec.TripleDes.ip 64 .t2 .t0 .t3 = instrs initialPermutation.lit :=
    congrArg instrs initialPermutation.lit_eq
  rw [hcode]
  obtain ⟨u₂, run₂, word₂, rd₂, wr₂, sp₂, mem₂, regs₂⟩ := fixedPermutation_ok Spec.TripleDes.ip
    (by decide) (by decide) VG.Proof.TripleDes.ip_bounds .t0 .t2 _ initialPermutation_check
    ((u.write .t1 ((u.mem (u.gpr dp + BitVec.ofNat 64 (doff + 7))).setWidth 64)).write .t0
      (be64 u.mem (u.gpr dp) doff))
  have hkeep : ∀ r ∈ blockKept,
      ((instrs initialPermutation.lit).all fun i => Straight.dst i != some r) = true := by
    decide +kernel
  refine WP.of_runBlock ⟨u₂, run₂, ?_⟩
  let x := Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock
    (Spec.TripleDes.blockAt u.mem (u.gpr dp + BitVec.ofNat 64 doff)))
  have hx : u₂.gpr .t2 = x := by
    rw [word₂, gpr_write_self, be64_decode]
    simp [x]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_shift_d (show 32 < 64 by decide),
    Option.some.injEq, exists_eq_left', gpr_write, lReg, rReg, reduceCtorEq, ite_true, ite_false,
    hx]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact upperHalf_extend x
  · exact lowerHalf_extend x
  · simp only [mem_write]; rw [mem₂]; rfl
  · simp only [rd_write]; rw [rd₂]; rfl
  · simp only [wr_write]; rw [wr₂]; rfl
  · simp only [sp_write]; rw [sp₂]; rfl
  · intro r hr
    have hr' : r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .t0 ∧ r ≠ .t1 := by revert hr; cases r <;> decide
    simp only [hr'.1, hr'.2.1, ite_false]
    rw [regs₂ r (hkeep r hr), gpr_write_of_ne _ _ hr'.2.2.1, gpr_write_of_ne _ _ hr'.2.2.2]

/-- FP of the halves to the block at `doff(dp)`. -/
theorem blockStore_ok (dp : Reg) (doff : Nat) (hdp : dp ∈ passKept) (ho : doff + 8 ≤ 2048)
    (u : State) (x : BitVec 64) (hw : WordState x u)
    (hin : InRegions u.wr (u.gpr dp + BitVec.ofNat 64 doff) 8) :
    WP isa (.block (blockStore dp doff)) u fun t =>
      t.mem = VG.WriteBytes.writeBytes u.mem (u.gpr dp + BitVec.ofNat 64 doff)
        (beBytes 8 (Spec.TripleDes.permute Spec.TripleDes.fp x)) ∧
      t.rd = u.rd ∧ t.wr = u.wr ∧ t.sp = u.sp ∧
      ∀ r ∈ blockKept, t.gpr r = u.gpr r := by
  have hne : Reg.t1 ≠ Reg.t2 ∧ Reg.t1 ≠ dp := by revert hdp; cases dp <;> decide
  unfold blockStore
  rw [WP.block_append_iff, WP.block_append_iff]
  let u₁ := (u.write .t0 (u.gpr lReg <<< 32)).write .t0
    ((u.write .t0 (u.gpr lReg <<< 32)).gpr .t0 ^^^ (u.write .t0 (u.gpr lReg <<< 32)).gpr rReg)
  have hu₁ : u₁.gpr .t0 = x := by
    have hl := hw.left
    have hr := hw.right
    simp only [lReg, rReg] at hl hr
    simp only [u₁, gpr_write_self, gpr_write, lReg, rReg, reduceCtorEq, ite_false, hl, hr]
    exact join_halves x
  refine WP.of_runBlock ⟨u₁, by
    rw [runBlock_cons, exec_shift_d (by decide), runStep_some, runBlock_cons, exec_logic,
      runStep_some, runBlock_nil], ?_⟩
  have hcode : permuteCode Spec.TripleDes.fp 64 .t2 .t0 .t3 = instrs finalPermutation.lit :=
    congrArg instrs finalPermutation.lit_eq
  rw [hcode]
  obtain ⟨u₂, run₂, word₂, rd₂, wr₂, sp₂, mem₂, regs₂⟩ := fixedPermutation_ok Spec.TripleDes.fp
    (by decide) (by decide) VG.Proof.TripleDes.fp_bounds .t0 .t2 _ finalPermutation_check u₁
  have hkeep : ∀ r ∈ blockKept,
      ((instrs finalPermutation.lit).all fun i => Straight.dst i != some r) = true := by
    decide +kernel
  have hkeep' : ((instrs finalPermutation.lit).all fun i => Straight.dst i != some dp) = true :=
    hkeep dp (by revert hdp; cases dp <;> decide)
  refine WP.of_runBlock ⟨u₂, run₂, ?_⟩
  have hdp₂ : u₂.gpr dp = u.gpr dp := by
    rw [regs₂ dp hkeep']
    have h0 : dp ≠ .t0 := by revert hdp; cases dp <;> decide
    simp only [u₁, gpr_write_of_ne _ _ h0]
  have hv : u₂.gpr .t2 = Spec.TripleDes.permute Spec.TripleDes.fp x := by
    rw [word₂, hu₁]; simp
  refine WP.mono (storeBE_ok (v := .t2) (tmp := .t1) (n := dp) (off := doff) (w := 8) hne.1 hne.2
    (by decide) (by decide) ho fun j hj => by
      rw [wr₂, hdp₂]
      exact in_byte' hin hj) fun t e => ?_
  subst e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_write, hdp₂, hv, mem₂]; rfl
  · simp only [rd_write]; rw [rd₂]; rfl
  · simp only [wr_write]; rw [wr₂]; rfl
  · simp only [sp_write]; rw [sp₂]; rfl
  · intro r hr
    have hr' : r ≠ .t1 ∧ r ≠ .t0 := by revert hr; cases r <;> decide
    rw [gpr_write_of_ne _ _ hr'.1]
    change u₂.gpr r = u.gpr r
    rw [regs₂ r (hkeep r hr)]
    simp only [u₁, gpr_write_of_ne _ _ hr'.2]

end VG.Proof.TripleDes.RISCV64
