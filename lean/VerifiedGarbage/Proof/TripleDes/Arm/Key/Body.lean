import VerifiedGarbage.Proof.TripleDes.Arm.Key.Permutation
import VerifiedGarbage.Proof.TripleDes.Arm.Bytes
import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.Arm.WordStore
import VerifiedGarbage.Proof.TripleDes.Arm.Word
import VerifiedGarbage.Proof.Rc2.Arm.KeySteps
import VerifiedGarbage.Proof.TripleDes.Arm.Key.Rotation
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Rc2.Arm.Lookup
import VerifiedGarbage.Proof.TripleDes.KeyMemory

/-! ## `Load` -/

section

namespace VG.Proof.TripleDes.Arm.Key
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm

def keyKept : List Reg := [.r0, .r1, .r2, .r3]

theorem readKey_ok (s : State) (offset : Nat) (ho : offset + 4 < 4096)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r0 + BitVec.ofNat 32 (offset + 4 * t))) 4) :
    ∃ s', runBlock isa [.ldr .r4 .r0 offset, .ldr .r5 .r0 (offset + 4),
        .rev .r4 .r4, .rev .r5 .r5] s = some s' ∧
      s'.gpr .r4 = rev (s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 offset)) 32) ∧
      s'.gpr .r5 = rev (s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (offset + 4))) 32) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) := by
  have h0 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 offset)) 4 := by
    simpa only [Nat.mul_zero, Nat.add_zero] using hr 0 (by decide)
  have h1 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (offset + 4))) 4 := by
    simpa only [Nat.mul_one] using hr 1 (by decide)
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show offset < 4096 from by omega, h0, show offset + 4 < 4096 from ho, ite_true, State.load32,
      gpr_setReg, reduceCtorEq, ite_false, rd_setReg, wr_setReg, h1,
      Option.map_some, mem_setReg, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · intro r h4 h5; simp only [gpr_setReg, h4, h5, ite_false]

def loadTail (component : Nat) : List Instr :=
  [imm .r9 0, .dp .add .r8 .r2 (.imm (BitVec.ofNat 32 (128 * component)))]

theorem loadTail_ok (s : State) (component : Nat) (hc : component < 3) :
    ∃ s', runBlock isa (loadTail component) s = some s' ∧
      s'.gpr .r9 = 0 ∧ s'.gpr .r8 = s.gpr .r2 + BitVec.ofNat 32 (128 * component) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r9 → r ≠ .r8 → s'.gpr r = s.gpr r) := by
  have henc : encodable (BitVec.ofNat 32 (128 * component)) = true := by
    have finite : ∀ c < 3, encodable (BitVec.ofNat 32 (128 * c)) = true := by decide
    exact finite component hc
  refine ⟨_, by
    simp (config := {decide := true}) only [loadTail, imm, runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, henc, ite_true, gpr_setReg,
      ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]; rfl
  · simp only [gpr_setReg_self]
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · intro r h9 h8; simp only [gpr_setReg, h9, h8, ite_false]

structure LoadPost (x : BitVec 56) (component : Nat) (s s' : State) : Prop where
  c : s'.gpr .r10 = ((x >>> 28).setWidth 28).setWidth 32
  d : s'.gpr .r11 = (x.setWidth 28).setWidth 32
  counter : s'.gpr .r9 = 0
  ptr : s'.gpr .r8 = s.gpr .r2 + BitVec.ofNat 32 (128 * component)
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ keyKept, s'.gpr r = s.gpr r

theorem load_ok (s : State) (offset component : Nat) (hc : component < 3)
    (ho : offset + 4 < 4096)
    (fit : (s.gpr .r0).toNat + offset + 8 ≤ 2 ^ 32)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r0 + BitVec.ofNat 32 (offset + 4 * t))) 4) :
    WP isa (.block (Impl.TripleDes.Arm.Key.load offset component)) s
      (LoadPost (Spec.TripleDes.permute Spec.TripleDes.pc1 (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 offset))))) component s) := by
  have code : Impl.TripleDes.Arm.Key.load offset component =
      (([.ldr .r4 .r0 offset, .ldr .r5 .r0 (offset + 4),
        .rev .r4 .r4, .rev .r5 .r5] : List Instr) ++
        permuteCode Spec.TripleDes.pc1 64 32 28 .r11 .r10 .r5 .r4 .r12 .lr) ++ loadTail component := by
    simp only [Impl.TripleDes.Arm.Key.load, loadTail, List.append_assoc]
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, hi₁, lo₁, mem₁, rd₁, wr₁, reg₁⟩ := readKey_ok s offset ho hr
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, lo₂, hi₂, rd₂, wr₂, _, mem₂, reg₂⟩ := pc1_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have key₁ : packedInput 64 32 (s₁.gpr .r5) (s₁.gpr .r4) =
      Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem
        (State.addr (s.gpr .r0 + BitVec.ofNat 32 offset))) := by
    rw [packedInput, lo₁, hi₁, decodeBlock_readW]
    simp only [BitVec.setWidth_eq]
    have ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 (offset + 4)) =
        State.addr (s.gpr .r0 + BitVec.ofNat 32 offset) + 4 := by
      rw [addr_add (by omega_using [fit]), addr_add (by omega_using [fit]),
        ← VG.Offset.add_ofNat_add_ofNat]
      rfl
    rw [ha]
  rw [key₁] at lo₂ hi₂
  obtain ⟨s₃, run₃, counter₃, ptr₃, mem₃, rd₃, wr₃, reg₃⟩ := loadTail_ok s₂ component hc
  refine WP.of_runBlock ⟨s₃, run₃, ⟨(reg₃ .r10 (by decide) (by decide)).trans hi₂,
    (reg₃ .r11 (by decide) (by decide)).trans lo₂, counter₃, ?_,
    mem₃.trans (mem₂.trans mem₁), rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_⟩⟩
  · rw [ptr₃, reg₂ .r2 (by decide +kernel), reg₁ .r2 (by decide) (by decide)]
  · intro r hr
    have unused : ∀ r ∈ keyKept, r ≠ .r9 ∧ r ≠ .r8 ∧ r ≠ .r4 ∧ r ≠ .r5 := by decide
    have hcheck : ∀ r ∈ keyKept,
        ((instrs keyPermutation1.lit).all fun op => dstOf op != some r) = true := by decide +kernel
    exact (reg₃ r (unused r hr).1 (unused r hr).2.1).trans
      ((reg₂ r (hcheck r hr)).trans (reg₁ r (unused r hr).2.2.1 (unused r hr).2.2.2))

end VG.Proof.TripleDes.Arm.Key

end

/-! ## `Store` -/

section

namespace VG.Proof.TripleDes.Arm.Key
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (gpr_subFlags mem_subFlags rd_subFlags wr_subFlags)

def tail : List Instr := [.str .r4 .r8 0, .str .r5 .r8 4,
  .dp .add .r8 .r8 (.imm 8), .dp .add .r9 .r9 (.imm 1), .cmp .r9 (.imm 16)]

theorem nextRound_values : ∀ j < 16,
    BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) ∧
    (!(BitVec.ofNat 32 j + 1 - (16 : BitVec 32) == 0)) = decide (j ≠ 15) := by decide

theorem tail_ok (s : State) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r9 = BitVec.ofNat 32 j)
    (fit : (s.gpr .r8).toNat + 8 ≤ 2 ^ 32)
    (hw : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r8 + BitVec.ofNat 32 (4 * t))) 4) :
    ∃ s', runBlock isa tail s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (s.gpr .r8)) (s.gpr .r5 ++ s.gpr .r4) ∧
      s'.gpr .r8 = s.gpr .r8 + 8 ∧ s'.gpr .r9 = BitVec.ofNat 32 (j + 1) ∧
      isa.eval .ne s' = some (decide (j ≠ 15)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r9 → r ≠ .r8 → s'.gpr r = s.gpr r) := by
  have h0 : InRegions s.wr (State.addr (s.gpr .r8 + BitVec.ofNat 32 0)) 4 := by
    simpa only [Nat.mul_zero] using hw 0 (by decide)
  have h1 : InRegions s.wr (State.addr (s.gpr .r8 + BitVec.ofNat 32 4)) 4 := by
    simpa only [Nat.mul_one] using hw 1 (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [tail, runBlock_cons, runStep_some, runBlock_nil,
      exec, State.store32, h0, h1, ite_true, Op2.eval, Option.map_some,
      gpr_setReg, ite_false, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_subFlags, mem_setReg, BitVec.add_zero]
    rw [addr_add (by omega_using [fit])]
    exact writeW_pair s.mem _ _ _
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
    rw [hc]; exact (nextRound_values j hj).1
  · change VG.Arm.eval .ne _ = _
    simp only [VG.Arm.eval, subFlags, hc]
    exact congrArg some (nextRound_values j hj).2
  · simp only [rd_subFlags, rd_setReg]
  · simp only [wr_subFlags, wr_setReg]
  · intro r h9 h8; simp only [gpr_subFlags, gpr_setReg, h9, h8, ite_false]

structure StorePost (c d : BitVec 28) (j : Nat) (s s' : State) : Prop where
  mem : s'.mem = s.mem.writeW (State.addr (s.gpr .r8))
    ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64)
  ptr : s'.gpr .r8 = s.gpr .r8 + 8
  counter : s'.gpr .r9 = BitVec.ofNat 32 (j + 1)
  flag : isa.eval .ne s' = some (decide (j ≠ 15))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ (keyKept ++ [.r10, .r11]), s'.gpr r = s.gpr r

theorem storeRound_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r10 = c.setWidth 32) (hd : s.gpr .r11 = d.setWidth 32)
    (hjreg : s.gpr .r9 = BitVec.ofNat 32 j)
    (fit : (s.gpr .r8).toNat + 8 ≤ 2 ^ 32)
    (hw : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r8 + BitVec.ofNat 32 (4 * t))) 4) :
    WP isa (.block Impl.TripleDes.Arm.Key.storeRound) s (StorePost c d j s) := by
  have code : Impl.TripleDes.Arm.Key.storeRound =
      permuteCode Spec.TripleDes.pc2 56 28 32 .r4 .r5 .r11 .r10 .r12 .lr ++ tail := rfl
  rw [code, WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, rd₁, wr₁, _, mem₁, reg₁⟩ := pc2_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have input : packedInput 56 28 (s.gpr .r11) (s.gpr .r10) = c ++ d := by
    rw [hd, hc]; exact packed28 c d
  rw [input] at lo₁ hi₁
  have checks : ∀ r ∈ (keyKept ++ [.r10, .r11, .r9, .r8]),
      ((instrs keyPermutation2.lit).all fun op => dstOf op != some r) = true := by decide +kernel
  have keep₁ : ∀ r ∈ (keyKept ++ [.r10, .r11, .r9, .r8]), s₁.gpr r = s.gpr r :=
    fun r hr => reg₁ r (checks r hr)
  have write₁ : ∀ t < 2, InRegions s₁.wr (State.addr (s₁.gpr .r8 + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [wr₁, keep₁ .r8 (by decide)]; exact hw
  have fit₁ : (s₁.gpr .r8).toNat + 8 ≤ 2 ^ 32 := by
    rw [keep₁ .r8 (by decide)]; exact fit
  obtain ⟨s₂, run₂, mem₂, ptr₂, counter₂, flag₂, rd₂, wr₂, reg₂⟩ :=
    tail_ok s₁ j hj ((keep₁ .r9 (by decide)).trans hjreg) fit₁ write₁
  refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, ?_, counter₂, flag₂, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩⟩
  · rw [mem₂, mem₁, keep₁ .r8 (by decide), lo₁, hi₁, BitVec.setWidth_eq, packed48]
  · rw [ptr₂, keep₁ .r8 (by decide)]
  · intro r hr
    have incl : ∀ r ∈ (keyKept ++ [.r10, .r11]),
        r ≠ .r9 ∧ r ≠ .r8 ∧ r ∈ (keyKept ++ [.r10, .r11, .r9, .r8]) := by decide
    exact (reg₂ r (incl r hr).1 (incl r hr).2.1).trans (keep₁ r (incl r hr).2.2)

end VG.Proof.TripleDes.Arm.Key

end

/-! ## `Loop` -/

section

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm
open VG.Proof.TripleDes.Arm.Key (keyKept)
open VG.Proof.TripleDes (keyPrefix keyInitial keyStep keyPrefix_succ)

theorem pointer_fit (base : BitVec 32) (fit : base.toNat + 128 ≤ 2 ^ 32)
    (j : Nat) (hj : j < 16) : (base + BitVec.ofNat 32 (8 * j)).toNat + 8 ≤ 2 ^ 32 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega_using [hj] : 8 * j < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega_using [fit, hj] : base.toNat + 8 * j < 2 ^ 32)]
  omega_using [fit, hj]

structure LoopState (key : BitVec 64) (base : BitVec 32) (origin : State) (j : Nat) (s : State) : Prop where
  c : s.gpr .r10 = (keyPrefix key j).1.setWidth 32
  d : s.gpr .r11 = (keyPrefix key j).2.1.setWidth 32
  counter : s.gpr .r9 = BitVec.ofNat 32 j
  pointer : s.gpr .r8 = base + BitVec.ofNat 32 (8 * j)
  keys : ∀ i < j, ∀ hi : i < 16, s.mem.readW (State.addr base + BitVec.ofNat 64 (8 * i)) 64 =
    ((keyPrefix key j).2.2[i]'hi).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  reg : ∀ r ∈ keyKept, s.gpr r = origin.gpr r
  frame : Frame [⟨State.addr base, 128⟩] origin.mem s.mem

def LoopInv (key : BitVec 64) (base : BitVec 32) (origin : State) (n : Nat) (s : State) : Prop :=
  1 ≤ n ∧ n ≤ 16 ∧ LoopState key base origin (16 - n) s

theorem loopBody_ok (key : BitVec 64) (base : BitVec 32) (origin : State)
    (fit : base.toNat + 128 ≤ 2 ^ 32)
    (hw : ∀ j < 16, ∀ t < 2, InRegions origin.wr
      (State.addr (base + BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 (4 * t))) 4)
    (j : Nat) (hj : j < 16) (s : State) (hs : LoopState key base origin j s) :
    WP isa (.seq Impl.TripleDes.Arm.Key.rotation (.block Impl.TripleDes.Arm.Key.storeRound)) s
      (fun s' => isa.eval .ne s' = some (decide (j ≠ 15)) ∧ LoopState key base origin (j + 1) s') := by
  apply WP.seq
  apply WP.mono (rotation_ok s _ _ j hj hs.c hs.d hs.counter)
  intro s₁ h₁
  have unused : ∀ r ∈ (keyKept ++ [.r9, .r8]),
      r ≠ .r4 ∧ r ≠ .r10 ∧ r ≠ .r11 := by decide
  have reg₁ : ∀ r ∈ (keyKept ++ [.r9, .r8]), s₁.gpr r = s.gpr r := by
    intro r hr
    exact h₁.reg r (unused r hr).1 (unused r hr).2.1 (unused r hr).2.2
  have fit₁ : (s₁.gpr .r8).toNat + 8 ≤ 2 ^ 32 := by
    rw [reg₁ .r8 (by decide), hs.pointer]
    exact pointer_fit base fit j hj
  have write₁ : ∀ t < 2, InRegions s₁.wr
      (State.addr (s₁.gpr .r8 + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [h₁.wr, hs.wr, reg₁ .r8 (by decide), hs.pointer]
    exact hw j hj
  apply WP.mono (storeRound_ok s₁ _ _ j hj h₁.c h₁.d
    ((reg₁ .r9 (by decide)).trans hs.counter) fit₁ write₁)
  intro s₂ h₂
  have hmem : s₂.mem = s.mem.writeW (State.addr base + BitVec.ofNat 64 (8 * j))
      ((Spec.TripleDes.permute Spec.TripleDes.pc2
        ((keyPrefix key j).1.rotateLeft (Spec.TripleDes.rotations.getD j 0) ++
          (keyPrefix key j).2.1.rotateLeft (Spec.TripleDes.rotations.getD j 0))).setWidth 64) := by
    rw [h₂.mem, h₁.mem, reg₁ .r8 (by decide), hs.pointer, addr_add (by omega_using [fit, hj])]
  refine ⟨h₂.flag, ⟨?_, ?_, h₂.counter, ?_, ?_, h₂.rd.trans (h₁.rd.trans hs.rd),
    h₂.wr.trans (h₁.wr.trans hs.wr), ?_, ?_⟩⟩
  · rw [keyPrefix_succ]
    exact (h₂.reg .r10 (by decide)).trans h₁.c
  · rw [keyPrefix_succ]
    exact (h₂.reg .r11 (by decide)).trans h₁.d
  · rw [h₂.ptr, reg₁ .r8 (by decide), hs.pointer]
    change base + BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 8 = _
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega)
  · intro i hi hi16
    rw [hmem, keyPrefix_succ]
    by_cases he : i = j
    · subst i
      rw [Mem.readW_writeW_self64]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_self hj).symm
    · rw [Mem.readW_writeW_sep (Offset.sep (State.addr base) (by omega_using [hi, he])
        (by omega_using [hi16]) (by omega_using [hj])) (by decide), hs.keys i (by omega_using [hi, he]) hi16]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_ne hi16 (Ne.symm he)).symm
  · intro r hr
    have incl : ∀ r ∈ keyKept,
        r ∈ (keyKept ++ [.r10, .r11]) ∧
        r ∈ (keyKept ++ [.r9, .r8]) := by decide
    exact (h₂.reg r (incl r hr).1).trans ((reg₁ r (incl r hr).2).trans (hs.reg r hr))
  · rw [hmem]
    exact hs.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base (State.addr base) (by omega_using [hj]) (by omega_using [hj]))

theorem loopStep (key : BitVec 64) (base : BitVec 32) (origin : State)
    (fit : base.toNat + 128 ≤ 2 ^ 32)
    (hw : ∀ j < 16, ∀ t < 2, InRegions origin.wr
      (State.addr (base + BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 (4 * t))) 4)
    (n : Nat) (s : State) (hs : LoopInv key base origin n s) :
    WP isa (.seq Impl.TripleDes.Arm.Key.rotation (.block Impl.TripleDes.Arm.Key.storeRound)) s
      (fun s' => (isa.eval .ne s' = some false ∧ LoopState key base origin 16 s') ∨
        (isa.eval .ne s' = some true ∧ ∃ m < n, LoopInv key base origin m s')) := by
  apply WP.mono (loopBody_ok key base origin fit hw (16 - n) (by omega_using [hs.1]) s hs.2.2)
  intro s' h
  by_cases last : n = 1
  · left
    have idx : 16 - n = 15 := by omega_using [last]
    refine ⟨?_, ?_⟩
    · simpa only [idx, ne_eq, not_true_eq_false, decide_false] using h.1
    · simpa only [idx] using h.2
  · right
    have idx : ¬16 - n = 15 := by omega_using [hs.1, hs.2.1, last]
    refine ⟨?_, n - 1, by omega_using [hs.1], ?_⟩
    · simpa only [idx, ne_eq, not_false_eq_true, decide_true] using h.1
    · refine ⟨by omega_using [hs.1, last], by omega_using [hs.2.1], ?_⟩
      have eq : 16 - n + 1 = 16 - (n - 1) := by omega_using [hs.1, hs.2.1]
      rw [← eq]
      exact h.2

theorem loop_ok (key : BitVec 64) (base : BitVec 32) (s : State)
    (fit : base.toNat + 128 ≤ 2 ^ 32)
    (hw : ∀ j < 16, ∀ t < 2, InRegions s.wr
      (State.addr (base + BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 (4 * t))) 4)
    (hc : s.gpr .r10 = (keyInitial key).1.setWidth 32)
    (hd : s.gpr .r11 = (keyInitial key).2.1.setWidth 32)
    (hcount : s.gpr .r9 = 0) (hptr : s.gpr .r8 = base) :
    WP isa (.loop (.seq Impl.TripleDes.Arm.Key.rotation
      (.block Impl.TripleDes.Arm.Key.storeRound)) .ne) s (LoopState key base s 16) := by
  apply WP.loop (M := isa) (body := .seq Impl.TripleDes.Arm.Key.rotation
      (.block Impl.TripleDes.Arm.Key.storeRound)) (c := .ne)
    (Q := LoopState key base s 16) (LoopInv key base s) (loopStep key base s fit hw) 16 s
  refine ⟨by decide, by decide, hc, hd, hcount, ?_, ?_, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  · exact hptr.trans (BitVec.add_zero base).symm
  · intro i hi
    omega

end VG.Proof.TripleDes.Arm.Key

end

/-! ## `Component` -/

section

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm
open VG.Proof.TripleDes.Arm.Key (keyKept)

structure ComponentPost (keys : Spec.TripleDes.DesSchedule) (base : Addr) (s s' : State) : Prop where
  keys : ∀ i < 16, s'.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 = (keys.getD i 0).setWidth 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ keyKept, s'.gpr r = s.gpr r
  frame : Frame [⟨base, 128⟩] s.mem s'.mem

theorem component_ok (s : State) (offset component : Nat) (hc : component < 3)
    (ho : offset + 4 < 4096)
    (keyFit : (s.gpr .r0).toNat + offset + 8 ≤ 2 ^ 32)
    (scheduleFit : (s.gpr .r2).toNat + 384 ≤ 2 ^ 32)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r0 + BitVec.ofNat 32 (offset + 4 * t))) 4)
    (hw : ∀ j < 16, ∀ t < 2, InRegions s.wr
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (128 * component) +
        BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 (4 * t))) 4) :
    WP isa (Impl.TripleDes.Arm.Key.component offset component) s
      (ComponentPost (Spec.TripleDes.expandDesKey (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 offset)))))
        (State.addr (s.gpr .r2 + BitVec.ofNat 32 (128 * component))) s) := by
  rw [Impl.TripleDes.Arm.Key.component]
  apply WP.seq
  apply WP.mono (load_ok s offset component hc ho keyFit hr)
  intro s₁ h₁
  have writes : ∀ j < 16, ∀ t < 2, InRegions s₁.wr
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (128 * component) +
        BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [h₁.wr]; exact hw
  have fit : (s.gpr .r2 + BitVec.ofNat 32 (128 * component)).toNat + 128 ≤ 2 ^ 32 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [hc] : 128 * component < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_using [scheduleFit, hc] : (s.gpr .r2).toNat + 128 * component < 2 ^ 32)]
    omega_using [scheduleFit, hc]
  apply WP.mono (loop_ok _ _ s₁ fit writes h₁.c h₁.d h₁.counter h₁.ptr)
  intro s₂ h₂
  refine ⟨?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), ?_⟩
  · intro i hi
    rw [VG.Proof.TripleDes.expandDesKey_prefix, VG.Proof.TripleDes.vector_getD _ i hi 0]
    exact h₂.keys i hi hi
  · rw [← h₁.mem]
    exact h₂.frame

end VG.Proof.TripleDes.Arm.Key

end

/-! ## `Copy` -/

section

namespace VG.Proof.TripleDes.Arm.Key
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (Keep)

def copyPair (a b : Nat) : List Instr :=
  [.ldr .r4 .r2 a, .ldr .r5 .r2 (a + 4), .str .r4 .r2 b, .str .r5 .r2 (b + 4)]

theorem copyPair_ok (s : State) (a b : Nat) (ha : a + 4 < 4096) (hb : b + 4 < 4096)
    (fit : (s.gpr .r2).toNat + max a b + 8 ≤ 2 ^ 32)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (a + 4 * t))) 4)
    (hw : ∀ t < 2, InRegions s.wr
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (b + 4 * t))) 4) :
    ∃ s', runBlock isa (copyPair a b) s = some s' ∧
      Keep [.r4, .r5] {s with
        mem := s.mem.writeW (State.addr (s.gpr .r2 + BitVec.ofNat 32 b))
          (s.mem.readW (State.addr (s.gpr .r2 + BitVec.ofNat 32 a)) 64)} s' := by
  have hr0 := hr 0 (by decide)
  have hr1 := hr 1 (by decide)
  have hw0 := hw 0 (by decide)
  have hw1 := hw 1 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at hr0 hw0
  simp only [Nat.mul_one] at hr1 hw1
  refine ⟨_, by
    simp only [copyPair, runBlock_cons, runStep_some, runBlock_nil, exec,
      show a < 4096 from by omega, ha, show b < 4096 from by omega, hb,
      ite_true, State.load32, State.store32, hr0, hr1, hw0, hw1, Option.map_some,
      gpr_setReg, reduceCtorEq, ite_true, ite_false, mem_setReg, rd_setReg, wr_setReg]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2, ite_false]
  · have ea : State.addr (s.gpr .r2 + BitVec.ofNat 32 (a + 4)) =
        State.addr (s.gpr .r2 + BitVec.ofNat 32 a) + 4 := by
      rw [addr_add (by omega_using [fit, Nat.le_max_left a b]),
        addr_add (by omega_using [fit, Nat.le_max_left a b]), ← Offset.add_ofNat_add_ofNat]
      rfl
    have eb : State.addr (s.gpr .r2 + BitVec.ofNat 32 (b + 4)) =
        State.addr (s.gpr .r2 + BitVec.ofNat 32 b) + 4 := by
      rw [addr_add (by omega_using [fit, Nat.le_max_right a b]),
        addr_add (by omega_using [fit, Nat.le_max_right a b]), ← Offset.add_ofNat_add_ofNat]
      rfl
    rw [ea, eb, writeW_pair, readW_pair]
  · rfl
  · rfl

 def copyCode (n : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    copyPair (8 * j) (256 + 8 * j)

structure CopyPost (base : Addr) (s : State) (n : Nat) (s' : State) : Prop where
  keys : ∀ i < n, s'.mem.readW (base + BitVec.ofNat 64 (256 + 8 * i)) 64 =
    s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r
  frame : Frame [⟨base + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copy_ok (s : State) (n : Nat) (hn : n ≤ 16)
    (fit : (s.gpr .r2).toNat + 384 ≤ 2 ^ 32)
    (hr : ∀ i < 16, ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (8 * i + 4 * t))) 4)
    (hw : ∀ i < 16, ∀ t < 2, InRegions s.wr
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (256 + 8 * i + 4 * t))) 4) :
    WP isa (.block (copyCode n)) s (CopyPost (State.addr (s.gpr .r2)) s n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ hi => by omega, rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [copyCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    apply WP.mono (ih (by omega))
    intro s₁ h₁
    have hbase : s₁.gpr .r2 = s.gpr .r2 := h₁.reg .r2 (by decide) (by decide)
    have readable : ∀ t < 2, InRegions (s₁.rd ++ s₁.wr)
        (State.addr (s₁.gpr .r2 + BitVec.ofNat 32 (8 * n + 4 * t))) 4 := by
      rw [h₁.rd, h₁.wr, hbase]; exact hr n (by omega)
    have writable : ∀ t < 2, InRegions s₁.wr
        (State.addr (s₁.gpr .r2 + BitVec.ofNat 32 (256 + 8 * n + 4 * t))) 4 := by
      rw [h₁.wr, hbase]; exact hw n (by omega)
    have fit₁ : (s₁.gpr .r2).toNat + max (8 * n) (256 + 8 * n) + 8 ≤ 2 ^ 32 := by
      rw [hbase, Nat.max_eq_right (by omega : 8 * n ≤ 256 + 8 * n)]
      omega_using [fit, hn]
    obtain ⟨s₂, run₂, keep₂⟩ := copyPair_ok s₁ (8 * n) (256 + 8 * n)
      (by omega) (by omega) fit₁ readable writable
    have source : s₁.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 (8 * n)) 64 =
        s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 (8 * n)) 64 := by
      apply h₁.frame.readW (r := ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 (8 * n), 8⟩)
        (Region.contains_self _ _) _ (by decide)
      intro r h
      obtain rfl := List.mem_singleton.mp h
      exact Offset.disjoint (State.addr (s.gpr .r2)) (by omega) (by omega) (by decide)
    have mem₂ : s₂.mem = s₁.mem.writeW (State.addr (s.gpr .r2) + BitVec.ofNat 64 (256 + 8 * n))
        (s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 (8 * n)) 64) := by
      have hm := keep₂.mem
      rw [hbase, addr_add (by omega_using [fit, hn]),
        addr_add (by omega_using [fit, hn]), source] at hm
      exact hm
    refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr,
      fun r h4 h5 => (keep₂.reg r (by
        simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using And.intro h4 h5)).trans (h₁.reg r h4 h5), ?_⟩⟩
    · intro i hi
      rw [mem₂]
      by_cases he : i = n
      · subst i; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep (State.addr (s.gpr .r2)) (by omega) (by omega) (by omega)) (by decide)]
        exact h₁.keys i (by omega)
    · rw [mem₂]
      apply h₁.frame.writeW (List.mem_singleton_self _) _
      have hc := Offset.contains_base (State.addr (s.gpr .r2) + BitVec.ofNat 64 256)
        (d := 8 * n) (n := 8) (k := 128) (by omega) (by omega)
      rw [Offset.add_ofNat_add_ofNat] at hc
      exact hc


end VG.Proof.TripleDes.Arm.Key

end

/-! ## `Composition` -/

section

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm
open VG.Proof.TripleDes (componentKeys componentOffset)

abbrev keyR (s : State) : Region := ⟨(State.addr (s.gpr .r0)), (s.gpr .r1).toNat⟩
abbrev outputR (s : State) : Region := ⟨(State.addr (s.gpr .r2)), 384⟩

def slot (base : Addr) (c j : Nat) : Addr := base + BitVec.ofNat 64 (128 * c + 8 * j)

structure Components (origin s : State) (done : Nat) : Prop where
  keys : ∀ c < done, ∀ j < 16, s.mem.readW (slot ((State.addr (origin.gpr .r2))) c j) 64 =
    ((componentKeys origin.mem ((State.addr (origin.gpr .r0))) (origin.gpr .r1).toNat c).getD j 0).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  reg : ∀ r ∈ keyKept, s.gpr r = origin.gpr r
  frame : Frame [outputR origin] origin.mem s.mem

structure Permissions (s : State) : Prop where
  reads : ∀ offset, offset + 4 ≤ (s.gpr .r1).toNat →
    InRegions (s.rd ++ s.wr) ((State.addr (s.gpr .r0)) + BitVec.ofNat 64 offset) 4
  writes : ∀ offset, offset + 4 ≤ 384 → InRegions s.wr ((State.addr (s.gpr .r2)) + BitVec.ofNat 64 offset) 4
  keyOutput : (keyR s).Disjoint (outputR s)
  valid : Spec.TripleDes.validKey (s.gpr .r1).toNat
  keyFit : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  outputFit : (s.gpr .r2).toNat + 384 ≤ 2 ^ 32

theorem componentStep_ok (origin s : State) (c : Nat) (hc : c < 3)
    (hp : Permissions origin) (hs : Components origin s c)
    (hoff : componentOffset (origin.gpr .r1).toNat c = 8 * c) :
    WP isa (Impl.TripleDes.Arm.Key.component (8 * c) c) s
      (Components origin · (c + 1)) := by
  have offsetBound := VG.Proof.TripleDes.componentOffset_bound _ c hp.valid hc
  rw [hoff] at offsetBound
  have keyFit : (s.gpr .r0).toNat + 8 * c + 8 ≤ 2 ^ 32 := by
    rw [hs.reg .r0 (by decide)]
    omega_using [hp.keyFit, offsetBound]
  have outputFit : (s.gpr .r2).toNat + 384 ≤ 2 ^ 32 := by
    rw [hs.reg .r2 (by decide)]; exact hp.outputFit
  have read : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r0 + BitVec.ofNat 32 (8 * c + 4 * t))) 4 := by
    intro t ht
    rw [hs.rd, hs.wr, hs.reg .r0 (by decide), addr_add (by omega_using [hp.keyFit, offsetBound, ht])]
    exact hp.reads _ (by omega_using [offsetBound, ht])
  have write : ∀ j < 16, ∀ t < 2, InRegions s.wr
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (128 * c) +
        BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 (4 * t))) 4 := by
    intro j hj t ht
    rw [hs.wr, hs.reg .r2 (by decide), Offset.add_ofNat_add_ofNat,
      Offset.add_ofNat_add_ofNat, addr_add (by omega_using [hp.outputFit, hc, hj, ht])]
    exact hp.writes _ (by omega_using [hc, hj, ht])
  apply WP.mono (component_ok s (8 * c) c hc (by omega) keyFit outputFit read write)
  intro t ht
  have frame : Frame [⟨(State.addr (origin.gpr .r2)) + BitVec.ofNat 64 (128 * c), 128⟩] s.mem t.mem := by
    have hf := ht.frame
    rw [hs.reg .r2 (by decide), addr_add (by omega_using [hp.outputFit, hc])] at hf
    exact hf
  have key : Spec.TripleDes.blockAt s.mem ((State.addr (s.gpr .r0)) + BitVec.ofNat 64 (8 * c)) =
      Spec.TripleDes.blockAt origin.mem ((State.addr (origin.gpr .r0)) + BitVec.ofNat 64 (8 * c)) := by
    rw [hs.reg .r0 (by decide)]
    apply VG.Proof.TripleDes.blockAt_eq_of_frame _ hs.frame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hp.keyOutput.sub_left (Offset.sub_base _ offsetBound)
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun r hr => (ht.reg r hr).trans (hs.reg r hr), hs.frame.trans (frame.sub ?_)⟩
  · intro k hk j hj
    by_cases he : k = c
    · subst k
      have h := ht.keys j hj
      rw [addr_add (a := s.gpr .r0) (k := 8 * c) (by omega_using [keyFit]), key, hs.reg .r2 (by decide),
        addr_add (by omega_using [hp.outputFit, hc]), Offset.add_ofNat_add_ofNat] at h
      unfold componentKeys
      rw [hoff]
      exact h
    · have before : k < c := by omega_using [hk, he]
      have sep : (Region.mk (slot ((State.addr (origin.gpr .r2))) k j) 8).Disjoint
          ⟨(State.addr (origin.gpr .r2)) + BitVec.ofNat 64 (128 * c), 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [hk, hc, hj]) (by omega_using [hc])
      have hmem := frame.readW (a := slot ((State.addr (origin.gpr .r2))) k j) (w := 64) (r := ⟨slot ((State.addr (origin.gpr .r2))) k j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys k before j hj)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by omega_using [hc])⟩

theorem copyThird_ok (origin s : State) (hp : Permissions origin)
    (hs : Components origin s 2) (hn : (origin.gpr .r1).toNat = 16) :
    WP isa (.block Impl.TripleDes.Arm.Key.copyThird) s (Components origin · 3) := by
  have fit : (s.gpr .r2).toNat + 384 ≤ 2 ^ 32 := by
    rw [hs.reg .r2 (by decide)]; exact hp.outputFit
  have reads : ∀ i < 16, ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (8 * i + 4 * t))) 4 := by
    intro i hi t ht
    rw [hs.rd, hs.wr, hs.reg .r2 (by decide), addr_add (by omega_using [hp.outputFit, hi, ht])]
    obtain ⟨r, hr, hc⟩ := hp.writes (8 * i + 4 * t) (by omega_using [hi, ht])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writes : ∀ i < 16, ∀ t < 2, InRegions s.wr
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (256 + 8 * i + 4 * t))) 4 := by
    intro i hi t ht
    rw [hs.wr, hs.reg .r2 (by decide), addr_add (by omega_using [hp.outputFit, hi, ht])]
    exact hp.writes _ (by omega_using [hi, ht])
  have code : Impl.TripleDes.Arm.Key.copyThird = copyCode 16 := rfl
  rw [code]
  apply WP.mono (copy_ok s 16 (by decide) fit reads writes)
  intro t ht
  have frame : Frame [⟨(State.addr (origin.gpr .r2)) + BitVec.ofNat 64 256, 128⟩] s.mem t.mem := by
    have h := ht.frame
    rw [hs.reg .r2 (by decide)] at h
    exact h
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr, ?_, hs.frame.trans (frame.sub ?_)⟩
  · intro c hc j hj
    by_cases he : c = 2
    · subst c
      have hRepeat : componentKeys origin.mem ((State.addr (origin.gpr .r0))) (origin.gpr .r1).toNat 2 =
          componentKeys origin.mem ((State.addr (origin.gpr .r0))) (origin.gpr .r1).toNat 0 := by
        rw [hn]; rfl
      have h := ht.keys j hj
      rw [hs.reg .r2 (by decide)] at h
      change t.mem.readW ((State.addr (origin.gpr .r2)) + BitVec.ofNat 64 (256 + 8 * j)) 64 = _
      rw [hRepeat]
      have first := hs.keys 0 (by decide) j hj
      simp only [slot, Nat.mul_zero, Nat.zero_add] at first
      exact h.trans first
    · have before : c < 2 := by omega_using [hc, he]
      have sep : (Region.mk (slot ((State.addr (origin.gpr .r2))) c j) 8).Disjoint
          ⟨(State.addr (origin.gpr .r2)) + BitVec.ofNat 64 256, 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [before, hj]) (by decide)
      have hmem := frame.readW (a := slot ((State.addr (origin.gpr .r2))) c j) (w := 64) (r := ⟨slot ((State.addr (origin.gpr .r2))) c j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys c before j hj)
  · intro r hr
    have unused : ∀ r ∈ keyKept, r ≠ .r4 ∧ r ≠ .r5 := by decide
    exact (ht.reg r (unused r hr).1 (unused r hr).2).trans (hs.reg r hr)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by decide)⟩

def componentIndex (i : Nat) : Nat := if i < 16 then 0 else if i < 32 then 1 else 2

theorem index_partition : ∀ i < 48, componentIndex i < 3 ∧ i % 16 < 16 ∧
    8 * i = 128 * componentIndex i + 8 * (i % 16) := by decide

theorem Components.schedule {origin s : State} (h : Components origin s 3) :
    Spec.TripleDes.scheduleAt s.mem ((State.addr (origin.gpr .r2))) =
      VG.Proof.TripleDes.expandedMemory origin.mem ((State.addr (origin.gpr .r0))) (origin.gpr .r1).toNat := by
  apply Vector.ext
  intro i hi
  have fact := index_partition i hi
  have keys := h.keys (componentIndex i) fact.1 (i % 16) fact.2.1
  rw [slot, ← fact.2.2] at keys
  rw [VG.Proof.TripleDes.scheduleAt_readW s.mem ((State.addr (origin.gpr .r2))) i hi]
  simp only [VG.Proof.TripleDes.expandedMemory, Vector.getElem_ofFn]
  by_cases h16 : i < 16
  · simpa only [componentIndex, h16, ite_true] using keys
  · by_cases h32 : i < 32
    · simpa only [componentIndex, h16, h32, ite_false, ite_true] using keys
    · simpa only [componentIndex, h16, h32, ite_false] using keys


end VG.Proof.TripleDes.Arm.Key

end

/-! ## `Body` -/

section

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm VG.Arm.RegUpd
open VG.Proof.Rc2.Arm (Keep)

theorem cmpLength_ok (s : State) :
    ∃ s', runBlock isa [.cmp .r1 (.imm 16)] s = some s' ∧
      isa.eval .eq s' = some (s.gpr .r1 == 16) ∧ Keep [.r4] s s' := by
  refine ⟨subFlags s (s.gpr .r1) 16, ?_, ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  · simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil,
      exec, Op2.eval, ite_true, Option.map_some]
  · change some (s.gpr .r1 - 16 == 0) = _
    exact congrArg some (by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      bv_omega)

theorem Components.keep {origin s t : State} {n : Nat} (hs : Components origin s n)
    (ht : Keep [.r4] s t) : Components origin t n :=
  ⟨fun c hc j hj => by rw [ht.mem]; exact hs.keys c hc j hj,
    ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun r hr => (ht.reg r (by revert hr; cases r <;> decide)).trans (hs.reg r hr), by rw [ht.mem]; exact hs.frame⟩

theorem beq16_toNat (x : BitVec 32) : (x == 16) = decide (x.toNat = 16) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    apply BitVec.eq_of_toNat_eq
    exact h

theorem body_ok (origin s : State) (hp : Permissions origin) (hs : Components origin s 0)
    (Q : State → Prop)
    (finish : ∀ t, Components origin t 3 → WP isa (.block Impl.TripleDes.Arm.Key.restore) t Q) :
    WP isa (.seq (Impl.TripleDes.Arm.Key.component 0 0)
      (.seq (Impl.TripleDes.Arm.Key.component 8 1)
        (.seq (.block [.cmp .r1 (.imm 16)])
          (.seq (.ite .eq (.block Impl.TripleDes.Arm.Key.copyThird)
            (Impl.TripleDes.Arm.Key.component 16 2)) (.block Impl.TripleDes.Arm.Key.restore))))) s Q := by
  apply WP.seq
  apply WP.mono (componentStep_ok origin s 0 (by decide) hp hs (by rfl))
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (componentStep_ok origin s₁ 1 (by decide) hp hs₁ (by rfl))
  intro s₂ hs₂
  apply WP.seq
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := cmpLength_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have hs₃ := hs₂.keep keep₃
  apply WP.seq
  apply WP.mono (Q := (Components origin · 3)) ?_
  · intro t ht
    exact finish t ht
  have flag : isa.eval .eq s₃ = some (decide ((origin.gpr .r1).toNat = 16)) := by
    rw [flag₃, hs₂.reg .r1 (by decide), beq16_toNat]
  by_cases h16 : (origin.gpr .r1).toNat = 16
  · apply WP.ite true (by simpa only [h16, decide_true] using flag)
    · intro _; exact copyThird_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simpa only [h16, decide_false] using flag)
    · simp
    · intro _
      exact componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false])

end VG.Proof.TripleDes.Arm.Key

end
