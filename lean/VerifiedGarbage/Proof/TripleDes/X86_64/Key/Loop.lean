module

import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Rotation
public import VerifiedGarbage.Impl.TripleDes.X86_64.ExpandKey
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Permutation
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rc2.X86_64.Lookup
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.TripleDes.KeySchedule
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `TripleDes.X86_64.Key.Store`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64
open VG.Proof.Rc2.X86_64 (offset_nat)

def pack : List Instr := [rr .rax .r12, .shift .ror .rax 36, .alu .xor .rax (.reg .r13)]

def tail : List Instr := [.store (memOp .r15 0) .rbx, .alu .add .r15 (.imm 8),
  .alu .add .r14 (.imm 1), .alu .cmp .r14 (.imm 16)]

theorem pack_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .r12 = c.setWidth 64) (hd : s.gpr .r13 = d.setWidth 64) :
    ∃ s', runBlock isa pack s = some s' ∧
      (s'.gpr .rax).setWidth 56 = c ++ d ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [pack, rr, runBlock_cons, runStep_some, exec, execShift,
      readSrc, Option.map_some, gpr_setReg, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    rw [hc, hd]
    exact VG.Proof.TripleDes.pack28_word c d
  · simp only [mem_setReg, mem_setFlags, mem_arithFlags]
  · simp only [rd_setReg, rd_setFlags, rd_arithFlags]
  · simp only [wr_setReg, wr_setFlags, wr_arithFlags]
  · intro r hr
    simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, hr, ite_false]

theorem nextRound_values : ∀ j < 16,
    BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) ∧
    ((BitVec.ofNat 64 j + 1 - (16 : BitVec 64)) == 0) = decide (j = 15) := by decide

theorem tail_ok (s : State) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r14 = BitVec.ofNat 64 j)
    (hw : InRegions s.wr (s.gpr .r15) 8) :
    ∃ s', runBlock isa tail s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r15) (s.gpr .rbx) ∧
      s'.gpr .r15 = s.gpr .r15 + 8 ∧ s'.gpr .r14 = BitVec.ofNat 64 (j + 1) ∧
      s'.zf = some (decide (j = 15)) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) := by
  have hoff : s.gpr .r15 + BitVec.ofInt 64 (Int.ofNat 0) = s.gpr .r15 := BitVec.add_zero _
  refine ⟨_, by
    simp only [tail, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, State.store64, State.ea, memOp, hoff, hw, ite_true, Option.bind_some,
      gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    rw [hc]
    exact (nextRound_values j hj).1
  · rw [zf_arithFlags, hc]
    exact congrArg some (nextRound_values j hj).2
  · simp only [rd_setReg, rd_arithFlags]
  · simp only [wr_setReg, wr_arithFlags]
  · intro r h14 h15
    simp only [gpr_setReg, gpr_arithFlags, h14, h15, ite_false]

structure StorePost (c d : BitVec 28) (j : Nat) (s s' : State) : Prop where
  mem : s'.mem = s.mem.writeW (s.gpr .r15) ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64)
  ptr : s'.gpr .r15 = s.gpr .r15 + 8
  counter : s'.gpr .r14 = BitVec.ofNat 64 (j + 1)
  flag : s'.zf = some (decide (j = 15))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13], s'.gpr r = s.gpr r

theorem storeRound_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r12 = c.setWidth 64) (hd : s.gpr .r13 = d.setWidth 64)
    (hjreg : s.gpr .r14 = BitVec.ofNat 64 j) (hw : InRegions s.wr (s.gpr .r15) 8) :
    WP isa (.block Impl.TripleDes.X86_64.Key.storeRound) s (StorePost c d j s) := by
  have code : Impl.TripleDes.X86_64.Key.storeRound =
      (pack ++ permuteCode Spec.TripleDes.pc2 56 .rbx .rax .rbp) ++ tail := rfl
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, reg₁⟩ := pack_ok s c d hc hd
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, mem₂, reg₂⟩ := pc2_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [word₁] at word₂
  have checks : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13, .r14, .r15],
      ((instrs keyPermutation2.lit).all fun op => op.dst != some r) = true := by decide +kernel
  have keep₂ : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13, .r14, .r15], s₂.gpr r = s.gpr r := by
    intro r hr
    have unused : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13, .r14, .r15], r ≠ .rax := by decide
    exact (reg₂ r (checks r hr)).trans (reg₁ r (unused r hr))
  have counter₂ := (keep₂ .r14 (by decide)).trans hjreg
  have write₂ : InRegions s₂.wr (s₂.gpr .r15) 8 := by
    rw [wr₂, wr₁, keep₂ .r15 (by decide)]; exact hw
  obtain ⟨s₃, run₃, mem₃, ptr₃, counter₃, flag₃, rd₃, wr₃, reg₃⟩ := tail_ok s₂ j hj counter₂ write₂
  refine WP.of_runBlock ⟨s₃, run₃, ⟨?_, ?_, counter₃, flag₃, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), ?_⟩⟩
  · rw [mem₃, mem₂, mem₁, keep₂ .r15 (by decide), word₂]
  · rw [ptr₃, keep₂ .r15 (by decide)]
  · intro r hr
    have incl : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13],
        r ≠ .r14 ∧ r ≠ .r15 ∧ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13, .r14, .r15] := by decide
    exact (reg₃ r (incl r hr).1 (incl r hr).2.1).trans (keep₂ r (incl r hr).2.2)

end VG.Proof.TripleDes.X86_64.Key

end

end


@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64
open VG.Proof.TripleDes (keyPrefix keyInitial keyStep keyPrefix_succ)

structure LoopState (key : BitVec 64) (base : Addr) (origin : State) (j : Nat) (s : State) : Prop where
  c : s.gpr .r12 = (keyPrefix key j).1.setWidth 64
  d : s.gpr .r13 = (keyPrefix key j).2.1.setWidth 64
  counter : s.gpr .r14 = BitVec.ofNat 64 j
  pointer : s.gpr .r15 = base + BitVec.ofNat 64 (8 * j)
  keys : ∀ i < j, ∀ hi : i < 16, s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 =
    ((keyPrefix key j).2.2[i]'hi).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  reg : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp], s.gpr r = origin.gpr r
  frame : Frame [⟨base, 128⟩] origin.mem s.mem

def LoopInv (key : BitVec 64) (base : Addr) (origin : State) (n : Nat) (s : State) : Prop :=
  1 ≤ n ∧ n ≤ 16 ∧ LoopState key base origin (16 - n) s

theorem loopBody_ok (key : BitVec 64) (base : Addr) (origin : State)
    (hw : ∀ j < 16, InRegions origin.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (j : Nat) (hj : j < 16) (s : State) (hs : LoopState key base origin j s) :
    WP isa (.seq Impl.TripleDes.X86_64.Key.rotation (.block Impl.TripleDes.X86_64.Key.storeRound)) s
      (fun s' => s'.zf = some (decide (j = 15)) ∧ LoopState key base origin (j + 1) s') := by
  apply WP.seq
  apply WP.mono (rotation_ok s _ _ j hj hs.c hs.d hs.counter)
  intro s₁ h₁
  have unused : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r14, .r15],
      r ≠ .rax ∧ r ≠ .r12 ∧ r ≠ .r13 := by decide
  have reg₁ : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r14, .r15], s₁.gpr r = s.gpr r := by
    intro r hr
    exact h₁.reg r (unused r hr).1 (unused r hr).2.1 (unused r hr).2.2
  have write₁ : InRegions s₁.wr (s₁.gpr .r15) 8 := by
    rw [h₁.wr, hs.wr, reg₁ .r15 (by decide), hs.pointer]
    exact hw j hj
  apply WP.mono (storeRound_ok s₁ _ _ j hj h₁.c h₁.d
    ((reg₁ .r14 (by decide)).trans hs.counter) write₁)
  intro s₂ h₂
  have hmem : s₂.mem = s.mem.writeW (base + BitVec.ofNat 64 (8 * j))
      ((Spec.TripleDes.permute Spec.TripleDes.pc2
        ((keyPrefix key j).1.rotateLeft (Spec.TripleDes.rotations.getD j 0) ++
          (keyPrefix key j).2.1.rotateLeft (Spec.TripleDes.rotations.getD j 0))).setWidth 64) := by
    rw [h₂.mem, h₁.mem, reg₁ .r15 (by decide), hs.pointer]
  refine ⟨h₂.flag, ⟨?_, ?_, h₂.counter, ?_, ?_, h₂.rd.trans (h₁.rd.trans hs.rd),
    h₂.wr.trans (h₁.wr.trans hs.wr), ?_, ?_⟩⟩
  · rw [keyPrefix_succ]
    exact (h₂.reg .r12 (by decide)).trans h₁.c
  · rw [keyPrefix_succ]
    exact (h₂.reg .r13 (by decide)).trans h₁.d
  · rw [h₂.ptr, reg₁ .r15 (by decide), hs.pointer]
    change base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 8 = _
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => base + BitVec.ofNat 64 n) (by omega_using [])
  · intro i hi hi16
    rw [hmem, keyPrefix_succ]
    by_cases he : i = j
    · subst i
      rw [Mem.readW_writeW_self64]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_self hj).symm
    · rw [Mem.readW_writeW_sep (Offset.sep base (by omega_using [hi, he])
        (by omega_using [hi16]) (by omega_using [hj])) (by decide), hs.keys i (by omega_using [hi, he]) hi16]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_ne hi16 (Ne.symm he)).symm
  · intro r hr
    have incl : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp],
        r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13] ∧
        r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r14, .r15] := by decide
    exact (h₂.reg r (incl r hr).1).trans ((reg₁ r (incl r hr).2).trans (hs.reg r hr))
  · rw [hmem]
    exact hs.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base base (by omega_using [hj]) (by omega_using [hj]))

theorem loopStep (key : BitVec 64) (base : Addr) (origin : State)
    (hw : ∀ j < 16, InRegions origin.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (n : Nat) (s : State) (hs : LoopInv key base origin n s) :
    WP isa (.seq Impl.TripleDes.X86_64.Key.rotation (.block Impl.TripleDes.X86_64.Key.storeRound)) s
      (fun s' => (isa.eval .ne s' = some false ∧ LoopState key base origin 16 s') ∨
        (isa.eval .ne s' = some true ∧ ∃ m < n, LoopInv key base origin m s')) := by
  apply WP.mono (loopBody_ok key base origin hw (16 - n) (by omega_using [hs.1]) s hs.2.2)
  intro s' h
  by_cases last : n = 1
  · left
    have idx : 16 - n = 15 := by omega_using [last]
    refine ⟨?_, ?_⟩
    · simp only [eval, h.1, idx, decide_true, Option.map_some, Bool.not_true]
    · simpa only [idx] using h.2
  · right
    have idx : ¬16 - n = 15 := by omega_using [hs.1, hs.2.1, last]
    refine ⟨?_, n - 1, by omega_using [hs.1], ?_⟩
    · simp only [eval, h.1, idx, decide_false, Option.map_some, Bool.not_false]
    · refine ⟨by omega_using [hs.1, last], by omega_using [hs.2.1], ?_⟩
      have eq : 16 - n + 1 = 16 - (n - 1) := by omega_using [hs.1, hs.2.1]
      rw [← eq]
      exact h.2

theorem loop_ok (key : BitVec 64) (base : Addr) (s : State)
    (hw : ∀ j < 16, InRegions s.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (hc : s.gpr .r12 = (keyInitial key).1.setWidth 64)
    (hd : s.gpr .r13 = (keyInitial key).2.1.setWidth 64)
    (hcount : s.gpr .r14 = 0) (hptr : s.gpr .r15 = base) :
    WP isa (.loop (.seq Impl.TripleDes.X86_64.Key.rotation
      (.block Impl.TripleDes.X86_64.Key.storeRound)) .ne) s (LoopState key base s 16) := by
  apply WP.loop (M := isa) (body := .seq Impl.TripleDes.X86_64.Key.rotation
      (.block Impl.TripleDes.X86_64.Key.storeRound)) (c := .ne)
    (Q := LoopState key base s 16) (LoopInv key base s) (loopStep key base s hw) 16 s
  refine ⟨by decide, by decide, hc, hd, hcount, ?_, ?_, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  · exact hptr.trans (BitVec.add_zero base).symm
  · intro i hi
    omega

end VG.Proof.TripleDes.X86_64.Key
