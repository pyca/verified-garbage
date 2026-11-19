module

public import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressCall
public import VerifiedGarbage.Impl.Argon2.AArch64.FillCompress
public import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.AArch64.Initialize
import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Argon2.AArch64.CountCandidates
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Argon2.AArch64.BlockAddress
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Argon2.AArch64.BlockAddress
meta import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
public import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
meta import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Argon2.AArch64.Finish
public import VerifiedGarbage.Impl.Argon2.AArch64.FillWrite
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64

/-! ### `Argon2.AArch64.FillWritePrefix`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Argon2.AArch64.FillWriteWord`. -/

@[expose] public section

section
/-! One output word, keeping register writes folded during execution. -/

namespace VG.Proof.Argon2.AArch64.FillWrite

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillWrite
open VG.Impl.Argon2.AArch64

/-- Registers preserved while copying/XORing matrix words and testing the pass. -/
def CopyKeeps (s t : State) : Prop :=
  (∀ r, r ≠ .x8 → r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
    t.rd = s.rd ∧ t.wr = s.wr

theorem CopyKeeps.trans {s t u : State} (h : CopyKeeps s t) (k : CopyKeeps t u) : CopyKeeps s u :=
  ⟨fun r h8 h13 h14 h15 => (k.1 r h8 h13 h14 h15).trans (h.1 r h8 h13 h14 h15),
    k.2.1.trans h.2.1, k.2.2.trans h.2.2⟩

def value (xorOld : Bool) (m : Mem) (src dest : Addr) (i : Nat) : Addr :=
  let next := m.readW (off src (8 * i)) 64
  if xorOld then next ^^^ m.readW (off dest (8 * i)) 64 else next

/-- The source is readable and the destination writable; its old contents
are read only on later passes. -/
theorem pair_ok (xorOld : Bool) (s : State) (i : Nat) (hi : i < 64)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x1) (16 * i)) 16)
    (hw : InRegions s.wr (off (s.gpr .x0) (16 * i)) 16)
    (ho : InRegions (s.rd ++ s.wr) (off (s.gpr .x0) (16 * i)) 16) :
    WP isa (.block (Impl.Argon2.AArch64.FillWrite.pair xorOld i)) s fun t =>
      t.mem = (s.mem.writeW (off (s.gpr .x0) (8 * (2 * i)))
          (value xorOld s.mem (s.gpr .x1) (s.gpr .x0) (2 * i))).writeW
        (off (s.gpr .x0) (8 * (2 * i + 1)))
          (value xorOld s.mem (s.gpr .x1) (s.gpr .x0) (2 * i + 1)) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have e : (16 * i) % 16 = 0 ∧ 16 * i < 65536 := by omega_using [hi]
  simp only [off] at hr hw ho
  have a0 : 8 * (2 * i) = 16 * i := by omega_using []
  have a1 : 8 * (2 * i + 1) = 16 * i + 8 := by omega_using []
  cases xorOld
  · refine WP.block_cons_iff.mpr ⟨_, exec_ldrq_dwords e hr, ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_strq_write e hw, ?_⟩
    refine WP.block_nil ⟨?_, rfl, rfl, rfl, rfl⟩
    simp only [RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.v_setV_self, write16_dwords,
      Offset.add_add, value, off, a0, a1, Bool.false_eq_true, ite_false]
  · refine WP.block_cons_iff.mpr ⟨_, exec_ldrq_dwords e hr, ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_ldrq_dwords e ho, ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_eor_v, ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_strq_write e hw, ?_⟩
    refine WP.block_nil ⟨?_, rfl, rfl, rfl, rfl⟩
    simp only [RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.v_setV_self,
      RegUpd.v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1), ofVDwords_xor, write16_dwords,
      Offset.add_add, value, off, a0, a1, ite_true]

end VG.Proof.Argon2.AArch64.FillWrite
end

/-! Compose the pair writes without re-executing a long load/store block. -/

namespace VG.Proof.Argon2.AArch64.FillWrite

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillWrite

def result (xorOld : Bool) (m : Mem) (src dest : Addr) : Block :=
  if xorOld then xorBlock (blockAt m src) (blockAt m dest) else blockAt m src

theorem result_get (xorOld : Bool) (m : Mem) (src dest : Addr) (i : Fin 128) :
    (result xorOld m src dest)[i] = value xorOld m src dest i.val := by
  cases xorOld <;> simp only [result, value, Bool.false_eq_true, ite_false, ite_true,
    xorBlock_get, blockAt_get]

theorem frame_extend {m m' : Mem} {dest : Addr} {n k : Nat}
    (hf : Frame [⟨dest, 8 * n⟩] m m') (h : n ≤ k) : Frame [⟨dest, 8 * k⟩] m m' := by
  apply hf.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨_, by simp, Region.sub_prefix (Nat.mul_le_mul_left 8 h)⟩

theorem source_read {m m' : Mem} {src dest : Addr} {n : Nat}
    (hf : Frame [⟨dest, 8 * n⟩] m m') (hn : n ≤ 128)
    (hd : (⟨src, 1024⟩ : Region).Disjoint ⟨dest, 1024⟩) (i : Fin 128) :
    m'.readW (off src (8 * i.val)) 64 = m.readW (off src (8 * i.val)) 64 := by
  have full := frame_extend hf hn
  exact full.readW (r := ⟨src, 1024⟩)
    (Offset.contains_base src (by omega_using []) (by omega_using []))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

theorem old_read {m m' : Mem} {dest : Addr} {n k : Nat}
    (hf : Frame [⟨dest, 8 * n⟩] m m') (hk : n ≤ k) (hk' : k < 128) :
    m'.readW (off dest (8 * k)) 64 = m.readW (off dest (8 * k)) 64 :=
  hf.readW (r := ⟨off dest (8 * k), 8⟩) (Region.contains_self _ _)
    (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact Offset.disjoint_base dest (by omega_using [hk]) (by omega_using [hk'])) (by decide)

theorem prefix_ok (xorOld : Bool) (n : Nat) (hn : n ≤ 64) (s : State)
    (hs : (⟨s.gpr .x1, 1024⟩ : Region) ∈ s.rd ++ s.wr)
    (hw : (⟨s.gpr .x0, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩) :
    WP isa (.block (words xorOld n)) s fun t =>
      Written t.mem (s.gpr .x0) (result xorOld s.mem (s.gpr .x1) (s.gpr .x0)) (2 * n) ∧
      Frame [⟨s.gpr .x0, 8 * (2 * n)⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    simp only [words, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega_using [hn])).mono ?_
    rintro t ⟨written, frame, gpr, rd, wr, mx⟩
    have hn' : n < 64 := by omega_using [hn]
    have src : t.gpr .x1 = s.gpr .x1 := congrFun gpr .x1
    have dest : t.gpr .x0 = s.gpr .x0 := congrFun gpr .x0
    have write : InRegions t.wr (off (t.gpr .x0) (16 * n)) 16 := by
      rw [dest, wr]
      exact ⟨_, hw, Offset.contains_base _ (by omega_using [hn]) (by omega_using [hn])⟩
    have read : InRegions (t.rd ++ t.wr) (off (t.gpr .x1) (16 * n)) 16 := by
      rw [src, rd, wr]
      exact ⟨_, hs, Offset.contains_base _ (by omega_using [hn]) (by omega_using [hn])⟩
    have old : InRegions (t.rd ++ t.wr) (off (t.gpr .x0) (16 * n)) 16 := by
      obtain ⟨r, hr, hc⟩ := write
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    refine (pair_ok xorOld t n hn' read write old).mono ?_
    rintro u ⟨mem, gpr', rd', wr', mx'⟩
    have v (k : Nat) (hk : k < 128) (hk' : 2 * n ≤ k) :
        value xorOld t.mem (t.gpr .x1) (t.gpr .x0) k =
          (result xorOld s.mem (s.gpr .x1) (s.gpr .x0))[(⟨k, hk⟩ : Fin 128)] := by
      rw [result_get, src, dest]
      unfold value
      rw [source_read frame (by omega_using [hn]) hd ⟨k, hk⟩]
      cases xorOld
      · rfl
      · rw [old_read frame hk' hk]
    refine ⟨?_, ?_, gpr'.trans gpr, rd'.trans rd, wr'.trans wr, mx'.trans mx⟩
    · rw [mem, v (2 * n) (by omega_using [hn]) (by omega_using []), v (2 * n + 1) (by omega_using [hn]) (by omega_using []), dest,
        show 2 * (n + 1) = 2 * n + 1 + 1 by omega_using []]
      exact written_step (by omega_using [hn]) (written_step (by omega_using [hn]) written)
    · rw [mem, dest]
      exact ((frame_extend frame (by omega_using [] : 2 * n ≤ 2 * (n + 1))).writeW
        (r := ⟨s.gpr .x0, 8 * (2 * (n + 1))⟩) (by simp) _
        (Offset.contains_base _ (by omega_using []) (by omega_using [hn]))).writeW
        (r := ⟨s.gpr .x0, 8 * (2 * (n + 1))⟩) (by simp) _
        (Offset.contains_base _ (by omega_using []) (by omega_using [hn]))

end VG.Proof.Argon2.AArch64.FillWrite
end

end

/-! ### `Argon2.AArch64.BlockAddress`, which the modules that import this one used -/

section

/-! ### `Argon2.AArch64.MemoryInitScale`, which this module and modules that import it used -/

section

/-! # Fixed scaling by public powers of two on ARM64 -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.MemoryInit
open VG VG.AArch64 VG.Impl.Argon2.AArch64

structure Scaled (s t : State) (r : Reg) (n : Nat) : Prop where
  value : t.gpr r = s.gpr r * BitVec.ofNat 64 (2 ^ n)
  other : ∀ q, q ≠ r → q ≠ .x15 → t.gpr q = s.gpr q
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem double_ok (s : State) (r : Reg) :
    WP isa (.block (Instructions.add r r)) s fun t =>
      t.gpr r = s.gpr r + s.gpr r ∧
      (∀ q, q ≠ r → q ≠ .x15 → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [Instructions.add, Instructions.mark, Instructions.mov,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun q hq hq' => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq, BitVec.add_zero, ite_self]
  · simp only [RegUpd.gpr_write, hq, hq', ite_false]

theorem scale_ok (s : State) (r : Reg) (n : Nat) :
    WP isa (.block (List.replicate n (Instructions.add r r)).flatten) s
      fun t => Scaled s t r n := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨by rw [Nat.pow_zero]; exact (BitVec.mul_one _).symm,
      fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons]
    rw [WP.block_append_iff]
    refine (double_ok s r).mono ?_
    rintro a ⟨value, other, mem, rd, wr, sp⟩
    refine (ih a).mono ?_
    intro t ht
    refine ⟨?_, fun q hq hq' => (ht.other q hq hq').trans (other q hq hq'),
      ht.mem.trans mem, ht.rd.trans rd, ht.wr.trans wr, ht.sp.trans sp⟩
    rw [ht.value, value, ← BitVec.mul_two, Nat.pow_succ, BitVec.ofNat_mul,
      BitVec.mul_assoc]
    exact congrArg (fun v => s.gpr r * v) (BitVec.mul_comm _ _)
end VG.Proof.Argon2.AArch64.MemoryInit

end

end

/-! Fault-free matrix pointer calculation, with no memory accesses. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.BlockAddress

open VG VG.AArch64 VG.Impl.Argon2.AArch64.BlockAddress
open VG.Impl.Argon2.AArch64

theorem flatten_ok (s : State) : WP isa (.block flatten) s fun t =>
    t.gpr .x8 = s.gpr .x8 * s.gpr .x20 + s.gpr .x3 ∧
    Divide.Keeps [.x8, .x2, .x15] s t := by
  apply WP.of_runBlock
  simp only [flatten, Instructions.mul, Instructions.add, Instructions.mark, Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem scale_ok (s : State) : WP isa (.block scale) s fun t =>
    t.gpr .x8 = s.gpr .x8 * 1024 ∧ Divide.Keeps [.x8, .x15] s t := by
  refine (MemoryInit.scale_ok s .x8 10).mono ?_
  intro t h
  refine ⟨h.value, ?_, h.mem, h.rd, h.wr, h.sp⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact h.other r hr.1 hr.2

theorem base_ok (s : State) : WP isa (.block ([Instructions.add .x8 .x4].flatten)) s fun t =>
    t.gpr .x8 = s.gpr .x8 + s.gpr .x4 ∧ Divide.Keeps [.x8, .x15] s t := by
  apply WP.of_runBlock
  simp only [Instructions.add, Instructions.mark, Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x8 = (s.gpr .x8 * s.gpr .x20 + s.gpr .x3) * 1024 + s.gpr .x4 ∧
    Divide.Keeps [.x8, .x2, .x15] s t := by
  unfold code
  refine WP.seq ((flatten_ok s).mono ?_)
  rintro a ⟨flat, ka⟩
  refine WP.seq ((scale_ok a).mono ?_)
  rintro b ⟨scaled, kb⟩
  refine (base_ok b).mono ?_
  rintro t ⟨result, kt⟩
  refine ⟨?_, ka.trans ((kb.mono (by decide)).trans (kt.mono (by decide)))⟩
  rw [result, scaled, flat, kb.regs .x4 (by decide), ka.regs .x4 (by decide)]

theorem code_nat_ok (s : State) (lane column q : Nat)
    (hl : s.gpr .x8 = BitVec.ofNat 64 lane)
    (hc : s.gpr .x3 = BitVec.ofNat 64 column)
    (hq : s.gpr .x20 = BitVec.ofNat 64 q) :
    WP isa code s fun t =>
      t.gpr .x8 = s.gpr .x4 + BitVec.ofNat 64 ((lane * q + column) * 1024) ∧
      Divide.Keeps [.x8, .x2, .x15] s t := by
  refine (code_ok s).mono ?_
  rintro t ⟨h, k⟩
  refine ⟨?_, k⟩
  rw [h, hl, hc, hq, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  change BitVec.ofNat 64 (lane * q + column) * BitVec.ofNat 64 1024 + s.gpr .x4 = _
  rw [← BitVec.ofNat_mul, BitVec.add_comm]

end VG.Proof.Argon2.AArch64.BlockAddress

end

end

/-! ### `Argon2.AArch64.FillWriteCover`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Argon2.AArch64.FillWrite`. -/

@[expose] public section

section
/-! Whole-block first-pass copying and later-pass XOR, with a frame proof. -/

namespace VG.Proof.Argon2.AArch64.FillWrite

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillWrite

theorem code_ok (s : State)
    (hs : (⟨s.gpr .x1, 1024⟩ : Region) ∈ s.rd ++ s.wr)
    (hw : (⟨s.gpr .x0, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩) :
    WP isa code s fun t =>
      blockAt t.mem (s.gpr .x0) =
        (if s.gpr .x5 = 0 then blockAt s.mem (s.gpr .x1)
          else xorBlock (blockAt s.mem (s.gpr .x1)) (blockAt s.mem (s.gpr .x0))) ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.sp = s.sp := by
  unfold code
  refine WP.seq ((CountCandidates.compare_ok s).mono ?_)
  rintro a ⟨flag, ka⟩
  have src : a.gpr .x1 = s.gpr .x1 := ka.regs .x1 (by simp)
  have dest : a.gpr .x0 = s.gpr .x0 := ka.regs .x0 (by simp)
  have hs' : (⟨a.gpr .x1, 1024⟩ : Region) ∈ a.rd ++ a.wr := by
    rw [src, ka.rd, ka.wr]; exact hs
  have hw' : (⟨a.gpr .x0, 1024⟩ : Region) ∈ a.wr := by
    rw [dest, ka.wr]; exact hw
  have hd' : (⟨a.gpr .x1, 1024⟩ : Region).Disjoint ⟨a.gpr .x0, 1024⟩ := by
    rw [src, dest]; exact hd
  refine WP.ite (decide (s.gpr .x5 = 0)) (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag, Bool.beq_eq_decide_eq]) ?_ ?_
  · intro h
    have zero := of_decide_eq_true h
    refine (prefix_ok false 64 (by decide) a hs' hw' hd').mono ?_
    rintro t ⟨written, frame, gpr, rd, wr, mx⟩
    have keeps : CopyKeeps a t := ⟨fun r _ _ _ _ => congrFun gpr r, rd, wr⟩
    refine ⟨?_, ?_, ?_, mx.trans ka.sp⟩
    · rw [dest] at written
      rw [ite_eq_left zero, written_block written]
      simp only [result, Bool.false_eq_true, ite_false, ka.mem, src]
    · rw [dest, ka.mem] at frame; exact frame
    · exact (show CopyKeeps s a from ⟨fun r _ h13 h14 h15 => ka.regs r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h13, h14, h15⟩), ka.rd, ka.wr⟩).trans keeps
  · intro h
    have nonzero := of_decide_eq_false h
    refine (prefix_ok true 64 (by decide) a hs' hw' hd').mono ?_
    rintro t ⟨written, frame, gpr, rd, wr, mx⟩
    have keeps : CopyKeeps a t := ⟨fun r _ _ _ _ => congrFun gpr r, rd, wr⟩
    refine ⟨?_, ?_, ?_, mx.trans ka.sp⟩
    · rw [dest] at written
      rw [ite_eq_right nonzero, written_block written]
      simp only [result, ite_true, ka.mem, src]
    · rw [dest, ka.mem] at frame; exact frame
    · exact (show CopyKeeps s a from ⟨fun r _ h13 h14 h15 => ka.regs r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h13, h14, h15⟩), ka.rd, ka.wr⟩).trans keeps

end VG.Proof.Argon2.AArch64.FillWrite
end

/-! Use block writes in a matrix allocation with larger permission regions. -/

namespace VG.Proof.Argon2.AArch64.FillWrite

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillWrite

theorem code_cover_ok (s : State)
    (hs : Covers [⟨s.gpr .x1, 1024⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨s.gpr .x0, 1024⟩] s.wr)
    (hd : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩) :
    WP isa code s fun t =>
      blockAt t.mem (s.gpr .x0) =
        (if s.gpr .x5 = 0 then blockAt s.mem (s.gpr .x1)
          else xorBlock (blockAt s.mem (s.gpr .x1)) (blockAt s.mem (s.gpr .x0))) ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.sp = s.sp := by
  let a := s.withRegions [⟨s.gpr .x1, 1024⟩] [⟨s.gpr .x0, 1024⟩]
  obtain ⟨tr, t, he, value, frame, keeps, mx⟩ := code_ok a (by simp [a]) (by simp [a]) hd
  have cover : Covers (a.rd ++ a.wr) (s.rd ++ s.wr) := by
    intro p n ⟨r, hr, hc⟩
    change r ∈ [⟨s.gpr .x1, 1024⟩, ⟨s.gpr .x0, 1024⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs p n ⟨_, by simp, hc⟩
    · obtain ⟨r, hr, hc⟩ := hw p n ⟨_, by simp, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  have he' := Exec.widen (rd := s.rd) (wr := s.wr) he cover hw
  simp only [a, State.withRegions_withRegions, State.withRegions_self] at he'
  refine ⟨tr, t.withRegions s.rd s.wr, he', value, frame, ?_, mx⟩
  exact ⟨keeps.1, rfl, rfl⟩

end VG.Proof.Argon2.AArch64.FillWrite

end

end

/-! ### `Argon2.AArch64.FillCompressOperation`, which only this module used -/

section

/-! Merged from `Proof.Argon2.AArch64.FillCompressArgs`. -/

@[expose] public section

section
/-! Save the current cell across G and reload the block-write arguments. -/
namespace VG.Proof.Argon2.AArch64.FillCompress
open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillCompress
open VG.Impl.Argon2.AArch64

theorem saveCurrent_ok (s : State)
    (hw : InRegions s.wr (off (s.gpr .x19) 16) 8) :
    WP isa (.block saveCurrent) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x19) 16) (s.gpr .x6) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [saveCurrent, Instructions.store, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, State.store, State.read, Size.bytes, and_self, Option.bind_some, Size.bits, BitVec.setWidth_eq, hw,
    show 16 % 8 = 0 ∧ 16 < 4096 * 8 from by decide,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial⟩

theorem compressArgs_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8) :
    WP isa (.block compressArgs) s fun t =>
      t.gpr .x3 = s.mem.readW (off (s.gpr .x19) 248) 64 ∧
      t.gpr .x2 = s.mem.readW (off (s.gpr .x19) 248) 64 + 4096 ∧ Divide.Keeps [.x3, .x2, .x12, .x15] s t := by
  simp only [off] at hr
  apply WP.of_runBlock
  simp only [compressArgs, Instructions.load, Instructions.mov, Instructions.addi,
    Instructions.imm, Instructions.mark, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bytes, off, and_self, Option.map_some, Option.bind_some,
    State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    hr,
    show 248 % 8 = 0 ∧ 248 < 4096 * 8 from by decide,
    show 0 < 4096 from by decide,
    show ¬4096 < 4096 from by decide,
    show 4096 < 65536 from by decide,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero, BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem writeArgs_ok (s : State)
    (destRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 16) 8)
    (workRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8) :
    WP isa (.block writeArgs) s fun t =>
      t.gpr .x0 = s.mem.readW (off (s.gpr .x19) 16) 64 ∧
      t.gpr .x1 = s.mem.readW (off (s.gpr .x19) 248) 64 + 4096 ∧
      t.gpr .x5 = s.mem.readW (off (s.gpr .x19) 0) 64 ∧ Divide.Keeps [.x0, .x1, .x5, .x12, .x15] s t := by
  simp only [off, BitVec.add_zero] at destRead workRead passRead
  apply WP.of_runBlock
  simp only [writeArgs, Instructions.load, Instructions.mov, Instructions.addi,
    Instructions.imm, Instructions.mark, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bytes, off, and_self, Option.map_some, Option.bind_some,
    State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, Size.bits, BitVec.setWidth_eq,
    show 16 % 8 = 0 ∧ 16 < 4096 * 8 from by decide,
    show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide, BitVec.add_zero,
    destRead, workRead, passRead,
    show 248 % 8 = 0 ∧ 248 < 4096 * 8 from by decide,
    show 0 < 4096 from by decide,
    show ¬4096 < 4096 from by decide,
    show 4096 < 65536 from by decide,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero, BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.AArch64.FillCompress
end

/-! Compression followed by first/later-pass writing, preserving the frame
slots and the old destination cell across the compression call. -/

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillCompress

def callWrites (s : State) : List Region :=
  [⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x3, 4096⟩, below s.sp 8]

def destination (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 16) 64

def pass (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 0) 64

structure OperationReady (s : State) : Prop where
  call : CallReady s
  frameRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  workWord : s.mem.readW (off (s.gpr .x19) 248) 64 = s.gpr .x3
  outputPointer : s.gpr .x3 + 4096 = s.gpr .x2
  destinationWrite : Covers [⟨destination s, 1024⟩] s.wr
  frameSafe : ∀ r ∈ callWrites s, (⟨s.gpr .x19, 272⟩ : Region).Disjoint r
  destinationSafe : ∀ r ∈ callWrites s, (⟨destination s, 1024⟩ : Region).Disjoint r

structure OperationDone (s t : State) : Prop where
  block : blockAt t.mem (destination s) =
    let next := Spec.Argon2.compress (blockAt s.mem (s.gpr .x0)) (blockAt s.mem (s.gpr .x1))
    if pass s = 0 then next else xorBlock next (blockAt s.mem (destination s))
  regs : ∀ r ∈ loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (⟨destination s, 1024⟩ :: callWrites s) s.mem t.mem

theorem frame_word {s t : State} (h : OperationReady s) (called : Called s t)
    (d : Nat) (hd : d + 8 ≤ 272) :
    t.mem.readW (off (s.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 :=
  called.frame.readW (r := ⟨s.gpr .x19, 272⟩)
    (Offset.contains_base _ hd (by omega_using [hd])) h.frameSafe (by decide)

theorem destination_unchanged {s t : State} (h : OperationReady s) (called : Called s t) :
    blockAt t.mem (destination s) = blockAt s.mem (destination s) := by
  apply Vector.ext
  intro i hi
  have read : t.mem.readW (off (destination s) (8 * i)) 64 =
      s.mem.readW (off (destination s) (8 * i)) 64 :=
    called.frame.readW (r := ⟨destination s, 1024⟩)
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) h.destinationSafe (by decide)
  rw [← blockAt_get t.mem (destination s) ⟨i, hi⟩,
    ← blockAt_get s.mem (destination s) ⟨i, hi⟩] at read
  exact read

theorem operation_ok (s : State) (h : OperationReady s) :
    WP isa operation s (OperationDone s) := by
  unfold operation
  refine WP.seq ((call_ok _ s h.call).mono ?_)
  intro a called
  have bp : a.gpr .x19 = s.gpr .x19 := called.regs .x19 (by simp [loopRegs])
  have reads (d : Nat) (hd : d ∈ [0, 16, 248]) :
      InRegions (a.rd ++ a.wr) (off (a.gpr .x19) d) 8 := by
    rw [called.rd, called.wr, bp]; exact h.frameRead d hd
  refine WP.seq ((writeArgs_ok a (reads 16 (by simp)) (reads 248 (by simp))
    (reads 0 (by simp))).mono ?_)
  rintro b ⟨dest, src, counter, keeps⟩
  have dest' : b.gpr .x0 = destination s := by
    rw [dest, bp, frame_word h called 16 (by decide), destination]
  have src' : b.gpr .x1 = s.gpr .x2 := by
    rw [src, bp, frame_word h called 248 (by decide), h.workWord, h.outputPointer]
  have counter' : b.gpr .x5 = pass s := by
    rw [counter, bp, frame_word h called 0 (by decide), pass]
  have readable : Covers [⟨b.gpr .x1, 1024⟩] (b.rd ++ b.wr) := by
    rw [src', keeps.rd, keeps.wr, called.rd, called.wr]
    intro p n hp
    obtain ⟨r, hr, hc⟩ := h.call.output p n hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writable : Covers [⟨b.gpr .x0, 1024⟩] b.wr := by
    rw [dest', keeps.wr, called.wr]; exact h.destinationWrite
  have sep : (⟨b.gpr .x1, 1024⟩ : Region).Disjoint ⟨b.gpr .x0, 1024⟩ := by
    rw [src', dest']; exact (h.destinationSafe _ (by simp [callWrites])).symm
  refine (FillWrite.code_cover_ok b readable writable sep).mono ?_
  rintro t ⟨value, frame, tk, tsp⟩
  refine ⟨?_, ?_, tk.2.1.trans (keeps.rd.trans called.rd),
    tk.2.2.trans (keeps.wr.trans called.wr), tsp.trans (keeps.sp.trans called.sp), ?_⟩
  · rw [dest', src', counter', keeps.mem, called.result, destination_unchanged h called] at value
    exact value
  · intro r hr
    have safe : r ≠ .x8 ∧ r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x15 ∧
        r ∉ [Reg.x0, .x1, .x5, .x12, .x15] := by
      simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (tk.1 r safe.1 safe.2.1 safe.2.2.1 safe.2.2.2.1).trans
      ((keeps.regs r safe.2.2.2.2).trans (called.regs r hr))
  · rw [dest'] at frame
    rw [keeps.mem] at frame
    exact (called.frame.mono (by intro r hr; exact List.mem_cons_of_mem _ hr)).trans
      (frame.mono (by simp))

end VG.Proof.Argon2.AArch64.FillCompress

end

end


/-! Establish compression-and-write invariants from the frame and allocations. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillCompress

def work (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 248) 64

def prefixWrites (s : State) : List Region := [⟨off (s.gpr .x19) 16, 8⟩]

structure Ready (s : State) : Prop where
  frameRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  frameWrite : InRegions s.wr (off (s.gpr .x19) 16) 8
  leftRead : Covers [⟨s.gpr .x0, 1024⟩] (s.rd ++ s.wr)
  rightRead : Covers [⟨s.gpr .x1, 1024⟩] (s.rd ++ s.wr)
  destinationWrite : Covers [⟨s.gpr .x6, 1024⟩] s.wr
  workWrite : Covers [⟨work s, 5120⟩] s.wr
  leftWork : (⟨s.gpr .x0, 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  rightWork : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  destinationWork : (⟨s.gpr .x6, 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  frameWork : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨work s, 5120⟩
  leftFrame : (⟨s.gpr .x0, 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  rightFrame : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  destinationFrame : (⟨s.gpr .x6, 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  stackLeft : (below s.sp 8).Disjoint ⟨s.gpr .x0, 1024⟩
  stackRight : (below s.sp 8).Disjoint ⟨s.gpr .x1, 1024⟩
  stackWork : (below s.sp 8).Disjoint ⟨work s, 5120⟩
  destinationStack : (⟨s.gpr .x6, 1024⟩ : Region).Disjoint (below s.sp 8)
  frameStack : (⟨s.gpr .x19, 272⟩ : Region).Disjoint (below s.sp 8)

structure Prepared (s t : State) : Prop where
  ready : OperationReady t
  dest : destination t = s.gpr .x6
  counter : pass t = pass s
  scratch : t.gpr .x3 = work s
  output : t.gpr .x2 = work s + 4096
  left : t.gpr .x0 = s.gpr .x0
  right : t.gpr .x1 = s.gpr .x1
  regs : ∀ r ∈ loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (prefixWrites s) s.mem t.mem
  leftBlock : blockAt t.mem (t.gpr .x0) = blockAt s.mem (s.gpr .x0)
  rightBlock : blockAt t.mem (t.gpr .x1) = blockAt s.mem (s.gpr .x1)
  oldBlock : blockAt t.mem (destination t) = blockAt s.mem (s.gpr .x6)

theorem block_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (p : Addr) (sep : ∀ r ∈ rs, (⟨p, 1024⟩ : Region).Disjoint r) :
    blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  have read : m'.readW (off p (8 * i)) 64 = m.readW (off p (8 * i)) 64 :=
    hf.readW (r := ⟨p, 1024⟩) (Offset.contains_base p (by omega_using [hi]) (by omega_using [hi])) sep (by decide)
  rw [← blockAt_get m' p ⟨i, hi⟩, ← blockAt_get m p ⟨i, hi⟩] at read
  exact read

theorem work_cover (s : State) (h : Ready s) (d n : Nat) (hd : d + n ≤ 5120) :
    Covers [⟨off (work s) d, n⟩] s.wr := by
  have sub : Covers [⟨off (work s) d, n⟩] [⟨work s, 5120⟩] := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨work s, 5120⟩, by simp, d, rfl, hd⟩
  exact fun p n hp => h.workWrite p n (sub p n hp)

theorem prepared_of_setup (s a b : State) (h : Ready s)
    (mem : a.mem = s.mem.writeW (off (s.gpr .x19) 16) (s.gpr .x6))
    (regs : a.gpr = s.gpr) (rd : a.rd = s.rd) (wr : a.wr = s.wr) (sp : a.sp = s.sp)
    (scratch : b.gpr .x3 = a.mem.readW (off (a.gpr .x19) 248) 64)
    (output : b.gpr .x2 = a.mem.readW (off (a.gpr .x19) 248) 64 + 4096)
    (keeps : Divide.Keeps [.x3, .x2, .x12, .x15] a b) : Prepared s b := by
  have g (r : Reg) (hr : r ∉ [Reg.x3, .x2, .x12, .x15]) : b.gpr r = s.gpr r :=
    (keeps.regs r hr).trans (congrFun regs r)
  have brd : b.rd = s.rd := keeps.rd.trans rd
  have bwr : b.wr = s.wr := keeps.wr.trans wr
  have bsp : b.sp = s.sp := keeps.sp.trans sp
  have bm : b.mem = s.mem.writeW (off (s.gpr .x19) 16) (s.gpr .x6) := keeps.mem.trans mem
  have unchanged (d : Nat) (sep : d + 8 ≤ 16 ∨ 24 ≤ d) (bound : d + 8 ≤ 272) :
      b.mem.readW (off (b.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
    rw [bm, g .x19 (by decide)]
    exact Mem.readW_writeW_sep (Offset.sep _ sep (by omega_using [bound]) (by decide)) (by decide)
  have work' : b.gpr .x3 = work s := by
    rw [scratch, regs, mem]
    exact Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)
  have out' : b.gpr .x2 = work s + 4096 := by
    rw [output, regs, mem,
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), work]
  have dest : destination b = s.gpr .x6 := by
    unfold destination
    rw [bm, g .x19 (by decide), Mem.readW_writeW_self64]
  have counter : pass b = pass s := unchanged 0 (by decide) (by decide)
  have frame : Frame (prefixWrites s) s.mem b.mem := by
    rw [bm]
    exact (Frame.refl _ _).writeW (r := ⟨off (s.gpr .x19) 16, 8⟩) (by simp [prefixWrites]) _
      (Region.contains_self _ _)
  have cellFrame (p : Addr) (sep : (⟨p, 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩) :
      blockAt b.mem p = blockAt s.mem p :=
    block_frame frame p (by
      intro r hr
      simp only [prefixWrites, List.mem_singleton] at hr
      subst r
      exact sep.sub_right (Offset.sub_base _ (by decide)))
  have tempSub : Region.Sub ⟨work s + 4096, 1024⟩ ⟨work s, 5120⟩ :=
    Offset.sub_base _ (by decide)
  have scratchSub : Region.Sub ⟨work s, 4096⟩ ⟨work s, 5120⟩ := Region.sub_prefix (by decide)
  refine ⟨?_, dest, counter, work', out', g .x0 (by decide), g .x1 (by decide), ?_, brd, bwr, bsp,
    frame, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [g .x0 (by decide), brd, bwr]; exact h.leftRead
      · rw [g .x1 (by decide), brd, bwr]; exact h.rightRead
      · rw [out', bwr]; exact work_cover s h 4096 1024 (by decide)
      · rw [work', bwr]
        simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
          using work_cover s h 0 4096 (by decide)
      · rw [g .x0 (by decide), work']; exact h.leftWork.sub_right scratchSub
      · rw [g .x1 (by decide), work']; exact h.rightWork.sub_right scratchSub
      · rw [out', work']; exact Offset.disjoint_base _ (by decide) (by decide)
      · rw [bsp, g .x0 (by decide)]; exact h.stackLeft
      · rw [bsp, g .x1 (by decide)]; exact h.stackRight
      · rw [bsp, out']; exact h.stackWork.sub_right tempSub
      · rw [bsp, work']; exact h.stackWork.sub_right scratchSub
    · intro d hd
      rw [brd, bwr, g .x19 (by decide)]; exact h.frameRead d hd
    · rw [unchanged 248 (by decide) (by decide), work']; rfl
    · rw [work', out']
    · rw [dest, bwr]; exact h.destinationWrite
    · intro r hr
      simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [g .x19 (by decide), out']; exact h.frameWork.sub_right tempSub
      · rw [g .x19 (by decide), work']; exact h.frameWork.sub_right scratchSub
      · rw [g .x19 (by decide), bsp]; exact h.frameStack
    · intro r hr
      rw [dest]
      simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [out']; exact h.destinationWork.sub_right tempSub
      · rw [work']; exact h.destinationWork.sub_right scratchSub
      · rw [bsp]; exact h.destinationStack
  · intro r hr
    apply g r
    simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [g .x0 (by decide)]; exact cellFrame _ h.leftFrame
  · rw [g .x1 (by decide)]; exact cellFrame _ h.rightFrame
  · rw [dest]; exact cellFrame _ h.destinationFrame

theorem setup_ok (s : State) (h : Ready s) :
    WP isa setup s (Prepared s) := by
  unfold setup
  refine WP.seq ((saveCurrent_ok s h.frameWrite).mono ?_)
  rintro a ⟨mem, regs, rd, wr, sp⟩
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 248) 8 := by
    rw [rd, wr, regs]; exact h.frameRead 248 (by simp)
  refine (compressArgs_ok a read).mono ?_
  rintro b ⟨scratch, output, keeps⟩
  exact prepared_of_setup s a b h mem regs rd wr sp scratch output keeps

end VG.Proof.Argon2.AArch64.FillCompress
