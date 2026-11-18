module

public import VerifiedGarbage.Impl.Argon2.AArch64.ClearBlock
public import VerifiedGarbage.Proof.Argon2.AArch64.Initialize
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.TCB.AArch64.Simd
import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
public import VerifiedGarbage.Impl.Argon2.AArch64.AddressHeader
public import VerifiedGarbage.Proof.Argon2.AArch64.Memory
public import VerifiedGarbage.Spec.Argon2.Contract

/-! ### `Argon2.AArch64.AddressHeaderWords`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Argon2.AArch64.BlockStore`. -/

@[expose] public section

section
/-! A single matrix or scratch block word write as a vector update. -/

namespace VG.Proof.Argon2.AArch64

open VG VG.Spec.Argon2

theorem blockAt_write (m : Mem) (p : Addr) (i : Fin 128) (v : Word) :
    blockAt (m.writeW (off p (8 * i.val)) v) p = (blockAt m p).set i v := by
  apply Vector.ext
  intro j hj
  simp only [blockAt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases eq : i.val = j
  · subst j
    simp only [ite_true]
    change (m.writeW (off p (8 * i.val)) v).readW (off p (8 * i.val)) 64 = v
    exact Mem.readW_writeW_self64 _ _ _
  · simp only [eq, ite_false]
    change (m.writeW (off p (8 * i.val)) v).readW (off p (8 * j)) 64 =
      m.readW (off p (8 * j)) 64
    exact Mem.readW_writeW_sep (Offset.sep p (by omega_using [eq]) (by omega_using [hj]) (by omega_using [])) (by decide)

theorem blockAt_write_nat (m : Mem) (p : Addr) (i : Nat) (hi : i < 128) (v : Word) :
    blockAt (m.writeW (off p (8 * i)) v) p = (blockAt m p).set i v hi :=
  blockAt_write m p ⟨i, hi⟩ v

end VG.Proof.Argon2.AArch64
end

/-! Short independent-address input header writes. -/

namespace VG.Proof.Argon2.AArch64.AddressHeader

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressHeader

theorem registerWord_ok (s : State) (i : Nat) (r : Reg)
    (hi : i < 128)
    (hw : InRegions s.wr (off (s.gpr .x0) (8 * i)) 8) :
    WP isa (.block (registerWord i r)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x0) (8 * i)) (s.gpr r) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [off] at hw
  have addrBound : (8 * i) % 8 = 0 ∧ 8 * i < 32768 := by omega_using [hi]
  apply WP.of_runBlock
  simp only [registerWord, VG.Impl.Argon2.AArch64.Instructions.store,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, addrBound, hw,
    and_self, ite_true, State.store, State.read, BitVec.setWidth_eq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial⟩

theorem frameWord_ok (s : State) (i offset : Nat) (hi : i < 128)
    (ha : offset % 8 = 0) (hb : offset + 8 ≤ 272)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) offset) 8)
    (hw : InRegions s.wr (off (s.gpr .x0) (8 * i)) 8) :
    WP isa (.block (frameWord i offset)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x0) (8 * i))
        (s.mem.readW (off (s.gpr .x19) offset) 64) ∧
      (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [off] at hr hw
  have addrBound : (8 * i) % 8 = 0 ∧ 8 * i < 32768 := by omega_using [hi]
  have offsetBound : offset % 8 = 0 ∧ offset < 32768 := ⟨ha, by omega_using [hb]⟩
  apply WP.of_runBlock
  simp only [frameWord, VG.Impl.Argon2.AArch64.Instructions.store,
    VG.Impl.Argon2.AArch64.Instructions.load,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, addrBound,
    offsetBound, hr, hw, and_self, ite_true, State.store, State.load, State.read,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.setWidth_eq, reduceCtorEq, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, trivial, trivial, rfl⟩
  intro r hr
  simp only [hr, ite_false]

end VG.Proof.Argon2.AArch64.AddressHeader

end

end

/-! ### `Argon2.AArch64.MemoryInitClearMemory`, which this module and modules that import it used -/

section

/-! # Zeroing the Argon2 matrix, independently of its initial contents -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit

def clearMem (m : Mem) (p : Addr) : Nat → Mem
  | 0 => m
  | n + 1 => (clearMem m p n).writeW (p + BitVec.ofNat 64 (8 * n)) (0 : BitVec 64)

theorem clearMem_frame (m : Mem) (p : Addr) (n : Nat) (bound : 8 * n < 2 ^ 64) :
    Frame [⟨p, 8 * n⟩] m (clearMem m p n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    have smaller : Frame [⟨p, 8 * (n + 1)⟩] m (clearMem m p n) :=
      (ih (by omega_using [bound])).sub (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [])⟩)
    exact smaller.writeW (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains_base _ (by omega_using []) (by omega_using [bound]))

theorem clearMem_word (m : Mem) (p : Addr) (n j : Nat)
    (bound : 8 * n < 2 ^ 64) (hj : j < n) :
    (clearMem m p n).readW (p + BitVec.ofNat 64 (8 * j)) 64 = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [clearMem]
    by_cases eq : j = n
    · subst j; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep ?_ (by decide)]
      · exact ih (by omega_using [bound]) (by omega_using [hj, eq])
      · exact Offset.sep p (by omega_using [eq]) (by omega_using [bound, hj]) (by omega_using [bound])

end VG.Proof.Argon2.AArch64.MemoryInit

end

end

/-! Zero every word, preserving the enclosing loop's registers and memory. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.ClearBlock

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.ClearBlock

theorem word_ok (s : State) (i : Nat) (hi : i < 128)
    (hw : InRegions s.wr (off (s.gpr .x0) (8 * i)) 8) :
    WP isa (.block (Impl.Argon2.AArch64.ClearBlock.word i)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x0) (8 * i)) (s.gpr .x8) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp :=
  AddressHeader.registerWord_ok s i .x8 hi hw

theorem prefix_ok (n : Nat) (hn : n ≤ 128) (s : State) (zero : s.gpr .x8 = 0)
    (write : Covers [⟨s.gpr .x0, 1024⟩] s.wr) :
    WP isa (.block (words n)) s fun t =>
      t.mem = MemoryInit.clearMem s.mem (s.gpr .x0) n ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    simp only [words, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega_using [hn])).mono ?_
    rintro a ⟨mem, regs, rd, wr, mx⟩
    have hw : InRegions a.wr (off (a.gpr .x0) (8 * n)) 8 := by
      rw [regs, wr]
      exact write _ _ ⟨⟨s.gpr .x0, 1024⟩, by simp,
        Offset.contains_base _ (d := 8 * n) (n := 8) (k := 1024) (by omega_using [hn]) (by omega_using [hn])⟩
    refine (word_ok a n (by omega_using [hn]) hw).mono ?_
    rintro t ⟨mem', regs', rd', wr', mx'⟩
    refine ⟨?_, regs'.trans regs, rd'.trans rd, wr'.trans wr, mx'.trans mx⟩
    rw [mem', regs, zero, mem]
    rfl

theorem zero_ok (s : State) :
    WP isa (.block [VG.Impl.Argon2.AArch64.Instructions.imm .x8 0].flatten) s fun t =>
      t.gpr .x8 = 0 ∧ (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.Instructions.imm,
    show 0 < 65536 from by decide, ite_true, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro r hr
  exact ite_eq_right hr

theorem code_ok (s : State) (write : Covers [⟨s.gpr .x0, 1024⟩] s.wr) :
    WP isa code s fun t => blockAt t.mem (s.gpr .x0) = zeroBlock ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.sp = s.sp := by
  unfold code
  refine WP.seq ((zero_ok s).mono ?_)
  rintro a ⟨zero, regs, mem, rd, wr, mx⟩
  have dest : a.gpr .x0 = s.gpr .x0 := regs .x0 (by decide)
  have write' : Covers [⟨a.gpr .x0, 1024⟩] a.wr := by rw [dest, wr]; exact write
  refine (prefix_ok 128 (by decide) a zero write').mono ?_
  rintro t ⟨mem', regs', rd', wr', mx'⟩
  have cleared : t.mem = MemoryInit.clearMem s.mem (s.gpr .x0) 128 := by
    rw [mem', mem, dest]
  refine ⟨?_, ?_, ⟨fun r hr _ => (congrFun regs' r).trans (regs r hr), rd'.trans rd, wr'.trans wr⟩,
    mx'.trans mx⟩
  · rw [cleared]
    apply Vector.ext
    intro i hi
    change (blockAt _ _)[(⟨i, hi⟩ : Fin 128)] = zeroBlock[(⟨i, hi⟩ : Fin 128)]
    rw [blockAt_get, MemoryInit.clearMem_word _ _ 128 i (by decide) hi]
    simp only [zeroBlock, Fin.getElem_fin, Vector.getElem_replicate]
  · rw [cleared]
    exact MemoryInit.clearMem_frame _ _ 128 (by decide)

end VG.Proof.Argon2.AArch64.ClearBlock
