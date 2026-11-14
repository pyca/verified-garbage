module

public import VerifiedGarbage.Proof.Rc2.AArch64.Lookup
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.TripleDes.AArch64.Lit
public import VerifiedGarbage.Proof.TripleDes.KeyMemory
public import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Load
import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Rotation
import VerifiedGarbage.Proof.TripleDes.AArch64.Word
import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Permutation
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.TripleDes.KeySchedule
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.TripleDes.Bytes

/-! ### `TripleDes.AArch64.Key.Copy`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64
open VG.Proof.Rc2.AArch64 (Keep)

theorem copy64_ok (s : State) (src dst : Reg) (a b : Nat) (hne : dst ≠ .x4)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 a) 8)
    (writable : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 b) 8)
    (ha : a % 8 = 0 ∧ a < 32768 := by decide)
    (hb : b % 8 = 0 ∧ b < 32768 := by decide) :
    ∃ s', runBlock isa [.ldr .x .x4 src a, .str .x .x4 dst b] s = some s' ∧
      Keep [.x4] {s with
        mem := s.mem.writeW (s.gpr dst + BitVec.ofNat 64 b) (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)} s' := by
  have hw : InRegions (s.write .x .x4 (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)).wr
      ((s.write .x .x4 (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)).gpr dst + BitVec.ofNat 64 b) 8 := by
    simpa only [wr_write, gpr_write, hne, ite_false] using writable
  refine ⟨_, by
    rw [runBlock_cons, exec_ldr_x ha readable, runStep_some,
      runBlock_cons, exec_str_x hb hw, runStep_some, runBlock_nil], ?_⟩
  constructor
  · intro r hr
    have hn : r ≠ .x4 := by intro h; subst r; exact hr (by simp)
    exact gpr_write_of_ne _ _ _ hn
  · simp only [gpr_write, hne, ite_false, ite_true, BitVec.setWidth_eq, mem_write]
  · rfl
  · rfl

 def copyCode (n : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    [.ldr .x .x4 .x2 (8 * j), .str .x .x4 .x2 (256 + 8 * j)]

structure CopyPost (base : Addr) (s : State) (n : Nat) (s' : State) : Prop where
  keys : ∀ i < n, s'.mem.readW (base + BitVec.ofNat 64 (256 + 8 * i)) 64 =
    s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .x4 → s'.gpr r = s.gpr r
  frame : Frame [⟨base + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copy_ok (s : State) (n : Nat) (hn : n ≤ 16)
    (hr : ∀ i < 16, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8)
    (hw : ∀ i < 16, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (256 + 8 * i)) 8) :
    WP isa (.block (copyCode n)) s (CopyPost (s.gpr .x2) s n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ hi => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [copyCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    apply WP.mono (ih (by omega_using [hn]))
    intro s₁ h₁
    have hbase : s₁.gpr .x2 = s.gpr .x2 := h₁.reg .x2 (by decide)
    have readable : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x2 + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [h₁.rd, h₁.wr, hbase]; exact hr n (by omega_using [hn])
    have writable : InRegions s₁.wr (s₁.gpr .x2 + BitVec.ofNat 64 (256 + 8 * n)) 8 := by
      rw [h₁.wr, hbase]; exact hw n (by omega_using [hn])
    obtain ⟨s₂, run₂, keep₂⟩ := copy64_ok s₁ .x2 .x2
      (8 * n) (256 + 8 * n) (by decide) readable writable (by omega_using [hn]) (by omega_using [hn])
    have source : s₁.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (8 * n)) 64 =
        s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (8 * n)) 64 := by
      apply h₁.frame.readW (r := ⟨s.gpr .x2 + BitVec.ofNat 64 (8 * n), 8⟩)
        (Region.contains_self _ _) _ (by decide)
      intro r h
      obtain rfl := List.mem_singleton.mp h
      exact Offset.disjoint (s.gpr .x2) (by omega_using [hn]) (by omega_using [hn]) (by decide)
    have mem₂ : s₂.mem = s₁.mem.writeW (s.gpr .x2 + BitVec.ofNat 64 (256 + 8 * n))
        (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (8 * n)) 64) := by
      have hm := keep₂.mem
      rw [hbase, source] at hm
      exact hm
    refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr,
      fun r hr => (keep₂.reg r (by simpa only [List.mem_singleton] using hr)).trans (h₁.reg r hr), ?_⟩⟩
    · intro i hi
      rw [mem₂]
      by_cases he : i = n
      · subst i; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep (s.gpr .x2) (by omega_using [he]) (by omega_using [hn, hi]) (by omega_using [hn])) (by decide)]
        exact h₁.keys i (by omega_using [hi, he])
    · rw [mem₂]
      apply h₁.frame.writeW (List.mem_singleton_self _) _
      have hc := Offset.contains_base (s.gpr .x2 + BitVec.ofNat 64 256)
        (d := 8 * n) (n := 8) (k := 128) (by omega_using [hn]) (by omega_using [hn])
      rw [Offset.add_ofNat_add_ofNat] at hc
      exact hc

end VG.Proof.TripleDes.AArch64.Key

end

end

/-! ### `TripleDes.AArch64.Key.Component`, which only this module used -/

section

/-! ### `TripleDes.AArch64.Key.Loop`, which only this module used -/

section

/-! ### `TripleDes.AArch64.Key.Store`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64

def pack : List Instr := [.lsl .x .x4 .x19 28, .logic .eor .x .x4 .x4 .x20]

def tail : List Instr := [.str .x .x5 .x22 0, .addImm .x .x22 .x22 8,
  .addImm .x .x21 .x21 1, .subImm .x .x4 .x21 16]

theorem pack_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .x19 = c.setWidth 64) (hd : s.gpr .x20 = d.setWidth 64) :
    ∃ s', runBlock isa pack s = some s' ∧
      (s'.gpr .x4).setWidth 56 = c ++ d ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .x4 → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [pack, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show (28 : Nat) < 64 from by decide, ite_true, State.read,
      BitVec.setWidth_eq, gpr_write_self]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
    rw [hc, hd]; exact pack28_shift c d
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · intro r hr; simp only [gpr_write, hr, ite_false]

theorem nextRound_values : ∀ j < 16,
    BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) ∧
    ((BitVec.ofNat 64 j + 1 - (16 : BitVec 64)) != 0) = decide (j ≠ 15) := by decide

theorem tail_ok (s : State) (j : Nat) (hj : j < 16)
    (hc : s.gpr .x21 = BitVec.ofNat 64 j)
    (hw : InRegions s.wr (s.gpr .x22) 8) :
    ∃ s', runBlock isa tail s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .x22) (s.gpr .x5) ∧
      s'.gpr .x22 = s.gpr .x22 + 8 ∧ s'.gpr .x21 = BitVec.ofNat 64 (j + 1) ∧
      isa.eval (.nonzero .x .x4) s' = some (decide (j ≠ 15)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .x4 → r ≠ .x21 → r ≠ .x22 → s'.gpr r = s.gpr r) := by
  have hstore := exec_str_x (t := .x5) (n := .x22) (off := 0) (by decide)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw)
  refine ⟨_, by
    rw [tail, runBlock_cons, hstore, runStep_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show (8 : Nat) < 4096 from by decide, show (1 : Nat) < 4096 from by decide,
      show (16 : Nat) < 4096 from by decide, ite_true, State.read, BitVec.setWidth_eq,
      gpr_write, reduceCtorEq, ite_false, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_write, BitVec.add_zero]
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
    rw [hc]; exact (nextRound_values j hj).1
  · change VG.AArch64.eval (.nonzero .x .x4) _ = _
    simp only [VG.AArch64.eval, State.read, gpr_write, BitVec.setWidth_eq,
      reduceCtorEq, ite_true, ite_false, hc]
    exact congrArg some (nextRound_values j hj).2
  · simp only [rd_write]
  · simp only [wr_write]
  · intro r h4 h21 h22; simp only [gpr_write, h4, h21, h22, ite_false]

structure StorePost (c d : BitVec 28) (j : Nat) (s s' : State) : Prop where
  mem : s'.mem = s.mem.writeW (s.gpr .x22) ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64)
  ptr : s'.gpr .x22 = s.gpr .x22 + 8
  counter : s'.gpr .x21 = BitVec.ofNat 64 (j + 1)
  flag : isa.eval (.nonzero .x .x4) s' = some (decide (j ≠ 15))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ (keyKept ++ [.x19, .x20]), s'.gpr r = s.gpr r

theorem storeRound_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .x19 = c.setWidth 64) (hd : s.gpr .x20 = d.setWidth 64)
    (hjreg : s.gpr .x21 = BitVec.ofNat 64 j) (hw : InRegions s.wr (s.gpr .x22) 8) :
    WP isa (.block Impl.TripleDes.AArch64.Key.storeRound) s (StorePost c d j s) := by
  have code : Impl.TripleDes.AArch64.Key.storeRound =
      (pack ++ permuteCode Spec.TripleDes.pc2 56 .x5 .x4 .x6 .x7) ++ tail := rfl
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, reg₁⟩ := pack_ok s c d hc hd
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, _, mem₂, reg₂⟩ := pc2_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [word₁] at word₂
  have checks : ∀ r ∈ (keyKept ++ [.x19, .x20, .x21, .x22]),
      ((instrs keyPermutation2.lit).all fun op => !clobbers op r) = true := by decide +kernel
  have keep₂ : ∀ r ∈ (keyKept ++ [.x19, .x20, .x21, .x22]), s₂.gpr r = s.gpr r := by
    intro r hr
    have unused : ∀ r ∈ (keyKept ++ [.x19, .x20, .x21, .x22]), r ≠ .x4 := by decide
    exact (reg₂ r (checks r hr)).trans (reg₁ r (unused r hr))
  have counter₂ := (keep₂ .x21 (by decide)).trans hjreg
  have write₂ : InRegions s₂.wr (s₂.gpr .x22) 8 := by
    rw [wr₂, wr₁, keep₂ .x22 (by decide)]; exact hw
  obtain ⟨s₃, run₃, mem₃, ptr₃, counter₃, flag₃, rd₃, wr₃, reg₃⟩ := tail_ok s₂ j hj counter₂ write₂
  refine WP.of_runBlock ⟨s₃, run₃, ⟨?_, ?_, counter₃, flag₃, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), ?_⟩⟩
  · rw [mem₃, mem₂, mem₁, keep₂ .x22 (by decide), word₂]
  · rw [ptr₃, keep₂ .x22 (by decide)]
  · intro r hr
    have incl : ∀ r ∈ (keyKept ++ [.x19, .x20]),
        r ≠ .x4 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ∈ (keyKept ++ [.x19, .x20, .x21, .x22]) := by decide
    exact (reg₃ r (incl r hr).1 (incl r hr).2.1 (incl r hr).2.2.1).trans (keep₂ r (incl r hr).2.2.2)

end VG.Proof.TripleDes.AArch64.Key

end

end


@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64
open VG.Proof.TripleDes.AArch64.Key (keyKept)
open VG.Proof.TripleDes (keyPrefix keyInitial keyStep keyPrefix_succ)

structure LoopState (key : BitVec 64) (base : Addr) (origin : State) (j : Nat) (s : State) : Prop where
  c : s.gpr .x19 = (keyPrefix key j).1.setWidth 64
  d : s.gpr .x20 = (keyPrefix key j).2.1.setWidth 64
  counter : s.gpr .x21 = BitVec.ofNat 64 j
  pointer : s.gpr .x22 = base + BitVec.ofNat 64 (8 * j)
  keys : ∀ i < j, ∀ hi : i < 16, s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 =
    ((keyPrefix key j).2.2[i]'hi).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  reg : ∀ r ∈ keyKept, s.gpr r = origin.gpr r
  frame : Frame [⟨base, 128⟩] origin.mem s.mem

def LoopInv (key : BitVec 64) (base : Addr) (origin : State) (n : Nat) (s : State) : Prop :=
  1 ≤ n ∧ n ≤ 16 ∧ LoopState key base origin (16 - n) s

theorem loopBody_ok (key : BitVec 64) (base : Addr) (origin : State)
    (hw : ∀ j < 16, InRegions origin.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (j : Nat) (hj : j < 16) (s : State) (hs : LoopState key base origin j s) :
    WP isa (.seq Impl.TripleDes.AArch64.Key.rotation (.block Impl.TripleDes.AArch64.Key.storeRound)) s
      (fun s' => isa.eval (.nonzero .x .x4) s' = some (decide (j ≠ 15)) ∧ LoopState key base origin (j + 1) s') := by
  apply WP.seq
  apply WP.mono (rotation_ok s _ _ j hj hs.c hs.d hs.counter)
  intro s₁ h₁
  have unused : ∀ r ∈ (keyKept ++ [.x21, .x22]),
      r ≠ .x4 ∧ r ≠ .x19 ∧ r ≠ .x20 := by decide
  have reg₁ : ∀ r ∈ (keyKept ++ [.x21, .x22]), s₁.gpr r = s.gpr r := by
    intro r hr
    exact h₁.reg r (unused r hr).1 (unused r hr).2.1 (unused r hr).2.2
  have write₁ : InRegions s₁.wr (s₁.gpr .x22) 8 := by
    rw [h₁.wr, hs.wr, reg₁ .x22 (by decide), hs.pointer]
    exact hw j hj
  apply WP.mono (storeRound_ok s₁ _ _ j hj h₁.c h₁.d
    ((reg₁ .x21 (by decide)).trans hs.counter) write₁)
  intro s₂ h₂
  have hmem : s₂.mem = s.mem.writeW (base + BitVec.ofNat 64 (8 * j))
      ((Spec.TripleDes.permute Spec.TripleDes.pc2
        ((keyPrefix key j).1.rotateLeft (Spec.TripleDes.rotations.getD j 0) ++
          (keyPrefix key j).2.1.rotateLeft (Spec.TripleDes.rotations.getD j 0))).setWidth 64) := by
    rw [h₂.mem, h₁.mem, reg₁ .x22 (by decide), hs.pointer]
  refine ⟨h₂.flag, ⟨?_, ?_, h₂.counter, ?_, ?_, h₂.rd.trans (h₁.rd.trans hs.rd),
    h₂.wr.trans (h₁.wr.trans hs.wr), ?_, ?_⟩⟩
  · rw [keyPrefix_succ]
    exact (h₂.reg .x19 (by decide)).trans h₁.c
  · rw [keyPrefix_succ]
    exact (h₂.reg .x20 (by decide)).trans h₁.d
  · rw [h₂.ptr, reg₁ .x22 (by decide), hs.pointer]
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
    have incl : ∀ r ∈ keyKept,
        r ∈ (keyKept ++ [.x19, .x20]) ∧
        r ∈ (keyKept ++ [.x21, .x22]) := by decide
    exact (h₂.reg r (incl r hr).1).trans ((reg₁ r (incl r hr).2).trans (hs.reg r hr))
  · rw [hmem]
    exact hs.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base base (by omega_using [hj]) (by omega_using [hj]))

theorem loopStep (key : BitVec 64) (base : Addr) (origin : State)
    (hw : ∀ j < 16, InRegions origin.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (n : Nat) (s : State) (hs : LoopInv key base origin n s) :
    WP isa (.seq Impl.TripleDes.AArch64.Key.rotation (.block Impl.TripleDes.AArch64.Key.storeRound)) s
      (fun s' => (isa.eval (.nonzero .x .x4) s' = some false ∧ LoopState key base origin 16 s') ∨
        (isa.eval (.nonzero .x .x4) s' = some true ∧ ∃ m < n, LoopInv key base origin m s')) := by
  apply WP.mono (loopBody_ok key base origin hw (16 - n) (by omega_using [hs.1]) s hs.2.2)
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

theorem loop_ok (key : BitVec 64) (base : Addr) (s : State)
    (hw : ∀ j < 16, InRegions s.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (hc : s.gpr .x19 = (keyInitial key).1.setWidth 64)
    (hd : s.gpr .x20 = (keyInitial key).2.1.setWidth 64)
    (hcount : s.gpr .x21 = 0) (hptr : s.gpr .x22 = base) :
    WP isa (.loop (.seq Impl.TripleDes.AArch64.Key.rotation
      (.block Impl.TripleDes.AArch64.Key.storeRound)) (.nonzero .x .x4)) s (LoopState key base s 16) := by
  apply WP.loop (M := isa) (body := .seq Impl.TripleDes.AArch64.Key.rotation
      (.block Impl.TripleDes.AArch64.Key.storeRound)) (c := .nonzero .x .x4)
    (Q := LoopState key base s 16) (LoopInv key base s) (loopStep key base s hw) 16 s
  refine ⟨by decide, by decide, hc, hd, hcount, ?_, ?_, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  · exact hptr.trans (BitVec.add_zero base).symm
  · intro i hi
    omega

end VG.Proof.TripleDes.AArch64.Key

end

end


@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64
open VG.Proof.TripleDes.AArch64.Key (keyKept)

structure ComponentPost (keys : Spec.TripleDes.DesSchedule) (base : Addr) (s s' : State) : Prop where
  keys : ∀ i < 16, s'.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 = (keys.getD i 0).setWidth 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ keyKept, s'.gpr r = s.gpr r
  frame : Frame [⟨base, 128⟩] s.mem s'.mem

theorem component_ok (s : State) (offset component : Nat) (hc : component < 3)
    (ho : offset % 8 = 0 ∧ offset < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 offset) 8)
    (hw : ∀ j < 16, InRegions s.wr
      (s.gpr .x2 + BitVec.ofNat 64 (128 * component) + BitVec.ofNat 64 (8 * j)) 8) :
    WP isa (Impl.TripleDes.AArch64.Key.component offset component) s
      (ComponentPost (Spec.TripleDes.expandDesKey (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .x0 + BitVec.ofNat 64 offset))))
        (s.gpr .x2 + BitVec.ofNat 64 (128 * component)) s) := by
  rw [Impl.TripleDes.AArch64.Key.component]
  apply WP.seq
  apply WP.mono (load_ok s offset component hc ho hr)
  intro s₁ h₁
  have writes : ∀ j < 16, InRegions s₁.wr
      (s.gpr .x2 + BitVec.ofNat 64 (128 * component) + BitVec.ofNat 64 (8 * j)) 8 := by
    rw [h₁.wr]; exact hw
  apply WP.mono (loop_ok _ _ s₁ writes h₁.c h₁.d h₁.counter h₁.ptr)
  intro s₂ h₂
  refine ⟨?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), ?_⟩
  · intro i hi
    rw [VG.Proof.TripleDes.expandDesKey_prefix, VG.Proof.TripleDes.vector_getD _ i hi 0]
    exact h₂.keys i hi hi
  · rw [← h₁.mem]
    exact h₂.frame

end VG.Proof.TripleDes.AArch64.Key

end

end


@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64
open VG.Proof.TripleDes (componentKeys componentOffset)

abbrev keyR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
abbrev outputR (s : State) : Region := ⟨s.gpr .x2, 384⟩

def slot (base : Addr) (c j : Nat) : Addr := base + BitVec.ofNat 64 (128 * c + 8 * j)

structure Components (origin s : State) (done : Nat) : Prop where
  keys : ∀ c < done, ∀ j < 16, s.mem.readW (slot (origin.gpr .x2) c j) 64 =
    ((componentKeys origin.mem (origin.gpr .x0) (origin.gpr .x1).toNat c).getD j 0).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  reg : ∀ r ∈ keyKept, s.gpr r = origin.gpr r
  frame : Frame [outputR origin] origin.mem s.mem

structure Permissions (s : State) : Prop where
  reads : ∀ offset, offset + 8 ≤ (s.gpr .x1).toNat →
    InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 offset) 8
  writes : ∀ offset, offset + 8 ≤ 384 → InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 offset) 8
  keyOutput : (keyR s).Disjoint (outputR s)
  valid : Spec.TripleDes.validKey (s.gpr .x1).toNat

theorem componentStep_ok (origin s : State) (c : Nat) (hc : c < 3)
    (hp : Permissions origin) (hs : Components origin s c)
    (hoff : componentOffset (origin.gpr .x1).toNat c = 8 * c) :
    WP isa (Impl.TripleDes.AArch64.Key.component (8 * c) c) s
      (Components origin · (c + 1)) := by
  have offsetBound := VG.Proof.TripleDes.componentOffset_bound _ c hp.valid hc
  rw [hoff] at offsetBound
  have read : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (8 * c)) 8 := by
    rw [hs.rd, hs.wr, hs.reg .x0 (by decide)]
    exact hp.reads _ offsetBound
  have write : ∀ j < 16, InRegions s.wr
      (s.gpr .x2 + BitVec.ofNat 64 (128 * c) + BitVec.ofNat 64 (8 * j)) 8 := by
    intro j hj
    rw [hs.wr, hs.reg .x2 (by decide), Offset.add_ofNat_add_ofNat]
    exact hp.writes _ (by omega_using [hc, hj])
  apply WP.mono (component_ok s (8 * c) c hc (by omega_using [hc]) read write)
  intro t ht
  have frame : Frame [⟨origin.gpr .x2 + BitVec.ofNat 64 (128 * c), 128⟩] s.mem t.mem := by
    have hf := ht.frame
    rw [hs.reg .x2 (by decide)] at hf
    exact hf
  have key : Spec.TripleDes.blockAt s.mem (s.gpr .x0 + BitVec.ofNat 64 (8 * c)) =
      Spec.TripleDes.blockAt origin.mem (origin.gpr .x0 + BitVec.ofNat 64 (8 * c)) := by
    rw [hs.reg .x0 (by decide)]
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
      rw [key, hs.reg .x2 (by decide), Offset.add_ofNat_add_ofNat] at h
      unfold componentKeys
      rw [hoff]
      exact h
    · have before : k < c := by omega_using [hk, he]
      have sep : (Region.mk (slot (origin.gpr .x2) k j) 8).Disjoint
          ⟨origin.gpr .x2 + BitVec.ofNat 64 (128 * c), 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [hk, hc, hj]) (by omega_using [hc])
      have hmem := frame.readW (a := slot (origin.gpr .x2) k j) (w := 64) (r := ⟨slot (origin.gpr .x2) k j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys k before j hj)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by omega_using [hc])⟩

theorem copyThird_ok (origin s : State) (hp : Permissions origin)
    (hs : Components origin s 2) (hn : (origin.gpr .x1).toNat = 16) :
    WP isa (.block Impl.TripleDes.AArch64.Key.copyThird) s (Components origin · 3) := by
  have reads : ∀ i < 16, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hs.rd, hs.wr, hs.reg .x2 (by decide)]
    obtain ⟨r, hr, hc⟩ := hp.writes (8 * i) (by omega_using [hi])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writes : ∀ i < 16, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (256 + 8 * i)) 8 := by
    intro i hi
    rw [hs.wr, hs.reg .x2 (by decide)]
    exact hp.writes _ (by omega_using [hi])
  apply WP.mono (copy_ok s 16 (by decide) reads writes)
  intro t ht
  have frame : Frame [⟨origin.gpr .x2 + BitVec.ofNat 64 256, 128⟩] s.mem t.mem := by
    have h := ht.frame
    rw [hs.reg .x2 (by decide)] at h
    exact h
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr, ?_, hs.frame.trans (frame.sub ?_)⟩
  · intro c hc j hj
    by_cases he : c = 2
    · subst c
      have hRepeat : componentKeys origin.mem (origin.gpr .x0) (origin.gpr .x1).toNat 2 =
          componentKeys origin.mem (origin.gpr .x0) (origin.gpr .x1).toNat 0 := by
        rw [hn]; rfl
      have h := ht.keys j hj
      rw [hs.reg .x2 (by decide)] at h
      change t.mem.readW (origin.gpr .x2 + BitVec.ofNat 64 (256 + 8 * j)) 64 = _
      rw [hRepeat]
      have first := hs.keys 0 (by decide) j hj
      simp only [slot, Nat.mul_zero, Nat.zero_add] at first
      exact h.trans first
    · have before : c < 2 := by omega_using [hc, he]
      have sep : (Region.mk (slot (origin.gpr .x2) c j) 8).Disjoint
          ⟨origin.gpr .x2 + BitVec.ofNat 64 256, 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [before, hj]) (by decide)
      have hmem := frame.readW (a := slot (origin.gpr .x2) c j) (w := 64) (r := ⟨slot (origin.gpr .x2) c j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys c before j hj)
  · intro r hr
    have unused : ∀ r ∈ keyKept, r ≠ .x4 := by decide
    exact (ht.reg r (unused r hr)).trans (hs.reg r hr)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by decide)⟩

def componentIndex (i : Nat) : Nat := if i < 16 then 0 else if i < 32 then 1 else 2

theorem index_partition : ∀ i < 48, componentIndex i < 3 ∧ i % 16 < 16 ∧
    8 * i = 128 * componentIndex i + 8 * (i % 16) := by decide

theorem Components.schedule {origin s : State} (h : Components origin s 3) :
    Spec.TripleDes.scheduleAt s.mem (origin.gpr .x2) =
      VG.Proof.TripleDes.expandedMemory origin.mem (origin.gpr .x0) (origin.gpr .x1).toNat := by
  apply Vector.ext
  intro i hi
  have fact := index_partition i hi
  have keys := h.keys (componentIndex i) fact.1 (i % 16) fact.2.1
  rw [slot, ← fact.2.2] at keys
  rw [VG.Proof.TripleDes.scheduleAt_readW s.mem (origin.gpr .x2) i hi]
  simp only [VG.Proof.TripleDes.expandedMemory, Vector.getElem_ofFn]
  by_cases h16 : i < 16
  · simpa only [componentIndex, h16, ite_true] using keys
  · by_cases h32 : i < 32
    · simpa only [componentIndex, h16, h32, ite_false, ite_true] using keys
    · simpa only [componentIndex, h16, h32, ite_false] using keys


end VG.Proof.TripleDes.AArch64.Key
