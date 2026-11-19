module

import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Range
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Contract
public meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Semantics
public meta import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Target
public meta import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Spec.Sm3
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa
meta import VerifiedGarbage.Spec.Sm3
meta import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Sm3.Spec
public import VerifiedGarbage.Impl.Sm3.RISCV64
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Sm3.Spec
meta import VerifiedGarbage.Impl.Sm3.RISCV64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import Mathlib.Data.List.Nodup
meta import Mathlib.Tactic.SplitIfs

/-! ### `Sm3.RISCV64.Rounds`, which only this module used -/

section

/-!
# SM3 compression function on RISC-V: the message expansion and the iterations

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/Sm3/PPC64LE/Compress.lean`), with the words the low 32 bits of
the registers (`Vars`), as in the SHA-256 proofs
(`Proof/Sha256/RISCV64/Rounds.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm3.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.Sm3.RISCV64 VG.Impl.Words.RISCV64
open VG.Spec.Sm3 (HashValue Word Block W p0 p1 ff gg)

/-- The registers `v` are in the low words of the registers of iteration `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  (s.gpr (var t 0)).setWidth 32 = v[0] ∧ (s.gpr (var t 1)).setWidth 32 = v[1] ∧
  (s.gpr (var t 2)).setWidth 32 = v[2] ∧ (s.gpr (var t 3)).setWidth 32 = v[3] ∧
  (s.gpr (var t 4)).setWidth 32 = v[4] ∧ (s.gpr (var t 5)).setWidth 32 = v[5] ∧
  (s.gpr (var t 6)).setWidth 32 = v[6] ∧ (s.gpr (var t 7)).setWidth 32 = v[7]

/-- The pointers, the count, the return address and the callee-saved
registers the iterations do not use: never written by the iterations. -/
def pubRegs : List Reg := [.a0, .a1, .a2, .a3, .ra, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9,
  .s10, .s11]

/-- `A … D` move one register along each iteration, and so do `E … H`:
the new `A` and `E` are written over `D` and `H`. -/
theorem var_succ (t : Nat) :
    var (t + 1) 0 = var t 3 ∧ var (t + 1) 1 = var t 0 ∧ var (t + 1) 2 = var t 1 ∧
    var (t + 1) 3 = var t 2 ∧ var (t + 1) 4 = var t 7 ∧ var (t + 1) 5 = var t 4 ∧
    var (t + 1) 6 = var t 5 ∧ var (t + 1) 7 = var t 6 := by
  simp only [var]
  rw [show (t + 1) % 4 = (t % 4 + 1) % 4 by omega_using []]
  have := Nat.mod_lt t (show 4 > 0 by decide)
  generalize t % 4 = c at *
  revert this; revert c; decide

/-- The registers of an iteration are all different. -/
theorem round_nodup (t : Nat) :
    ([var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, T0, T1, T2, T3] ++
      pubRegs).Nodup := by
  simp only [var]
  have := Nat.mod_lt t (show 4 > 0 by decide)
  generalize t % 4 = c at *
  revert this; revert c; decide

theorem slot_lt (j : Nat) : slot j < 2048 := by
  simp only [slot]; omega_using []

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : Addr) (j : Nat) : Addr := scr + BitVec.ofNat 64 (slot j)

/-- With `scratch` 8-byte aligned, the slots are naturally aligned. -/
theorem slot_al {scr : Addr} (hal : scr.toNat % 8 = 0) (j : Nat) :
    (scr + BitVec.ofNat 64 (slot j)).toNat % 4 = 0 := by
  simp only [slot]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * (j % 16)) (by omega_using [])]
  have := scr.isLt
  omega_using [hal]

/-- A load of a slot, with `scratch` (`a3`) aligned. -/
theorem exec_lw_slot {s : State} {t : Reg} {j : Nat} (hal : (s.gpr .a3).toNat % 8 = 0)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .a3 + BitVec.ofNat 64 (slot j)) 4) :
    exec (.load .w t .a3 (slot j)) s =
      some (s.write t ((s.mem.readW (s.gpr .a3 + BitVec.ofNat 64 (slot j)) 32).setWidth 64)) :=
  exec_load_w (slot_lt j) (slot_al hal j) hin

/-- A store to a slot, with `scratch` (`a3`) aligned. -/
theorem exec_sw_slot {s : State} {t : Reg} {j : Nat} (hal : (s.gpr .a3).toNat % 8 = 0)
    (hout : InRegions s.wr (s.gpr .a3 + BitVec.ofNat 64 (slot j)) 4) :
    exec (.store .w t .a3 (slot j)) s =
      some { s with mem := s.mem.writeW (s.gpr .a3 + BitVec.ofNat 64 (slot j)) ((s.gpr t).setWidth 32) } :=
  exec_store_w (slot_lt j) (slot_al hal j) hout

/-- A rotation left, as `rotl` computes it in the low word. -/
theorem rotl_lo (y : Word) {n : Nat} (hn : n < 32) :
    (sext32 (y >>> (32 - n)) ||| sext32 (y <<< n)).setWidth 32 = y.rotateLeft n := by
  rw [lo32_or, lo32_sext, lo32_sext, BitVec.or_comm, rotl_shifts _ hn]

/-- The rotations of the code, as rotations right by the complement (the
form of the lemmas about the specification). -/
theorem rotl_lo' (y : Word) {n : Nat} (h₀ : 0 < n) (hn : n < 32) :
    (sext32 (y >>> (32 - n)) ||| sext32 (y <<< n)).setWidth 32 = y.rotateRight (32 - n) := by
  rw [rotl_lo y hn, rotateLeft_eq y h₀ hn]

/-- The symbolic execution of an iteration, of either shape (`t < 16` or
not), for any registers `A … H` (which `round_nodup` says are different
from each other and the others). -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w w₄ : Word) (scr : Addr)
    (hv : Vars t s v) (hr3 : s.gpr .a3 = scr) (hal : scr.toNat % 8 = 0)
    (hin : InRegions (s.rd ++ s.wr) (slotAddr scr t) 4)
    (hin₄ : InRegions (s.rd ++ s.wr) (slotAddr scr (t + 4)) 4)
    (hw : s.mem.readW (slotAddr scr t) 32 = w) (hw₄ : s.mem.readW (slotAddr scr (t + 4)) 32 = w₄) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundW v t w w₄) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  have hs := (List.nodup_append.mp (round_nodup t)).1
  have hs' := List.nodup_reverse.mpr hs
  have hdj := (List.nodup_append.mp (round_nodup t)).2.2
  -- The registers the iteration writes are not in `pubRegs`.
  have hpw : ∀ r ∈ pubRegs, r ≠ var t 1 ∧ r ≠ var t 3 ∧ r ≠ var t 5 ∧ r ≠ var t 7 ∧
      r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 := fun r hr =>
    ⟨fun e => hdj _ (by simp) r hr e.symm, fun e => hdj _ (by simp) r hr e.symm,
      fun e => hdj _ (by simp) r hr e.symm, fun e => hdj _ (by simp) r hr e.symm,
      fun e => hdj _ (by simp) r hr e.symm, fun e => hdj _ (by simp) r hr e.symm,
      fun e => hdj _ (by simp) r hr e.symm, fun e => hdj _ (by simp) r hr e.symm⟩
  clear hdj
  have hr3w := hpw .a3 (by simp [pubRegs])
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := var_succ t
  simp only [Vars, e0, e1, e2, e3, e4, e5, e6, e7] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  simp only [slotAddr] at hin hin₄ hw hw₄
  rw [← hr3] at hin hin₄ hw hw₄ hal
  apply WP.of_runBlock
  by_cases ht : t < 16 <;> (
    simp only [Impl.Sm3.RISCV64.round, rotl, li32, ht, ite_true, ite_false, List.cons_append,
      List.nil_append]
    generalize var t 0 = a at *
    generalize var t 1 = b at *
    generalize var t 2 = c at *
    generalize var t 3 = d at *
    generalize var t 4 = e at *
    generalize var t 5 = f at *
    generalize var t 6 = g at *
    generalize var t 7 = h at *
    simp only [T0, T1, T2, T3] at hpw hr3w ⊢
    simp only [T0, T1, T2, T3, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
      List.nodup_nil, and_true] at hs hs'
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_logic, exec_lui,
      exec_addiw_lo12, exec_shift_w (show 12 < 32 by decide), exec_shift_w (show 32 - 12 < 32 by decide),
      exec_shift_w (show 7 < 32 by decide), exec_shift_w (show 32 - 7 < 32 by decide),
      exec_shift_w (show 9 < 32 by decide), exec_shift_w (show 32 - 9 < 32 by decide),
      exec_shift_w (show 19 < 32 by decide), exec_shift_w (show 32 - 19 < 32 by decide),
      exec_shift_w (show 17 < 32 by decide), exec_shift_w (show 32 - 17 < 32 by decide),
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hs, hs', hr3w,
      exec_lw_slot, hal, hin, hin₄, Option.some.injEq, exists_eq_left', ↓reduceIte, true_and]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_⟩
    rotate_right
    · obtain ⟨n1, n3, n5, n7, n16, n17, n18, n19⟩ := hpw r hr
      simp only [n1, n3, n5, n7, n16, n17, n18, n19, ↓reduceIte]
    all_goals
      simp only [lo32_add, lo32_xor, lo32_and, lo32_or, lo32_sext, lo32_ext, li32_val,
        rotl_lo' _ (show 0 < 12 by decide) (show 12 < 32 by decide),
        rotl_lo' _ (show 0 < 7 by decide) (show 7 < 32 by decide),
        rotl_lo' _ (show 0 < 9 by decide) (show 9 < 32 by decide),
        rotl_lo' _ (show 0 < 19 by decide) (show 19 < 32 by decide),
        rotl_lo' _ (show 0 < 17 by decide) (show 17 < 32 by decide),
        h0, h1, h2, h3, h4, h5, h6, h7, hw, hw₄]
    all_goals
      simp only [roundW_0, roundW_1, roundW_2, roundW_3, roundW_4, roundW_5, roundW_6, roundW_7,
        Spec.Sm3.ff, Spec.Sm3.gg, ht, ite_true, ite_false, maj_eq, ch_eq, tj, rotl9,
        rotl12, rotl7, rotl19, Nat.reduceSub] <;>
      first | exact tt1_eq _ _ _ _ _ | exact tt2_eq _ _ _ _)

theorem expand_ok (i : Nat) (s : State) (M : Block) (bp scr : Addr)
    (hr1 : s.gpr .a1 = bp) (hr3 : s.gpr .a3 = scr) (hal : scr.toNat % 8 = 0)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 4)
    (hbin : i < 16 → InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4 * i)) 4)
    (hblk : i < 16 → beWord s.mem bp (4 * i) = W M i)
    (hwin : 16 ≤ i → ∀ j, j < i → i ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j) :
    WP isa (.block (expand i)) s fun s' =>
      s'.mem = s.mem.writeW (slotAddr scr i) (W M i) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → r ≠ T3 → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hin hout hwin ⊢
  by_cases hi : i < 16
  · have hi' := hbin hi
    have hb := hblk hi
    simp only [Impl.Sm3.RISCV64.expand, hi, ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (loadBE32_ok (by decide) (by decide) (by decide) (by omega_using [hi]) (by rw [hr1]; exact hi'))
      fun s₁ e => ?_
    have g3 : s₁.gpr .a3 = scr := by rw [e, ← hr3]; rfl
    have gw : s₁.wr = s.wr := by rw [e]; rfl
    have gr : s₁.rd = s.rd := by rw [e]; rfl
    have gm : s₁.mem = s.mem := by rw [e]; rfl
    have g0 : (s₁.gpr T0).setWidth 32 = W M i := by
      rw [e, RegUpd.gpr_write_self, lo32_ext, hr1, hb]
    have gk : ∀ r, r ≠ T0 → r ≠ T1 → s₁.gpr r = s.gpr r := fun r h0 h1 => by
      rw [e, RegUpd.gpr_write_of_ne _ _ h0, RegUpd.gpr_write_of_ne _ _ h1]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil,
      exec_store_w (s := s₁) (slot_lt i) (by rw [g3]; exact slot_al hal i)
        (by rw [gw, g3]; exact hout i), Option.some.injEq, exists_eq_left', g3]
    exact ⟨by rw [gm, g0], gr, gw, fun r h0 h1 _ _ => gk r h0 h1⟩
  · have hw := hwin (by omega_using [hi])
    have e16 := hw (i - 16) (by omega_using [hi]) (by omega_using [])
    have e9 := hw (i - 9) (by omega_using [hi]) (by omega_using [])
    have e3 := hw (i - 3) (by omega_using [hi]) (by omega_using [])
    have e13 := hw (i - 13) (by omega_using [hi]) (by omega_using [])
    have e6 := hw (i - 6) (by omega_using [hi]) (by omega_using [])
    rw [show slot (i - 16) = slot i by simp only [slot]; omega_using [hi]] at e16
    rw [show slot (i - 9) = slot (i + 7) by simp only [slot]; omega_using [hi]] at e9
    rw [show slot (i - 3) = slot (i + 13) by simp only [slot]; omega_using [hi]] at e3
    rw [show slot (i - 13) = slot (i + 3) by simp only [slot]; omega_using [hi]] at e13
    rw [show slot (i - 6) = slot (i + 10) by simp only [slot]; omega_using [hi]] at e6
    simp only [Impl.Sm3.RISCV64.expand, hi, ite_false, rotl, T0, T1, T2, T3, List.cons_append,
      List.nil_append]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_logic,
      exec_shift_w (show 15 < 32 by decide), exec_shift_w (show 32 - 15 < 32 by decide),
      exec_shift_w (show 23 < 32 by decide), exec_shift_w (show 32 - 23 < 32 by decide),
      exec_shift_w (show 7 < 32 by decide), exec_shift_w (show 32 - 7 < 32 by decide),
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, reduceCtorEq,
      ↓reduceIte, hr3, exec_lw_slot, exec_sw_slot, hal, hin, hout, Option.some.injEq,
      exists_eq_left']
    have hW := W_ge M (j := i) (by omega_using [hi])
    rw [Spec.Sm3.p1] at hW
    simp only [lo32_xor, lo32_ext, rotl_lo _ (show 15 < 32 by decide),
      rotl_lo _ (show 23 < 32 by decide), rotl_lo _ (show 7 < 32 by decide), e16, e9, e3, e13, e6,
      ← hW, true_and]
    exact fun r h0 h1 h2 h3 => by simp only [h0, h1, h2, h3, ↓reduceIte]

/-! ## The 64 iterations -/

theorem var_mem (t k : Nat) : var t k ∈ group₁ ++ group₂ := by
  unfold var
  split
  · refine List.mem_append_left _ ?_
    unfold List.getD
    cases hn : group₁[(k + 4 - t % 4) % 4]?
    · simp [group₁]
    · exact List.mem_of_getElem? hn
  · refine List.mem_append_right _ ?_
    unfold List.getD
    cases hn : group₂[(k + 4 - t % 4) % 4]?
    · have := Nat.mod_lt (k + 4 - t % 4) (show 4 > 0 by decide)
      simp [group₂] at hn; omega
    · exact List.mem_of_getElem? hn

theorem work_ne' : ∀ r ∈ group₁ ++ group₂, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 := by
  decide

theorem work_ne {r : Reg} (h : r ∈ group₁ ++ group₂) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 :=
  work_ne' r h

theorem pubRegs_ne' : ∀ r ∈ pubRegs, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 := by decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 :=
  pubRegs_ne' r h

/-- The window `⟨scr, 64⟩`. -/
abbrev winRegion (scr : Addr) : Region := ⟨scr, 64⟩

theorem win_contains (scr : Addr) (j : Nat) : (winRegion scr).Contains (slotAddr scr j) 4 := by
  simp only [Region.Contains, slotAddr, slot]
  have : j % 16 < 16 := Nat.mod_lt _ (by omega_using [])
  generalize j % 16 = p at *
  rw [Offset.add_sub_cancel_left]
  simp only [BitVec.toNat_ofNat]
  omega_using [this]

theorem slot_sep (scr : Addr) {i j : Nat} (h : i % 16 ≠ j % 16) :
    Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  simp only [slotAddr, slot]
  exact Offset.sep _ (by omega_using [h]) (by omega_using []) (by omega_using [])

/-- What holds during the iterations, relative to the state `sB` at their
start: the registers `V` are those of iteration `t`, and the window holds
`W_j` for the 16 words `j` before `i`. -/
structure Inv (V : HashValue) (M : Block) (scr : Addr) (sB : State) (t i : Nat) (s : State) : Prop where
  vars : Vars t s V
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [winRegion scr] sB.mem s.mem
  win : ∀ j < i, i ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j

/-- After iteration `t`, the window holds `W_{t-12} … W_{t+3}`. -/
abbrev RInv (H : HashValue) (M : Block) (scr : Addr) (sB : State) (t : Nat) : State → Prop :=
  Inv (Spec.Sm3.rounds H M t) M scr sB t (t + 4)

section
variable {H : HashValue} {M : Block} {bp scr : Addr} {sB : State}
  (hr4 : sB.gpr .a1 = bp) (hr6 : sB.gpr .a3 = scr) (hal : scr.toNat % 8 = 0)
  (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
  (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
  (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (4 * t)) 4)
  (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
    ∀ t : Nat, t < 16 → beWord m bp (4 * t) = W M t)
include hr4 hr6 hal hin hout hbin hblk

theorem expand_inv {V : HashValue} {t i : Nat} {s : State} (hs : Inv V M scr sB t i s) :
    WP isa (.block (expand i)) s (Inv V M scr sB t (i + 1)) := by
  refine WP.mono (expand_ok i s M bp scr ((hs.pub .a1 (by decide)).trans hr4)
    ((hs.pub .a3 (by decide)).trans hr6) hal
    (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.wr]; exact hout)
    (fun h => by rw [hs.rd, hs.wr]; exact hbin i h) (hblk _ hs.frame i)
    (fun _ => hs.win)) fun s₁ ⟨hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
  refine ⟨?_, fun r hr => ?_, by rw [hrd₁, hs.rd], by rw [hwr₁, hs.wr], ?_, ?_⟩
  · have hv := hs.vars
    have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k =>
      have := work_ne (var_mem t k); hr₁ _ this.1 this.2.1 this.2.2.1 this.2.2.2
    simp only [Vars, e] at hv ⊢
    exact hv
  · have := pubRegs_ne hr
    rw [hr₁ r this.1 this.2.1 this.2.2.1 this.2.2.2, hs.pub r hr]
  · rw [hm₁]
    exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains scr i)
  · intro j hj hj'
    rw [hm₁]
    by_cases hji : j = i
    · subst hji; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (slot_sep scr (by omega_using [hj, hj', hji])) (by decide)]
      exact hs.win j (by omega_using [hj, hji]) (by omega_using [hj'])

theorem rounds_ok (h0 : Vars 0 sB H) : ∀ t ≤ 64, WP isa (rounds t) sB (RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    have i₀ : Inv H M scr sB 0 0 sB :=
      ⟨h0, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (by omega_using [])⟩
    show WP isa (.block (expand 0 ++ expand 1 ++ expand 2 ++ expand 3)) sB _
    rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (expand_inv hr4 hr6 hal hin hout hbin hblk i₀) fun s₁ h₁ => ?_
    refine WP.mono (expand_inv hr4 hr6 hal hin hout hbin hblk h₁) fun s₂ h₂ => ?_
    refine WP.mono (expand_inv hr4 hr6 hal hin hout hbin hblk h₂) fun s₃ h₃ => ?_
    exact expand_inv hr4 hr6 hal hin hout hbin hblk h₃
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega_using [ht])) fun s hs => ?_)
    rw [WP.block_append_iff]
    refine WP.mono (expand_inv hr4 hr6 hal hin hout hbin hblk hs) fun s₁ h₁ => ?_
    have hr6₁ : s₁.gpr .a3 = scr := (h₁.pub .a3 (by decide)).trans hr6
    refine WP.mono (round_ok t s₁ _ (W M t) (W M (t + 4)) scr h₁.vars hr6₁ hal
      (by rw [h₁.rd, h₁.wr]; exact hin t) (by rw [h₁.rd, h₁.wr]; exact hin (t + 4))
      (h₁.win t (by omega_using []) (by omega_using [])) (h₁.win (t + 4) (by omega_using []) (by omega_using [])))
      fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => by rw [hr₂ r hr, h₁.pub r hr], by rw [hrd₂, h₁.rd],
      by rw [hwr₂, h₁.wr], by rw [hm₂]; exact h₁.frame, fun j hj hj' => ?_⟩
    · rw [rounds_succ, round_eq]; exact hv₂
    · rw [hm₂]; exact h₁.win j (by omega_using [hj]) (by omega_using [hj'])

end

end VG.Proof.Sm3.RISCV64

end

end

/-! ### `Sm3.RISCV64.Contract`, which only this module used -/

section

/-!
# SM3: the RISC-V contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply them
(`Contract.Implies`). The return address is in `ra`, which the target's
calling convention requires to be preserved (`VG.RISCV64.abiPreserved`),
not on the stack. `update` and `finalize` keep their working space in a
frame of 144 bytes below the stack pointer, which must not overlap their
buffers.
-/

@[expose] public section

namespace VG.Proof.Sm3

open Spec.Sm3

open _root_.VG.RISCV64 in
/-- RISC-V contract for
`vg_sm3_compress(state: *mut [u32; 8], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 10])`:
updates the hash value at `state` with the `n` 64-byte blocks at `blocks`.

The code may read `blocks` (`64 * n` bytes) and read and write `state`
(32 bytes) and `scratch` (80 bytes, whose contents on exit are unspecified).
These may not overlap each other. The pointers and `n` are public; the hash
value and the blocks are secret. -/
def compressRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 32⟩
    let blocks : Region := ⟨s.gpr .a1, 64 * (s.gpr .a2).toNat⟩
    let scratch : Region := ⟨s.gpr .a3, 80⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    stateAt s'.mem (s.gpr .a0) =
      compressBlocks (stateAt s.mem (s.gpr .a0)) s.mem (s.gpr .a1) (s.gpr .a2).toNat
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

open _root_.VG.RISCV64 in
/-- RISC-V contract for `vg_sm3_init(state: *mut [u8; 96])`: makes the
streaming state at `state` represent the empty message.

The code may write `state` (96 bytes). The pointer is public. -/
def initRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 96⟩
    s.rd = [] ∧ s.wr = [state]
  post s s' := Repr s'.mem (s.gpr .a0) []
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.sp = s₂.sp

open _root_.VG.RISCV64 in
/-- RISC-V contract for
`vg_sm3_update(state: *mut [u8; 96], count: u64, data: *const u8, len: usize)`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), then afterwards it represents `m` followed by the `len` bytes at
`data`.

The code may read `data` (`len` bytes) and read and write `state` (96
bytes). These may not overlap each other, nor the 144 bytes below the stack
pointer (its frame), which do not wrap around. The stack pointer is 16-byte
aligned. The pointers, `count` and `len` are public; the state and the data
are secret. -/
def updateRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 96⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - 144, 144⟩
    s.rd = [data] ∧ s.wr = [state] ∧ data.Disjoint state ∧
    s.sp.toNat % 16 = 0 ∧ 144 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data
  post s s' := ∀ m, Repr s.mem (s.gpr .a0) m → s.gpr .a1 = BitVec.ofNat 64 m.length →
    Repr s'.mem (s.gpr .a0) (m ++ bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

open _root_.VG.RISCV64 in
/-- RISC-V contract for
`vg_sm3_finalize(state: *mut [u8; 96], count: u64, out: *mut [u8; 32])`: if
the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), writes the SM3 digest of `m` to `out`.

The code may read and write `state` (96 bytes, whose contents on exit are
unspecified) and `out` (32 bytes). These may not overlap each other, nor the
144 bytes below the stack pointer (its frame), which do not wrap around.
The stack pointer is 16-byte aligned. The pointers and `count` are public;
the state is secret. -/
def finalizeRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 96⟩
    let out : Region := ⟨s.gpr .a2, 32⟩
    let stack : Region := ⟨s.sp - 144, 144⟩
    s.rd = [] ∧ s.wr = [state, out] ∧ state.Disjoint out ∧
    s.sp.toNat % 16 = 0 ∧ 144 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out
  post s s' := ∀ m, Repr s.mem (s.gpr .a0) m → s.gpr .a1 = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (s.gpr .a2) 32 = Spec.Sm3.hash m
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp

end VG.Proof.Sm3

end

end

/-!
# SM3 compression function on RISC-V: the whole function

Untrusted: everything here is checked by Lean. The structure of SHA-256's
RISC-V proof (`Proof/Sha256/RISCV64/Compress.lean`), with the hash value
read and written a byte at a time (`Proof/Framework/RISCV64/ByteLoad.lean`),
the scratch space rounded up to a multiple of 8 first, and `s0` saved in it.
-/

@[expose] public section

namespace VG.Proof.Sm3.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.Sm3.RISCV64 VG.Impl.Words.RISCV64
open VG.Spec.Sm3 (HashValue Word Block W stateAt blockAt compressBlocks compress parseBlock)
open VG.Proof.Sm3 (W_lt)

/-! ## Rounding the scratch space up -/

/-- How far `x` is below the next multiple of 8. -/
def pad (x : Addr) : Nat := (8 - x.toNat % 8) % 8

theorem pad_lt (x : Addr) : pad x < 8 := Nat.mod_lt _ (by decide)

theorem and_neg8 (y : BitVec 64) : y &&& BitVec.ofInt 64 (-8) = (y >>> 3) <<< 3 := by
  have : BitVec.ofInt 64 (-8) = BitVec.allOnes 64 <<< 3 := by decide
  rw [this]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes, hi, decide_true, Bool.true_and]
  by_cases h3 : i < 3
  · simp [h3]
  · simp [h3, show 3 + (i - 3) = i by omega_using [h3], show i - 3 < 64 by omega_using [hi]]

/-- `addi 7` then `andi -8`. -/
theorem align_eq (x : Addr) :
    (x + BitVec.ofInt 64 7) &&& BitVec.ofInt 64 (-8) = x + BitVec.ofNat 64 (pad x) := by
  rw [and_neg8]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, pad]
  have := x.isLt
  rw [show BitVec.toNat (BitVec.ofInt 64 7) = 7 from rfl]
  omega_using []

theorem align_al (x : Addr) : (x + BitVec.ofNat 64 (pad x)).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  unfold pad
  have := x.isLt
  omega_using []

/-! ## Addresses and regions -/

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 8) (hk : k < 8)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
    m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (Offset.sep p (by omega_using [h]) (by omega_using [hj]) (by omega_using [hk])) (by decide)

theorem stateAt_eq {m : Mem} {p : Addr} {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 8) → m.readW (p + BitVec.ofNat 64 (4 * k)) 32 = v[k]) :
    stateAt m p = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  exact h k hk

theorem stateAt_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 8) :
    (stateAt m p)[k] = m.readW (p + BitVec.ofNat 64 (4 * k)) 32 := by
  simp only [stateAt, Vector.getElem_ofFn]

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev bp : Addr := s₀.gpr .a1
abbrev nb : Nat := (s₀.gpr .a2).toNat
abbrev scr₀ : Addr := s₀.gpr .a3
/-- The scratch space, rounded up to a multiple of 8. -/
abbrev scr : Addr := scr₀ s₀ + BitVec.ofNat 64 (pad (scr₀ s₀))
abbrev stR : Region := ⟨st s₀, 32⟩
abbrev blR : Region := ⟨bp s₀, 64 * nb s₀⟩
abbrev scrR : Region := ⟨scr₀ s₀, 80⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)
/-- Where `s0` is saved. -/
abbrev savAddr : Addr := scr s₀ + BitVec.ofNat 64 64
abbrev savR : Region := ⟨savAddr s₀, 8⟩

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

/-- An offset of the rounded scratch space, as one of `scratch`. -/
theorem scr_add (s₀ : State) (d : Nat) :
    scr s₀ + BitVec.ofNat 64 d = scr₀ s₀ + BitVec.ofNat 64 (pad (scr₀ s₀) + d) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem scr_contains (s₀ : State) {d n : Nat} (h : d + n ≤ 72) :
    (scrR s₀).Contains (scr s₀ + BitVec.ofNat 64 d) n := by
  rw [scr_add]
  have := pad_lt (scr₀ s₀)
  exact Offset.contains_base _ (by omega_using [h, this]) (by omega_using [h, this])

theorem scr_sub (s₀ : State) {d n : Nat} (h : d + n ≤ 72) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) := by
  rw [scr_add]
  have := pad_lt (scr₀ s₀)
  exact Offset.sub_base _ (by omega_using [h, this])

theorem win_sub (s₀ : State) : Region.Sub (winRegion (scr s₀)) (scrR s₀) := by
  have := scr_sub s₀ (d := 0) (n := 64) (by omega_using [])
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (scrR s₀) := scr_sub s₀ (by omega_using [])

theorem win_sav (s₀ : State) : (winRegion (scr s₀)).Disjoint (savR s₀) := by
  have := Offset.disjoint (scr s₀) (d := 0) (n := 64) (e := 64) (k := 8) (by omega_using []) (by omega_using [])
    (by omega_using [])
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sm3.compressRISCV64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem nb_lt : 64 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega_using [hn]

theorem in_state {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩

theorem out_state {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], scr_contains s₀ (by simp only [slot]; omega_using [])⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], scr_contains s₀ (by simp only [slot]; omega_using [])⟩

theorem in_sav (rs : List Region) : InRegions (rs ++ s₀.wr) (savAddr s₀) 8 :=
  ⟨scrR s₀, by simp [h.wr], scr_contains s₀ (by omega_using [])⟩

theorem out_sav : InRegions s₀.wr (savAddr s₀) 8 :=
  ⟨scrR s₀, by simp [h.wr], scr_contains s₀ (by omega_using [])⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 := by
  have := h.nb_lt
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) by rw [BitVec.ofNat_add, BitVec.add_assoc]]
  exact Offset.contains_base _ (by omega_using [hi, ht]) (by omega_using [hi, ht, this])

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## Saving and restoring `s0` -/

/-- The callee-saved registers (and the return address) the code does not
use: never written. -/
def keepRegs : List Reg := [.ra, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11]

theorem keepRegs_pub : ∀ r ∈ keepRegs, r ∈ pubRegs := by decide

theorem keepRegs_ne : ∀ r ∈ keepRegs, r ≠ .a3 ∧ r ≠ .s0 := by decide

/-- A preserved register is `s0`, or kept. -/
theorem preserved_cases : ∀ r ∈ preserved, r = .s0 ∨ r ∈ keepRegs := by decide

/-- After `save`. -/
structure Saved (s₀ : State) (s : State) : Prop where
  a3 : s.gpr .a3 = scr s₀
  gpr : ∀ r, r ≠ .a3 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [savR s₀] s₀.mem s.mem
  sav : s.mem.readW (savAddr s₀) 64 = s₀.gpr .s0

theorem save_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block save) s₀ (Saved s₀) := by
  obtain hal : (scr s₀ + BitVec.ofNat 64 64).toNat % 8 = 0 := by
    have := align_al (scr₀ s₀)
    change (scr₀ s₀ + BitVec.ofNat 64 (pad (scr₀ s₀)) + BitVec.ofNat 64 64).toNat % 8 = 0
    rw [BitVec.toNat_add (scr₀ s₀ + _), BitVec.toNat_ofNat 64 64]
    omega_using [this]
  apply WP.of_runBlock
  simp only [save, runBlock_cons, runStep_some, exec_addi (show imm12 7 by decide),
    exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, align_eq,
    RegUpd.write_write]
  rw [exec_store_d (show 64 < 2048 by decide) (by rw [RegUpd.gpr_write_self]; exact hal)
      (by rw [RegUpd.gpr_write_self, RegUpd.wr_write]; exact hp.out_sav), runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, RegUpd.gpr_write_self s₀ .a3 _, fun r hr => RegUpd.gpr_write_of_ne s₀ _ hr, rfl,
    rfl, ?_, ?_⟩
  · simp only [RegUpd.gpr_write_self, RegUpd.mem_write]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · simp only [RegUpd.gpr_write_self, RegUpd.mem_write,
      RegUpd.gpr_write_of_ne _ _ (show Reg.s0 ≠ Reg.a3 by decide)]
    exact Mem.readW_writeW_self64 _ _ _

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = st s₀
  a3 : s.gpr .a3 = scr s₀
  kept : ∀ r ∈ keepRegs, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  sav : s.mem.readW (savAddr s₀) 64 = s₀.gpr .s0
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  a1 : s.gpr .a1 = blkAddr s₀ i
  a2 : s.gpr .a2 = BitVec.ofNat 64 (nb s₀ - i)

/-! ## Loading the hash value -/

theorem var0_inj {j k : Nat} (hj : j < 8) (hk : k < 8) (h : var 0 j = var 0 k) : j = k := by
  obtain key : ∀ j < 8, ∀ k < 8, var 0 j = var 0 k → j = k := by decide
  exact key j hj k hk h

theorem var0_ne {k : Nat} (hk : k < 8) : var 0 k ≠ .a0 ∧ var 0 k ≠ T0 ∧ var 0 k ≠ T1 := by
  obtain key : ∀ k < 8, var 0 k ≠ .a0 ∧ var 0 k ≠ T0 ∧ var 0 k ≠ T1 := by decide
  exact key k hk

theorem var0_pub {k : Nat} (hk : k < 8) : ∀ r ∈ pubRegs, r ≠ var 0 k := by
  obtain key : ∀ k < 8, ∀ r ∈ pubRegs, r ≠ var 0 k := by decide
  exact key k hk

/-- The first `k` words of the hash value are loaded. -/
structure LdI (s₁ : State) (k : Nat) (s : State) : Prop where
  vars : ∀ j < k, (s.gpr (var 0 j)).setWidth 32 = (stateAt s₁.mem (s₁.gpr .a0))[j]!
  pub : ∀ r ∈ pubRegs, s.gpr r = s₁.gpr r
  mem : s.mem = s₁.mem
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr

theorem load_step {s₀ s₁ : State} (hp : Pre s₀) (hr0 : s₁.gpr .a0 = st s₀) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) {k : Nat} (hk : k < 8) {s : State} (h : LdI s₁ k s) :
    WP isa (.block (loadLE32 (var 0 k) T0 .a0 (4 * k))) s (LdI s₁ (k + 1)) := by
  obtain ne := var0_ne hk
  obtain h0 : s.gpr .a0 = st s₀ := (h.pub .a0 (by decide)).trans hr0
  refine WP.mono (loadLE32_ok ne.1 (by decide) ne.2.1 (by omega_using [hk])
    (by rw [h.rd, h.wr, hrd, hwr, h0]; exact hp.in_state hk)) fun s' e => ?_
  subst e
  refine ⟨fun j hj => ?_, fun r hr => ?_, h.mem, h.rd, h.wr⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [RegUpd.gpr_write_of_ne _ _ (fun e => absurd (var0_inj (by omega_arith) hk e) (by omega_using [hj])),
        RegUpd.gpr_write_of_ne _ _ (var0_ne (by omega_arith : j < 8)).2.1]
      exact h.vars j hj
    · rw [RegUpd.gpr_write_self, lo32_ext, h.mem, h0, ← hr0, getElem!_pos _ j hk,
        stateAt_get _ _ hk]
  · rw [RegUpd.gpr_write_of_ne _ _ (var0_pub hk r hr),
      RegUpd.gpr_write_of_ne _ _ fun e => (pubRegs_ne hr).1 e]
    exact h.pub r hr

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hr0 : s.gpr .a0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  refine WP.mono (wp_range_flatMap (M := isa) (LdI s) (fun k s' hk h => load_step hp hr0 hrd hwr hk h)
    8 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega_using []), fun _ _ => rfl, rfl, rfl, rfl⟩)
    fun s₁ h => ⟨?_, h.pub, h.rd, h.wr, h.mem⟩
  have v := h.vars
  rw [hr0] at v
  exact ⟨v 0 (by decide), v 1 (by decide), v 2 (by decide), v 3 (by decide), v 4 (by decide),
    v 5 (by decide), v 6 (by decide), v 7 (by decide)⟩

/-! ## Adding the hash value into the working variables -/

/-- The first `k` of eight words `f` written at `p`. -/
def writeUpTo (m : Mem) (p : Addr) (f : HashValue) (k : Nat) : Mem :=
  (List.range k).foldl (fun m j => m.writeW (p + BitVec.ofNat 64 (4 * j)) f[j]!) m

theorem writeUpTo_succ (m : Mem) (p : Addr) (f : HashValue) (k : Nat) :
    writeUpTo m p f (k + 1) = (writeUpTo m p f k).writeW (p + BitVec.ofNat 64 (4 * k)) f[k]! := by
  simp [writeUpTo, List.range_succ, List.foldl_append]

theorem readW_writeUpTo (m : Mem) (p : Addr) (f : HashValue) {k j : Nat} (hk : k ≤ 8) (hj : j < 8) :
    (writeUpTo m p f k).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      if j < k then f[j]! else m.readW (p + BitVec.ofNat 64 (4 * j)) 32 := by
  induction k with
  | zero => simp [writeUpTo]
  | succ k ih =>
    rw [writeUpTo_succ]
    by_cases hjk : j = k
    · subst hjk; rw [Mem.readW_writeW_self32]; simp
    · rw [readW_writeW_word _ _ _ hj (by omega_using [hk]) hjk, ih (by omega_using [hk])]
      by_cases h : j < k
      · simp [h, show j < k + 1 by omega_using [h]]
      · simp [h, show ¬ j < k + 1 by omega_using [hjk, h]]

theorem frame_writeUpTo {r : Region} {m : Mem} {p : Addr} (f : HashValue) {k : Nat} (hk : k ≤ 8)
    (hc : ∀ j < 8, r.Contains (p + BitVec.ofNat 64 (4 * j)) 4) :
    Frame [r] m (writeUpTo m p f k) := by
  induction k with
  | zero => exact Frame.refl _ _
  | succ k ih =>
    rw [writeUpTo_succ]
    exact (ih (by omega_using [hk])).writeW (List.mem_singleton_self _) _ (hc k (by omega_using [hk]))

/-- The first `k` words are updated, from the state `s₂` after the rounds,
whose working variables are `V`, and the hash value `H` it holds. -/
structure UInv (s₀ s₂ : State) (V H : HashValue) (k : Nat) (s : State) : Prop where
  vars : ∀ j, k ≤ j → j < 8 → (s.gpr (var 0 j)).setWidth 32 = V[j]!
  pub : ∀ r ∈ pubRegs, s.gpr r = s₂.gpr r
  mem : s.mem = writeUpTo s₂.mem (st s₀) (Vector.zipWith (· ^^^ ·) V H) k
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr

theorem update_step {s₀ s₂ : State} (hp : Pre s₀) (V H : HashValue) (hr0 : s₂.gpr .a0 = st s₀)
    (hrd : s₂.rd = s₀.rd) (hwr : s₂.wr = s₀.wr)
    (hH : ∀ j < 8, s₂.mem.readW (st s₀ + BitVec.ofNat 64 (4 * j)) 32 = H[j]!)
    {k : Nat} (hk : k < 8) {s : State} (h : UInv s₀ s₂ V H k s) :
    WP isa (.block (updateW k)) s (UInv s₀ s₂ V H (k + 1)) := by
  obtain ne := var0_ne hk
  obtain h0 : s.gpr .a0 = st s₀ := (h.pub .a0 (by decide)).trans hr0
  obtain hin : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [h.rd, h.wr, hrd, hwr, h0]; exact hp.in_state hk
  unfold updateW
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (loadLE32_ok (by decide) (by decide) (by decide) (by omega_using [hk]) hin) fun s₁ e₁ => ?_
  subst e₁
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_logic, Option.some.injEq,
    exists_eq_left']
  -- The state after the addition.
  generalize hs₂' : State.write _ _ _ = s₃
  obtain g0 : s₃.gpr .a0 = st s₀ := by
    rw [← hs₂', RegUpd.gpr_write_of_ne _ _ (Ne.symm ne.1), RegUpd.gpr_write_of_ne _ _ (by decide),
      RegUpd.gpr_write_of_ne _ _ (by decide), h0]
  obtain gv : (s₃.gpr (var 0 k)).setWidth 32 = V[k]! ^^^ H[k]! := by
    rw [← hs₂', RegUpd.gpr_write_self, lo32_xor, RegUpd.gpr_write_of_ne _ _ ne.2.1,
      RegUpd.gpr_write_of_ne _ _ ne.2.2, h.vars k (Nat.le_refl _) hk, RegUpd.gpr_write_self, lo32_ext,
      h0, h.mem, readW_writeUpTo _ _ _ (by omega_using [hk]) hk]
    simp only [Nat.lt_irrefl, ite_false]
    rw [hH k hk]
  obtain gm : s₃.mem = s.mem := by rw [← hs₂']; rfl
  obtain gwr : s₃.wr = s.wr := by rw [← hs₂']; rfl
  obtain grd : s₃.rd = s.rd := by rw [← hs₂']; rfl
  obtain gr : ∀ r, r ≠ var 0 k → r ≠ T0 → r ≠ T1 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [← hs₂', RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2,
      RegUpd.gpr_write_of_ne _ _ h3]
  refine WP.mono (storeLE32_ok (Ne.symm ne.2.1) (by decide) (by omega_using [hk])
    (by rw [gwr, h.wr, hwr, g0]; exact hp.out_state hk)) fun s₄ e₄ => ?_
  subst e₄
  refine ⟨fun j hj hj' => ?_, fun r hr => ?_, ?_, grd.trans h.rd, gwr.trans h.wr⟩
  · have hne : var 0 j ≠ var 0 k := fun e => absurd (var0_inj hj' hk e) (by omega_using [hj])
    rw [RegUpd.gpr_write_of_ne _ _ (var0_ne hj').2.1]
    show (s₃.gpr (var 0 j)).setWidth 32 = _
    rw [gr _ hne (var0_ne hj').2.1 (var0_ne hj').2.2]
    exact h.vars j (by omega_using [hj]) hj'
  · rw [RegUpd.gpr_write_of_ne _ _ fun e => (pubRegs_ne hr).1 e]
    show s₃.gpr r = _
    rw [gr r (var0_pub hk r hr) (fun e => (pubRegs_ne hr).1 e) (fun e => (pubRegs_ne hr).2.1 e)]
    exact h.pub r hr
  · rw [RegUpd.mem_write]
    show s₃.mem.writeW _ _ = _
    rw [gm, h.mem, writeUpTo_succ, g0, gv]
    congr 1
    rw [getElem!_pos (Vector.zipWith _ V H) k hk, Vector.getElem_zipWith, getElem!_pos V k hk,
      getElem!_pos H k hk]

theorem vars_get {s : State} {V : HashValue} (h : Vars 0 s V) :
    ∀ j, j < 8 → (s.gpr (var 0 j)).setWidth 32 = V[j]! := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  intro j hj
  rw [getElem!_pos V j hj]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega_using [hj]) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5, h6, h7]

theorem update_ok {s₀ s₂ : State} (hp : Pre s₀) (V H : HashValue) (hv : Vars 0 s₂ V)
    (hr0 : s₂.gpr .a0 = st s₀) (hrd : s₂.rd = s₀.rd) (hwr : s₂.wr = s₀.wr)
    (hH : ∀ j < 8, s₂.mem.readW (st s₀ + BitVec.ofNat 64 (4 * j)) 32 = H[j]!) :
    WP isa (.block ((List.range 8).flatMap updateW)) s₂ (UInv s₀ s₂ V H 8) :=
  wp_range_flatMap (M := isa) (UInv s₀ s₂ V H) (fun _ _ hk h => update_step hp V H hr0 hrd hwr hH hk h)
    8 (Nat.le_refl _) s₂ ⟨fun j _ hj => vars_get hv j hj, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i t : Nat) (ht : t < 16) :
    beWord s₀.mem (blkAddr s₀ i) (4 * t) = W (blk s₀ i) t := by
  rw [W_lt _ ht]; rfl

theorem frame_byte {rs : List Region} {m m' : Mem} {R : Region} {x : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, R.Disjoint r) (hx : R.Contains x 1) : m' x = m x :=
  hf x fun r hr hc => hd r hr x hx hc

theorem frame_beWord {rs : List Region} {m m' : Mem} {R : Region} {p : Addr} {off : Nat}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, R.Disjoint r) (hc : R.Contains (p + BitVec.ofNat 64 off) 4) :
    beWord m' p off = beWord m p off := by
  obtain h0 := contains_byte hc (k := 0) (by decide)
  rw [Nat.add_zero] at h0
  simp only [beWord, frame_byte hf hd h0, frame_byte hf hd (contains_byte hc (k := 1) (by decide)),
    frame_byte hf hd (contains_byte hc (k := 2) (by decide)),
    frame_byte hf hd (contains_byte hc (k := 3) (by decide))]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .a2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .a2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.a0 hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  obtain hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  obtain hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      beWord m (blkAddr s₀ i) (4 * t) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [frame_beWord hm hwin (hp.blk_contains hi ht), hm₁,
      frame_beWord hL.frame (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (hp.blk_contains hi ht)]
    exact blk_word i t ht
  obtain hr1₁ : s₁.gpr .a1 = blkAddr s₀ i := (hpub₁ .a1 (by decide)).trans hL.a1
  obtain hr3₁ : s₁.gpr .a3 = scr s₀ := (hpub₁ .a3 (by decide)).trans hL.a3
  refine WP.seq (WP.mono (rounds_ok (H := stateAt s.mem (st s₀)) hr1₁ hr3₁ (align_al _)
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 64 (Nat.le_refl _))
    fun s₂ hR => ?_)
  obtain hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  obtain pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  obtain hr0₂ : s₂.gpr .a0 = st s₀ := by rw [pub₂ .a0 (by decide), hL.a0]
  obtain hrd₂ : s₂.rd = s₀.rd := by rw [hR.rd, hrd₁, hL.rd]
  obtain hwr₂ : s₂.wr = s₀.wr := by rw [hR.wr, hwr₁, hL.wr]
  rw [WP.block_append_iff]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hr0₂ hrd₂ hwr₂ fun k hk => ?_)
    fun s₃ h₃ => ?_
  · rw [hR.frame.readW (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])) hst (by decide), hm₁,
      getElem!_pos _ k hk, stateAt_get _ _ hk]
  obtain hr1₃ : s₃.gpr .a1 = blkAddr s₀ i := by rw [h₃.pub .a1 (by decide), pub₂ .a1 (by decide), hL.a1]
  obtain hr2₃ : s₃.gpr .a2 = BitVec.ofNat 64 (nb s₀ - i) := by
    rw [h₃.pub .a2 (by decide), pub₂ .a2 (by decide), hL.a2]
  obtain hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩) ?_
    rw [h₃.mem]
    exact (frame_writeUpTo (r := stR s₀) _ (Nat.le_refl _) fun j hj =>
      Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])).mono fun r hr => by simp at hr; simp [hr]
  obtain hsav : s₃.mem.readW (savAddr s₀) 64 = s₀.gpr .s0 := by
    obtain hd : (savR s₀).Disjoint (stR s₀) :=
      Region.Disjoint.sub_left hp.st_scr.symm (savR_sub s₀)
    rw [h₃.mem, (frame_writeUpTo (r := stR s₀) _ (Nat.le_refl _) fun j hj =>
        Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])).readW (r := savR s₀)
        (Region.contains_self _ _) (by simpa using hd) (by decide),
      hR.frame.readW (r := savR s₀) (Region.contains_self _ _) (by simpa using (win_sav s₀).symm)
        (by decide), hm₁]
    exact hL.sav
  obtain hstate : stateAt s₃.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1) := by
    rw [compressBlocks_succ, ← hL.state]
    apply stateAt_eq
    intro k hk
    rw [h₃.mem, readW_writeUpTo _ _ _ (Nat.le_refl _) hk]
    simp only [hk, ↓reduceIte]
    rw [getElem!_pos _ k hk]
    rfl
  apply WP.of_runBlock
  simp only [advance, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 64 by decide),
    exec_addi (show imm12 (-1) by decide), Option.some.injEq, exists_eq_left']
  -- The state after advancing.
  generalize hs₄ : State.write _ _ _ = s₄
  obtain g1 : s₄.gpr .a1 = blkAddr s₀ (i + 1) := by
    rw [← hs₄, RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_self, hr1₃]
    simp only [blkAddr]
    rw [show BitVec.ofInt 64 64 = BitVec.ofNat 64 64 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      Nat.mul_succ]
  have hnb := hp.nb_lt
  obtain g2 : s₄.gpr .a2 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [← hs₄, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ (by decide), hr2₃]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (BitVec.ofInt 64 (-1)).toNat = 2 ^ 64 - 1 from rfl]
    omega_using [hi]
  obtain gr : ∀ r, r ≠ .a1 → r ≠ .a2 → s₄.gpr r = s₃.gpr r := fun r h1 h2 => by
    rw [← hs₄, RegUpd.gpr_write_of_ne _ _ h2, RegUpd.gpr_write_of_ne _ _ h1]
  obtain gm : s₄.mem = s₃.mem := by rw [← hs₄]; rfl
  obtain grd : s₄.rd = s₃.rd := by rw [← hs₄]; rfl
  obtain gwr : s₄.wr = s₃.wr := by rw [← hs₄]; rfl
  obtain hcommon : Common s₀ (i + 1) s₄ := by
    refine ⟨by rw [gr _ (by decide) (by decide), h₃.pub .a0 (by decide), hr0₂],
      by rw [gr _ (by decide) (by decide), h₃.pub .a3 (by decide), pub₂ .a3 (by decide), hL.a3],
      fun r hr => ?_, by rw [grd, h₃.rd, hrd₂], by rw [gwr, h₃.wr, hwr₂], by rw [gm]; exact hframe,
      by rw [gm]; exact hsav, by rw [gm]; exact hstate⟩
    obtain hp' := keepRegs_pub r hr
    rw [gr r (fun e => by subst e; simp [keepRegs] at hr) (fun e => by subst e; simp [keepRegs] at hr),
      h₃.pub r hp', pub₂ r hp', hL.kept r hr]
  obtain hev : eval (.nonzero .a2) s₄ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, g2]
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    obtain hne : nb s₀ - (i + 1) ≠ 0 := by omega_using [hi, hlast]
    obtain h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      obtain h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hnb])] at h'
      exact hne h'
    exact ⟨by rw [hev]; simpa using h0, by omega_using [hi, hlast], { hcommon with a1 := g1, a2 := g2 }⟩

/-! ## The whole function -/

theorem blocks_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (hc₀ : Common s₀ 0 s₁)
    (hr1 : s₁.gpr .a1 = bp s₀) (hr2 : s₁.gpr .a2 = s₀.gpr .a2) :
    WP isa blocks s₁ (Common s₀ (nb s₀)) := by
  refine WP.ite (s₁.gpr .a2 == 0) (by simp [eval]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp [hr2] at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq, hr2] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    obtain hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .a2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .a2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega_using [hi], i + 1, rfl, hi', hL'⟩
    obtain hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        a1 := by simp [blkAddr, hr1]
        a2 := by simp [nb, hr2] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      Proof.Sm3.compressRISCV64.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ h₁ => ?_)
  obtain hc₀ : Common s₀ 0 s₁ := by
    refine ⟨h₁.gpr _ (by decide), h₁.a3, fun r hr => h₁.gpr _ (keepRegs_ne r hr).1, h₁.rd, h₁.wr,
      h₁.frame.sub fun r hr => ?_, h₁.sav, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, savR_sub s₀⟩
    · show stateAt s₁.mem (st s₀) = H₀ s₀
      apply stateAt_eq
      intro k hk
      rw [h₁.frame.readW (r := stR s₀) (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk]))
        (by simpa using Region.Disjoint.sub_right hp.st_scr (savR_sub s₀)) (by decide),
        ← stateAt_get _ _ hk]
  refine WP.seq (WP.mono (blocks_ok hp hc₀ (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)))
    fun s₂ h₂ => ?_)
  obtain hal : (s₂.gpr .a3 + BitVec.ofNat 64 64).toNat % 8 = 0 := by
    have := align_al (scr₀ s₀)
    rw [h₂.a3]
    change (scr₀ s₀ + BitVec.ofNat 64 (pad (scr₀ s₀)) + BitVec.ofNat 64 64).toNat % 8 = 0
    rw [BitVec.toNat_add (scr₀ s₀ + _), BitVec.toNat_ofNat 64 64]
    omega_using [this]
  apply WP.of_runBlock
  rw [restore, runBlock_cons, exec_load_d (show 64 < 2048 by decide) hal
    (by rw [h₂.a3, h₂.rd, h₂.wr]; exact hp.in_sav _), runStep_some, runBlock_nil]
  refine ⟨_, rfl, fun r hr => ?_, ?_, ?_⟩
  · rcases preserved_cases r hr with rfl | hk
    · rw [RegUpd.gpr_write_self, h₂.a3, h₂.sav]
    · rw [RegUpd.gpr_write_of_ne _ _ fun e => by subst e; simp [keepRegs] at hk, h₂.kept r hk]
  · rw [RegUpd.gpr_write_of_ne _ _ (by decide), h₂.kept _ (by decide)]
  · show stateAt s₂.mem (s₀.gpr .a0) = _
    exact h₂.state

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 80⟩]

/-! The code as a literal (`materialize_flat_code`): the summary below and its frame, and the
checks of the modules that import this one, read it rather than build the unrolled rounds again. -/
materialize_flat_code Impl.Sm3.RISCV64.compress

/-! The constant-time analysis of the compression function from its arguments, done once for
every check of code that calls it (`taint_decide_sum [compressSum]`), which keeps what is public
of `s1`–`s11`: it writes none of them. -/
taint_summary compressSum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3]) Impl.Sm3.RISCV64.compress
  keeping (Taint.ofRegs [.s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])

theorem compress_verified :
    Verified RISCV64.target Impl.Sm3.RISCV64.compress Proof.Sm3.compressRISCV64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, hra, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩
  · refine VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) ?_
      (VG.Taint.exists_check_of_sumOk compressSum (RegSet.subset_refl _))
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h1, h2, h3, h4]
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sm3.RISCV64
