module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Sm3.Spec
public import VerifiedGarbage.Impl.Sm3.RISCV64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Data.List.Nodup
import all Init.Data.Nat.Bitwise.Basic
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# SM3 compression function on RISC-V: the message expansion and the iterations

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/Sm3/PPC64LE/Rounds.lean`), with the words the low 32 bits of
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
  rw [show (t + 1) % 4 = (t % 4 + 1) % 4 by omega]
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
  simp only [slot]; omega

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : Addr) (j : Nat) : Addr := scr + BitVec.ofNat 64 (slot j)

/-- With `scratch` 8-byte aligned, the slots are naturally aligned. -/
theorem slot_al {scr : Addr} (hal : scr.toNat % 8 = 0) (j : Nat) :
    (scr + BitVec.ofNat 64 (slot j)).toNat % 4 = 0 := by
  simp only [slot]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * (j % 16)) (by omega)]
  have := scr.isLt
  omega

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
    refine WP.mono (loadBE32_ok (by decide) (by decide) (by decide) (by omega) (by rw [hr1]; exact hi'))
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
  · have hw := hwin (by omega)
    have e16 := hw (i - 16) (by omega) (by omega)
    have e9 := hw (i - 9) (by omega) (by omega)
    have e3 := hw (i - 3) (by omega) (by omega)
    have e13 := hw (i - 13) (by omega) (by omega)
    have e6 := hw (i - 6) (by omega) (by omega)
    rw [show slot (i - 16) = slot i by simp only [slot]; omega] at e16
    rw [show slot (i - 9) = slot (i + 7) by simp only [slot]; omega] at e9
    rw [show slot (i - 3) = slot (i + 13) by simp only [slot]; omega] at e3
    rw [show slot (i - 13) = slot (i + 3) by simp only [slot]; omega] at e13
    rw [show slot (i - 6) = slot (i + 10) by simp only [slot]; omega] at e6
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
    have hW := W_ge M (j := i) (by omega)
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
  have : j % 16 < 16 := Nat.mod_lt _ (by omega)
  generalize j % 16 = p at *
  rw [Offset.add_sub_cancel_left]
  simp only [BitVec.toNat_ofNat]
  omega

theorem slot_sep (scr : Addr) {i j : Nat} (h : i % 16 ≠ j % 16) :
    Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  simp only [slotAddr, slot]
  exact Offset.sep _ (by omega) (by omega) (by omega)

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
    · rw [Mem.readW_writeW_sep (slot_sep scr (by omega)) (by decide)]
      exact hs.win j (by omega) (by omega)

theorem rounds_ok (h0 : Vars 0 sB H) : ∀ t ≤ 64, WP isa (rounds t) sB (RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    have i₀ : Inv H M scr sB 0 0 sB :=
      ⟨h0, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (by omega)⟩
    show WP isa (.block (expand 0 ++ expand 1 ++ expand 2 ++ expand 3)) sB _
    rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (expand_inv hr4 hr6 hal hin hout hbin hblk i₀) fun s₁ h₁ => ?_
    refine WP.mono (expand_inv hr4 hr6 hal hin hout hbin hblk h₁) fun s₂ h₂ => ?_
    refine WP.mono (expand_inv hr4 hr6 hal hin hout hbin hblk h₂) fun s₃ h₃ => ?_
    exact expand_inv hr4 hr6 hal hin hout hbin hblk h₃
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    refine WP.mono (expand_inv hr4 hr6 hal hin hout hbin hblk hs) fun s₁ h₁ => ?_
    have hr6₁ : s₁.gpr .a3 = scr := (h₁.pub .a3 (by decide)).trans hr6
    refine WP.mono (round_ok t s₁ _ (W M t) (W M (t + 4)) scr h₁.vars hr6₁ hal
      (by rw [h₁.rd, h₁.wr]; exact hin t) (by rw [h₁.rd, h₁.wr]; exact hin (t + 4))
      (h₁.win t (by omega) (by omega)) (h₁.win (t + 4) (by omega) (by omega)))
      fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => by rw [hr₂ r hr, h₁.pub r hr], by rw [hrd₂, h₁.rd],
      by rw [hwr₂, h₁.wr], by rw [hm₂]; exact h₁.frame, fun j hj hj' => ?_⟩
    · rw [rounds_succ, round_eq]; exact hv₂
    · rw [hm₂]; exact h₁.win j (by omega) (by omega)

end

end VG.Proof.Sm3.RISCV64
