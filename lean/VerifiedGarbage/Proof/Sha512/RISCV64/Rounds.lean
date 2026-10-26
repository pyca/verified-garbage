module

import Mathlib.Data.List.Nodup
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Sha512.Spec
import VerifiedGarbage.Proof.Sha512.Shifts
public import VerifiedGarbage.Impl.Sha512.RISCV64
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad

/-!
# SHA-512 compression function on RISC-V: the message schedule and the rounds

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proofs (`Proof/Sha512/PPC64LE/Rounds.lean`,
`Proof/Sha256/RISCV64/Rounds.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha512.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.Sha512.RISCV64 VG.Impl.Words.RISCV64
open VG.Spec.Sha512 (HashValue Word Block K W bsig0 bsig1 ch maj ssig0 ssig1)

/-! ## The functions as the shifts compute them -/

theorem bsig1_shifts (x : Word) :
    bsig1 x = x >>> 14 ^^^ x <<< 50 ^^^ x >>> 18 ^^^ x <<< 46 ^^^ x >>> 41 ^^^ x <<< 23 := by
  simp only [bsig1, rotateRight_eq_shifts x (show 0 < 14 by decide) (show 14 < 64 by decide),
    rotateRight_eq_shifts x (show 0 < 18 by decide) (show 18 < 64 by decide),
    rotateRight_eq_shifts x (show 0 < 41 by decide) (show 41 < 64 by decide), Nat.reduceSub,
    BitVec.xor_assoc]

theorem bsig0_shifts (x : Word) :
    bsig0 x = x >>> 28 ^^^ x <<< 36 ^^^ x >>> 34 ^^^ x <<< 30 ^^^ x >>> 39 ^^^ x <<< 25 := by
  simp only [bsig0, rotateRight_eq_shifts x (show 0 < 28 by decide) (show 28 < 64 by decide),
    rotateRight_eq_shifts x (show 0 < 34 by decide) (show 34 < 64 by decide),
    rotateRight_eq_shifts x (show 0 < 39 by decide) (show 39 < 64 by decide), Nat.reduceSub,
    BitVec.xor_assoc]

theorem ssig1_shifts (x : Word) :
    ssig1 x = x >>> 19 ^^^ x <<< 45 ^^^ x >>> 61 ^^^ x <<< 3 ^^^ x >>> 6 := by
  simp only [ssig1, rotateRight_eq_shifts x (show 0 < 19 by decide) (show 19 < 64 by decide),
    rotateRight_eq_shifts x (show 0 < 61 by decide) (show 61 < 64 by decide), Nat.reduceSub,
    BitVec.xor_assoc]

theorem ssig0_shifts (x : Word) :
    ssig0 x = x >>> 1 ^^^ x <<< 63 ^^^ x >>> 8 ^^^ x <<< 56 ^^^ x >>> 7 := by
  simp only [ssig0, rotateRight_eq_shifts x (show 0 < 1 by decide) (show 1 < 64 by decide),
    rotateRight_eq_shifts x (show 0 < 8 by decide) (show 8 < 64 by decide), Nat.reduceSub,
    BitVec.xor_assoc]

/-! ## One round -/

/-- The working variables `v` are in the registers of round `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0] ∧ s.gpr (var t 1) = v[1] ∧
  s.gpr (var t 2) = v[2] ∧ s.gpr (var t 3) = v[3] ∧
  s.gpr (var t 4) = v[4] ∧ s.gpr (var t 5) = v[5] ∧
  s.gpr (var t 6) = v[6] ∧ s.gpr (var t 7) = v[7]

/-- The pointers, the count, the return address and the callee-saved
registers the rounds do not use: never written by the rounds. -/
def pubRegs : List Reg := [.a0, .a1, .a2, .a3, .ra, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9,
  .s10, .s11]

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 7) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega_arith

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 7 := by
  simp only [var]; congr 1; omega_arith

/-- The registers of a round are all different. -/
theorem round_nodup (t : Nat) :
    ([var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, T0, T1, T2, T3] ++
      pubRegs).Nodup := by
  simp only [var]
  have := Nat.mod_lt t (show 8 > 0 by omega_arith)
  generalize t % 8 = c at *
  revert this; revert c; decide

/-- The round is symbolically executed once, for any registers `a … h`
(which `round_nodup` says are different from each other and the others). -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars t s v) (hw : s.gpr T0 = w) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  -- The registers the round reads and writes.
  have hs := (List.nodup_append.mp (round_nodup t)).1
  have hs' := List.nodup_reverse.mpr hs
  have hdj := (List.nodup_append.mp (round_nodup t)).2.2
  -- The registers the round writes are not in `pubRegs`.
  have hpw : ∀ r ∈ pubRegs, r ≠ var t 3 ∧ r ≠ var t 7 ∧ r ≠ T1 ∧ r ≠ T2 :=
    fun r hr => ⟨fun e => hdj _ (by simp) r hr e.symm, fun e => hdj _ (by simp) r hr e.symm,
      fun e => hdj _ (by simp) r hr e.symm, fun e => hdj _ (by simp) r hr e.symm⟩
  clear hdj
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 7 by omega_arith),
    var_succ t _ (show 1 < 7 by omega_arith), var_succ t _ (show 2 < 7 by omega_arith),
    var_succ t _ (show 3 < 7 by omega_arith), var_succ t _ (show 4 < 7 by omega_arith),
    var_succ t _ (show 5 < 7 by omega_arith), var_succ t _ (show 6 < 7 by omega_arith)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  apply WP.of_runBlock
  simp only [Impl.Sha512.RISCV64.round, bsig, xorRotr, li64, li32, List.cons_append, List.nil_append]
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  generalize var t 5 = f at *
  generalize var t 6 = g at *
  generalize var t 7 = h at *
  simp only [T0, T1, T2] at hpw hw ⊢
  simp only [T0, T1, T2, T3, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hs hs'
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_logic,
    exec_shift_d (show 14 < 64 by decide), exec_shift_d (show 64 - 14 < 64 by decide),
    exec_shift_d (show 18 < 64 by decide), exec_shift_d (show 64 - 18 < 64 by decide),
    exec_shift_d (show 41 < 64 by decide), exec_shift_d (show 64 - 41 < 64 by decide),
    exec_shift_d (show 28 < 64 by decide), exec_shift_d (show 64 - 28 < 64 by decide),
    exec_shift_d (show 34 < 64 by decide), exec_shift_d (show 64 - 34 < 64 by decide),
    exec_shift_d (show 39 < 64 by decide), exec_shift_d (show 64 - 39 < 64 by decide),
    exec_shift_d (show 32 < 64 by decide),
    exec_lui, exec_addiw_lo12, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, hs, hs', Option.some.injEq, exists_eq_left', ↓reduceIte, true_and]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_⟩
  rotate_right
  · obtain ⟨n3, n7, n17, n18⟩ := hpw r hr
    simp only [n3, n7, n17, n18, ↓reduceIte]
  all_goals
    simp (config := {failIfUnchanged := false}) only [lo32_sext, li32_val, li64_val, h0, h1, h2, h3,
      h4, h5, h6, h7, hw]
  all_goals
    simp (config := {failIfUnchanged := false}) only [roundKW, bsig1_shifts, ch_eq, bsig0_shifts,
      maj_eq, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, Nat.reduceSub] <;>
    simp (config := {failIfUnchanged := false}) only [BitVec.add_assoc]

/-! ## The message schedule -/

theorem slot_lt (j : Nat) : slot j < 2048 := by
  simp only [slot]; omega_arith

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : Addr) (j : Nat) : Addr := scr + BitVec.ofNat 64 (slot j)

/-- With `scratch` 8-byte aligned, the slots are naturally aligned. -/
theorem slot_al {scr : Addr} (hal : scr.toNat % 8 = 0) (j : Nat) :
    (scr + BitVec.ofNat 64 (slot j)).toNat % 8 = 0 := by
  simp only [slot]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * (j % 16)) (by omega_arith)]
  have := scr.isLt
  omega_arith

/-- A load of a slot, with `scratch` (`a3`) aligned. -/
theorem exec_ld_slot {s : State} {t : Reg} {j : Nat} (hal : (s.gpr .a3).toNat % 8 = 0)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .a3 + BitVec.ofNat 64 (slot j)) 8) :
    exec (.load .d t .a3 (slot j)) s =
      some (s.write t (s.mem.readW (s.gpr .a3 + BitVec.ofNat 64 (slot j)) 64)) :=
  exec_load_d (slot_lt j) (slot_al hal j) hin

/-- A store to a slot, with `scratch` (`a3`) aligned. -/
theorem exec_sd_slot {s : State} {t : Reg} {j : Nat} (hal : (s.gpr .a3).toNat % 8 = 0)
    (hout : InRegions s.wr (s.gpr .a3 + BitVec.ofNat 64 (slot j)) 8) :
    exec (.store .d t .a3 (slot j)) s =
      some { s with mem := s.mem.writeW (s.gpr .a3 + BitVec.ofNat 64 (slot j)) (s.gpr t) } :=
  exec_store_d (slot_lt j) (slot_al hal j) hout

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : Addr)
    (hr1 : s.gpr .a1 = bp) (hr3 : s.gpr .a3 = scr) (hal : scr.toNat % 8 = 0)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 8)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 8)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (8 * t)) 8)
    (hblk : t < 16 → be64 s.mem bp (8 * t) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (slotAddr scr j) 64 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      s'.gpr T0 = W M t ∧
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → r ≠ T3 → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hin hout hwin ⊢
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    simp only [Impl.Sha512.RISCV64.schedule, ht, ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (loadBE64_ok (by decide) (by decide) (by decide) (by omega_arith) (by rw [hr1]; exact hi))
      fun s₁ e => ?_
    have g3 : s₁.gpr .a3 = scr := by rw [e, ← hr3]; rfl
    have gw : s₁.wr = s.wr := by rw [e]; rfl
    have gr : s₁.rd = s.rd := by rw [e]; rfl
    have gm : s₁.mem = s.mem := by rw [e]; rfl
    have g0 : s₁.gpr T0 = W M t := by
      rw [e, RegUpd.gpr_write_self, hr1, hb]
    have gk : ∀ r, r ≠ T0 → r ≠ T1 → s₁.gpr r = s.gpr r := fun r h0 h1 => by
      rw [e, RegUpd.gpr_write_of_ne _ _ h0, RegUpd.gpr_write_of_ne _ _ h1]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil,
      exec_store_d (s := s₁) (slot_lt t) (by rw [g3]; exact slot_al hal t)
        (by rw [gw, g3]; exact hout t), Option.some.injEq, exists_eq_left', g3]
    exact ⟨g0, by rw [gm, g0], gr, gw, fun r h0 h1 _ _ => gk r h0 h1⟩
  · have hw := hwin (by omega_arith)
    have e2 := hw (t - 2) (by omega_arith) (by omega_arith)
    have e7 := hw (t - 7) (by omega_arith) (by omega_arith)
    have e15 := hw (t - 15) (by omega_arith) (by omega_arith)
    have e16 := hw (t - 16) (by omega_arith) (by omega_arith)
    rw [show slot (t - 2) = slot (t + 14) by simp only [slot]; omega_arith] at e2
    rw [show slot (t - 7) = slot (t + 9) by simp only [slot]; omega_arith] at e7
    rw [show slot (t - 15) = slot (t + 1) by simp only [slot]; omega_arith] at e15
    rw [show slot (t - 16) = slot t by simp only [slot]; omega_arith] at e16
    simp only [Impl.Sha512.RISCV64.schedule, ht, ite_false, ssig, xorRotr, T0, T1, T2, T3,
      List.cons_append, List.nil_append]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_logic,
      exec_shift_d (show 19 < 64 by decide), exec_shift_d (show 64 - 19 < 64 by decide),
      exec_shift_d (show 61 < 64 by decide), exec_shift_d (show 64 - 61 < 64 by decide),
      exec_shift_d (show 6 < 64 by decide), exec_shift_d (show 1 < 64 by decide),
      exec_shift_d (show 64 - 1 < 64 by decide), exec_shift_d (show 8 < 64 by decide),
      exec_shift_d (show 64 - 8 < 64 by decide), exec_shift_d (show 7 < 64 by decide),
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, reduceCtorEq,
      ↓reduceIte, hr3, exec_ld_slot, exec_sd_slot, hal, hin, hout, Option.some.injEq,
      exists_eq_left']
    simp only [e2, e7, e15, e16]
    have hW := W_ge M (t := t) (by omega_arith)
    rw [ssig1_shifts, ssig0_shifts] at hW
    simp only [Nat.reduceSub, ← hW, true_and]
    intro r h0 h1 h2 h3
    simp only [h0, h1, h2, h3, ↓reduceIte]

/-! ## The 80 rounds -/

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 8 - t % 8) % 8]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne' : ∀ r ∈ work, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 := by decide

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 :=
  work_ne' r h

theorem pubRegs_ne' : ∀ r ∈ pubRegs, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 := by decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 :=
  pubRegs_ne' r h

/-- The window `⟨scr, 128⟩`. -/
abbrev winRegion (scr : Addr) : Region := ⟨scr, 128⟩

theorem win_contains (scr : Addr) (j : Nat) : (winRegion scr).Contains (slotAddr scr j) 8 := by
  simp only [slotAddr, slot]
  exact Offset.contains_base scr (by omega_arith) (by omega_arith)

theorem slot_sep (scr : Addr) {i j : Nat} (h : i % 16 ≠ j % 16) :
    Mem.Sep (slotAddr scr i) 8 (slotAddr scr j) 8 := by
  simp only [slotAddr, slot]
  exact Offset.sep scr (by omega_arith) (by omega_arith) (by omega_arith)

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : Addr) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (VG.Spec.Sha512.rounds H M t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [winRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (slotAddr scr j) 64 = W M j

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : Addr) (sB : State)
    (hr1 : sB.gpr .a1 = bp) (hr3 : sB.gpr .a3 = scr) (hal : scr.toNat % 8 = 0)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 8)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 8)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (8 * t)) 8)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → be64 m bp (8 * t) = W M t)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 80, WP isa (rounds t) sB (RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, Frame.refl _ _,
      fun j hj => absurd hj (by omega_arith)⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega_arith)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_r1 : s.gpr .a1 = bp := (hs.pub .a1 (by decide)).trans hr1
    have hs_r3 : s.gpr .a3 = scr := (hs.pub .a3 (by decide)).trans hr3
    refine WP.mono (schedule_ok t s M bp scr hs_r1 hs_r3 hal
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.wr]; exact hout)
      (fun h => by rw [hs.rd, hs.wr]; exact hbin t h) (hblk _ hs.frame t)
      (fun _ => hs.win)) fun s₁ ⟨hT0, hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
    have hv₁ : Vars t s₁ (VG.Spec.Sha512.rounds H M t) := by
      have hv := hs.vars
      have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k =>
        have := work_ne (var_mem t k); hr₁ _ this.1 this.2.1 this.2.2.1 this.2.2.2
      simp only [Vars, e] at hv ⊢
      exact hv
    refine WP.mono (round_ok t s₁ _ _ hv₁ hT0) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr], ?_, ?_⟩
    · have e : VG.Spec.Sha512.rounds H M (t + 1) =
          roundKW (VG.Spec.Sha512.rounds H M t) (K t) (W M t) := by
        rw [rounds_succ, round_eq]
      rw [e]; exact hv₂
    · have := pubRegs_ne hr
      rw [hr₂ r hr, hr₁ r this.1 this.2.1 this.2.2.1 this.2.2.2, hs.pub r hr]
    · rw [hm₂, hm₁]
      exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains scr t)
    · intro j hj hj'
      rw [hm₂, hm₁]
      by_cases hjt : j = t
      · subst hjt; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (slot_sep scr (by omega_arith)) (by decide)]
        exact hs.win j (by omega_arith) (by omega_arith)

end VG.Proof.Sha512.RISCV64
