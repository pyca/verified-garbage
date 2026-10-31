module

import Mathlib.Data.List.Nodup
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.Sha256.Spec
public import VerifiedGarbage.Impl.Sha256.PPC64LE
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# SHA-256 compression function on PPC64LE: the message schedule and the rounds

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.Sha256.PPC64LE

open VG VG.PPC64LE VG.Impl.Sha256.PPC64LE
open VG.Spec.Sha256 (HashValue Word Block K W bsig0 bsig1 ch maj ssig0 ssig1)

theorem packed_word1 (f : Nat → BitVec 32) :
    ((List.range 4).foldl (fun x i => x ||| ((f i).setWidth 128 <<< (32*(3-i)))) (0 : BitVec 128)).extractLsb' 64 32 = f 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.foldl_cons, List.foldl_nil,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero,
    Nat.reduceSub, Nat.reduceMul, hj, decide_true, Bool.true_and]
  simp only [show 64+j < 128 by omega, show 64+j < 96 by omega,
    show ¬64+j < 64 by omega, show ¬64+j < 32 by omega, Nat.not_lt_zero,
    decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and,
    show 64+j-64 = j by omega, show 64+j-32 = 32+j by omega, Nat.sub_zero,
    show j < 128 by omega, show 32+j < 128 by omega,
    BitVec.getLsbD_of_ge (f 2) (32+j) (by omega), BitVec.getLsbD_of_ge (f 3) (64+j) (by omega),
    Bool.false_or, Bool.or_false]


theorem packed_low32 (f : Nat → BitVec 32) :
    (((List.range 4).foldl (fun x i => x ||| ((f i).setWidth 128 <<< (32*(3-i)))) (0 : BitVec 128)).extractLsb' 64 64).setWidth 32 = f 1 := by
  rw [BitVec.setWidth_extractLsb'_of_le (show 32 ≤ 64 by decide), packed_word1]

theorem word1_append (a b : BitVec 64) : vword (a ++ b) 1 = a.setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [vword, Nat.reduceSub, Nat.reduceMul, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
  rw [ite_eq_right (show ¬64+j < 64 by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem high_word_append (a b : BitVec 64) :
    (a ++ b).extractLsb' 64 32 = a.setWidth 32 := by
  simpa only [vword, Nat.reduceSub, Nat.reduceMul] using word1_append a b

/-- The working variables `v` are in the registers of round `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  vword (s.vpr (vvar t 0)) 1 = v[0] ∧ vword (s.vpr (vvar t 1)) 1 = v[1] ∧
  vword (s.vpr (vvar t 2)) 1 = v[2] ∧ vword (s.vpr (vvar t 3)) 1 = v[3] ∧
  vword (s.vpr (vvar t 4)) 1 = v[4] ∧ vword (s.vpr (vvar t 5)) 1 = v[5] ∧
  vword (s.vpr (vvar t 6)) 1 = v[6] ∧ vword (s.vpr (vvar t 7)) 1 = v[7]

/-- The pointers, the count and the nonvolatile registers the rounds do not
use: never written by the rounds. -/
def pubRegs : List Reg := [.r3, .r4, .r5, .r6, .r2, .r20, .r21, .r22, .r23, .r24, .r25, .r26,
  .r27, .r28, .r29, .r30, .r31]

/-- Reassociate the independent constant/message sum before the state-dependent terms. -/
theorem t1_add_tree (h k w s c : Word) :
    h + (k + w) + s + c = h + s + c + k + w := by
  ac_rfl

theorem vvar_succ (t k : Nat) (hk : k < 7) : vvar (t + 1) (k + 1) = vvar t k := by
  simp only [vvar]; congr 1; omega

theorem vvar_succ_zero (t : Nat) : vvar (t + 1) 0 = vvar t 7 := by
  simp only [vvar]; congr 1; omega

theorem vround_nodup (t : Nat) :
    ([vvar t 0, vvar t 1, vvar t 2, vvar t 3, vvar t 4, vvar t 5, vvar t 6, vvar t 7,
      .v12, .v13, .v14, .v15] : List VReg).Nodup := by
  simp only [vvar]
  have := Nat.mod_lt t (show 8 > 0 by omega)
  generalize t % 8 = c at *
  revert this; revert c; decide

/-- The working state stays in vectors, so neither sigma needs a register-bank transfer. -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars t s v) (hw : (s.gpr T0).setWidth 32 = w) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  have hs := vround_nodup t
  have hs' := List.nodup_reverse.mpr hs
  simp only [Vars, vvar_succ_zero, vvar_succ t _ (show 0 < 7 by omega),
    vvar_succ t _ (show 1 < 7 by omega), vvar_succ t _ (show 2 < 7 by omega),
    vvar_succ t _ (show 3 < 7 by omega), vvar_succ t _ (show 4 < 7 by omega),
    vvar_succ t _ (show 5 < 7 by omega), vvar_succ t _ (show 6 < 7 by omega)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  apply WP.of_runBlock
  simp only [Impl.Sha256.PPC64LE.round]
  generalize vvar t 0 = a at *
  generalize vvar t 1 = b at *
  generalize vvar t 2 = c at *
  generalize vvar t 3 = d at *
  generalize vvar t 4 = e at *
  generalize vvar t 5 = f at *
  generalize vvar t 6 = g at *
  generalize vvar t 7 = h at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hs hs'
  simp only [vword, Nat.reduceSub, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7
  simp only [T0] at hw
  simp only [T0, T1, runBlock_cons, runStep_some, runBlock_nil, reduceExec, reduceVOpEval,
    Option.map_some, vpr_writeV, vpr_write, gpr_writeV, mem_writeV, rd_writeV, wr_writeV,
    vword, Nat.reduceSub, Nat.reduceMul, packed_word1, high_word_append, lo32_add, lis_ori, BitVec.extractLsb'_xor,
    BitVec.extractLsb'_and, BitVec.extractLsb'_or,
    show (4 : Nat).testBit 2 = true by decide, show (0 : Nat).testBit 2 = false by decide,
    isa, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hs, hs', h0, h1, h2, h3, h4, h5, h6, h7, hw, Option.some.injEq, exists_eq_left',
    Nat.reduceAdd, Nat.reduceLT, reduceCtorEq, ↓reduceIte, true_and]
  refine ⟨?_, fun r hr => ?_⟩
  · simp only [roundKW, bsig1, ch_eq, bsig0, maj_eq, VG.PPC64LE.sigma256,
      ite_true, ite_false, Bool.false_eq_true, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    simp only [t1_add_tree, and_self]
  · have hn : r ≠ .r17 := by
      simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [hn, ite_false]

theorem slot_ok (j : Nat) : slot j < 2 ^ 15 := by
  simp only [slot]; omega

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : Addr) (j : Nat) : Addr := scr + BitVec.ofNat 64 (slot j)

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : Addr)
    (hr4 : s.gpr .r4 = bp) (hr6 : s.gpr .r6 = scr)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 4)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4 * t)) 4)
    (hblk : t < 16 → rev32 (s.mem.readW (bp + BitVec.ofNat 64 (4 * t)) 32) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      (s'.gpr T0).setWidth 32 = W M t ∧
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → r ≠ T3 → r ≠ .r0 → s'.gpr r = s.gpr r) ∧
      ∀ r ∈ vwork, s'.vpr r = s.vpr r := by
  simp only [slotAddr] at hin hout hwin ⊢
  apply WP.of_runBlock
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    simp only [Impl.Sha256.PPC64LE.schedule, ht, ite_true, T0, T1, T2, T3]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_li (show 4 * t < 2 ^ 15 by omega),
      exec_loadRev_w, exec_store_w, slot_ok, isa, vpr_write, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hr4, hr6, hi, hout, 
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, hb, Option.some.injEq,
      exists_eq_left', 
      Nat.reduceLeDiff, reduceCtorEq, ↓reduceIte, ne_eq,
      not_false_eq_true, true_and]
    refine ⟨fun r h0 _ _ _ h4 => ?_, fun _ _ => True.intro⟩
    simp [h0, h4]
  · have hw := hwin (by omega)
    have e2 := hw (t - 2) (by omega) (by omega)
    have e7 := hw (t - 7) (by omega) (by omega)
    have e15 := hw (t - 15) (by omega) (by omega)
    have e16 := hw (t - 16) (by omega) (by omega)
    rw [show slot (t - 2) = slot (t + 14) by simp only [slot]; omega] at e2
    rw [show slot (t - 7) = slot (t + 9) by simp only [slot]; omega] at e7
    rw [show slot (t - 15) = slot (t + 1) by simp only [slot]; omega] at e15
    rw [show slot (t - 16) = slot t by simp only [slot]; omega] at e16
    simp only [Impl.Sha256.PPC64LE.schedule, ht, ite_false, T0, T1, T2, T3]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_load_w, exec_store_w, slot_ok,
      exec_add, reduceExec, reduceVOpEval, Option.map_some,
      vpr_writeV, vpr_write, gpr_writeV, mem_writeV, rd_writeV, wr_writeV, vdword, Nat.sub_zero, Nat.mul_one, isa, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hr6, hin, hout, 
      Option.some.injEq, exists_eq_left', 
      Nat.reduceLT, reduceCtorEq,
      ↓reduceIte, ne_eq, not_false_eq_true, true_and
      ]
    simp only [lo32_add, packed_low32, word1_append, Nat.reduceSub,
      show (4 : Nat).testBit 2 = true by decide, show (0 : Nat).testBit 2 = false by decide,
      VG.PPC64LE.sigma256, ite_true, ite_false, Bool.false_eq_true,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      e2, e7, e15, e16, 
      Nat.reduceLeDiff
      ]
    have hW := W_ge M (t := t) (by omega)
    refine ⟨by rw [hW]; rfl, by rw [hW]; rfl, (fun r h0 h1 h2 h3 _ => ?_), fun r hr => ?_⟩
    · simp [h0, h1, h2]
    · have hn : r ≠ .v0 ∧ r ≠ .v1 := by
        simp only [vwork, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [hn.1, hn.2, ite_false]


/-! ## The 64 rounds -/

theorem pubRegs_ne' : ∀ r ∈ pubRegs, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 ∧ r ≠ .r0 := by decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 ∧ r ≠ .r0 :=
  pubRegs_ne' r h

/-- The window `⟨scr, 64⟩`. -/
abbrev winRegion (scr : Addr) : Region := ⟨scr, 64⟩

theorem win_contains (scr : Addr) (j : Nat) : (winRegion scr).Contains (slotAddr scr j) 4 := by
  simp only [Region.Contains, slotAddr, slot]
  have : j % 16 < 16 := Nat.mod_lt _ (by omega)
  generalize j % 16 = p at *
  rw [show scr + BitVec.ofNat 64 (4 * p) - scr = BitVec.ofNat 64 (4 * p) by bv_omega]
  simp only [BitVec.toNat_ofNat]
  omega

theorem slot_sep (scr : Addr) {i j : Nat} (h : i % 16 ≠ j % 16) :
    Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  intro x hx hy
  simp only [slotAddr, slot] at hx hy
  have hi : i % 16 < 16 := Nat.mod_lt _ (by omega)
  have hj : j % 16 < 16 := Nat.mod_lt _ (by omega)
  generalize i % 16 = p at *
  generalize j % 16 = q at *
  bv_omega

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : Addr) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (VG.Spec.Sha256.rounds H M t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [winRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : Addr) (sB : State)
    (hrsi : sB.gpr .r4 = bp) (hrcx : sB.gpr .r6 = scr)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (4 * t)) 4)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → rev32 (m.readW (bp + BitVec.ofNat 64 (4 * t)) 32) = W M t)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 64, WP isa (rounds t) sB (RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (by omega)⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_rsi : s.gpr .r4 = bp := (hs.pub .r4 (by decide)).trans hrsi
    have hs_rcx : s.gpr .r6 = scr := (hs.pub .r6 (by decide)).trans hrcx
    refine WP.mono (schedule_ok t s M bp scr hs_rsi hs_rcx
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.wr]; exact hout)
      (fun h => by rw [hs.rd, hs.wr]; exact hbin t h) (hblk _ hs.frame t)
      (fun _ => hs.win)) fun s₁ ⟨hT0, hm₁, hrd₁, hwr₁, hr₁, hvr₁⟩ => ?_
    have hv₁ : Vars t s₁ (VG.Spec.Sha256.rounds H M t) := by
      have hv := hs.vars
      have e : ∀ k, s₁.vpr (vvar t k) = s.vpr (vvar t k) := fun k => hvr₁ _ (by
        unfold vvar List.getD
        cases h : vwork[(k + 8 - t % 8) % 8]?
        · simp [vwork]
        · exact List.mem_of_getElem? h)
      simp only [Vars, e] at hv ⊢
      exact hv
    refine WP.mono (round_ok t s₁ _ _ hv₁ hT0) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr], ?_, ?_⟩
    · have e : VG.Spec.Sha256.rounds H M (t + 1) =
          roundKW (VG.Spec.Sha256.rounds H M t) (K t) (W M t) := by
        rw [rounds_succ, round_eq]
      rw [e]; exact hv₂
    · have := pubRegs_ne hr
      rw [hr₂ r hr, hr₁ r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2, hs.pub r hr]
    · rw [hm₂, hm₁]
      exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains scr t)
    · intro j hj hj'
      rw [hm₂, hm₁]
      by_cases hjt : j = t
      · subst hjt; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (slot_sep scr (by omega)) (by decide)]
        exact hs.win j (by omega) (by omega)

end VG.Proof.Sha256.PPC64LE
