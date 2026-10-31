module

import Mathlib.Data.List.Nodup
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.Sha512.Spec
public import VerifiedGarbage.Impl.Sha512.PPC64LE
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# SHA-512 compression function on PPC64LE: the message schedule and the rounds

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.Sha512.PPC64LE

open VG VG.PPC64LE VG.Impl.Sha512.PPC64LE
open VG.Spec.Sha512 (HashValue Word Block K W bsig0 bsig1 ch maj ssig0 ssig1)

theorem high64_append (a b : BitVec 64) : (a ++ b).extractLsb' 64 64 = a :=
  BitVec.extractLsb'_append_eq_left

/-- The working variables `v` are in the registers of round `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  vdword (s.vpr (vvar t 0)) 0 = v[0] ∧ vdword (s.vpr (vvar t 1)) 0 = v[1] ∧
  vdword (s.vpr (vvar t 2)) 0 = v[2] ∧ vdword (s.vpr (vvar t 3)) 0 = v[3] ∧
  vdword (s.vpr (vvar t 4)) 0 = v[4] ∧ vdword (s.vpr (vvar t 5)) 0 = v[5] ∧
  vdword (s.vpr (vvar t 6)) 0 = v[6] ∧ vdword (s.vpr (vvar t 7)) 0 = v[7]

/-- The pointers, the count and the nonvolatile registers the rounds do not
use: never written by the rounds. -/
def pubRegs : List Reg := [.r3, .r4, .r5, .r6, .r2, .r20, .r21, .r22, .r23, .r24, .r25, .r26,
  .r27, .r28, .r29, .r30, .r31]

/-- `movImm64` leaves the constant in the register. -/
theorem movImm64_eq (x : BitVec 64) :
    ((x.extractLsb' 48 16 ++ (0 : BitVec 16)).signExtend 64 ||| (x.extractLsb' 32 16).setWidth 64) <<< 32 |||
      (x.extractLsb' 16 16).setWidth 64 <<< 16 ||| (x.extractLsb' 0 16).setWidth 64 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_signExtend, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (by omega : i < 16 ∨ 16 ≤ i ∧ i < 32 ∨ 32 ≤ i ∧ i < 48 ∨ 48 ≤ i) with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
  · simp [hi, h, show i < 32 by omega]
  · simp [hi, h2, show ¬ i < 16 by omega, show i - 16 < 16 by omega, show 16 + (i - 16) = i by omega,
      show i - 16 < 64 by omega]
  · simp [hi, show ¬ i < 32 by omega, show ¬ i < 16 by omega, show i - 32 < 16 by omega,
      show 32 + (i - 32) = i by omega, show ¬ i - 16 < 16 by omega, show i - 32 < 64 by omega,
      show ¬ 32 ≤ i - 32 by omega]
  · simp [hi, show ¬ i < 32 by omega, show ¬ i < 16 by omega, show ¬ i - 32 < 16 by omega,
      show i - 32 < 32 by omega, show i - 32 - 16 < 16 by omega, show 48 + (i - 32 - 16) = i by omega,
      show ¬ i - 16 < 16 by omega, show i - 32 < 64 by omega]

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 7) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 7 := by
  simp only [var]; congr 1; omega

/-- The registers of a round are all different. -/
theorem round_nodup (t : Nat) :
    ([var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, T0, T1, T2, T3] ++
      pubRegs).Nodup := by
  simp only [var]
  have := Nat.mod_lt t (show 8 > 0 by omega)
  generalize t % 8 = c at *
  revert this; revert c; decide

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
    (hv : Vars t s v) (hw : s.gpr T0 = w) :
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
  simp only [Impl.Sha512.PPC64LE.round, movImm64, List.cons_append, List.nil_append]
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
  simp only [vdword, Nat.sub_zero, Nat.mul_one] at h0 h1 h2 h3 h4 h5 h6 h7
  simp only [T0] at hw
  simp only [T0, T1, runBlock_cons, runStep_some, runBlock_nil, reduceExec, reduceVOpEval,
    Option.map_some, vpr_writeV, vpr_write, gpr_writeV, mem_writeV, rd_writeV, wr_writeV,
    vdword, Nat.sub_zero, Nat.mul_one, high64_append, BitVec.extractLsb'_xor,
    BitVec.extractLsb'_and, BitVec.extractLsb'_or,
    show (8 : Nat) &&& 5 = 0 by decide, show (0 : Nat) &&& 5 = 0 by decide,
    show (8 : Nat).testBit 3 = true by decide, show (8 : Nat).testBit 1 = false by decide,
    show (0 : Nat).testBit 3 = false by decide, show (0 : Nat).testBit 1 = false by decide,
    and_self, isa, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hs, hs', h0, h1, h2, h3, h4, h5, h6, h7, hw, Option.some.injEq, exists_eq_left',
    Nat.reduceAdd, Nat.reduceLT, reduceCtorEq, ↓reduceIte, true_and]
  refine ⟨?_, fun r hr => ?_⟩
  · simp only [roundKW, bsig1, ch_eq, bsig0, maj_eq, VG.PPC64LE.sigma512,
      ite_true, ite_false, Bool.false_eq_true, movImm64_eq, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    simp only [t1_add_tree, and_self]
  · have hn : r ≠ .r17 := by
      simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [hn, ite_false]

theorem slot_ok (j : Nat) : slot j < 2 ^ 15 ∧ slot j % 4 = 0 := by
  simp only [slot]; omega

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : Addr) (j : Nat) : Addr := scr + BitVec.ofNat 64 (slot j)

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : Addr)
    (hr4 : s.gpr .r4 = bp) (hr6 : s.gpr .r6 = scr)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 8)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 8)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (8 * t)) 8)
    (hblk : t < 16 → rev64 (s.mem.readW (bp + BitVec.ofNat 64 (8 * t)) 64) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (slotAddr scr j) 64 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      s'.gpr T0 = W M t ∧
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → r ≠ T3 → r ≠ .r0 → s'.gpr r = s.gpr r) ∧
      ∀ r ∈ vwork, s'.vpr r = s.vpr r := by
  simp only [slotAddr] at hin hout hwin ⊢
  apply WP.of_runBlock
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    simp only [Impl.Sha512.PPC64LE.schedule, ht, ite_true, T0, T1, T2, T3]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_li (show 8 * t < 2 ^ 15 by omega),
      exec_loadRev_d, exec_store_d, slot_ok, isa, vpr_write, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hr4, hr6, hi, hout, hb,
      Option.some.injEq, exists_eq_left', reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true,
      and_self, true_and]
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
    simp only [Impl.Sha512.PPC64LE.schedule, ht, ite_false, T0, T1, T2, T3]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_load_d, exec_store_d, slot_ok,
      exec_add, reduceExec, reduceVOpEval, Option.map_some,
      vpr_writeV, vpr_write, gpr_writeV, mem_writeV, rd_writeV, wr_writeV, vdword, Nat.sub_zero, Nat.mul_one,
      high64_append, VG.PPC64LE.sigma512, Bool.false_eq_true,
      show (8 : Nat) &&& 5 = 0 by decide, show (0 : Nat) &&& 5 = 0 by decide,
      show (8 : Nat).testBit 3 = true by decide, show (8 : Nat).testBit 1 = false by decide,
      show (0 : Nat).testBit 3 = false by decide, show (0 : Nat).testBit 1 = false by decide,
      isa, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hr6, hin, hout, e2, e7, e15,
      e16, Option.some.injEq, exists_eq_left', Nat.reduceLT, reduceCtorEq, ↓reduceIte, ne_eq,
      not_false_eq_true, and_self, true_and]
    have hW := W_ge M (t := t) (by omega)
    refine ⟨by rw [hW]; rfl, by rw [hW]; rfl, (fun r h0 h1 h2 h3 _ => ?_), fun r hr => ?_⟩
    · simp [h0, h1, h2]
    · have hn : r ≠ .v0 ∧ r ≠ .v1 := by
        simp only [vwork, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [hn.1, hn.2, ite_false]


/-! ## The 80 rounds -/

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 8 - t % 8) % 8]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne' : ∀ r ∈ work, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 ∧ r ≠ .r0 := by decide

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 ∧ r ≠ .r0 :=
  work_ne' r h

theorem pubRegs_ne' : ∀ r ∈ pubRegs, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 ∧ r ≠ .r0 := by decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 ∧ r ≠ .r0 :=
  pubRegs_ne' r h

/-- The window `⟨scr, 128⟩`. -/
abbrev winRegion (scr : Addr) : Region := ⟨scr, 128⟩

theorem win_contains (scr : Addr) (j : Nat) : (winRegion scr).Contains (slotAddr scr j) 8 := by
  simp only [Region.Contains, slotAddr, slot]
  have : j % 16 < 16 := Nat.mod_lt _ (by omega)
  generalize j % 16 = p at *
  rw [show scr + BitVec.ofNat 64 (8 * p) - scr = BitVec.ofNat 64 (8 * p) by bv_omega]
  simp only [BitVec.toNat_ofNat]
  omega

theorem slot_sep (scr : Addr) {i j : Nat} (h : i % 16 ≠ j % 16) :
    Mem.Sep (slotAddr scr i) 8 (slotAddr scr j) 8 := by
  intro x hx hy
  simp only [slotAddr, slot] at hx hy
  have hi : i % 16 < 16 := Nat.mod_lt _ (by omega)
  have hj : j % 16 < 16 := Nat.mod_lt _ (by omega)
  generalize i % 16 = p at *
  generalize j % 16 = q at *
  bv_omega

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : Addr) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (VG.Spec.Sha512.rounds H M t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [winRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (slotAddr scr j) 64 = W M j

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : Addr) (sB : State)
    (hrsi : sB.gpr .r4 = bp) (hrcx : sB.gpr .r6 = scr)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 8)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 8)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (8 * t)) 8)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → rev64 (m.readW (bp + BitVec.ofNat 64 (8 * t)) 64) = W M t)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 80, WP isa (rounds t) sB (RInv H M scr sB t) := by
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
    have hv₁ : Vars t s₁ (VG.Spec.Sha512.rounds H M t) := by
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
    · have e : VG.Spec.Sha512.rounds H M (t + 1) =
          roundKW (VG.Spec.Sha512.rounds H M t) (K t) (W M t) := by
        rw [rounds_succ, round_eq]
      rw [e]; exact hv₂
    · have := pubRegs_ne hr
      rw [hr₂ r hr, hr₁ r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2, hs.pub r hr]
    · rw [hm₂, hm₁]
      exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains scr t)
    · intro j hj hj'
      rw [hm₂, hm₁]
      by_cases hjt : j = t
      · subst hjt; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (slot_sep scr (by omega)) (by decide)]
        exact hs.win j (by omega) (by omega)

end VG.Proof.Sha512.PPC64LE
