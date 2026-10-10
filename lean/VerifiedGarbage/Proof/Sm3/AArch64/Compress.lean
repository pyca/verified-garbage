import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Sm3.Spec
import VerifiedGarbage.Impl.Sm3.AArch64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sm3.StateMem
import VerifiedGarbage.Proof.Sm3.AArch64.Contract
import VerifiedGarbage.Proof.Sm3.AArch64.Lit

/-!
# SM3 compression function on AArch64: the message expansion and the iterations
-/

namespace VG.Proof.Sm3.AArch64

open VG VG.AArch64 VG.Impl.Sm3.AArch64
open VG.Spec.Sm3 (HashValue Word Block W p0 p1 ff gg)

/-- The registers `v` are in the registers of iteration `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0].setWidth 64 ∧ s.gpr (var t 1) = v[1].setWidth 64 ∧
  s.gpr (var t 2) = v[2].setWidth 64 ∧ s.gpr (var t 3) = v[3].setWidth 64 ∧
  s.gpr (var t 4) = v[4].setWidth 64 ∧ s.gpr (var t 5) = v[5].setWidth 64 ∧
  s.gpr (var t 6) = v[6].setWidth 64 ∧ s.gpr (var t 7) = v[7].setWidth 64

/-- The pointers, the count and the registers the ABI requires us to
preserve: never written by the iterations. -/
def pubRegs : List Reg := [.x0, .x1, .x2, .x3, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
  .x26, .x27, .x28, .x30]

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

/-! The registers an iteration reads are not those it writes after them
(`T0 … T3`, `B`, `D`, `F`, `H`). In parts: `decide` cannot synthesize the
instance of one long conjunction. -/

theorem round_ne0 (t : Nat) :
    ¬var t 0 = .x12 ∧ ¬var t 0 = .x13 ∧ ¬var t 0 = .x14 ∧ ¬var t 0 = .x15 ∧
      ¬var t 1 = .x12 ∧ ¬var t 1 = .x13 ∧ ¬var t 1 = .x14 ∧ ¬var t 1 = .x15 ∧
      ¬var t 2 = .x12 ∧ ¬var t 2 = .x13 ∧ ¬var t 2 = .x14 ∧ ¬var t 2 = .x15 := by
  simp only [var]
  have := Nat.mod_lt t (show 4 > 0 by decide)
  generalize t % 4 = c at *
  revert this; revert c; decide

theorem round_ne1 (t : Nat) :
    ¬var t 3 = .x12 ∧ ¬var t 3 = .x13 ∧ ¬var t 3 = .x14 ∧ ¬var t 3 = .x15 ∧
      ¬var t 4 = .x12 ∧ ¬var t 4 = .x13 ∧ ¬var t 4 = .x14 ∧ ¬var t 4 = .x15 ∧
      ¬var t 5 = .x12 ∧ ¬var t 5 = .x13 ∧ ¬var t 5 = .x14 ∧ ¬var t 5 = .x15 := by
  simp only [var]
  have := Nat.mod_lt t (show 4 > 0 by decide)
  generalize t % 4 = c at *
  revert this; revert c; decide

theorem round_ne2 (t : Nat) :
    ¬var t 6 = .x12 ∧ ¬var t 6 = .x13 ∧ ¬var t 6 = .x14 ∧ ¬var t 6 = .x15 ∧
      ¬var t 7 = .x12 ∧ ¬var t 7 = .x13 ∧ ¬var t 7 = .x14 ∧ ¬var t 7 = .x15 ∧
      ¬Reg.x12 = var t 1 ∧ ¬Reg.x12 = var t 3 ∧ ¬Reg.x12 = var t 5 ∧ ¬Reg.x12 = var t 7 := by
  simp only [var]
  have := Nat.mod_lt t (show 4 > 0 by decide)
  generalize t % 4 = c at *
  revert this; revert c; decide

theorem round_ne3 (t : Nat) :
    ¬Reg.x13 = var t 1 ∧ ¬Reg.x13 = var t 3 ∧ ¬Reg.x13 = var t 5 ∧ ¬Reg.x13 = var t 7 ∧
      ¬Reg.x14 = var t 1 ∧ ¬Reg.x14 = var t 3 ∧ ¬Reg.x14 = var t 5 ∧ ¬Reg.x14 = var t 7 ∧
      ¬Reg.x15 = var t 1 ∧ ¬Reg.x15 = var t 3 ∧ ¬Reg.x15 = var t 5 ∧ ¬Reg.x15 = var t 7 := by
  simp only [var]
  have := Nat.mod_lt t (show 4 > 0 by decide)
  generalize t % 4 = c at *
  revert this; revert c; decide

theorem round_ne4 (t : Nat) :
    ¬Reg.x3 = var t 1 ∧ ¬Reg.x3 = var t 3 ∧ ¬Reg.x3 = var t 5 ∧ ¬Reg.x3 = var t 7 ∧
      ¬var t 0 = var t 1 ∧ ¬var t 0 = var t 3 ∧ ¬var t 0 = var t 5 ∧ ¬var t 0 = var t 7 ∧
      ¬var t 1 = var t 3 ∧ ¬var t 1 = var t 5 ∧ ¬var t 1 = var t 7 ∧ ¬var t 2 = var t 1 := by
  simp only [var]
  have := Nat.mod_lt t (show 4 > 0 by decide)
  generalize t % 4 = c at *
  revert this; revert c; decide

theorem round_ne5 (t : Nat) :
    ¬var t 2 = var t 3 ∧ ¬var t 2 = var t 5 ∧ ¬var t 2 = var t 7 ∧ ¬var t 3 = var t 1 ∧
      ¬var t 3 = var t 5 ∧ ¬var t 3 = var t 7 ∧ ¬var t 4 = var t 1 ∧ ¬var t 4 = var t 3 ∧
      ¬var t 4 = var t 5 ∧ ¬var t 4 = var t 7 ∧ ¬var t 5 = var t 1 ∧ ¬var t 5 = var t 3 := by
  simp only [var]
  have := Nat.mod_lt t (show 4 > 0 by decide)
  generalize t % 4 = c at *
  revert this; revert c; decide

theorem round_ne6 (t : Nat) :
    ¬var t 5 = var t 7 ∧ ¬var t 6 = var t 1 ∧ ¬var t 6 = var t 3 ∧ ¬var t 6 = var t 5 ∧
      ¬var t 6 = var t 7 ∧ ¬var t 7 = var t 1 ∧ ¬var t 7 = var t 3 ∧ ¬var t 7 = var t 5 := by
  simp only [var]
  have := Nat.mod_lt t (show 4 > 0 by decide)
  generalize t % 4 = c at *
  revert this; revert c; decide

/-- The registers the iterations keep are none of those an iteration writes. -/
theorem pub_ne (t : Nat) :
    ∀ r ∈ pubRegs, ¬r = .x12 ∧ ¬r = .x13 ∧ ¬r = .x14 ∧ ¬r = .x15 ∧
      ¬r = var t 1 ∧ ¬r = var t 3 ∧ ¬r = var t 5 ∧ ¬r = var t 7 := by
  simp only [var]
  have := Nat.mod_lt t (show 4 > 0 by omega)
  generalize t % 4 = c at *
  revert this; revert c; decide

/-- `movz` of the low half then `movk` of the high half (`movz_movk`, with
the mask a literal, as `exec_movk_w` leaves it). -/
theorem movzk (x : BitVec 32) :
    (x.extractLsb' 0 16).setWidth 32 &&& (65535 : BitVec 32) ||| (x.extractLsb' 16 16).setWidth 32 <<< 16 = x :=
  movz_movk x

theorem slot_ok (j : Nat) : slot j % 4 = 0 ∧ slot j < 16384 := by
  simp only [slot]; omega

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : Addr) (j : Nat) : Addr := scr + BitVec.ofNat 64 (slot j)

set_option hygiene false in
/-- The symbolic execution of an iteration (`round_lo`, `round_hi`): for any
registers `A … H` (which `round_ne0 … round_ne6` say are different where it
matters), with the register writes kept folded (`VG.AArch64.RegUpd`). -/
macro "round_tac" : tactic => `(tactic| (
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := round_ne0 t
  obtain ⟨n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23⟩ := round_ne1 t
  obtain ⟨n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35⟩ := round_ne2 t
  obtain ⟨n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47⟩ := round_ne3 t
  obtain ⟨n48, n49, n50, n51, n52, n53, n54, n55, n56, n57, n58, n59⟩ := round_ne4 t
  obtain ⟨n60, n61, n62, n63, n64, n65, n66, n67, n68, n69, n70, n71⟩ := round_ne5 t
  obtain ⟨n72, n73, n74, n75, n76, n77, n78, n79⟩ := round_ne6 t
  have hp := pub_ne t
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := var_succ t
  simp only [Vars, e0, e1, e2, e3, e4, e5, e6, e7] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  simp only [slotAddr] at hin hin₄ hw hw₄
  apply WP.of_runBlock
  simp only [Impl.Sm3.AArch64.round, ht, ite_true, ite_false, List.cons_append, List.nil_append]
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  generalize var t 5 = f at *
  generalize var t 6 = g at *
  generalize var t 7 = h at *
  simp only [T0, T1, T2, T3, runBlock_cons, runStep_some, runBlock_nil, exec_ldr_w (slot_ok _),
    exec_movz_w, exec_movk_w, exec_add, exec_logic, exec_ror_w, isa, State.read, Size.bits,
    RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, ite_true, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceMul, not_false_eq_true,
    reduceCtorEq, hrcx, hin, hin₄, hw, hw₄,
    n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55, n56, n57, n58, n59, n60, n61, n62, n63, n64, n65, n66, n67, n68, n69, n70, n71, n72, n73, n74, n75, n76, n77, n78, n79,
    h0, h1, h2, h3, h4, h5, h6, h7,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, trivial, trivial, trivial, fun r hr => ?_⟩
  rotate_right
  · obtain ⟨p₁, p₂, p₃, p₄, p₅, p₆, p₇, p₈⟩ := hp r hr
    simp only [RegUpd.gpr_write_of_ne, p₁, p₂, p₃, p₄, p₅, p₆, p₇, p₈, not_false_eq_true]
  all_goals
    refine congrArg (BitVec.setWidth 64) ?_
    simp only [roundW_0, roundW_1, roundW_2, roundW_3, roundW_4, roundW_5, roundW_6, roundW_7,
      Spec.Sm3.ff, Spec.Sm3.gg, ht, ite_true, ite_false, maj_eq, ch_eq, tj, movzk, rotl9,
      rotl12, rotl7, rotl19] <;>
    first | exact tt1_eq _ _ _ _ _ | exact tt2_eq _ _ _ _))

theorem round_lo (t : Nat) (ht : t < 16) (s : State) (v : HashValue) (w w₄ : Word) (scr : Addr)
    (hv : Vars t s v) (hrcx : s.gpr .x3 = scr)
    (hin : InRegions (s.rd ++ s.wr) (slotAddr scr t) 4)
    (hin₄ : InRegions (s.rd ++ s.wr) (slotAddr scr (t + 4)) 4)
    (hw : s.mem.readW (slotAddr scr t) 32 = w) (hw₄ : s.mem.readW (slotAddr scr (t + 4)) 32 = w₄) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundW v t w w₄) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  round_tac

theorem round_hi (t : Nat) (ht : ¬t < 16) (s : State) (v : HashValue) (w w₄ : Word) (scr : Addr)
    (hv : Vars t s v) (hrcx : s.gpr .x3 = scr)
    (hin : InRegions (s.rd ++ s.wr) (slotAddr scr t) 4)
    (hin₄ : InRegions (s.rd ++ s.wr) (slotAddr scr (t + 4)) 4)
    (hw : s.mem.readW (slotAddr scr t) 32 = w) (hw₄ : s.mem.readW (slotAddr scr (t + 4)) 32 = w₄) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundW v t w w₄) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  round_tac

theorem round_ok (t : Nat) (s : State) (v : HashValue) (w w₄ : Word) (scr : Addr)
    (hv : Vars t s v) (hrcx : s.gpr .x3 = scr)
    (hin : InRegions (s.rd ++ s.wr) (slotAddr scr t) 4)
    (hin₄ : InRegions (s.rd ++ s.wr) (slotAddr scr (t + 4)) 4)
    (hw : s.mem.readW (slotAddr scr t) 32 = w) (hw₄ : s.mem.readW (slotAddr scr (t + 4)) 32 = w₄) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundW v t w w₄) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  by_cases ht : t < 16
  · exact round_lo t ht s v w w₄ scr hv hrcx hin hin₄ hw hw₄
  · exact round_hi t ht s v w w₄ scr hv hrcx hin hin₄ hw hw₄

theorem expand_ok (i : Nat) (s : State) (M : Block) (bp scr : Addr)
    (hx1 : s.gpr .x1 = bp) (hx3 : s.gpr .x3 = scr)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 4)
    (hbin : i < 16 → InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4 * i)) 4)
    (hblk : i < 16 → rev32 (s.mem.readW (bp + BitVec.ofNat 64 (4 * i)) 32) = W M i)
    (hwin : 16 ≤ i → ∀ j, j < i → i ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j) :
    WP isa (.block (expand i)) s fun s' =>
      s'.mem = s.mem.writeW (slotAddr scr i) (W M i) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → r ≠ T3 → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hin hout hwin ⊢
  apply WP.of_runBlock
  by_cases hi : i < 16
  · have hi' := hbin hi
    have hb := hblk hi
    have ho : 4 * i % 4 = 0 ∧ 4 * i < 16384 := by omega
    simp only [Impl.Sm3.AArch64.expand, hi, ite_true, T0]
    simp only [runBlock_cons, runStep_some,
      runBlock_nil, exec_ldr_w ho, exec_str_w (slot_ok _),
      exec_rev32, isa, State.read, Size.bits, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne,
      RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, not_false_eq_true, reduceCtorEq,
      Nat.reduceLeDiff, hx1, hx3, hi', hout,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, hb,
      Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, trivial, fun r h0 _ _ _ => ?_⟩
    simp only [RegUpd.gpr_write_of_ne, h0, not_false_eq_true]
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
    simp only [Impl.Sm3.AArch64.expand, hi, ite_false, T0, T1, T2]
    simp only [runBlock_cons, runStep_some,
      runBlock_nil, exec_ldr_w (slot_ok _),
      exec_str_w (slot_ok _), exec_logic, exec_ror_w, isa, State.read,
      Size.bits, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, Nat.reduceLT, Nat.reduceLeDiff, not_false_eq_true, reduceCtorEq, hx3, hin,
      hout, BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq, e16, e9, e3, e13, e6, Option.some.injEq, exists_eq_left']
    have hW := W_ge M (j := i) (by omega)
    rw [Spec.Sm3.p1, rotl15 (W M (i - 3)), rotl7, rotl15, rotl23] at hW
    refine ⟨by rw [hW], trivial, trivial, fun r h0 h1 h2 _ => ?_⟩
    simp only [RegUpd.gpr_write_of_ne, h0, h1, h2, not_false_eq_true]

/-! ## The 64 iterations -/

theorem getD_mem (l : List Reg) (n : Nat) (h : Reg.x4 ∈ l) : l.getD n .x4 ∈ l := by
  unfold List.getD
  cases hn : l[n]?
  · exact h
  · exact List.mem_of_getElem? hn

theorem var_mem (t k : Nat) : var t k ∈ group₁ ++ group₂ := by
  unfold var
  split
  · exact List.mem_append_left _ (getD_mem _ _ (by decide))
  · refine List.mem_append_right _ ?_
    unfold List.getD
    cases hn : group₂[(k + 4 - t % 4) % 4]?
    · have := Nat.mod_lt (k + 4 - t % 4) (show 4 > 0 by decide)
      simp [group₂] at hn; omega
    · exact List.mem_of_getElem? hn

theorem work_ne' : ∀ r ∈ group₁ ++ group₂, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 := by decide

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
  (hx1 : sB.gpr .x1 = bp) (hx3 : sB.gpr .x3 = scr)
  (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
  (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
  (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (4 * t)) 4)
  (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
    ∀ t : Nat, t < 16 → rev32 (m.readW (bp + BitVec.ofNat 64 (4 * t)) 32) = W M t)
include hx1 hx3 hin hout hbin hblk

theorem expand_inv {V : HashValue} {t i : Nat} {s : State} (hs : Inv V M scr sB t i s) :
    WP isa (.block (expand i)) s (Inv V M scr sB t (i + 1)) := by
  refine WP.mono (expand_ok i s M bp scr ((hs.pub .x1 (by decide)).trans hx1)
    ((hs.pub .x3 (by decide)).trans hx3)
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
    refine WP.mono (expand_inv hx1 hx3 hin hout hbin hblk i₀) fun s₁ h₁ => ?_
    refine WP.mono (expand_inv hx1 hx3 hin hout hbin hblk h₁) fun s₂ h₂ => ?_
    refine WP.mono (expand_inv hx1 hx3 hin hout hbin hblk h₂) fun s₃ h₃ => ?_
    exact expand_inv hx1 hx3 hin hout hbin hblk h₃
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    refine WP.mono (expand_inv hx1 hx3 hin hout hbin hblk hs) fun s₁ h₁ => ?_
    have hx3₁ : s₁.gpr .x3 = scr := (h₁.pub .x3 (by decide)).trans hx3
    refine WP.mono (round_ok t s₁ _ (W M t) (W M (t + 4)) scr h₁.vars hx3₁
      (by rw [h₁.rd, h₁.wr]; exact hin t) (by rw [h₁.rd, h₁.wr]; exact hin (t + 4))
      (h₁.win t (by omega) (by omega)) (h₁.win (t + 4) (by omega) (by omega)))
      fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => by rw [hr₂ r hr, h₁.pub r hr], by rw [hrd₂, h₁.rd],
      by rw [hwr₂, h₁.wr], by rw [hm₂]; exact h₁.frame, fun j hj hj' => ?_⟩
    · rw [rounds_succ, round_eq]; exact hv₂
    · rw [hm₂]; exact h₁.win j (by omega) (by omega)

end

end VG.Proof.Sm3.AArch64

/-!
# SM3 compression function on AArch64: the whole function
-/

namespace VG.Proof.Sm3.AArch64

open VG VG.AArch64 VG.Impl.Sm3.AArch64
open VG.Spec.Sm3 (HashValue Word Block W stateAt blockAt compressBlocks compress parseBlock)

/-! The hash value in memory and offsets into regions (`Proof/Sm3/StateMem.lean`). -/
export VG.Proof.Sm3.StateMem (toNat_ofNat_lt contains_offset sub_offset word_sep
  readW_writeW_word stateAt_eq stateAt_get writeState stateAt_writeState)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev bp : Addr := s₀.gpr .x1
abbrev nb : Nat := (s₀.gpr .x2).toNat
abbrev scr : Addr := s₀.gpr .x3
abbrev stR : Region := ⟨st s₀, 32⟩
abbrev blR : Region := ⟨bp s₀, 64 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 64⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sm3.compressAArch64.pre s₀) : Pre s₀ := by
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
  omega

theorem in_state {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega) (by omega)⟩

theorem out_state {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega) (by omega)⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by simp only [slot]; omega) (by simp only [slot]; omega)⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by simp only [slot]; omega) (by simp only [slot]; omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 := by
  have := h.nb_lt
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) from Offset.add_add _ _ _]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x3 : s.gpr .x3 = scr s₀
  kept : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  x1 : s.gpr .x1 = blkAddr s₀ i
  x2 : s.gpr .x2 = BitVec.ofNat 64 (nb s₀ - i)

theorem preserved_sub : ∀ r ∈ preserved, r ∈ pubRegs := by decide

/-! ## One block -/

theorem load_eq : load = [
    .ldr .w .x4 .x0 (4 * 0), .ldr .w .x5 .x0 (4 * 1), .ldr .w .x6 .x0 (4 * 2),
    .ldr .w .x7 .x0 (4 * 3), .ldr .w .x8 .x0 (4 * 4), .ldr .w .x9 .x0 (4 * 5),
    .ldr .w .x10 .x0 (4 * 6), .ldr .w .x11 .x0 (4 * 7)] := by
  decide

theorem update_eq : update ++ advance = [
    .ldr .w .x12 .x0 (4 * 0), .ldr .w .x13 .x0 (4 * 1), .ldr .w .x14 .x0 (4 * 2),
    .ldr .w .x15 .x0 (4 * 3),
    .logic .eor .w .x4 .x4 .x12, .logic .eor .w .x5 .x5 .x13, .logic .eor .w .x6 .x6 .x14,
    .logic .eor .w .x7 .x7 .x15,
    .ldr .w .x12 .x0 (4 * (0 + 4)), .ldr .w .x13 .x0 (4 * (1 + 4)), .ldr .w .x14 .x0 (4 * (2 + 4)),
    .ldr .w .x15 .x0 (4 * (3 + 4)),
    .logic .eor .w .x8 .x8 .x12, .logic .eor .w .x9 .x9 .x13, .logic .eor .w .x10 .x10 .x14,
    .logic .eor .w .x11 .x11 .x15,
    .str .w .x4 .x0 (4 * 0), .str .w .x5 .x0 (4 * 1), .str .w .x6 .x0 (4 * 2),
    .str .w .x7 .x0 (4 * 3), .str .w .x8 .x0 (4 * 4), .str .w .x9 .x0 (4 * 5),
    .str .w .x10 .x0 (4 * 6), .str .w .x11 .x0 (4 * 7),
    .addImm .x .x1 .x1 64, .subImm .x .x2 .x2 1] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .x4 = v[0].setWidth 64 ∧ s.gpr .x5 = v[1].setWidth 64 ∧
    s.gpr .x6 = v[2].setWidth 64 ∧ s.gpr .x7 = v[3].setWidth 64 ∧
    s.gpr .x8 = v[4].setWidth 64 ∧ s.gpr .x9 = v[5].setWidth 64 ∧
    s.gpr .x10 = v[6].setWidth 64 ∧ s.gpr .x11 = v[7].setWidth 64 := Iff.rfl

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hx0 : s.gpr .x0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 8 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide); have h5 := hin 5 (by decide)
  have h6 := hin 6 (by decide); have h7 := hin 7 (by decide)
  apply WP.of_runBlock
  rw [load_eq]
  simp (config := {decide := true}) only [vars0, runBlock_cons, runStep_some,
    runBlock_nil, exec_ldr_w, isa, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hx0,
    h0, h1, h2, h3, h4, h5, h6, h7, Option.some.injEq,
    exists_eq_left']
  simp only [stateAt_get _ _ (show 0 < 8 by decide), stateAt_get _ _ (show 1 < 8 by decide),
    stateAt_get _ _ (show 2 < 8 by decide), stateAt_get _ _ (show 3 < 8 by decide),
    stateAt_get _ _ (show 4 < 8 by decide), stateAt_get _ _ (show 5 < 8 by decide),
    stateAt_get _ _ (show 6 < 8 by decide), stateAt_get _ _ (show 7 < 8 by decide)]
  refine ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩, fun r hr => ?_, trivial⟩
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;>
    simp (disch := decide) only [RegUpd.gpr_write_of_ne]

theorem frame_writeState {s₀ : State} {m m' : Mem} (h : Frame [stR s₀] m m') (v : HashValue) :
    Frame [stR s₀] m (writeState m' (st s₀) v) := by
  have c : ∀ k, k < 8 → (stR s₀).Contains (st s₀ + BitVec.ofNat 64 (4 * k)) (32 / 8) :=
    fun k hk => contains_offset (by omega) (by omega)
  simp only [writeState]
  refine (((((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _ (c 6 ?_)).writeW ?_ _ (c 7 ?_) <;>
  simp

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hx0 : s.gpr .x0 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 8) → s.mem.readW (st s₀ + BitVec.ofNat 64 (4 * k)) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· ^^^ ·) V H) ∧
      s'.gpr .x1 = s.gpr .x1 + 64 ∧ s'.gpr .x2 = s.gpr .x2 - 1 ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.gpr .x3 = s.gpr .x3 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 8 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 8 → InRegions s.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin (0 + 4) (by decide); have i5 := hin (1 + 4) (by decide)
  have i6 := hin (2 + 4) (by decide); have i7 := hin (3 + 4) (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide); have o5 := hout 5 (by decide)
  have o6 := hout 6 (by decide); have o7 := hout 7 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH (0 + 4) (by decide); have m5 := hH (1 + 4) (by decide)
  have m6 := hH (2 + 4) (by decide); have m7 := hH (3 + 4) (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec_ldr_w, exec_str_w, exec_logic, exec_addImm_x, exec_subImm_x, State.read,
    RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, Size.bits, hx0,
    i0, i1, i2, i3, i4, i5, i6, i7, o0, o1, o2, o3, o4, o5, o6, o7,
    m0, m1, m2, m3, m4, m5, m6, m7, v0, v1, v2, v3, v4, v5, v6, v7,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · simp only [writeState, Vector.getElem_zipWith]
  and_intros
  all_goals first
    | trivial
    | rfl
    | (intro r hr
       simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
       simp (disch := decide) only [RegUpd.gpr_write_of_ne])

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i t : Nat) (ht : t < 16) :
    rev32 (s₀.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 32) = W (blk s₀ i) t := by
  rw [W_lt _ ht, rev32_readW]
  simp only [blk, blockAt, parseBlock]
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 1) from
      Offset.add_add _ _ 1,
    show blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 1) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 2) from
      Offset.add_add _ _ 1,
    show blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 2) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 3) from
      Offset.add_add _ _ 1]

theorem win_sub (p : Addr) : Region.Sub (winRegion p) ⟨p, 64⟩ := Region.sub_prefix (by omega)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .x .x2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.x0 hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      rev32 (m.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 32) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide), hm₁,
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i t ht
  have hx1₁ : s₁.gpr .x1 = blkAddr s₀ i := (hpub₁ .x1 (by decide)).trans hL.x1
  have hx3₁ : s₁.gpr .x3 = scr s₀ := (hpub₁ .x3 (by decide)).trans hL.x3
  refine WP.seq (WP.mono (rounds_ok (M := blk s₀ i) (scr := scr s₀) (sB := s₁) hx1₁ hx3₁
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 64 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hx0₂ : s₂.gpr .x0 = st s₀ := by rw [pub₂ .x0 (by decide), hL.x0]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hx0₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.frame.readW (contains_offset (by omega) (by omega)) hst (by decide), hm₁,
      stateAt_get _ _ hk]
  obtain ⟨hm₃, hx1₃, hx2₃, hx0₃, hx3₃, hkept₃, hrd₃, hwr₃⟩ := h₃
  have hx2 : s₂.gpr .x2 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [pub₂ .x2 (by decide), hL.x2]
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩) ?_
    rw [hm₃]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hx0₃, hx0₂], by rw [hx3₃, pub₂ .x3 (by decide), hL.x3],
      fun r hr => by rw [hkept₃ r hr, pub₂ r (preserved_sub r hr), hL.kept r hr],
      by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_⟩
    rw [hm₃, stateAt_writeState, compressBlocks_succ, ← hL.state]
    rfl
  have hev : eval (.nonzero .x .x2) s₃ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hx2₃, hx2]
  have := hp.nb_lt
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon _ rfl with x1 := ?_, x2 := ?_ }⟩
    · rw [hx1₃, pub₂ .x1 (by decide), hL.x1]
      exact (Offset.add_add _ _ 64).trans
        (congrArg (bp s₀ + ·) (congrArg (BitVec.ofNat 64) (by omega)))
    · rw [hx2₃, hx2]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sm3.compressAArch64.post s₀ s' := by
  have hc₀ : Common s₀ 0 s₀ :=
    ⟨rfl, rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl⟩
  refine WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s' hc => ⟨hc.kept, hc.state⟩
  refine WP.ite (s₀.gpr .x2 == 0) (by simp [eval, State.read]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .x .x2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₀ :=
      { hc₀ with
        x1 := by simp [blkAddr]
        x2 := by simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₀ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 64⟩]

theorem compress_verified :
    Verified AArch64.target Impl.Sm3.AArch64.compress Proof.Sm3.compressAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_⟩ <;>
    first
    | exact Offset.disjoint_of_le (by decide) (by decide)
    | exact Region.Disjoint.symm (Offset.disjoint_of_le (by decide) (by decide))

end VG.Proof.Sm3.AArch64
