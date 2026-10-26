module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Sha1.Spec
public import VerifiedGarbage.Impl.Sha1.RISCV64
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa
import Mathlib.Tactic.SplitIfs

/-!
# SHA-1 compression function on RISC-V: the message schedule and the rounds

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/Sha1/PPC64LE/Compress.lean`): each round is `f(b, c, d)`,
symbolically executed once per function (`fcode_ok`), between the addition
of `Wₜ` and the rest of the round (`sum_ok`), executed once for all rounds.
The words are the low 32 bits of the registers (`Vars`).
-/

@[expose] public section

namespace VG.Proof.Sha1.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.Sha1.RISCV64 VG.Impl.Words.RISCV64
open VG.Spec.Sha1 (HashValue Word Block K W f)
open VG.Proof.Sha1 (roundKW round_eq rounds_zero rounds_succ W_lt W_ge ch_eq maj_eq)

/-- The working variables `v` are in the low 32 bits of the registers of round `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  (s.gpr (var t 0)).setWidth 32 = v[0] ∧ (s.gpr (var t 1)).setWidth 32 = v[1] ∧
  (s.gpr (var t 2)).setWidth 32 = v[2] ∧ (s.gpr (var t 3)).setWidth 32 = v[3] ∧
  (s.gpr (var t 4)).setWidth 32 = v[4]

/-- The pointers, the count, the return address and the callee-saved
registers: never written by the rounds. -/
def pubRegs : List Reg := [.a0, .a1, .a2, .a3, .ra, .s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8,
  .s9, .s10, .s11]

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 4) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 4 := by
  simp only [var]; congr 1; omega

/-- The registers of the working variables are all different. -/
theorem round_nodup (t : Nat) : [var t 0, var t 1, var t 2, var t 3, var t 4].Nodup := by
  have h : ∀ c < 5, [work.getD ((0 + 5 - c) % 5) .t0, work.getD ((1 + 5 - c) % 5) .t0,
      work.getD ((2 + 5 - c) % 5) .t0, work.getD ((3 + 5 - c) % 5) .t0,
      work.getD ((4 + 5 - c) % 5) .t0].Nodup := by decide
  exact h (t % 5) (Nat.mod_lt _ (by omega))

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 5 - t % 5) % 5]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne' : ∀ r ∈ work, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ∉ pubRegs := by decide

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ∉ pubRegs := work_ne' r h

theorem pubRegs_ne' : ∀ r ∈ pubRegs, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 := by decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 := pubRegs_ne' r h

/-! ## One round -/

/-- `fₜ` as the code computes it. -/
def fval : Fn → Word → Word → Word → Word
  | .ch, x, y, z => (y ^^^ z) &&& x ^^^ z
  | .parity, x, y, z => x ^^^ y ^^^ z
  | .maj, x, y, z => (x ||| y) &&& z ||| x &&& y

theorem f_eq (t : Nat) (x y z : Word) : f t x y z = fval (fn t) x y z := by
  unfold Spec.Sha1.f fn
  split_ifs <;> simp only [fval, ch_eq, maj_eq, Spec.Sha1.parity]

theorem fcode_ok (g : Fn) (b c d : Reg) (s : State) (x y z : Word)
    (hbw : b ∈ work) (hcw : c ∈ work) (hdw : d ∈ work)
    (hb : (s.gpr b).setWidth 32 = x) (hc : (s.gpr c).setWidth 32 = y) (hd : (s.gpr d).setWidth 32 = z) :
    WP isa (.block (fcode g b c d)) s fun s' =>
      (s'.gpr T1).setWidth 32 = fval g x y z ∧ (∀ r, r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨-, b1, b2, -⟩ := work_ne hbw
  obtain ⟨-, c1, c2, -⟩ := work_ne hcw
  obtain ⟨-, d1, d2, -⟩ := work_ne hdw
  simp only [T1, T2] at b1 c1 d1 b2 c2 d2 ⊢
  apply WP.of_runBlock
  cases g <;>
  simp only [fcode, T1, T2, runBlock_cons, runStep_some, runBlock_nil, exec_logic, RegUpd.gpr_write,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, b1, c1, d1, ↓reduceIte,
    reduceCtorEq, Option.some.injEq, exists_eq_left'] <;>
  refine ⟨?_, fun r h1 h2 => by simp [h1, h2], trivial, trivial, trivial⟩ <;>
  simp only [lo32_xor, lo32_and, lo32_or, hb, hc, hd, fval]

/-- The instructions of a round after `f(b, c, d)`. -/
def sumI (t : Nat) (a b e : Reg) : List Instr :=
  ([.add e e T1] : List Instr) ++ li32 T1 (K t) ++ ([.add e e T1] : List Instr) ++ rotl T1 T2 a 5 ++
    ([.add e e T1] : List Instr) ++ rotl b T1 b 30

theorem round_split (t : Nat) :
    round t = ([.add (var t 4) (var t 4) T0] : List Instr) ++
      (fcode (fn t) (var t 1) (var t 2) (var t 3) ++ sumI t (var t 0) (var t 1) (var t 4)) := by
  simp only [Impl.Sha1.RISCV64.round, sumI, List.append_assoc]

/-- A rotation left, as `rotl` computes it in the low word. -/
theorem rotl_lo (y : Word) {n : Nat} (hn : n < 32) :
    (sext32 (y >>> (32 - n)) ||| sext32 (y <<< n)).setWidth 32 = y.rotateLeft n := by
  rw [lo32_or, lo32_sext, lo32_sext, BitVec.or_comm, rotl_shifts _ hn]

theorem sum_ok (t : Nat) (a b e : Reg) (s : State) (x y z fv : Word)
    (haw : a ∈ work) (hbw : b ∈ work) (hew : e ∈ work) (hbe : b ≠ e) (hae : a ≠ e)
    (ha : (s.gpr a).setWidth 32 = x) (hb : (s.gpr b).setWidth 32 = y) (he : (s.gpr e).setWidth 32 = z)
    (hf : (s.gpr T1).setWidth 32 = fv) :
    WP isa (.block (sumI t a b e)) s fun s' =>
      (s'.gpr e).setWidth 32 = z + fv + K t + x.rotateLeft 5 ∧
      (s'.gpr b).setWidth 32 = y.rotateLeft 30 ∧
      (∀ r, r ≠ e → r ≠ b → r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨-, a1, a2, -⟩ := work_ne haw
  obtain ⟨-, e1, e2, -⟩ := work_ne hew
  obtain ⟨-, b1, b2, -⟩ := work_ne hbw
  have heb := hbe.symm
  simp only [T1, T2] at a1 e1 b1 a2 e2 b2 hf ⊢
  apply WP.of_runBlock
  simp only [sumI, rotl, li32, T1, T2, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec_add, exec_logic, exec_lui, exec_addiw_lo12,
    exec_shift_w (show 5 < 32 by decide), exec_shift_w (show 32 - 5 < 32 by decide),
    exec_shift_w (show 30 < 32 by decide), exec_shift_w (show 32 - 30 < 32 by decide),
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    a1, e1, b1, a2, e2, b2, Ne.symm b1, hbe, heb, hae, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4], trivial, trivial, trivial⟩
  · simp only [lo32_add, lo32_sext, li32_val, rotl_lo _ (show 5 < 32 by decide), ha, he, hf]
  · rw [rotl_lo _ (by decide), hb]

/-- The round is symbolically executed once per function `f`, for any
registers `a … e`. -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars t s v) (hw : (s.gpr T0).setWidth 32 = w) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (f t v[1] v[2] v[3]) (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hv
  have hd := round_nodup t
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hd
  obtain ⟨⟨h01, -, -, h04⟩, ⟨h12, h13, h14⟩, ⟨-, h24⟩, h34⟩ := hd
  have m0 := var_mem t 0; have m1 := var_mem t 1; have m2 := var_mem t 2
  have m3 := var_mem t 3; have m4 := var_mem t 4
  rw [round_split, WP.block_append_iff]
  -- `e += Wₜ`
  refine WP.block_cons_iff.mpr ⟨_, exec_add, WP.block_nil ?_⟩
  generalize hs₀ : s.write (var t 4) (s.gpr (var t 4) + s.gpr T0) = s₀
  have he₀ : (s₀.gpr (var t 4)).setWidth 32 = v[4] + w := by
    rw [← hs₀, RegUpd.gpr_write_self, lo32_add, h4, hw]
  have k₀ : ∀ r, r ≠ var t 4 → s₀.gpr r = s.gpr r := fun r hr => by
    rw [← hs₀, RegUpd.gpr_write_of_ne _ _ hr]
  rw [WP.block_append_iff]
  refine WP.mono (fcode_ok (fn t) _ _ _ s₀ v[1] v[2] v[3] m1 m2 m3 (by rw [k₀ _ h14]; exact h1)
    (by rw [k₀ _ h24]; exact h2) (by rw [k₀ _ h34]; exact h3))
    fun s₁ ⟨hT1, hk₁, hm₁, hrd₁, hwr₁⟩ => ?_
  have k₁ : ∀ r ∈ work, s₁.gpr r = s₀.gpr r := fun r hr =>
    hk₁ r (work_ne hr).2.1 (work_ne hr).2.2.1
  refine WP.mono (sum_ok t (var t 0) (var t 1) (var t 4) s₁ v[0] v[1] (v[4] + w) _ m0 m1 m4 h14 h04
    (by rw [k₁ _ m0, k₀ _ h04]; exact h0) (by rw [k₁ _ m1, k₀ _ h14]; exact h1)
    (by rw [k₁ _ m4]; exact he₀) hT1)
    fun s₂ ⟨he, hb, hk₂, hm₂, hrd₂, hwr₂⟩ => ?_
  have hm₀ : s₀.mem = s.mem := by rw [← hs₀]; rfl
  have hrd₀ : s₀.rd = s.rd := by rw [← hs₀]; rfl
  have hwr₀ : s₀.wr = s.wr := by rw [← hs₀]; rfl
  refine ⟨?_, by rw [hm₂, hm₁, hm₀], by rw [hrd₂, hrd₁, hrd₀], by rw [hwr₂, hwr₁, hwr₀], fun r hr => ?_⟩
  · simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 4 by omega),
      var_succ t _ (show 1 < 4 by omega), var_succ t _ (show 2 < 4 by omega),
      var_succ t _ (show 3 < 4 by omega)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [he, ← f_eq]; simp only [roundKW, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero]
      ac_rfl
    · rw [hk₂ _ h04 h01 (work_ne m0).2.1 (work_ne m0).2.2.1, k₁ _ m0, k₀ _ h04, h0]; rfl
    · rw [hb]; rfl
    · rw [hk₂ _ h24 (Ne.symm h12) (work_ne m2).2.1 (work_ne m2).2.2.1, k₁ _ m2, k₀ _ h24, h2]; rfl
    · rw [hk₂ _ h34 (Ne.symm h13) (work_ne m3).2.1 (work_ne m3).2.2.1, k₁ _ m3, k₀ _ h34, h3]; rfl
  · have hp := pubRegs_ne hr
    have hne : ∀ k, var t k ≠ r := fun k h => (work_ne (var_mem t k)).2.2.2 (h ▸ hr)
    rw [hk₂ r (Ne.symm (hne 4)) (Ne.symm (hne 1)) hp.2.1 hp.2.2, hk₁ r hp.2.1 hp.2.2,
      k₀ r (Ne.symm (hne 4))]

/-! ## The message schedule -/

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

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : Addr)
    (hr1 : s.gpr .a1 = bp) (hr3 : s.gpr .a3 = scr) (hal : scr.toNat % 8 = 0)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 4)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4 * t)) 4)
    (hblk : t < 16 → beWord s.mem bp (4 * t) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      (s'.gpr T0).setWidth 32 = W M t ∧
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ≠ T0 → r ≠ T1 → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hin hout hwin ⊢
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    simp only [Impl.Sha1.RISCV64.schedule, ht, ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (loadBE32_ok (by decide) (by decide) (by decide) (by omega) (by rw [hr1]; exact hi))
      fun s₁ e => ?_
    have g3 : s₁.gpr .a3 = scr := by rw [e, ← hr3]; rfl
    have gw : s₁.wr = s.wr := by rw [e]; rfl
    have gr : s₁.rd = s.rd := by rw [e]; rfl
    have gm : s₁.mem = s.mem := by rw [e]; rfl
    have g0 : (s₁.gpr T0).setWidth 32 = W M t := by
      rw [e, RegUpd.gpr_write_self, lo32_ext, hr1, hb]
    have gk : ∀ r, r ≠ T0 → r ≠ T1 → s₁.gpr r = s.gpr r := fun r h0 h1 => by
      rw [e, RegUpd.gpr_write_of_ne _ _ h0, RegUpd.gpr_write_of_ne _ _ h1]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil,
      exec_store_w (s := s₁) (slot_lt t) (by rw [g3]; exact slot_al hal t)
        (by rw [gw, g3]; exact hout t), Option.some.injEq, exists_eq_left', g3]
    exact ⟨g0, by rw [gm, g0], gr, gw, gk⟩
  · have hw := hwin (by omega)
    have e3 := hw (t - 3) (by omega) (by omega)
    have e8 := hw (t - 8) (by omega) (by omega)
    have e14 := hw (t - 14) (by omega) (by omega)
    have e16 := hw (t - 16) (by omega) (by omega)
    rw [show slot (t - 3) = slot (t + 13) by simp only [slot]; omega] at e3
    rw [show slot (t - 8) = slot (t + 8) by simp only [slot]; omega] at e8
    rw [show slot (t - 14) = slot (t + 2) by simp only [slot]; omega] at e14
    rw [show slot (t - 16) = slot t by simp only [slot]; omega] at e16
    simp only [Impl.Sha1.RISCV64.schedule, ht, ite_false, rotl, T0, T1, List.cons_append,
      List.nil_append]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_logic,
      exec_shift_w (show 1 < 32 by decide), exec_shift_w (show 32 - 1 < 32 by decide),
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, reduceCtorEq,
      ↓reduceIte, hr3, exec_lw_slot, exec_sw_slot, hal, hin, hout, Option.some.injEq,
      exists_eq_left']
    have hW := W_ge M (t := t) (by omega)
    simp only [lo32_xor, lo32_ext, e3, e8, e14, e16, rotl_lo _ (show 1 < 32 by decide), ← hW]
    exact ⟨trivial, trivial, trivial, trivial, fun r h0 h1 => by simp only [h0, h1, ↓reduceIte]⟩

/-! ## The 80 rounds -/

/-- The window `⟨scr, 64⟩`. -/
abbrev winRegion (scr : Addr) : Region := ⟨scr, 64⟩

theorem win_contains (scr : Addr) (j : Nat) : (winRegion scr).Contains (slotAddr scr j) 4 := by
  simp only [slotAddr, slot]
  exact Offset.contains_base scr (by omega) (by omega)

theorem slot_sep (scr : Addr) {i j : Nat} (h : i % 16 ≠ j % 16) :
    Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  simp only [slotAddr, slot]
  exact Offset.sep scr (by omega) (by omega) (by omega)

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : Addr) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (VG.Spec.Sha1.rounds H M t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [winRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : Addr) (sB : State)
    (hr1 : sB.gpr .a1 = bp) (hr3 : sB.gpr .a3 = scr) (hal : scr.toNat % 8 = 0)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (4 * t)) 4)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → beWord m bp (4 * t) = W M t)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 80, WP isa (rounds t) sB (RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, Frame.refl _ _,
      fun j hj => absurd hj (by omega)⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_r1 : s.gpr .a1 = bp := (hs.pub .a1 (by decide)).trans hr1
    have hs_r3 : s.gpr .a3 = scr := (hs.pub .a3 (by decide)).trans hr3
    refine WP.mono (schedule_ok t s M bp scr hs_r1 hs_r3 hal
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.wr]; exact hout)
      (fun h => by rw [hs.rd, hs.wr]; exact hbin t h) (hblk _ hs.frame t)
      (fun _ => hs.win)) fun s₁ ⟨hT0, hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
    have hv₁ : Vars t s₁ (VG.Spec.Sha1.rounds H M t) := by
      have hv := hs.vars
      have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k =>
        have := work_ne (var_mem t k); hr₁ _ this.1 this.2.1
      simp only [Vars, e] at hv ⊢
      exact hv
    refine WP.mono (round_ok t s₁ _ _ hv₁ hT0) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr], ?_, ?_⟩
    · rw [rounds_succ, round_eq]; exact hv₂
    · have := pubRegs_ne hr
      rw [hr₂ r hr, hr₁ r this.1 this.2.1, hs.pub r hr]
    · rw [hm₂, hm₁]
      exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains scr t)
    · intro j hj hj'
      rw [hm₂, hm₁]
      by_cases hjt : j = t
      · subst hjt; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (slot_sep scr (by omega)) (by decide)]
        exact hs.win j (by omega) (by omega)

end VG.Proof.Sha1.RISCV64
