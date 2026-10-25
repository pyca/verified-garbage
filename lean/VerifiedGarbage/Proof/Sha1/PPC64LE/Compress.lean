module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Sha1.Spec
public import VerifiedGarbage.Impl.Sha1.PPC64LE
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Sha1.StateMem
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Range
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Sha1.Spec
meta import VerifiedGarbage.Impl.Sha1.PPC64LE
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Sha1.StateMem
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.IntervalCases
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# SHA-1 compression function on PPC64LE

The same structure as the AArch64 proof (`VG.Proof.Sha1.AArch64`), with the
words the low 32 bits of the registers (`Vars`).
-/

@[expose] public section

namespace VG.Proof.Sha1.PPC64LE

open VG VG.PPC64LE VG.Impl.Sha1.PPC64LE
open VG.Spec.Sha1 (HashValue Word Block K W f)

/-- The working variables `v` are in the low 32 bits of the registers of round `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  (s.gpr (var t 0)).setWidth 32 = v[0] ∧ (s.gpr (var t 1)).setWidth 32 = v[1] ∧
  (s.gpr (var t 2)).setWidth 32 = v[2] ∧ (s.gpr (var t 3)).setWidth 32 = v[3] ∧
  (s.gpr (var t 4)).setWidth 32 = v[4]

/-- The pointers, the count and the registers the ABI requires us to
preserve: never written by the rounds. -/
def pubRegs : List Reg := [.r3, .r4, .r5, .r6, .r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
  .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 4) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 4 := by
  simp only [var]; congr 1; omega

/-- The registers of the working variables are all different. -/
theorem round_nodup (t : Nat) : [var t 0, var t 1, var t 2, var t 3, var t 4].Nodup := by
  have h : ∀ c < 5, [work.getD ((0 + 5 - c) % 5) .r7, work.getD ((1 + 5 - c) % 5) .r7,
      work.getD ((2 + 5 - c) % 5) .r7, work.getD ((3 + 5 - c) % 5) .r7,
      work.getD ((4 + 5 - c) % 5) .r7].Nodup := by decide
  exact h (t % 5) (Nat.mod_lt _ (by omega))

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 5 - t % 5) % 5]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne' : ∀ r ∈ work, r ≠ T0 ∧ r ≠ T1 ∧ r ∉ pubRegs := by decide

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ T0 ∧ r ≠ T1 ∧ r ∉ pubRegs := work_ne' r h

theorem pubRegs_ne' : ∀ r ∈ pubRegs, r ≠ T0 ∧ r ≠ T1 := by decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ T0 ∧ r ≠ T1 := pubRegs_ne' r h

/-- The registers the rounds never write: `pubRegs` but `r14`–`r17`. -/
def fixRegs : List Reg := [.r3, .r4, .r5, .r6, .r2, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25,
  .r26, .r27, .r28, .r29, .r30, .r31]

theorem fix_pub : ∀ r ∈ fixRegs, r ∈ pubRegs := by decide

theorem Kr_ne : Kr ∈ pubRegs ∧ Kr ∉ fixRegs ∧ Kr ≠ T0 ∧ Kr ≠ T1 := by decide

theorem wreg_ne' : ∀ c < 3, saved (1 + c) ∈ pubRegs ∧ saved (1 + c) ∉ fixRegs ∧
    saved (1 + c) ≠ T0 ∧ saved (1 + c) ≠ T1 ∧ saved (1 + c) ≠ Kr := by decide

theorem wreg_ne (t : Nat) : wreg t ∈ pubRegs ∧ wreg t ∉ fixRegs ∧
    wreg t ≠ T0 ∧ wreg t ≠ T1 ∧ wreg t ≠ Kr := wreg_ne' (t % 3) (Nat.mod_lt _ (by omega))

theorem wreg_inj {t j : Nat} (h : t % 3 ≠ j % 3) : wreg t ≠ wreg j := by
  have key : ∀ a < 3, ∀ b < 3, saved (1 + a) = saved (1 + b) → a = b := by decide
  exact fun e => h (key _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega)) e)

theorem fix_ne {r : Reg} (h : r ∈ fixRegs) (t : Nat) : r ≠ wreg t ∧ r ≠ Kr :=
  ⟨fun e => (wreg_ne t).2.1 (e ▸ h), fun e => Kr_ne.2.1 (e ▸ h)⟩

/-- `Kₜ` changes only every 20 rounds. -/
theorem K_succ : ∀ t < 79, (t + 1) % 20 ≠ 0 → K (t + 1) = K t := by decide

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
      (s'.gpr T1).setWidth 32 = fval g x y z ∧ (∀ r, r ≠ T1 → r ≠ T0 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨-, b1, -⟩ := work_ne hbw
  obtain ⟨-, c1, -⟩ := work_ne hcw
  obtain ⟨-, d1, -⟩ := work_ne hdw
  simp only [T0, T1] at b1 c1 d1 ⊢
  apply WP.of_runBlock
  cases g <;>
  simp only [fcode, T0, T1, runBlock_cons, runStep_some, runBlock_nil, exec_logic, isa, State.write,
    b1, c1, d1, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left'] <;>
  refine ⟨?_, fun r h1 h2 => by simp [h1, h2], by trivial⟩ <;>
  simp only [BitVec.setWidth_xor, BitVec.setWidth_and, BitVec.setWidth_or, hb, hc, hd, fval]

/-- The instructions of a round after `f(b, c, d)`. -/
def sumI (a b e : Reg) : List Instr := [
  .add e e T1,
  .add e e Kr,
  .rotr .w T1 a 27,
  .add e e T1,
  .rotr .w b b 2]

theorem round_split (t : Nat) :
    round t = ([.add (var t 4) (var t 4) (wreg t)] : List Instr) ++
      (fcode (fn t) (var t 1) (var t 2) (var t 3) ++ sumI (var t 0) (var t 1) (var t 4)) := by
  simp only [Impl.Sha1.PPC64LE.round, sumI, List.append_assoc]

theorem sum_ok (t : Nat) (a b e : Reg) (s : State) (x y z fv : Word)
    (haw : a ∈ work) (hbw : b ∈ work) (hew : e ∈ work) (hbe : b ≠ e) (hae : a ≠ e)
    (ha : (s.gpr a).setWidth 32 = x) (hb : (s.gpr b).setWidth 32 = y) (he : (s.gpr e).setWidth 32 = z)
    (hf : (s.gpr T1).setWidth 32 = fv) (hk : (s.gpr Kr).setWidth 32 = K t) :
    WP isa (.block (sumI a b e)) s fun s' =>
      (s'.gpr e).setWidth 32 = z + fv + K t + x.rotateRight 27 ∧
      (s'.gpr b).setWidth 32 = y.rotateRight 2 ∧
      (∀ r, r ≠ e → r ≠ b → r ≠ T1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨-, a1, -⟩ := work_ne haw
  obtain ⟨-, e1, -⟩ := work_ne hew
  obtain ⟨-, b1, -⟩ := work_ne hbw
  have heb := hbe.symm
  have hKe : Kr ≠ e := fun h => (work_ne hew).2.2 (h ▸ Kr_ne.1)
  simp only [T1] at a1 e1 b1 hf ⊢
  apply WP.of_runBlock
  simp only [sumI, T1, runBlock_cons, runStep_some, runBlock_nil, exec_add,
    exec_rotr_w (show 27 < 32 by decide), exec_rotr_w (show 2 < 32 by decide), isa, State.write,
    e1, b1, hbe, heb, hae, hKe, ↓reduceIte, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun r h1 h2 h3 => by simp [h1, h2, h3], by trivial⟩
  · simp only [lo32_add, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      Nat.reduceLeDiff, ha, he, hf, hk]
  · simp only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff, hb]

theorem rotl5 (x : Word) : x.rotateLeft 5 = x.rotateRight 27 := rotateLeft_eq x (by omega)
theorem rotl30 (x : Word) : x.rotateLeft 30 = x.rotateRight 2 := rotateLeft_eq x (by omega)
theorem rotl1 (x : Word) : x.rotateLeft 1 = x.rotateRight 31 := rotateLeft_eq x (by omega)

/-- The round is symbolically executed once per function `f`, for any
registers `a … e`. -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars t s v) (hw : (s.gpr (wreg t)).setWidth 32 = w) (hk : (s.gpr Kr).setWidth 32 = K t) :
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
  generalize hs₀ : s.write (var t 4) (s.gpr (var t 4) + s.gpr (wreg t)) = s₀
  have he₀ : (s₀.gpr (var t 4)).setWidth 32 = v[4] + w := by
    rw [← hs₀]; simp [State.write, lo32_add, h4, hw]
  have k₀ : ∀ r, r ≠ var t 4 → s₀.gpr r = s.gpr r := fun r hr => by rw [← hs₀]; simp [State.write, hr]
  rw [WP.block_append_iff]
  refine WP.mono (fcode_ok (fn t) _ _ _ s₀ v[1] v[2] v[3] m1 m2 m3 (by rw [k₀ _ h14]; exact h1)
    (by rw [k₀ _ h24]; exact h2) (by rw [k₀ _ h34]; exact h3))
    fun s₁ ⟨hT1, hk₁, hm₁, hrd₁, hwr₁⟩ => ?_
  have k₁ : ∀ r ∈ work, s₁.gpr r = s₀.gpr r := fun r hr =>
    hk₁ r (work_ne hr).2.1 (work_ne hr).1
  refine WP.mono (sum_ok t (var t 0) (var t 1) (var t 4) s₁ v[0] v[1] (v[4] + w) _ m0 m1 m4 h14 h04
    (by rw [k₁ _ m0, k₀ _ h04]; exact h0) (by rw [k₁ _ m1, k₀ _ h14]; exact h1)
    (by rw [k₁ _ m4]; exact he₀) hT1
    (by rw [hk₁ _ Kr_ne.2.2.2 Kr_ne.2.2.1, k₀ _ fun h => (work_ne m4).2.2 (h ▸ Kr_ne.1)]; exact hk))
    fun s₂ ⟨he, hb, hk₂, hm₂, hrd₂, hwr₂⟩ => ?_
  have hm₀ : s₀.mem = s.mem := by rw [← hs₀]; rfl
  have hrd₀ : s₀.rd = s.rd := by rw [← hs₀]; rfl
  have hwr₀ : s₀.wr = s.wr := by rw [← hs₀]; rfl
  refine ⟨?_, by rw [hm₂, hm₁, hm₀], by rw [hrd₂, hrd₁, hrd₀], by rw [hwr₂, hwr₁, hwr₀], fun r hr => ?_⟩
  · simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 4 by omega),
      var_succ t _ (show 1 < 4 by omega), var_succ t _ (show 2 < 4 by omega),
      var_succ t _ (show 3 < 4 by omega)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [he, ← f_eq]; simp only [roundKW, rotl5, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero]
      ac_rfl
    · rw [hk₂ _ h04 h01 (work_ne m0).2.1, k₁ _ m0, k₀ _ h04, h0]; rfl
    · rw [hb]; simp only [roundKW, rotl30]; rfl
    · rw [hk₂ _ h24 (Ne.symm h12) (work_ne m2).2.1, k₁ _ m2, k₀ _ h24, h2]; rfl
    · rw [hk₂ _ h34 (Ne.symm h13) (work_ne m3).2.1, k₁ _ m3, k₀ _ h34, h3]; rfl
  · have hp := pubRegs_ne hr
    have hne : ∀ k, var t k ≠ r := fun k h => (work_ne (var_mem t k)).2.2 (h ▸ hr)
    rw [hk₂ r (Ne.symm (hne 4)) (Ne.symm (hne 1)) hp.2, hk₁ r hp.2 hp.1, k₀ r (Ne.symm (hne 4))]

/-! ## The message schedule -/

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
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j)
    (hw3 : 16 ≤ t → (s.gpr (wreg t)).setWidth 32 = W M (t - 3)) :
    WP isa (.block (schedule t)) s fun s' =>
      (s'.gpr (wreg t)).setWidth 32 = W M t ∧
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ≠ wreg t → r ≠ T0 → r ≠ T1 → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hin hout hwin ⊢
  have h6 : (Reg.r6 = wreg t) = False := eq_false fun h => (wreg_ne t).2.1 (h ▸ by decide)
  have h0' : (wreg t = T0) = False := eq_false (wreg_ne t).2.2.1
  simp only [T0] at h0'
  apply WP.of_runBlock
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    simp only [Impl.Sha1.PPC64LE.schedule, ht, ite_true, T0, T1]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_li (show 4 * t < 2 ^ 15 by omega),
      exec_loadRev_w, exec_store_w, slot_ok, isa, State.write, hr4, hr6, h6, hi, hout,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, hb, Option.some.injEq,
      exists_eq_left', Nat.reduceLeDiff, reduceCtorEq, ↓reduceIte, ne_eq,
      not_false_eq_true, true_and]
    intro r e0 _ e2
    simp [e0, e2]
  · have hw := hwin (by omega)
    have e3 := hw3 (by omega)
    have e8 := hw (t - 8) (by omega) (by omega)
    have e14 := hw (t - 14) (by omega) (by omega)
    have e16 := hw (t - 16) (by omega) (by omega)
    rw [show slot (t - 8) = slot (t + 8) by simp only [slot]; omega] at e8
    rw [show slot (t - 14) = slot (t + 2) by simp only [slot]; omega] at e14
    rw [show slot (t - 16) = slot t by simp only [slot]; omega] at e16
    simp only [Impl.Sha1.PPC64LE.schedule, ht, ite_false, T0, T1]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_load_w, exec_store_w, exec_logic,
      exec_rotr_w (show 31 < 32 by decide), slot_ok, isa, State.write, hr6, h0', h6, hin, hout,
      Option.some.injEq, exists_eq_left', reduceCtorEq, ↓reduceIte, ne_eq,
      not_false_eq_true, true_and]
    have hW := W_ge M (t := t) (by omega)
    rw [rotl1] at hW
    refine ⟨?_, ?_, fun r e0 e1 _ => by simp [e0, e1]⟩
    · simp only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_xor,
        Nat.reduceLeDiff, e3, e8, e14, e16, hW]
    · simp only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_xor,
        Nat.reduceLeDiff, e3, e8, e14, e16, hW]

/-- Setting `Kr` where `Kₜ` changes. -/
theorem kset_ok (t : Nat) (s : State) (hk : t % 20 ≠ 0 → (s.gpr Kr).setWidth 32 = K t) :
    WP isa (.block (kset t)) s fun s' =>
      (s'.gpr Kr).setWidth 32 = K t ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ≠ Kr → s'.gpr r = s.gpr r := by
  by_cases h : t % 20 = 0
  · apply WP.of_runBlock
    simp only [kset, h, runBlock_cons, runStep_some, runBlock_nil, exec_lis, exec_ori, isa,
      State.write, ↓reduceIte, Option.some.injEq, exists_eq_left']
    refine ⟨?_, trivial, trivial, trivial, fun r hr => by simp [hr]⟩
    simp only [BitVec.setWidth_or, BitVec.setWidth_setWidth_of_le, Nat.reduceLeDiff, lis_ori']
  · simp only [kset, h, ite_false]
    exact WP.block_nil (M := isa) ⟨hk h, rfl, rfl, rfl, fun _ _ => rfl⟩

/-! ## The 80 rounds -/

/-- The window `⟨scr, 64⟩`. -/
abbrev winRegion (scr : Addr) : Region := ⟨scr, 64⟩

theorem win_contains (scr : Addr) (j : Nat) : (winRegion scr).Contains (slotAddr scr j) 4 := by
  simp only [slotAddr, slot]
  exact Offset.contains_base _ (by omega) (by omega)

theorem slot_sep (scr : Addr) {i j : Nat} (h : i % 16 ≠ j % 16) :
    Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  simp only [slotAddr, slot]
  exact Offset.sep _ (by omega) (by omega) (by omega)

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : Addr) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (VG.Spec.Sha1.rounds H M t)
  pub : ∀ r ∈ fixRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [winRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j
  kreg : t % 20 ≠ 0 → (s.gpr Kr).setWidth 32 = K t
  wregs : ∀ j < t, t ≤ j + 3 → (s.gpr (wreg j)).setWidth 32 = W M j

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : Addr) (sB : State)
    (hr4 : sB.gpr .r4 = bp) (hr6 : sB.gpr .r6 = scr)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (4 * t)) 4)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → rev32 (m.readW (bp + BitVec.ofNat 64 (4 * t)) 32) = W M t)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 80, WP isa (rounds t) sB (RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, Frame.refl _ _,
      fun j hj => absurd hj (by omega), fun h => absurd rfl h, fun j hj => absurd hj (by omega)⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (kset_ok t s hs.kreg) fun s₀ ⟨hk₀, hm₀, hrd₀, hwr₀, hr₀⟩ => ?_
    have hs_r4 : s₀.gpr .r4 = bp := by rw [hr₀ _ (by decide)]; exact (hs.pub .r4 (by decide)).trans hr4
    have hs_r6 : s₀.gpr .r6 = scr := by rw [hr₀ _ (by decide)]; exact (hs.pub .r6 (by decide)).trans hr6
    refine WP.mono (schedule_ok t s₀ M bp scr hs_r4 hs_r6
      (by rw [hrd₀, hwr₀, hs.rd, hs.wr]; exact hin) (by rw [hwr₀, hs.wr]; exact hout)
      (fun h => by rw [hrd₀, hwr₀, hs.rd, hs.wr]; exact hbin t h)
      (by rw [hm₀]; exact hblk _ hs.frame t) (by rw [hm₀]; exact fun _ => hs.win)
      (fun h => by
        rw [hr₀ _ (wreg_ne t).2.2.2.2, show wreg t = wreg (t - 3) by
          simp only [wreg]; congr 2; omega]
        exact hs.wregs (t - 3) (by omega) (by omega)))
      fun s₁ ⟨hW₁, hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
    have hv₁ : Vars t s₁ (VG.Spec.Sha1.rounds H M t) := by
      have hv := hs.vars
      have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k => by
        have := work_ne (var_mem t k)
        have hw : var t k ≠ wreg t := fun h => this.2.2 (h ▸ (wreg_ne t).1)
        have hK : var t k ≠ Kr := fun h => this.2.2 (h ▸ Kr_ne.1)
        rw [hr₁ _ hw this.1 this.2.1, hr₀ _ hK]
      simp only [Vars, e] at hv ⊢
      exact hv
    have hk₁ : (s₁.gpr Kr).setWidth 32 = K t := by
      rw [hr₁ _ (wreg_ne t).2.2.2.2.symm Kr_ne.2.2.1 Kr_ne.2.2.2]; exact hk₀
    refine WP.mono (round_ok t s₁ _ _ hv₁ hW₁ hk₁) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hrd₀, hs.rd], by rw [hwr₂, hwr₁, hwr₀, hs.wr], ?_, ?_,
      fun h => ?_, fun j hj hj' => ?_⟩
    · rw [rounds_succ, round_eq]; exact hv₂
    · have := pubRegs_ne (fix_pub r hr)
      have hf := fix_ne hr t
      rw [hr₂ r (fix_pub r hr), hr₁ r hf.1 this.1 this.2, hr₀ r hf.2, hs.pub r hr]
    · rw [hm₂, hm₁, hm₀]
      exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains scr t)
    · intro j hj hj'
      rw [hm₂, hm₁, hm₀]
      by_cases hjt : j = t
      · subst hjt; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (slot_sep scr (by omega)) (by decide)]
        exact hs.win j (by omega) (by omega)
    · rw [hr₂ _ Kr_ne.1, K_succ t (by omega) h]; exact hk₁
    · rw [hr₂ _ (wreg_ne j).1]
      by_cases hjt : j = t
      · subst hjt; exact hW₁
      · have hne : wreg j ≠ wreg t := wreg_inj (by omega)
        rw [hr₁ _ hne (wreg_ne j).2.2.1 (wreg_ne j).2.2.2.1, hr₀ _ (wreg_ne j).2.2.2.2]
        exact hs.wregs j (by omega) (by omega)

end VG.Proof.Sha1.PPC64LE

/-!
## SHA-1: the PPC64LE contracts

The contracts the proofs are written against; the artifacts are emitted with
the shared contracts of `Spec/`, which imply these (`Contract.Implies`). The
return address is in the link register, which the target's calling
convention requires to be preserved (`VG.PPC64LE.abiPreserved`); `update`
and `finalize` save it in a 48-byte frame below the stack pointer.
-/

namespace VG.Proof.Sha1

open Spec.Sha1

open VG.PPC64LE in
/-- PPC64LE contract for
`vg_sha1_compress(state: *mut [u32; 5], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 14])`:
updates the hash value at `state` with the `n` 64-byte blocks at `blocks`.

The code may read `blocks` (`64 * n` bytes) and read and write `state`
(20 bytes) and `scratch` (112 bytes, whose contents on exit are unspecified).
These may not overlap each other. The pointers and `n` are public; the hash
value and the blocks are secret. -/
def compressPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 20⟩
    let blocks : Region := ⟨s.gpr .r4, 64 * (s.gpr .r5).toNat⟩
    let scratch : Region := ⟨s.gpr .r6, 112⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    stateAt s'.mem (s.gpr .r3) =
      compressBlocks (stateAt s.mem (s.gpr .r3)) s.mem (s.gpr .r4) (s.gpr .r5).toNat
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

open VG.PPC64LE in
/-- PPC64LE contract for `vg_sha1_init(state: *mut [u8; 84])`: makes the
streaming state at `state` represent the empty message.

The code may write `state` (84 bytes). The pointer is public. -/
def initPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 84⟩
    s.rd = [] ∧ s.wr = [state]
  post s s' := Repr s'.mem (s.gpr .r3) []
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp

open VG.PPC64LE in
/-- PPC64LE contract for
`vg_sha1_update(state: *mut [u8; 84], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 20])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), then afterwards it represents `m` followed by the `len` bytes at
`data`.

The code may read `data` (`len` bytes) and read and write `state` (84
bytes) and `scratch` (160 bytes, whose contents on exit are unspecified).
These may not overlap each other, nor the 48 bytes below the stack pointer
(the frame saving the link register), which do not wrap around. The
pointers, `count` and `len` are public; the state and the data are secret. -/
def updatePPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 84⟩
    let data : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, 160⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ m, Repr s.mem (s.gpr .r3) m → s.gpr .r4 = BitVec.ofNat 64 m.length →
    Repr s'.mem (s.gpr .r3) (m ++ bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

open VG.PPC64LE in
/-- PPC64LE contract for
`vg_sha1_finalize(state: *mut [u8; 84], count: u64, out: *mut [u8; 20], scratch: *mut [u64; 20])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), writes the SHA-1 digest of `m` to `out`.

The code may read and write `state` (84 bytes, whose contents on exit are
unspecified), `out` (20 bytes) and `scratch` (160 bytes, whose contents on
exit are unspecified). These may not overlap each other, nor the 48 bytes
below the stack pointer (the frame saving the link register), which do not
wrap around. The pointers and `count` are public; the state is secret. -/
def finalizePPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 84⟩
    let out : Region := ⟨s.gpr .r5, 20⟩
    let scratch : Region := ⟨s.gpr .r6, 160⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ m, Repr s.mem (s.gpr .r3) m → s.gpr .r4 = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (s.gpr .r5) 20 = Spec.Sha1.hash m
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

end VG.Proof.Sha1

namespace VG.Proof.Sha1.PPC64LE

open VG VG.PPC64LE VG.Impl.Sha1.PPC64LE
open VG.Spec.Sha1 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! The hash value in memory and offsets into regions (`Proof/Sha1/StateMem.lean`). -/
export VG.Proof.Sha1.StateMem (toNat_ofNat_lt contains_offset sub_offset word_sep readW_writeW_word
  stateAt_eq stateAt_get writeState stateAt_writeState)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .r3
abbrev bp : Addr := s₀.gpr .r4
abbrev nb : Nat := (s₀.gpr .r5).toNat
abbrev scr : Addr := s₀.gpr .r6
abbrev stR : Region := ⟨st s₀, 20⟩
abbrev blR : Region := ⟨bp s₀, 64 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 112⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)
/-- Where the nonvolatile registers are saved. -/
abbrev savR : Region := ⟨scr s₀ + BitVec.ofNat 64 64, 32⟩
/-- Where nonvolatile register `i` is saved. -/
abbrev savAddr (i : Nat) : Addr := scr s₀ + BitVec.ofNat 64 (64 + 8 * i)

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

theorem pre_of (s₀ : State) (h : Proof.Sha1.compressPPC64LE.pre s₀) : Pre s₀ := by
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

theorem in_state {k : Nat} (hk : k < 5) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega) (by omega)⟩

theorem out_state {k : Nat} (hk : k < 5) :
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
    bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) from Offset.add_ofNat_add_ofNat _ _ _]
  exact contains_offset (by omega) (by omega)

theorem in_sav {i : Nat} (hi : i < 4) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (scr s₀ + BitVec.ofNat 64 (64 + 8 * i)) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by omega) (by omega)⟩

theorem out_sav {i : Nat} (hi : i < 4) : InRegions s₀.wr (scr s₀ + BitVec.ofNat 64 (64 + 8 * i)) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by omega) (by omega)⟩

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## Saving and restoring the nonvolatile registers -/

/-- The nonvolatile registers the code does not use: never written. -/
def keepRegs : List Reg := [.r2, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28,
  .r29, .r30, .r31]

theorem keepRegs_fix : ∀ r ∈ keepRegs, r ∈ fixRegs := by decide

theorem keepRegs_preserved : ∀ r ∈ keepRegs, r ∈ preserved := by decide

/-- A preserved register is saved, or kept. -/
theorem preserved_cases : ∀ r ∈ preserved, (∃ i < 4, r = saved i) ∨ r ∈ keepRegs := by decide

theorem saved_inj {i j : Nat} (hi : i < 4) (hj : j < 4) (h : saved i = saved j) : i = j := by
  have key : ∀ i < 4, ∀ j < 4, saved i = saved j → i = j := by decide
  exact key i hi j hj h

theorem saved_ne {i : Nat} (hi : i < 4) : saved i ≠ .r3 ∧ saved i ≠ .r6 ∧ saved i ∉ keepRegs := by
  have key : ∀ i < 4, saved i ≠ .r3 ∧ saved i ≠ .r6 ∧ saved i ∉ keepRegs := by decide
  exact key i hi

theorem sav_sep (p : Addr) {i j : Nat} (hi : i < 4) (hj : j < 4) (h : i ≠ j) :
    Mem.Sep (p + BitVec.ofNat 64 (64 + 8 * i)) 8 (p + BitVec.ofNat 64 (64 + 8 * j)) 8 :=
  Offset.sep p (by omega) (by omega) (by omega)

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (scrR s₀) := sub_offset (by omega) (by omega)

theorem win_sav (s₀ : State) : (winRegion (scr s₀)).Disjoint (savR s₀) :=
  Offset.base_disjoint _ (by omega) (by omega)

theorem sav_contains (s₀ : State) {i : Nat} (hi : i < 4) : (savR s₀).Contains (savAddr s₀ i) 8 :=
  Offset.contains _ (by omega) (by omega) (by omega)

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [savR s₀] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (savAddr s₀ i) 64 = s₀.gpr (saved i)

theorem save_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 4) {s : State} (h : SI s₀ n s) :
    WP isa (.block [.store .d (saved n) .r6 (64 + 8 * n)]) s (SI s₀ (n + 1)) := by
  have hr6 : s.gpr .r6 = scr s₀ := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr .r6 + BitVec.ofNat 64 (64 + 8 * n)) 8 := by
    rw [h.wr, hr6]; exact hp.out_sav hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (by decide) (show 64 + 8 * n < 2 ^ 15 ∧ (64 + 8 * n) % 4 = 0 by omega) hout,
    Option.some.injEq, exists_eq_left', hr6]
  refine ⟨h.gpr, h.rd, h.wr, h.frame.writeW (List.mem_singleton_self _) _ (sav_contains s₀ hn),
    fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega) hn (by omega)) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

/-- The first `n` registers are restored, from the state `sB` the restoring
starts in. -/
structure RI (s₀ sB : State) (n : Nat) (s : State) : Prop where
  restored : ∀ i < n, s.gpr (saved i) = s₀.gpr (saved i)
  others : ∀ r, (∀ i < 4, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem restore_step {s₀ sB : State} (hp : Pre s₀) (hr6 : sB.gpr .r6 = scr s₀)
    (hsav : ∀ i < 4, sB.mem.readW (savAddr s₀ i) 64 = s₀.gpr (saved i))
    {n : Nat} (hn : n < 4) {s : State} (h : RI s₀ sB n s) :
    WP isa (.block [.load .d (saved n) .r6 (64 + 8 * n)]) s (RI s₀ sB (n + 1)) := by
  have hr6' : s.gpr .r6 = scr s₀ := by
    rw [h.others _ fun i hi e => (saved_ne hi).2.1 e.symm, hr6]
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r6 + BitVec.ofNat 64 (64 + 8 * n)) 8 := by
    rw [h.rd, h.wr, hr6']; exact hp.in_sav hn _
  have hv : s.mem.readW (scr s₀ + BitVec.ofNat 64 (64 + 8 * n)) 64 = s₀.gpr (saved n) := by
    rw [h.mem]; exact hsav n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (by decide) (show 64 + 8 * n < 2 ^ 15 ∧ (64 + 8 * n) % 4 = 0 by omega) hin,
    Option.some.injEq, exists_eq_left', hr6', hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr⟩
  · simp only [State.write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e => absurd (saved_inj (by omega) hn e) (by omega)
      simp only [e, ite_false]; exact h.restored i hi
    · simp
  · simp only [State.write, hr n hn, ite_false]; exact h.others r hr

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = st s₀
  r6 : s.gpr .r6 = scr s₀
  kept : ∀ r ∈ keepRegs, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  sav : ∀ i < 4, s.mem.readW (savAddr s₀ i) 64 = s₀.gpr (saved i)
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  r4 : s.gpr .r4 = blkAddr s₀ i
  r5 : s.gpr .r5 = BitVec.ofNat 64 (nb s₀ - i)

/-! ## One block -/

theorem load_eq : load = [
    .load .w .r7 .r3 (4 * 0), .load .w .r8 .r3 (4 * 1), .load .w .r9 .r3 (4 * 2),
    .load .w .r10 .r3 (4 * 3), .load .w .r11 .r3 (4 * 4)] := by
  decide

theorem update_eq : update ++ advance = [
    .load .w .r12 .r3 (4 * 0), .add .r7 .r7 .r12, .load .w .r12 .r3 (4 * 1), .add .r8 .r8 .r12,
    .load .w .r12 .r3 (4 * 2), .add .r9 .r9 .r12, .load .w .r12 .r3 (4 * 3), .add .r10 .r10 .r12,
    .load .w .r12 .r3 (4 * 4), .add .r11 .r11 .r12,
    .store .w .r7 .r3 (4 * 0), .store .w .r8 .r3 (4 * 1), .store .w .r9 .r3 (4 * 2),
    .store .w .r10 .r3 (4 * 3), .store .w .r11 .r3 (4 * 4),
    .addi .r4 .r4 64, .subi .r5 .r5 1] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    (s.gpr .r7).setWidth 32 = v[0] ∧ (s.gpr .r8).setWidth 32 = v[1] ∧
    (s.gpr .r9).setWidth 32 = v[2] ∧ (s.gpr .r10).setWidth 32 = v[3] ∧
    (s.gpr .r11).setWidth 32 = v[4] := Iff.rfl

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hr3 : s.gpr .r3 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 5 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
  simp only [Nat.reduceMul] at h0 h1 h2 h3 h4
  apply WP.of_runBlock
  rw [load_eq]
  simp only [vars0, runBlock_cons, runStep_some, runBlock_nil, exec_load_w, isa, State.write, hr3,
    h0, h1, h2, h3, h4, Option.some.injEq, exists_eq_left', Nat.reduceMul,
    Nat.reducePow, Nat.reduceLT, reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, and_self,
    and_true]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_⟩
  · rw [lo32_ext, stateAt_get _ _ (show 0 < 5 by decide)]
  · rw [lo32_ext, stateAt_get _ _ (show 1 < 5 by decide)]
  · rw [lo32_ext, stateAt_get _ _ (show 2 < 5 by decide)]
  · rw [lo32_ext, stateAt_get _ _ (show 3 < 5 by decide)]
  · rw [lo32_ext, stateAt_get _ _ (show 4 < 5 by decide)]
  · have : r ≠ .r7 ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 := by revert r; decide
    simp [this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2]

theorem frame_writeState {s₀ : State} {m m' : Mem} (h : Frame [stR s₀] m m') (v : HashValue) :
    Frame [stR s₀] m (writeState m' (st s₀) v) := by
  have c : ∀ k, k < 5 → (stR s₀).Contains (st s₀ + BitVec.ofNat 64 (4 * k)) (32 / 8) :=
    fun k hk => contains_offset (by omega) (by omega)
  simp only [writeState]
  refine ((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_) <;>
  simp

theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hr3 : s.gpr .r3 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 5) → s.mem.readW (st s₀ + BitVec.ofNat 64 (4 * k)) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .r4 = s.gpr .r4 + 64 ∧ s'.gpr .r5 = s.gpr .r5 - 1 ∧
      s'.gpr .r3 = s.gpr .r3 ∧ s'.gpr .r6 = s.gpr .r6 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 5 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 5 → InRegions s.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin 4 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH 4 (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_load_w, exec_store_w, exec_add,
    exec_addi, exec_subi, State.write, hr3, i0, i1, i2, i3, i4, o0, o1, o2, o3, o4,
    Option.some.injEq, exists_eq_left', Nat.reduceMul, Nat.reducePow,
    Nat.reduceLeDiff, Nat.reduceLT, reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, and_self,
    true_and, and_true]
  simp only [lo32_add, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, m0, m1, m2, m3, m4,
    v0, v1, v2, v3, v4, Nat.reduceLeDiff]
  refine ⟨?_, ?_⟩
  · simp only [writeState, Vector.getElem_zipWith]
  and_intros
  all_goals first
    | trivial
    | rfl
    | (intro r hr
       simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
         rfl | rfl | rfl | rfl | rfl <;> rfl)

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i t : Nat) (ht : t < 16) :
    rev32 (s₀.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 32) = W (blk s₀ i) t := by
  rw [W_lt _ ht, rev32_readW]
  simp only [blk, blockAt, parseBlock, Offset.add_ofNat_add_one, Nat.add_assoc, Nat.reduceAdd]

theorem win_sub (p : Addr) : Region.Sub (winRegion p) ⟨p, 112⟩ := Region.sub_prefix (by omega)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .d .r5) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .d .r5) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.r3 hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      rev32 (m.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 32) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide), hm₁,
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i t ht
  have hr4₁ : s₁.gpr .r4 = blkAddr s₀ i := (hpub₁ .r4 (by decide)).trans hL.r4
  have hr6₁ : s₁.gpr .r6 = scr s₀ := (hpub₁ .r6 (by decide)).trans hL.r6
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) _ (scr s₀) s₁ hr4₁ hr6₁
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 80 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  have pub₂ : ∀ r ∈ fixRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r (fix_pub r hr)]
  have hr3₂ : s₂.gpr .r3 = st s₀ := by rw [pub₂ .r3 (by decide), hL.r3]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hr3₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.frame.readW (contains_offset (by omega) (by omega)) hst (by decide), hm₁,
      stateAt_get _ _ hk]
  obtain ⟨hm₃, hr4₃, hr5₃, hr3₃, hr6₃, hkept₃, hrd₃, hwr₃⟩ := h₃
  have hr5 : s₂.gpr .r5 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [pub₂ .r5 (by decide), hL.r5, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩) ?_
    rw [hm₃]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hsav : ∀ j < 4, s₃.mem.readW (savAddr s₀ j) 64 = s₀.gpr (saved j) := by
    intro j hj
    have hd : (savR s₀).Disjoint (stR s₀) :=
      Region.Disjoint.sub_left hp.st_scr.symm (savR_sub s₀)
    rw [hm₃, writeState]
    simp only [savAddr]
    iterate 5 rw [Mem.readW_writeW_sep (hd.sep (sav_contains s₀ hj) (contains_offset (by omega)
      (by omega))) (by decide)]
    rw [hR.frame.readW (r := savR s₀) (sav_contains s₀ hj) (by simpa using (win_sav s₀).symm)
      (by decide), hm₁]
    exact hL.sav j hj
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hr3₃, hr3₂], by rw [hr6₃, pub₂ .r6 (by decide), hL.r6],
      fun r hr => by rw [hkept₃ r (keepRegs_preserved r hr), pub₂ r (keepRegs_fix r hr), hL.kept r hr],
      by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, hsav, ?_⟩
    rw [hm₃, stateAt_writeState, compressBlocks_succ, ← hL.state]
    rfl
  have hev : eval (.nonzero .d .r5) s₃ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hr5₃, hr5]
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
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon _ rfl with r4 := ?_, r5 := ?_ }⟩
    · rw [hr4₃, pub₂ .r4 (by decide), hL.r4]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec _) = BitVec.ofNat _ 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hr5₃, hr5]

/-! ## The whole function -/

theorem blocks_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (hc₀ : Common s₀ 0 s₁)
    (hr4 : s₁.gpr .r4 = bp s₀) (hr5 : s₁.gpr .r5 = s₀.gpr .r5) :
    WP isa blocks s₁ (Common s₀ (nb s₀)) := by
  refine WP.ite (s₁.gpr .r5 == 0) (by simp [eval, State.read]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp [hr5] at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq, hr5] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .d .r5) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .d .r5) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        r4 := by simp [blkAddr, hr4]
        r5 := by simp [nb, hr5] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha1.compressPPC64LE.post s₀ s' := by
  have hs₀ : SI s₀ 0 s₀ := ⟨rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  have hsave : WP isa (.block save) s₀ (SI s₀ 4) := by
    unfold save
    exact wp_range_flatMap (M := isa) (SI s₀) (fun k s hk h => save_step hp hk h) 4 (Nat.le_refl _) s₀ hs₀
  refine WP.seq (WP.mono hsave fun s₁ h₁ => ?_)
  have hc₀ : Common s₀ 0 s₁ := by
    refine ⟨by rw [h₁.gpr], by rw [h₁.gpr], fun r _ => by rw [h₁.gpr], h₁.rd, h₁.wr,
      h₁.frame.sub fun r hr => ?_, h₁.saved, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, savR_sub s₀⟩
    · show stateAt s₁.mem (st s₀) = H₀ s₀
      apply stateAt_eq
      intro k hk
      rw [h₁.frame.readW (r := stR s₀) (contains_offset (by omega) (by omega))
        (by simpa using Region.Disjoint.sub_right hp.st_scr (savR_sub s₀)) (by decide),
        ← stateAt_get _ _ hk]
  refine WP.seq (WP.mono (blocks_ok hp hc₀ (by rw [h₁.gpr]) (by rw [h₁.gpr])) fun s₂ h₂ => ?_)
  have hr₀ : RI s₀ s₂ 0 s₂ := ⟨fun _ h => absurd h (by omega), fun _ _ => rfl, rfl, h₂.rd, h₂.wr⟩
  unfold restore
  refine WP.mono (wp_range_flatMap (M := isa) (RI s₀ s₂)
    (fun k s hk h => restore_step hp h₂.r6 h₂.sav hk h) 4 (Nat.le_refl _) s₂ hr₀) fun s' h => ⟨?_, ?_⟩
  · intro r hr
    rcases preserved_cases r hr with ⟨i, hi, rfl⟩ | hk
    · exact h.restored i hi
    · rw [h.others r fun i hi e => (saved_ne hi).2.2 (e ▸ hk), h₂.kept r hk]
  · show stateAt s'.mem (s₀.gpr .r3) = _
    rw [h.mem]
    exact h₂.state

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 20⟩, ⟨0x3000, 112⟩]

theorem compress_verified :
    Verified PPC64LE.target Impl.Sha1.PPC64LE.compress Proof.Sha1.compressPPC64LE := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.lr he (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha1.PPC64LE
