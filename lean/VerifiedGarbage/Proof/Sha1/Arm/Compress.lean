module

import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Sha1.Spec
public import VerifiedGarbage.Impl.Sha1.Arm
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Reduce
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sha1.Arm.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Sha1.Spec
meta import VerifiedGarbage.Impl.Sha1.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Spill
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Sha1.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
/-!
# SHA-1 compression function on ARMv7: the message schedule and the rounds
-/

@[expose] public section

namespace VG.Proof.Sha1.Arm

open VG VG.Arm VG.Impl.Sha1.Arm
open VG.Spec.Sha1 (HashValue Word Block K W f)

/-- The working variables `v` are in the registers of round `t`: `c`, `d`
and `e` rotated left by 2. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0] ∧ s.gpr (var t 1) = v[1] ∧ (s.gpr (var t 2)).rotateRight 2 = v[2] ∧
  (s.gpr (var t 3)).rotateRight 2 = v[3] ∧ (s.gpr (var t 4)).rotateRight 2 = v[4]

/-- The pointers and the count: never written by the rounds. -/
def pubRegs : List Reg := [.r0, .r1, .r2, .r3]

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : BitVec 32) (j : Nat) : Addr := State.addr (scr + BitVec.ofNat 32 (slot j))

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 4) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 4 := by
  simp only [var]; congr 1; omega_using []

/-- The registers of the working variables are all different. -/
theorem round_nodup (t : Nat) : [var t 0, var t 1, var t 2, var t 3, var t 4].Nodup := by
  have h : ∀ c < 5, [work.getD ((0 + 5 - c) % 5) .r4, work.getD ((1 + 5 - c) % 5) .r4,
      work.getD ((2 + 5 - c) % 5) .r4, work.getD ((3 + 5 - c) % 5) .r4,
      work.getD ((4 + 5 - c) % 5) .r4].Nodup := by decide
  exact h (t % 5) (Nat.mod_lt _ (by bdd_omega))

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 5 - t % 5) % 5]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne' : ∀ r ∈ work, r ≠ T ∧ r ≠ KR ∧ r ∉ wregs ∧ r ∉ pubRegs := by decide

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ T ∧ r ≠ KR ∧ r ∉ wregs ∧ r ∉ pubRegs := work_ne' r h

theorem pubRegs_ne' : ∀ r ∈ pubRegs, r ≠ T ∧ r ≠ KR ∧ r ∉ wregs := by decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ T ∧ r ≠ KR ∧ r ∉ wregs := pubRegs_ne' r h

theorem wreg_mem (t : Nat) : wreg t ∈ wregs := by
  unfold wreg List.getD
  cases h : wregs[t % 3]?
  · simp [wregs]
  · exact List.mem_of_getElem? h

/-- The schedule's registers are none of the others. -/
theorem wregs_ne' : ∀ r ∈ wregs, r ≠ T ∧ r ≠ KR ∧ r ≠ .r3 := by decide

theorem wreg_ne_T (t : Nat) : wreg t ≠ T := (wregs_ne' _ (wreg_mem t)).1

theorem wreg_ne_KR (t : Nat) : wreg t ≠ KR := (wregs_ne' _ (wreg_mem t)).2.1

theorem var_ne_wreg (t k j : Nat) : var t k ≠ wreg j := fun h =>
  (work_ne (var_mem t k)).2.2.1 (h ▸ wreg_mem j)

/-- The schedule's register depends on the round modulo 3 only. -/
theorem wreg_congr {a b : Nat} (h : a % 3 = b % 3) : wreg a = wreg b := by
  simp only [wreg, h]

theorem wreg_ne {a b : Nat} (h : a % 3 ≠ b % 3) : wreg a ≠ wreg b := by
  obtain ha := Nat.mod_lt a (show 3 > 0 by decide)
  obtain hb := Nat.mod_lt b (show 3 > 0 by decide)
  simp only [wreg]
  generalize a % 3 = x at *
  generalize b % 3 = y at *
  revert h; revert hb; revert y; revert ha; revert x
  decide

/-! ## Rotations -/

/-- Bit `i` of a rotated word. -/
theorem getLsbD_rotateRight (x : Word) (r : Nat) {i : Nat} (hi : i < 32) :
    (x.rotateRight r).getLsbD i = x.getLsbD ((i + r) % 32) := by
  rw [BitVec.getLsbD_rotateRight]
  have := Nat.mod_lt r (show 32 > 0 by decide)
  split
  · exact congrArg x.getLsbD (by omega_arith)
  · rw [decide_eq_true hi, Bool.true_and]; exact congrArg x.getLsbD (by omega_arith)

theorem rotateRight_xor (x y : Word) (n : Nat) :
    (x ^^^ y).rotateRight n = x.rotateRight n ^^^ y.rotateRight n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_xor, getLsbD_rotateRight _ _ hi, getLsbD_rotateRight _ _ hi,
    getLsbD_rotateRight _ _ hi, BitVec.getLsbD_xor]

/-- A value rotated left by 2, as the rounds keep it, and back. -/
theorem ror30_ror2 (x : Word) : (x.rotateRight 30).rotateRight 2 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_rotateRight _ _ hi, getLsbD_rotateRight _ _ (Nat.mod_lt _ (by decide))]
  exact congrArg x.getLsbD (by omega_arith)

theorem rotl5 (x : Word) : x.rotateLeft 5 = x.rotateRight 27 := rotateLeft_eq x (by bdd_omega)
theorem rotl30 (x : Word) : x.rotateLeft 30 = x.rotateRight 2 := rotateLeft_eq x (by bdd_omega)
theorem rotl1 (x : Word) : x.rotateLeft 1 = x.rotateRight 31 := rotateLeft_eq x (by bdd_omega)

/-! ## One round -/

/-- `fₜ` as the code computes it, from `c` and `d` rotated left by 2. -/
def fval : Fn → Word → Word → Word → Word
  | .ch, x, y, z => x &&& (y ^^^ z).rotateRight 2 ^^^ z.rotateRight 2
  | .parity, x, y, z => x ^^^ (y ^^^ z).rotateRight 2
  | .maj, x, y, z => (x &&& y.rotateRight 2) + ((x ^^^ y.rotateRight 2) &&& z.rotateRight 2)

/-- `Maj` as the sum of two terms with no bit in common. -/
theorem maj_add (x y z : Word) : Spec.Sha1.maj x y z = (x &&& y) + ((x ^^^ y) &&& z) := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i; simp only [Spec.Sha1.maj, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_or]
    cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl
  · ext i; simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_zero]
    cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem f_eq (t : Nat) (x y z : Word) :
    f t x (y.rotateRight 2) (z.rotateRight 2) = fval (fn t) x y z := by
  unfold Spec.Sha1.f fn
  (repeat' split) <;>
    simp only [fval, ch_eq, maj_add, Spec.Sha1.parity, rotateRight_xor, BitVec.and_comm x,
      BitVec.xor_assoc]

/-- The round's code is symbolically executed once per function `f`, for any
registers `a … e` and any register of `Wₜ`. -/
theorem round_run (g : Fn) (a b c d e cw : Reg) (hae : a ≠ e) (hbe : b ≠ e) (hce : c ≠ e)
    (hde : d ≠ e) (hwe : cw ≠ e) (ha : a ≠ T) (hb : b ≠ T) (hc : c ≠ T) (hd : d ≠ T) (he : e ≠ T)
    (s : State) (A B C D E k w : Word) (h₀ : s.gpr a = A) (h₁ : s.gpr b = B) (h₂ : s.gpr c = C)
    (h₃ : s.gpr d = D) (h₄ : s.gpr e = E) (hk : s.gpr KR = k) (hw : s.gpr cw = w) :
    WP isa (.block (([.dp .add e KR (.shifted e .ror 2), .dp .add e e (.reg cw)] : List Instr) ++
        (fcode g b c d e ++ ([.dp .add e e (.shifted a .ror 27)] : List Instr)))) s fun s' =>
      s'.gpr e = k + E.rotateRight 2 + w + fval g B C D + A.rotateRight 27 ∧
      (∀ r, r ≠ e → r ≠ T → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [T, KR] at ha hb hc hd he hk ⊢
  apply WP.of_runBlock
  cases g <;>
  simp only [↓reduceIte, Nat.reduceLeDiff, and_self, fcode, T, List.cons_append,
    List.nil_append, runBlock_cons, runStep_some, runBlock_nil, reduceExec, Op2.eval, isa,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    hae, hbe, hce, hde, hwe, ha, hb, hc, hd, he, h₀, h₁, h₂, h₃, h₄, hk, hw,
    Option.map_some, Option.some.injEq, exists_eq_left'] <;>
  refine ⟨?_, fun r h1 h2 => by simp [h1, h2], trivial⟩
  · rfl
  · rfl
  · simp only [fval, BitVec.add_assoc]

/-- The sum of the round, in the order the code adds it up. -/
theorem t_sum (k e w g a : Word) : k + e + w + g + a = a + g + e + k + w := by ac_rfl

/-- The round, for any registers `a … e`. -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars t s v) (hk : s.gpr KR = K t) (hw : s.gpr (wreg t) = w) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (f t v[1] v[2] v[3]) (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ≠ var t 4 → r ≠ T → s'.gpr r = s.gpr r := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hv
  obtain hd := round_nodup t
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hd
  obtain ⟨⟨-, -, -, h04⟩, ⟨-, -, h14⟩, ⟨-, h24⟩, h34⟩ := hd
  obtain nT : ∀ k, var t k ≠ T := fun k => (work_ne (var_mem t k)).1
  refine WP.mono (round_run (fn t) (var t 0) (var t 1) (var t 2) (var t 3) (var t 4) (wreg t)
    h04 h14 h24 h34 (Ne.symm (var_ne_wreg t 4 t)) (nT 0) (nT 1) (nT 2) (nT 3) (nT 4) s _ _ _ _ _ _ _
    h0 h1 rfl rfl rfl hk hw) fun s' ⟨he, hr, hm, hrd, hwr⟩ => ?_
  refine ⟨?_, hm, hrd, hwr, hr⟩
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 4 by bdd_omega),
    var_succ t _ (show 1 < 4 by bdd_omega), var_succ t _ (show 2 < 4 by bdd_omega),
    var_succ t _ (show 3 < 4 by bdd_omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [he, ← f_eq, h2, h3, h4]; simp only [roundKW, rotl5]; exact t_sum _ _ _ _ _
  · rw [hr _ h04 (nT 0), h0]; rfl
  · rw [hr _ h14 (nT 1), h1]; simp only [roundKW, rotl30]; rfl
  · rw [hr _ h24 (nT 2), h2]; rfl
  · rw [hr _ h34 (nT 3), h3]; rfl

/-! ## The constant -/

/-- `Kₜ` is the constant of the round before, but in the first of its twenty. -/
theorem K_pred {t : Nat} (h : t % 20 ≠ 0) : K (t - 1) = K t := by
  simp only [K]
  rcases (by omega_arith : t < 20 ∨ (20 ≤ t ∧ t < 40) ∨ (40 ≤ t ∧ t < 60) ∨ 60 ≤ t) with h' | h' | h' | h' <;>
    simp (disch := omega_using [h, h']) only [↓ite_eq_left, ↓ite_eq_right]

theorem kload_ok (t : Nat) (s : State) (hk : t % 20 ≠ 0 → s.gpr KR = K t) :
    WP isa (.block (kload t)) s fun s' =>
      s'.gpr KR = K t ∧ (∀ r, r ≠ KR → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  by_cases h : t % 20 = 0
  · simp only [kload, h, ite_true]
    refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil ?_⟩⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
    · simp only [RegUpd.gpr_setReg_self, movw_movt]
    · simp only [RegUpd.gpr_setReg_of_ne _ _ hr]
  · simp only [kload, h, ite_false]
    exact WP.block_nil ⟨hk h, fun _ _ => rfl, rfl, rfl, rfl⟩

/-! ## The message schedule -/

/-- The words of the block: `Wₜ` for `t < 16`, into any register. -/
theorem wload_ok (t : Nat) (ht : t < 16) (cw : Reg) (n3 : cw ≠ .r3) (s : State) (bp scr : BitVec 32)
    (w : Word) (hr1 : s.gpr .r1 = bp) (hr3 : s.gpr .r3 = scr)
    (hout : InRegions s.wr (slotAddr scr t) 4)
    (hbin : InRegions (s.rd ++ s.wr) (State.addr (bp + BitVec.ofNat 32 (4 * t))) 4)
    (hblk : rev (s.mem.readW (State.addr (bp + BitVec.ofNat 32 (4 * t))) 32) = w) :
    WP isa (.block [.ldr cw .r1 (4 * t), .rev cw cw, .str cw .r3 (slot t)]) s fun s' =>
      s'.mem = s.mem.writeW (slotAddr scr t) w ∧ s'.gpr cw = w ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ cw → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hout ⊢
  obtain hs : slot t < 4096 := by simp only [slot]; omega_using []
  obtain ho : 4 * t < 4096 := by bdd_omega
  obtain n3' := Ne.symm n3
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, isa, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    not_false_eq_true, State.load32, State.store32, n3', hr1, hr3, hbin, hout, ho, hs,
    ite_true, hblk, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, fun r h1 => ?_⟩
  simp only [RegUpd.gpr_setReg_of_ne, h1, not_false_eq_true]

/-- The schedule's code for `t ≥ 16`, for any register of `Wₜ₋₃` and any
slots. -/
theorem expand_ok (s : State) (cw : Reg) (nT : cw ≠ T) (n3 : cw ≠ .r3)
    (o8 o14 o16 : Nat) (b8 : o8 < 4096) (b14 : o14 < 4096) (b16 : o16 < 4096)
    (scr : BitVec 32) (w3 w8 w14 w16 : Word) (hr3 : s.gpr .r3 = scr) (h3 : s.gpr cw = w3)
    (i8 : InRegions (s.rd ++ s.wr) (State.addr (scr + BitVec.ofNat 32 o8)) 4)
    (i14 : InRegions (s.rd ++ s.wr) (State.addr (scr + BitVec.ofNat 32 o14)) 4)
    (i16 : InRegions (s.rd ++ s.wr) (State.addr (scr + BitVec.ofNat 32 o16)) 4)
    (hout : InRegions s.wr (State.addr (scr + BitVec.ofNat 32 o16)) 4)
    (e8 : s.mem.readW (State.addr (scr + BitVec.ofNat 32 o8)) 32 = w8)
    (e14 : s.mem.readW (State.addr (scr + BitVec.ofNat 32 o14)) 32 = w14)
    (e16 : s.mem.readW (State.addr (scr + BitVec.ofNat 32 o16)) 32 = w16) :
    WP isa (.block [.ldr T .r3 o8, .dp .eor cw cw (.reg T), .ldr T .r3 o14, .dp .eor cw cw (.reg T),
        .ldr T .r3 o16, .dp .eor cw cw (.reg T), .mov cw (.shifted cw .ror 31), .str cw .r3 o16]) s
      fun s' =>
      s'.mem = s.mem.writeW (State.addr (scr + BitVec.ofNat 32 o16))
        ((w3 ^^^ w8 ^^^ w14 ^^^ w16).rotateRight 31) ∧
      s'.gpr cw = (w3 ^^^ w8 ^^^ w14 ^^^ w16).rotateRight 31 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ cw → r ≠ T → s'.gpr r = s.gpr r := by
  obtain n3' := Ne.symm n3
  simp only [T] at nT ⊢
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, Op2.eval, isa,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, Nat.reduceLeDiff, and_self, not_false_eq_true, reduceCtorEq, State.load32,
    State.store32, nT, n3', hr3, h3, i8, i14, i16, hout, b8, b14, b16, ite_true,
    e8, e14, e16, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, fun r h1 h2 => ?_⟩
  simp only [RegUpd.gpr_setReg_of_ne, h1, h2, not_false_eq_true]

theorem slot_lt (j : Nat) : slot j < 4096 := by simp only [slot]; omega_using []

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : BitVec 32)
    (hr1 : s.gpr .r1 = bp) (hr3 : s.gpr .r3 = scr)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 4)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (State.addr (bp + BitVec.ofNat 32 (4 * t))) 4)
    (hblk : t < 16 → rev (s.mem.readW (State.addr (bp + BitVec.ofNat 32 (4 * t))) 32) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j)
    (hreg : 16 ≤ t → s.gpr (wreg t) = W M (t - 3)) :
    WP isa (.block (schedule t)) s fun s' =>
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧ s'.gpr (wreg t) = W M t ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ wreg t → r ≠ T → s'.gpr r = s.gpr r := by
  obtain n3 := (wregs_ne' _ (wreg_mem t)).2.2
  by_cases ht : t < 16
  · simp only [Impl.Sha1.Arm.schedule, ht, ite_true]
    exact WP.mono (wload_ok t ht (wreg t) n3 s bp scr _ hr1 hr3 (hout t) (hbin ht) (hblk ht))
      fun s' ⟨hm, hw, hrd, hwr, hr⟩ => ⟨hm, hw, hrd, hwr, fun r h _ => hr r h⟩
  · have hw := hwin (by bdd_omega)
    obtain e8 := hw (t - 8) (by bdd_omega) (by bdd_omega)
    obtain e14 := hw (t - 14) (by bdd_omega) (by bdd_omega)
    obtain e16 := hw (t - 16) (by bdd_omega) (by bdd_omega)
    simp only [slotAddr] at hin hout e8 e14 e16 ⊢
    rw [show slot (t - 8) = slot (t + 8) by simp only [slot]; omega_using [ht]] at e8
    rw [show slot (t - 14) = slot (t + 2) by simp only [slot]; omega_using [ht]] at e14
    rw [show slot (t - 16) = slot t by simp only [slot]; omega_using [ht]] at e16
    simp only [Impl.Sha1.Arm.schedule, ht, ite_false]
    rw [W_ge M (t := t) (by bdd_omega), rotl1]
    exact expand_ok s (wreg t) (wreg_ne_T t) n3 _ _ _ (slot_lt _) (slot_lt _) (slot_lt _) scr _ _ _ _
      hr3 (hreg (by bdd_omega)) (hin _) (hin _) (hin _) (hout _) e8 e14 e16

/-! ## The 80 rounds -/

/-- The scratch area the rounds write: the window. -/
abbrev winRegion (scr : BitVec 32) : Region := ⟨State.addr scr, 64⟩

theorem slotAddr_eq {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (j : Nat) :
    slotAddr scr j = State.addr scr + BitVec.ofNat 64 (slot j) :=
  addr_add (by simp only [slot]; omega_using [h])

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem win_contains {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (j : Nat) :
    (winRegion scr).Contains (slotAddr scr j) 4 := by
  rw [slotAddr_eq h]; exact contains_offset (by simp only [slot]; omega_using []) (by simp only [slot]; omega_using [])

theorem slot_sep {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) {i j : Nat}
    (hij : i % 16 ≠ j % 16) : Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  rw [slotAddr_eq h, slotAddr_eq h]
  simp only [slot]
  exact Offset.sep _ (by bdd_omega) (by bdd_omega) (by bdd_omega)

/-- Rounds invariant, relative to the state `sB` at the start of the rounds:
`KR` holds the constant of the round before, and the schedule's registers
its last three words. -/
structure RInv (H : HashValue) (M : Block) (scr : BitVec 32) (sB : State) (t : Nat) (s : State) :
    Prop where
  vars : Vars t s (VG.Spec.Sha1.rounds H M t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  kreg : 0 < t → s.gpr KR = K (t - 1)
  wwin : ∀ j < t, t ≤ j + 3 → s.gpr (wreg j) = W M j
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [winRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : BitVec 32) (sB : State)
    (hscr : scr.toNat + 112 ≤ 2 ^ 32)
    (hr1 : sB.gpr .r1 = bp) (hr3 : sB.gpr .r3 = scr)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
    (hbin : ∀ t : Nat, t < 16 →
      InRegions (sB.rd ++ sB.wr) (State.addr (bp + BitVec.ofNat 32 (4 * t))) 4)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → rev (m.readW (State.addr (bp + BitVec.ofNat 32 (4 * t))) 32) = W M t)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 80, WP isa (rounds t) sB (RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, fun h => absurd h (Nat.lt_irrefl 0),
      fun j hj => absurd hj (by bdd_omega), rfl, rfl, Frame.refl _ _,
      fun j hj => absurd hj (by bdd_omega)⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by bdd_omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    -- The constant.
    refine WP.mono (kload_ok t s fun h => by
      rw [hs.kreg (by omega_using [h]), K_pred h]) fun s₀ ⟨hk₀, hr₀, hm₀, hrd₀, hwr₀⟩ => ?_
    obtain hpub₀ : ∀ r ∈ pubRegs, s₀.gpr r = sB.gpr r := fun r hr => by
      rw [hr₀ r (pubRegs_ne hr).2.1, hs.pub r hr]
    rw [WP.block_append_iff]
    -- The word of the schedule.
    refine WP.mono (schedule_ok t s₀ M bp scr ((hpub₀ .r1 (by decide)).trans hr1)
      ((hpub₀ .r3 (by decide)).trans hr3)
      (by rw [hrd₀, hwr₀, hs.rd, hs.wr]; exact hin) (by rw [hwr₀, hs.wr]; exact hout)
      (fun h => by rw [hrd₀, hwr₀, hs.rd, hs.wr]; exact hbin t h)
      (by rw [hm₀]; exact hblk _ hs.frame t) (fun _ => by rw [hm₀]; exact hs.win)
      (fun h => by
        rw [hr₀ _ (wreg_ne_KR t), wreg_congr (show t % 3 = (t - 3) % 3 by omega_using [h])]
        exact hs.wwin (t - 3) (by bdd_omega) (by bdd_omega)))
      fun s₁ ⟨hm₁, hw₁, hrd₁, hwr₁, hr₁⟩ => ?_
    obtain e₁ : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k => by
      rw [hr₁ _ (var_ne_wreg t k t) (work_ne (var_mem t k)).1, hr₀ _ (work_ne (var_mem t k)).2.1]
    obtain hv₁ : Vars t s₁ (VG.Spec.Sha1.rounds H M t) := by
      have hv := hs.vars
      simp only [Vars, e₁] at hv ⊢
      exact hv
    obtain hk₁ : s₁.gpr KR = K t := by
      rw [hr₁ _ (Ne.symm (wreg_ne_KR t)) (by decide), hk₀]
    -- The round.
    refine WP.mono (round_ok t s₁ _ _ hv₁ hk₁ hw₁) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    obtain keep : ∀ r, r ∉ work → r ≠ T → s₂.gpr r = s₁.gpr r := fun r hw hT =>
      hr₂ r (fun e => hw (e ▸ var_mem t 4)) hT
    refine ⟨?_, fun r hr => ?_, fun _ => ?_, fun j hj hj' => ?_, by rw [hrd₂, hrd₁, hrd₀, hs.rd],
      by rw [hwr₂, hwr₁, hwr₀, hs.wr], ?_, ?_⟩
    · rw [rounds_succ, round_eq]; exact hv₂
    · obtain ⟨p1, p2, p3⟩ := pubRegs_ne hr
      rw [keep r (fun h => (work_ne h).2.2.2 hr) p1, hr₁ r (fun e => p3 (e ▸ wreg_mem t)) p1,
        hpub₀ r hr]
    · rw [keep _ (by decide) (by decide), hk₁]; rfl
    · obtain nw : wreg j ∉ work := fun h => (work_ne h).2.2.1 (wreg_mem j)
      rw [keep _ nw (wreg_ne_T j)]
      by_cases hjt : j = t
      · subst hjt; exact hw₁
      · rw [hr₁ _ (wreg_ne (by bdd_omega)) (wreg_ne_T j), hr₀ _ (wreg_ne_KR j)]
        exact hs.wwin j (by bdd_omega) (by bdd_omega)
    · rw [hm₂, hm₁, hm₀]
      exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains hscr t)
    · intro j hj hj'
      rw [hm₂, hm₁, hm₀]
      by_cases hjt : j = t
      · subst hjt; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (slot_sep hscr (by bdd_omega)) (by decide)]
        exact hs.win j (by bdd_omega) (by bdd_omega)

end VG.Proof.Sha1.Arm

/-!
# SHA-1 compression function on ARMv7: the whole function
-/

/-!
## SHA-1: the 32-bit ARM contract

The contracts the proofs are written against; the artifacts are emitted with the
shared contracts of `Spec/`, which imply these (`Contract.Implies`). The
contracts of the 32-bit ARM implementations of the compression function and of
the streaming functions (`init`, `update`, `finalize`; see `VG.Spec.Sha1.Repr`),
in terms of `Spec/Sha1.lean`. The streaming contracts are those of x86-64 and
AArch64 (`Proof/Sha1/X86_64/Compress.lean`, `Proof/Sha1/AArch64/Compress.lean`),
with the arguments where AAPCS passes them.
-/

namespace VG.Proof.Sha1

open Spec.Sha1

open VG.Arm in
/-- 32-bit ARM contract for
`vg_sha1_compress(state: *mut [u32; 5], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 14])`:
updates the hash value at `state` with the `n` 64-byte blocks at `blocks`.

The code may read `blocks` (`64 * n` bytes) and read and write `state`
(20 bytes) and `scratch` (112 bytes, whose contents on exit are unspecified).
These may not overlap each other, and none of them may wrap around the end of
the (32-bit) address space. The pointers and `n` are public; the hash value
and the blocks are secret. -/
def compressArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 20⟩
    let blocks : Region := ⟨State.addr (s.gpr .r1), 64 * (s.gpr .r2).toNat⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 112⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    (s.gpr .r0).toNat + 20 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 64 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + 112 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem (State.addr (s.gpr .r0)) =
      compressBlocks (stateAt s.mem (State.addr (s.gpr .r0))) s.mem (State.addr (s.gpr .r1))
        (s.gpr .r2).toNat
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

open VG.Arm in
/-- The 64-bit `count` argument of `update`/`finalize`, in `r2:r3` (AAPCS: the
low word in `r2`). -/
def countArm (s : Arm.State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

open VG.Arm in
/-- 32-bit ARM contract for `vg_sha1_init(state: *mut [u8; 84])`: makes the
streaming state at `state` represent the empty message.

The code may write `state` (84 bytes), which may not wrap around the end of
the (32-bit) address space. The pointer is public. -/
def initArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 84⟩
    s.rd = [] ∧ s.wr = [state] ∧ (s.gpr .r0).toNat + 84 ≤ 2 ^ 32
  post s s' := Repr s'.mem (State.addr (s.gpr .r0)) []
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0

open VG.Arm in
/-- 32-bit ARM contract for
`vg_sha1_update(state: *mut [u8; 84], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 20])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), then afterwards it represents `m` followed by the `len` bytes at
`data`.

Under AAPCS, `state` is in `r0`, `count` in `r2:r3`, and `data`, `len` and
`scratch` are the stack arguments 0, 1 and 2. The code may read those
arguments (12 bytes at `sp`) and `data` (`len` bytes), and read and write
`state` (84 bytes) and `scratch` (160 bytes, whose contents on exit are
unspecified). The writable buffers may not overlap each other, the data or
the arguments; the data may not overlap them either; and nothing may wrap
around the end of the (32-bit) address space. `sp`, the pointers, `count`
and `len` are public; the state and the data are secret. -/
def updateArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 84⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 2), 160⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 84 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
    (stackArg s 2).toNat + 160 ≤ 2 ^ 32 ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' := ∀ m, Repr s.mem (State.addr (s.gpr .r0)) m → countArm s = BitVec.ofNat 64 m.length →
    Repr s'.mem (State.addr (s.gpr .r0))
      (m ++ bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

open VG.Arm in
/-- 32-bit ARM contract for
`vg_sha1_finalize(state: *mut [u8; 84], count: u64, out: *mut [u8; 20], scratch: *mut [u64; 20])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), writes the SHA-1 digest of `m` to `out`.

Under AAPCS, `state` is in `r0`, `count` in `r2:r3`, and `out` and `scratch`
are the stack arguments 0 and 1. The code may read those arguments (8 bytes
at `sp`), and read and write `state` (84 bytes, whose contents on exit are
unspecified), `out` (20 bytes) and `scratch` (160 bytes, whose contents on
exit are unspecified). These may not overlap each other or the arguments,
and nothing may wrap around the end of the (32-bit) address space. `sp`, the
pointers and `count` are public; the state is secret. -/
def finalizeArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 84⟩
    let out : Region := ⟨State.addr (stackArg s 0), 20⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 160⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 84 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 20 ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 160 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ m, Repr s.mem (State.addr (s.gpr .r0)) m → countArm s = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (State.addr (stackArg s 0)) 20 = Spec.Sha1.hash m
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.Sha1


namespace VG.Proof.Sha1.Arm

open VG VG.Arm VG.Impl.Sha1.Arm
open VG.Spec.Sha1 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev bp : BitVec 32 := s₀.gpr .r1
abbrev nb : Nat := (s₀.gpr .r2).toNat
abbrev scr : BitVec 32 := s₀.gpr .r3
abbrev stR : Region := ⟨State.addr (st s₀), 20⟩
abbrev blR : Region := ⟨State.addr (bp s₀), 64 * nb s₀⟩
abbrev scrR : Region := ⟨State.addr (scr s₀), 112⟩
abbrev H₀ : HashValue := stateAt s₀.mem (State.addr (st s₀))

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := bp s₀ + BitVec.ofNat 32 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (State.addr (bp s₀) + BitVec.ofNat 64 (64 * i))

/-- The address of word `k` of the hash value. -/
abbrev stAddr (k : Nat) : Addr := State.addr (st s₀ + BitVec.ofNat 32 (4 * k))

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  st_fits : (st s₀).toNat + 20 ≤ 2 ^ 32
  blk_fits : (bp s₀).toNat + 64 * nb s₀ ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 112 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha1.compressArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem contains_sub {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64)
    {a : Addr} (ha : a = base + BitVec.ofNat 64 off) : (⟨base, len⟩ : Region).Contains a n := by
  subst ha; exact contains_offset h ho

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem stAddr_eq {k : Nat} (hk : k < 5) :
    stAddr s₀ k = State.addr (st s₀) + BitVec.ofNat 64 (4 * k) :=
  addr_add (by have := h.st_fits; omega_using [hk, this])

theorem blkAddr_eq {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t)) =
      State.addr (bp s₀) + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) := by
  have := h.blk_fits
  rw [addr_add (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (bp s₀).isLt; omega_arith),
    addr_add (by bdd_omega)]

theorem in_state {k : Nat} (hk : k < 5) : InRegions (s₀.rd ++ s₀.wr) (stAddr s₀ k) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_sub (by bdd_omega) (by bdd_omega) (h.stAddr_eq hk)⟩

theorem out_state {k : Nat} (hk : k < 5) : InRegions s₀.wr (stAddr s₀ k) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_sub (by bdd_omega) (by bdd_omega) (h.stAddr_eq hk)⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_sub (by simp only [slot]; omega_using []) (by simp only [slot]; omega_using [])
    (slotAddr_eq h.scr_fits j)⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_sub (by simp only [slot]; omega_using []) (by simp only [slot]; omega_using [])
    (slotAddr_eq h.scr_fits j)⟩

theorem in_save {d : Nat} (hd : d + 4 ≤ 112) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (scr s₀) + BitVec.ofNat 64 d) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset hd (by bdd_omega)⟩

theorem out_save {d : Nat} (hd : d + 4 ≤ 112) : InRegions s₀.wr (State.addr (scr s₀) + BitVec.ofNat 64 d) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset hd (by bdd_omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 4 := by
  have := h.blk_fits
  rw [h.blkAddr_eq hi ht, Offset.add_ofNat_add_ofNat]
  exact contains_offset (by bdd_omega) (by bdd_omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 5) (hk : k < 5) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofNat 64 (4 * j)) 4 (p + BitVec.ofNat 64 (4 * k)) 4 :=
  Offset.sep p (by bdd_omega) (by bdd_omega) (by bdd_omega)

/-- Reading word `j` of the hash value after writing word `k`. -/
theorem readW_writeW_word {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {j k : Nat} (hj : j < 5)
    (hk : k < 5) (h : j ≠ k) :
    (m.writeW (stAddr s₀ k) v).readW (stAddr s₀ j) 32 = m.readW (stAddr s₀ j) 32 := by
  rw [hp.stAddr_eq hj, hp.stAddr_eq hk]
  exact Mem.readW_writeW_sep (word_sep _ hj hk h) (by decide)

theorem stateAt_eq {m : Mem} {s₀ : State} (hp : Pre s₀) {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 5) → m.readW (stAddr s₀ k) 32 = v[k]) :
    stateAt m (State.addr (st s₀)) = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← hp.stAddr_eq hk]; exact h k hk

theorem stateAt_get {s₀ : State} (hp : Pre s₀) (m : Mem) {k : Nat} (hk : k < 5) :
    (stateAt m (State.addr (st s₀)))[k] = m.readW (stAddr s₀ k) 32 := by
  simp only [stateAt, Vector.getElem_ofFn, hp.stAddr_eq hk]

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch buffer. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (State.addr (scr s₀)) s₀.gpr saved

theorem saved_slots : Spill.Slots 64 100 saved := by decide

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = st s₀
  r3 : s.gpr .r3 = scr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (State.addr (st s₀)) =
    compressBlocks (H₀ s₀) s₀.mem (State.addr (bp s₀)) i
  saved : Saved s₀ s.mem

/-- The hash value `v` is in the working variables' registers. -/
def Regs (s : State) (v : HashValue) : Prop :=
  s.gpr .r4 = v[0] ∧ s.gpr .r5 = v[1] ∧ s.gpr .r6 = v[2] ∧ s.gpr .r7 = v[3] ∧ s.gpr .r8 = v[4]

/-- The loop invariant, at the start of block `i`: the hash value is also in
the registers. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  r1 : s.gpr .r1 = blkAddr s₀ i
  r2 : s.gpr .r2 = BitVec.ofNat 32 (nb s₀ - i)
  regs : Regs s (stateAt s.mem (State.addr (st s₀)))

/-! ## One block -/

theorem load_eq : load = [
    .ldr .r4 .r0 (4 * 0), .ldr .r5 .r0 (4 * 1), .ldr .r6 .r0 (4 * 2), .ldr .r7 .r0 (4 * 3),
    .ldr .r8 .r0 (4 * 4)] := by
  decide

theorem update_eq : update ++ advance = [
    .ldr .r12 .r0 (4 * 0), .dp .add .r4 .r4 (.reg .r12), .str .r4 .r0 (4 * 0),
    .ldr .r12 .r0 (4 * 1), .dp .add .r5 .r5 (.reg .r12), .str .r5 .r0 (4 * 1),
    .ldr .r12 .r0 (4 * 2), .dp .add .r6 .r12 (.shifted .r6 .ror 2), .str .r6 .r0 (4 * 2),
    .ldr .r12 .r0 (4 * 3), .dp .add .r7 .r12 (.shifted .r7 .ror 2), .str .r7 .r0 (4 * 3),
    .ldr .r12 .r0 (4 * 4), .dp .add .r8 .r12 (.shifted .r8 .ror 2), .str .r8 .r0 (4 * 4),
    .dp .add .r1 .r1 (.imm 64), .subs .r2 .r2 (.imm 1)] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .r4 = v[0] ∧ s.gpr .r5 = v[1] ∧ (s.gpr .r6).rotateRight 2 = v[2] ∧
    (s.gpr .r7).rotateRight 2 = v[3] ∧ (s.gpr .r8).rotateRight 2 = v[4] := Iff.rfl

/-- After the 80 rounds the variables are in the registers they started in. -/
theorem vars80 (s : State) (v : HashValue) : Vars 80 s v ↔ Vars 0 s v := Iff.rfl

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hr0 : s.gpr .r0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Regs s₁ (stateAt s.mem (State.addr (st s₀))) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 5 →
      InRegions (s.rd ++ s.wr) (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
  apply WP.of_runBlock
  rw [load_eq]
  simp (config := {decide := true}) only [Regs, runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, State.load32,
    hr0, h0, h1, h2, h3, h4, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  simp only [stateAt_get hp _ (show 0 < 5 by decide), stateAt_get hp _ (show 1 < 5 by decide),
    stateAt_get hp _ (show 2 < 5 by decide), stateAt_get hp _ (show 3 < 5 by decide),
    stateAt_get hp _ (show 4 < 5 by decide)]
  simp (config := {decide := true}) [pubRegs]

/-- `c`, `d` and `e` rotated left by 2, as the rounds keep them. -/
theorem enter_ok {s : State} {v : HashValue} (hv : Regs s v) :
    WP isa (.block enter) s fun s' =>
      Vars 0 s' v ∧ (∀ r ∈ pubRegs, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hv
  apply WP.of_runBlock
  rw [show enter = [.mov .r6 (.shifted .r6 .ror 30), .mov .r7 (.shifted .r7 .ror 30),
    .mov .r8 (.shifted .r8 .ror 30)] from rfl]
  simp only [vars0, runBlock_cons, runStep_some, runBlock_nil, reduceExec, Op2.eval, isa,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, Nat.reduceLeDiff, and_self, not_false_eq_true, reduceCtorEq, ite_true,
    h0, h1, h2, h3, h4, ror30_ror2, Option.map_some, Option.some.injEq, exists_eq_left', true_and]
  refine ⟨fun r hr => ?_, trivial⟩
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    simp only [RegUpd.gpr_setReg_of_ne, not_false_eq_true, reduceCtorEq]

/-- Five words written in order to the hash value. -/
def writeState (s₀ : State) (m : Mem) (v : HashValue) : Mem :=
  (((((m.writeW (stAddr s₀ 0) v[0]).writeW (stAddr s₀ 1) v[1]).writeW (stAddr s₀ 2) v[2]).writeW
    (stAddr s₀ 3) v[3]).writeW (stAddr s₀ 4) v[4])

set_option simprocs false in
theorem stateAt_writeState {s₀ : State} (hp : Pre s₀) (m : Mem) (v : HashValue) :
    stateAt (writeState s₀ m v) (State.addr (st s₀)) = v := by
  apply stateAt_eq hp
  intro k hk
  simp only [writeState]
  rcases (by bdd_omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_writeW_word hp]

theorem frame_writeState {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Frame [stR s₀] m m')
    (v : HashValue) : Frame [stR s₀] m (writeState s₀ m' v) := by
  have c : ∀ k, k < 5 → (stR s₀).Contains (stAddr s₀ k) (32 / 8) :=
    fun k hk => contains_sub (by bdd_omega) (by bdd_omega) (hp.stAddr_eq hk)
  simp only [writeState]
  refine ((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_) <;>
  simp

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hr0 : s.gpr .r0 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 5) → s.mem.readW (stAddr s₀ k) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s₀ s.mem (Vector.zipWith (· + ·) V H) ∧
      Regs s' (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .r1 = s.gpr .r1 + 64 ∧ s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r3 = s.gpr .r3 ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 5 →
      InRegions (s.rd ++ s.wr) (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 5 → InRegions s.wr (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
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
  simp (config := {decide := true}) only [Regs, runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    State.load32, State.store32, subFlags, hr0,
    i0, i1, i2, i3, i4, o0, o1, o2, o3, o4,
    readW_writeW_word hp,
    m0, m1, m2, m3, m4, v0, v1, v2, v3, v4, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  and_intros
  · simp only [writeState, Vector.getElem_zipWith, BitVec.add_comm H[2] V[2],
      BitVec.add_comm H[3] V[3], BitVec.add_comm H[4] V[4]]
  all_goals first
    | trivial
    | (simp only [Vector.getElem_zipWith]; exact BitVec.add_comm _ _)
    | simp only [Vector.getElem_zipWith]

theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [winRegion (scr s₀)] m m' ∨ Frame [stR s₀] m m') : Saved s₀ m' := by
  rcases hf with hf | hf <;> refine h.frame saved_slots hf fun r hr => ?_ <;> rw [List.mem_singleton.mp hr]
  · exact Offset.disjoint_base _ (by decide) (by decide)
  · exact Region.Disjoint.sub_left hp.st_scr.symm (Offset.sub_base _ (by decide))

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (hp : Pre s₀) {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    rev (s₀.mem.readW (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 32) = W (blk s₀ i) t := by
  rw [hp.blkAddr_eq hi ht, W_lt _ ht, rev_readW]
  simp only [blk, blockAt, parseBlock, Offset.add_ofNat_add_one, Nat.add_assoc, Nat.reduceAdd]

theorem win_sub (p : BitVec 32) : Region.Sub (winRegion p) ⟨State.addr p, 112⟩ :=
  Region.sub_prefix (by bdd_omega)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (enter_ok hL.regs) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  obtain hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  obtain hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      rev (m.readW (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 32) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide), hm₁,
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word hp hi ht
  obtain hr1₁ : s₁.gpr .r1 = blkAddr s₀ i := (hpub₁ .r1 (by decide)).trans hL.r1
  obtain hr3₁ : s₁.gpr .r3 = scr s₀ := (hpub₁ .r3 (by decide)).trans hL.r3
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) _ (scr s₀) s₁ hp.scr_fits hr1₁ hr3₁
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 80 (Nat.le_refl _))
    fun s₂ hR => ?_)
  obtain hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  obtain pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  obtain hr0₂ : s₂.gpr .r0 = st s₀ := by rw [pub₂ .r0 (by decide), hL.r0]
  refine WP.mono (update_ok hp _ (stateAt s.mem (State.addr (st s₀))) ((vars80 _ _).mp hR.vars) hr0₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.frame.readW (contains_sub (by bdd_omega) (by bdd_omega) (hp.stAddr_eq hk)) hst (by decide), hm₁,
      stateAt_get hp _ hk]
  obtain ⟨hm₃, hregs₃, hr1₃, hr2₃, hz₃, hr0₃, hr3₃, hrd₃, hwr₃⟩ := h₃
  obtain hnb : nb s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
  obtain hr2 : s₂.gpr .r2 - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [pub₂ .r2 (by decide), hL.r2, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      Offset.ofNat_sub_ofNat (by bdd_omega), Nat.sub_sub]
  obtain hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩) ?_
    rw [hm₃]
    exact (frame_writeState hp (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  obtain hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hr0₃, hr0₂], by rw [hr3₃, pub₂ .r3 (by decide), hL.r3],
      by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_, ?_⟩
    · rw [hm₃, stateAt_writeState hp, compressBlocks_succ, ← hL.state]
      rfl
    · rw [hm₃]
      refine saved_frame hp ?_ (.inr (frame_writeState hp (Frame.refl _ _) _))
      refine saved_frame hp ?_ (.inl hR.frame)
      rw [hm₁]; exact hL.saved
  obtain hev : eval .ne s₃ = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, hz₃, hr2]
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    obtain hne : nb s₀ - (i + 1) ≠ 0 := by bdd_omega
    obtain h0 : BitVec.ofNat 32 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      obtain h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by bdd_omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by bdd_omega,
      { hcommon _ rfl with r1 := ?_, r2 := ?_, regs := ?_ }⟩
    · rw [hr1₃, pub₂ .r1 (by decide), hL.r1]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hr2₃, hr2]
    · rw [hm₃, stateAt_writeState hp]; exact hregs₃

/-! ## Prologue and epilogue -/

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (State.addr (scr s₀)) s₀.gpr saved

theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save ++ ([.cmp .r2 (.imm 0)] : List Instr))) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.z = (s₀.gpr .r2 - 0 == 0) :=
  Spill.save_slots_ok saved_slots (Nat.le_trans (Nat.add_le_add_left (by decide : 100 ≤ 112) _) hp.scr_fits)
    (fun _ _ hd => hp.out_save (by bdd_omega)) (WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩⟩)

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := Spill.saveMem_saved _ _ _ _ saved_slots

theorem saveMem_frame (s₀ : State) : Frame [scrR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame _ _ _ (by decide) saved (by decide)

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hg : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) : Common s₀ 0 s₁ := by
  refine ⟨by rw [hg], by rw [hg], hrd, hwr, ?_, ?_, by rw [hm]; exact saveMem_saved s₀⟩
  · rw [hm]; exact (saveMem_frame s₀).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply stateAt_eq hp
    intro k hk
    rw [(saveMem_frame s₀).readW (contains_sub (len := 20) (off := 4 * k) (by bdd_omega) (by bdd_omega)
      (hp.stAddr_eq hk))
      (by simpa using hp.st_scr) (by decide), ← stateAt_get hp _ hk]
    rfl

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha1.compressArm.post s₀ s' := by
  rw [restore, ← List.append_nil (saved.map _)]
  refine Spill.restore_slots_ok saved_slots (by decide) (g := s₀.gpr) (by rw [hc.r3]; have := hp.scr_fits; omega_using [this])
    (fun _ _ hd => by rw [hc.rd, hc.wr, hc.r3]; exact hp.in_save (by bdd_omega)) (by rw [hc.r3]; exact hc.saved)
    fun s' hs _ hm _ _ _ => WP.block_nil ⟨Spill.restored_of hs (by decide), (congrArg (stateAt · _) hm).trans hc.state⟩

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha1.compressArm.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ ⟨hg, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => restore_ok hp hc)
  have hc₀ := common_zero hp hg hrd hwr hm
  refine WP.ite (s₀.gpr .r2 - 0 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by bdd_omega, i + 1, rfl, hi', hL'⟩
    refine WP.seq (WP.mono (load_ok hp hc₀.r0 hrd hwr) fun s₂ ⟨hv₂, hk₂, hrd₂, hwr₂, hm₂⟩ => ?_)
    obtain hL₀ : LInv s₀ 0 s₂ :=
      { r0 := (hk₂ .r0 (by decide)).trans hc₀.r0
        r3 := (hk₂ .r3 (by decide)).trans hc₀.r3
        rd := hrd₂.trans hrd
        wr := hwr₂.trans hwr
        frame := by rw [hm₂]; exact hc₀.frame
        state := by rw [hm₂]; exact hc₀.state
        saved := by rw [hm₂]; exact hc₀.saved
        r1 := by rw [hk₂ .r1 (by decide), hg]; simp [blkAddr]
        r2 := by rw [hk₂ .r2 (by decide), hg]; simp [nb]
        regs := by rw [hm₂]; exact hv₂ }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₂ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 20⟩, ⟨0x3000, 112⟩]

theorem compress_verified :
    Verified Arm.target Impl.Sha1.Arm.compress Proof.Sha1.compressArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ?_
      (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_, by decide, by decide, by decide⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha1.Arm
