module

import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Reduce
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Sha256.Spec
public import VerifiedGarbage.Impl.Sha256.Arm
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Sha256.Arm.Contract
import VerifiedGarbage.Proof.Sha256.Arm.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Spill
meta import VerifiedGarbage.Proof.Sha256.Spec
meta import VerifiedGarbage.Impl.Sha256.Arm
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sha256.Arm.Contract
meta import VerifiedGarbage.Proof.Sha256.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# SHA-256 compression function on ARMv7: the message schedule and the rounds
-/

@[expose] public section

namespace VG.Proof.Sha256.Arm

open VG VG.Arm VG.Impl.Sha256.Arm
open VG.Spec.Sha256 (HashValue Word Block K W bsig0 bsig1 ch maj ssig0 ssig1)

/-- The working variables `v` are in the registers of round `t`, and
`b ⊕ c` in `mreg (t + 1)`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0] ∧ s.gpr (var t 1) = v[1] ∧ s.gpr (var t 2) = v[2] ∧
  s.gpr (var t 3) = v[3] ∧ s.gpr (var t 4) = v[4] ∧ s.gpr (var t 5) = v[5] ∧
  s.gpr (var t 6) = v[6] ∧ s.gpr (var t 7) = v[7] ∧ s.gpr (mreg (t + 1)) = v[1] ^^^ v[2]

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : BitVec 32) (j : Nat) : Addr := State.addr (scr + BitVec.ofNat 32 (slot j))

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 7) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 7 := by
  simp only [var]; congr 1; omega_using []

/-- `a ⊕ b` of a round is in the register of two rounds before. -/
theorem mreg_add2 (t : Nat) : mreg (t + 1 + 1) = mreg t := by
  simp only [mreg]; rw [show (t + 1 + 1) % 2 = t % 2 by omega_using []]

/-- The registers of round `t` that alternate. -/
theorem mreg_cases (t : Nat) :
    (mreg t = .r12 ∧ mreg (t + 1) = .lr) ∨ (mreg t = .lr ∧ mreg (t + 1) = .r12) := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · exact .inl (by simp [mreg, h, show (t + 1) % 2 = 1 by omega_using [h]])
  · exact .inr (by simp [mreg, h, show (t + 1) % 2 = 0 by omega_using [h]])

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 8 - t % 8) % 8]?
  · simp [work]
  · exact List.mem_of_getElem? h

/-- The working variables' registers are none of the others. -/
theorem work_ne : ∀ r ∈ work, r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 ∧ r ≠ .lr := by decide

/-- The alternating registers are none of the pointers' and the count's. -/
theorem mreg_ne (t : Nat) : mreg t ≠ .r0 ∧ mreg t ≠ .r1 ∧ mreg t ≠ .r2 ∧ mreg t ≠ .r3 := by
  rcases mreg_cases t with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> decide

theorem mreg_ne_succ (t : Nat) : mreg (t + 1) ≠ mreg t := by
  rcases mreg_cases t with ⟨e, e'⟩ | ⟨e, e'⟩ <;> rw [e, e'] <;> decide

theorem var_ne_mreg (t k j : Nat) : var t k ≠ mreg j := by
  obtain h := work_ne _ (var_mem t k)
  rcases mreg_cases j with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e]
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2

/-- The registers of a round are all different. -/
theorem round_nodup (t : Nat) :
    [var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, mreg t, mreg (t + 1)].Nodup := by
  rcases mreg_cases t with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> simp only [var] <;>
    have := Nat.mod_lt t (show 8 > 0 by omega_using []) <;> generalize t % 8 = c at * <;>
    revert this <;> revert c <;> decide

/-- `Maj`, from `b ⊕ c` and `a ⊕ b`. -/
theorem maj_xor (x y z : Word) : maj x y z = (y ^^^ z) &&& (x ^^^ y) ^^^ y := by
  ext i; simp only [maj, BitVec.getElem_xor, BitVec.getElem_and]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

/-- `Σ₁` and `Σ₀`, with the last rotation taken out. -/
theorem bsig1_ror (x : Word) :
    bsig1 x = (x ^^^ x.rotateRight 5 ^^^ x.rotateRight 19).rotateRight 6 := by
  rw [rotateRight_xor, rotateRight_xor, rotateRight_rotateRight x, rotateRight_rotateRight x]; rfl

theorem bsig0_ror (x : Word) :
    bsig0 x = (x ^^^ x.rotateRight 11 ^^^ x.rotateRight 20).rotateRight 2 := by
  rw [rotateRight_xor, rotateRight_xor, rotateRight_rotateRight x, rotateRight_rotateRight x]; rfl

/-- `T₁`, and `T₁ + T₂`, in the order the code adds them up. -/
theorem t1_sum (h w k c s : Word) : h + w + k + c + s = h + s + c + k + w := by ac_rfl

theorem t12_sum (h w k c s z m : Word) : h + w + k + c + s + z + m = h + s + c + k + w + (z + m) := by
  ac_rfl

/-- The round is symbolically executed once, for any registers `a … h` and
the two that alternate (which `round_nodup` says are different), with the
register writes kept folded (`VG.Arm.RegUpd`). -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars t s v) (hw : s.gpr (wreg t) = w) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ≠ var t 7 → r ≠ var t 3 → r ≠ mreg t → r ≠ mreg (t + 1) → s'.gpr r = s.gpr r := by
  obtain hs := round_nodup t
  obtain hs' := VG.nodup_reverse hs
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 7 by bdd_omega),
    var_succ t _ (show 1 < 7 by bdd_omega), var_succ t _ (show 2 < 7 by bdd_omega),
    var_succ t _ (show 3 < 7 by bdd_omega), var_succ t _ (show 4 < 7 by bdd_omega),
    var_succ t _ (show 5 < 7 by bdd_omega), var_succ t _ (show 6 < 7 by bdd_omega), mreg_add2] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv
  apply WP.of_runBlock
  simp only [Impl.Sha256.Arm.round]
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  generalize var t 5 = f at *
  generalize var t 6 = g at *
  generalize var t 7 = h at *
  generalize mreg (t + 1) = p at *
  generalize mreg t = q at *
  generalize wreg t = cw at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, or_false, not_or, List.nodup_nil, and_true] at hs hs'
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, Op2.eval, isa,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, ite_true, Nat.reduceLeDiff, and_self, not_false_eq_true,
    hs, hs', h0, h1, h2, h3, h4, h5, h6, h7, h8, hw,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, trivial, trivial, trivial, fun r nh nd nq np => ?_⟩
  rotate_right
  · simp only [RegUpd.gpr_setReg_of_ne, nh, nd, nq, np, not_false_eq_true]
  all_goals
    simp (config := {failIfUnchanged := false}) only [roundKW_0, roundKW_1, roundKW_2, roundKW_3,
      roundKW_4, roundKW_5, roundKW_6, roundKW_7, bsig1_ror, ch_eq, bsig0_ror, maj_xor, movw_movt]
  · exact t12_sum _ _ _ _ _ _ _
  · exact congrArg _ (t1_sum _ _ _ _ _)

/-! ## The message schedule -/

/-- The words of the block: `Wₜ` for `t < 16`. -/
theorem wload_ok (t : Nat) (ht : t < 16) (s : State) (bp scr : BitVec 32) (w : Word)
    (hr1 : s.gpr .r1 = bp) (hr3 : s.gpr .r3 = scr)
    (hout : InRegions s.wr (slotAddr scr t) 4)
    (hbin : InRegions (s.rd ++ s.wr) (State.addr (bp + BitVec.ofNat 32 (4 * t))) 4)
    (hblk : rev (s.mem.readW (State.addr (bp + BitVec.ofNat 32 (4 * t))) 32) = w) :
    WP isa (.block [.ldr B .r1 (4 * t), .rev B B, .str B .r3 (slot t)]) s fun s' =>
      s'.mem = s.mem.writeW (slotAddr scr t) w ∧ s'.gpr B = w ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ B → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hout ⊢
  obtain hs : slot t < 4096 := by simp only [slot]; omega_using []
  obtain ho : 4 * t < 4096 := by bdd_omega
  apply WP.of_runBlock
  simp only [B, runBlock_cons, runStep_some, runBlock_nil, reduceExec, isa, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    not_false_eq_true, reduceCtorEq, State.load32, State.store32, hr1, hr3, hbin, hout, ho, hs,
    ite_true, hblk, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, fun r h1 => ?_⟩
  simp only [RegUpd.gpr_setReg_of_ne, h1, not_false_eq_true]

/-- The schedule's code for `t ≥ 16`, for any temporary `q` and any slots. -/
theorem expand_ok (s : State) (q : Reg) (n1 : q ≠ .r1) (n2 : q ≠ .r2) (n3 : q ≠ .r3)
    (o15 o2 o7 o16 : Nat) (b15 : o15 < 4096) (b2 : o2 < 4096) (b7 : o7 < 4096) (b16 : o16 < 4096)
    (scr : BitVec 32) (w15 w2 w7 w16 : Word) (hr3 : s.gpr .r3 = scr)
    (i15 : InRegions (s.rd ++ s.wr) (State.addr (scr + BitVec.ofNat 32 o15)) 4)
    (i2 : InRegions (s.rd ++ s.wr) (State.addr (scr + BitVec.ofNat 32 o2)) 4)
    (i7 : InRegions (s.rd ++ s.wr) (State.addr (scr + BitVec.ofNat 32 o7)) 4)
    (i16 : InRegions (s.rd ++ s.wr) (State.addr (scr + BitVec.ofNat 32 o16)) 4)
    (hout : InRegions s.wr (State.addr (scr + BitVec.ofNat 32 o16)) 4)
    (e15 : s.mem.readW (State.addr (scr + BitVec.ofNat 32 o15)) 32 = w15)
    (e2 : s.mem.readW (State.addr (scr + BitVec.ofNat 32 o2)) 32 = w2)
    (e7 : s.mem.readW (State.addr (scr + BitVec.ofNat 32 o7)) 32 = w7)
    (e16 : s.mem.readW (State.addr (scr + BitVec.ofNat 32 o16)) 32 = w16) :
    WP isa (.block [.ldr .r1 .r3 o15, .ldr .r2 .r3 o2,
        .mov q (.shifted .r1 .ror 7), .dp .eor q q (.shifted .r1 .ror 18),
        .dp .eor q q (.shifted .r1 .lsr 3),
        .mov .r1 (.shifted .r2 .ror 17), .dp .eor .r1 .r1 (.shifted .r2 .ror 19),
        .dp .eor .r1 .r1 (.shifted .r2 .lsr 10),
        .ldr .r2 .r3 o7, .dp .add .r1 .r1 (.reg .r2), .dp .add q .r1 (.reg q),
        .ldr .r2 .r3 o16, .dp .add q q (.reg .r2), .str q .r3 o16]) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (scr + BitVec.ofNat 32 o16)) (ssig1 w2 + w7 + ssig0 w15 + w16) ∧
      s'.gpr q = ssig1 w2 + w7 + ssig0 w15 + w16 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ q → s'.gpr r = s.gpr r := by
  obtain n1' := Ne.symm n1
  obtain n2' := Ne.symm n2
  obtain n3' := Ne.symm n3
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, Op2.eval, isa,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, Nat.reduceLeDiff, and_self, not_false_eq_true, reduceCtorEq, State.load32,
    State.store32, n1, n2, n1', n2', n3', hr3, i15, i2, i7, i16, hout, b15, b2, b7, b16, ite_true,
    e15, e2, e7, e16, ssig0, ssig1, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, fun r h1 h2 h3 => ?_⟩
  simp only [RegUpd.gpr_setReg_of_ne, h1, h2, h3, not_false_eq_true]

theorem slot_lt (j : Nat) : slot j < 4096 := by simp only [slot]; omega_using []

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : BitVec 32)
    (hr1 : t < 16 → s.gpr .r1 = bp) (hr3 : s.gpr .r3 = scr)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 4)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (State.addr (bp + BitVec.ofNat 32 (4 * t))) 4)
    (hblk : t < 16 → rev (s.mem.readW (State.addr (bp + BitVec.ofNat 32 (4 * t))) 32) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧ s'.gpr (wreg t) = W M t ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ mreg t → s'.gpr r = s.gpr r) ∧
      (t < 16 → s'.gpr .r1 = s.gpr .r1) := by
  by_cases ht : t < 16
  · simp only [Impl.Sha256.Arm.schedule, wreg, ht, ite_true]
    refine WP.mono (wload_ok t ht s bp scr _ (hr1 ht) hr3 (hout t) (hbin ht) (hblk ht))
      fun s' ⟨hm, hw, hrd, hwr, hr⟩ => ⟨hm, hw, hrd, hwr, fun r _ h2 _ => hr r h2, fun _ => hr .r1 (by decide)⟩
  · have hw := hwin (by bdd_omega)
    obtain e2 := hw (t - 2) (by bdd_omega) (by bdd_omega)
    obtain e7 := hw (t - 7) (by bdd_omega) (by bdd_omega)
    obtain e15 := hw (t - 15) (by bdd_omega) (by bdd_omega)
    obtain e16 := hw (t - 16) (by bdd_omega) (by bdd_omega)
    simp only [slotAddr] at hin hout e2 e7 e15 e16 ⊢
    rw [show slot (t - 2) = slot (t + 14) by simp only [slot]; omega_using [ht]] at e2
    rw [show slot (t - 7) = slot (t + 9) by simp only [slot]; omega_using [ht]] at e7
    rw [show slot (t - 15) = slot (t + 1) by simp only [slot]; omega_using [ht]] at e15
    rw [show slot (t - 16) = slot t by simp only [slot]; omega_using [ht]] at e16
    obtain ⟨-, n1, n2, n3⟩ := mreg_ne t
    simp only [Impl.Sha256.Arm.schedule, wreg, ht, ite_false, A, B]
    rw [W_ge M (t := t) (by bdd_omega)]
    refine WP.mono (expand_ok s (mreg t) n1 n2 n3 _ _ _ _ (slot_lt _) (slot_lt _) (slot_lt _) (slot_lt _)
      scr _ _ _ _ hr3 (hin _) (hin _) (hin _) (hin _) (hout _) e15 e2 e7 e16)
      fun s' ⟨hm, hw, hrd, hwr, hr⟩ => ⟨hm, hw, hrd, hwr, hr, fun h => h.elim⟩

/-! ## The 64 rounds -/

/-- The scratch area the rounds write: the window. -/
abbrev workRegion (scr : BitVec 32) : Region := ⟨State.addr scr, 64⟩

theorem slotAddr_eq {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (j : Nat) :
    slotAddr scr j = State.addr scr + BitVec.ofNat 64 (slot j) :=
  addr_add (by simp only [slot]; omega_using [h])

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem win_contains {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (j : Nat) :
    (workRegion scr).Contains (slotAddr scr j) 4 := by
  rw [slotAddr_eq h]; exact contains_offset (by simp only [slot]; omega_using []) (by simp only [slot]; omega_using [])

theorem slot_sep {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) {i j : Nat}
    (hij : i % 16 ≠ j % 16) : Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  rw [slotAddr_eq h, slotAddr_eq h]
  simp only [slot]
  exact Offset.sep _ (by bdd_omega) (by bdd_omega) (by bdd_omega)

/-- Rounds invariant, relative to the state `sB` at the start of the rounds:
the pointer to the block is kept as long as the rounds read it. -/
structure RInv (H : HashValue) (M : Block) (scr : BitVec 32) (sB : State) (t : Nat) (s : State) :
    Prop where
  vars : Vars t s (VG.Spec.Sha256.rounds H M t)
  r0 : s.gpr .r0 = sB.gpr .r0
  r1 : t ≤ 16 → s.gpr .r1 = sB.gpr .r1
  r3 : s.gpr .r3 = sB.gpr .r3
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [workRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : BitVec 32) (sB : State)
    (hscr : scr.toNat + 112 ≤ 2 ^ 32)
    (hr1 : sB.gpr .r1 = bp) (hr3 : sB.gpr .r3 = scr)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
    (hbin : ∀ t : Nat, t < 16 →
      InRegions (sB.rd ++ sB.wr) (State.addr (bp + BitVec.ofNat 32 (4 * t))) 4)
    (hblk : ∀ m, Frame [workRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → rev (m.readW (State.addr (bp + BitVec.ofNat 32 (4 * t))) 32) = W M t)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 64, WP isa (rounds t) sB (RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, rfl, fun _ => rfl, rfl, rfl, rfl, Frame.refl _ _,
      fun j hj => absurd hj (by bdd_omega)⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by bdd_omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    obtain hs_r3 : s.gpr .r3 = scr := hs.r3.trans hr3
    refine WP.mono (schedule_ok t s M bp scr (fun h => (hs.r1 (by bdd_omega)).trans hr1) hs_r3
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.wr]; exact hout)
      (fun h => by rw [hs.rd, hs.wr]; exact hbin t h) (hblk _ hs.frame t)
      (fun _ => hs.win)) fun s₁ ⟨hm₁, hw₁, hrd₁, hwr₁, hr₁, hk₁⟩ => ?_
    obtain ⟨m0, m1, m2, m3⟩ := mreg_ne t
    obtain ⟨p0, p1, p2, p3⟩ := mreg_ne (t + 1)
    obtain hv₁ : Vars t s₁ (VG.Spec.Sha256.rounds H M t) := by
      have hv := hs.vars
      obtain e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k =>
        have := work_ne _ (var_mem t k); hr₁ _ this.2.1 this.2.2.1 (var_ne_mreg t k t)
      obtain e' : s₁.gpr (mreg (t + 1)) = s.gpr (mreg (t + 1)) := hr₁ _ p1 p2 (mreg_ne_succ t)
      simp only [Vars, e, e'] at hv ⊢
      exact hv
    refine WP.mono (round_ok t s₁ _ _ hv₁ hw₁) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    obtain hk : ∀ r, r ∉ work → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s₁.gpr r := fun r hw h12 hlr =>
      hr₂ r (fun e => hw (e ▸ var_mem t 7)) (fun e => hw (e ▸ var_mem t 3))
        (by rcases mreg_cases t with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> first | exact h12 | exact hlr)
        (by rcases mreg_cases t with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] <;> first | exact h12 | exact hlr)
    refine ⟨?_, ?_, fun h => ?_, ?_, by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr], ?_, ?_⟩
    · have e : VG.Spec.Sha256.rounds H M (t + 1) =
          roundKW (VG.Spec.Sha256.rounds H M t) (K t) (W M t) := by
        rw [rounds_succ, round_eq]
      rw [e]; exact hv₂
    · rw [hk .r0 (by decide) (by decide) (by decide), hr₁ .r0 (by decide) (by decide) (Ne.symm m0), hs.r0]
    · rw [hk .r1 (by decide) (by decide) (by decide), hk₁ (by bdd_omega), hs.r1 (by bdd_omega)]
    · rw [hk .r3 (by decide) (by decide) (by decide), hr₁ .r3 (by decide) (by decide) (Ne.symm m3), hs.r3]
    · rw [hm₂, hm₁]
      exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains hscr t)
    · intro j hj hj'
      rw [hm₂, hm₁]
      by_cases hjt : j = t
      · subst hjt; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (slot_sep hscr (by bdd_omega)) (by decide)]
        exact hs.win j (by bdd_omega) (by bdd_omega)

end VG.Proof.Sha256.Arm

/-!
# SHA-256 compression function on ARMv7: the whole function
-/

namespace VG.Proof.Sha256.Arm

open VG VG.Arm VG.Impl.Sha256.Arm
open VG.Spec.Sha256 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev bp : BitVec 32 := s₀.gpr .r1
abbrev nb : Nat := (s₀.gpr .r2).toNat
abbrev scr : BitVec 32 := s₀.gpr .r3
abbrev stR : Region := ⟨State.addr (st s₀), 32⟩
abbrev blR : Region := ⟨State.addr (bp s₀), 64 * nb s₀⟩
abbrev scrR : Region := ⟨State.addr (scr s₀), 112⟩
abbrev H₀ : HashValue := stateAt s₀.mem (State.addr (st s₀))

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := bp s₀ + BitVec.ofNat 32 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (State.addr (bp s₀) + BitVec.ofNat 64 (64 * i))

/-- The address of word `k` of the hash value. -/
abbrev stAddr (k : Nat) : Addr := State.addr (st s₀ + BitVec.ofNat 32 (4 * k))

end

/-- The two words of the scratch buffer that keep the block pointer and the
count of blocks left, and their addresses. -/
abbrev ctlR (s₀ : State) : Region := ⟨State.addr (scr s₀) + BitVec.ofNat 64 104, 8⟩
abbrev ptrAddr (s₀ : State) : Addr := State.addr (scr s₀ + BitVec.ofNat 32 ptrSlot)
abbrev cntAddr (s₀ : State) : Addr := State.addr (scr s₀ + BitVec.ofNat 32 cntSlot)

theorem ctl_sub (p : BitVec 32) :
    Region.Sub ⟨State.addr p + BitVec.ofNat 64 104, 8⟩ ⟨State.addr p, 112⟩ :=
  Offset.sub_base _ (by decide)

/-- The two words are apart from the window. -/
theorem ctl_work (p : BitVec 32) :
    ∀ r' ∈ [workRegion p], Region.Disjoint ⟨State.addr p + BitVec.ofNat 64 104, 8⟩ r' := by
  simpa using Offset.disjoint_base (State.addr p) (d := 104) (n := 8) (k := 64) (by decide) (by decide)

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  st_fits : (st s₀).toNat + 32 ≤ 2 ^ 32
  blk_fits : (bp s₀).toNat + 64 * nb s₀ ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 112 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha256.compressArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem contains_sub {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64)
    {a : Addr} (ha : a = base + BitVec.ofNat 64 off) : (⟨base, len⟩ : Region).Contains a n := by
  subst ha; exact contains_offset h ho

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem stAddr_eq {k : Nat} (hk : k < 8) :
    stAddr s₀ k = State.addr (st s₀) + BitVec.ofNat 64 (4 * k) :=
  addr_add (by have := h.st_fits; omega_using [hk, this])

theorem blkAddr_eq {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t)) =
      State.addr (bp s₀) + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) := by
  have := h.blk_fits
  rw [addr_add (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (bp s₀).isLt; omega_arith),
    addr_add (by bdd_omega)]

theorem in_state {k : Nat} (hk : k < 8) : InRegions (s₀.rd ++ s₀.wr) (stAddr s₀ k) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_sub (by bdd_omega) (by bdd_omega) (h.stAddr_eq hk)⟩

theorem out_state {k : Nat} (hk : k < 8) : InRegions s₀.wr (stAddr s₀ k) 4 :=
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

theorem ptrAddr_eq : ptrAddr s₀ = State.addr (scr s₀) + BitVec.ofNat 64 ptrSlot :=
  addr_add (by have := h.scr_fits; simp only [ptrSlot]; omega_using [this])

theorem cntAddr_eq : cntAddr s₀ = State.addr (scr s₀) + BitVec.ofNat 64 cntSlot :=
  addr_add (by have := h.scr_fits; simp only [cntSlot]; omega_using [this])

theorem ptr_contains : (ctlR s₀).Contains (ptrAddr s₀) (32 / 8) := by
  rw [h.ptrAddr_eq]; exact Offset.contains _ (by decide) (by decide) (by decide)

theorem cnt_contains : (ctlR s₀).Contains (cntAddr s₀) (32 / 8) := by
  rw [h.cntAddr_eq]; exact Offset.contains _ (by decide) (by decide) (by decide)

theorem cnt_ptr_sep : Mem.Sep (cntAddr s₀) (32 / 8) (ptrAddr s₀) (32 / 8) := by
  rw [h.cntAddr_eq, h.ptrAddr_eq]; exact Offset.sep _ (by decide) (by decide) (by decide)

theorem in_ptr : InRegions (s₀.rd ++ s₀.wr) (ptrAddr s₀) 4 := by
  rw [h.ptrAddr_eq]; exact h.in_save (by decide)

theorem in_cnt : InRegions (s₀.rd ++ s₀.wr) (cntAddr s₀) 4 := by
  rw [h.cntAddr_eq]; exact h.in_save (by decide)

theorem out_ptr : InRegions s₀.wr (ptrAddr s₀) 4 := by
  rw [h.ptrAddr_eq]; exact h.out_save (by decide)

theorem out_cnt : InRegions s₀.wr (cntAddr s₀) 4 := by
  rw [h.cntAddr_eq]; exact h.out_save (by decide)

/-- The state and the blocks are apart from the two words. -/
theorem st_ctl : ∀ r' ∈ [ctlR s₀], (stR s₀).Disjoint r' := by
  simpa using Region.Disjoint.sub_right h.st_scr (ctl_sub _)

theorem blk_ctl : ∀ r' ∈ [ctlR s₀], (blR s₀).Disjoint r' := by
  simpa using Region.Disjoint.sub_right h.blk_scr (ctl_sub _)

theorem ctl_st : ∀ r' ∈ [stR s₀], (ctlR s₀).Disjoint r' := by
  simpa using (Region.Disjoint.sub_right h.st_scr (ctl_sub _)).symm

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 4 := by
  have := h.blk_fits
  rw [h.blkAddr_eq hi ht, show State.addr (bp s₀) + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) =
    State.addr (bp s₀) + BitVec.ofNat 64 (64 * i + 4 * t) from Offset.add_add _ _ _]
  exact contains_offset (by bdd_omega) (by bdd_omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 8) (hk : k < 8) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofNat 64 (4 * j)) 4 (p + BitVec.ofNat 64 (4 * k)) 4 := by
  exact Offset.sep p (by bdd_omega) (by bdd_omega) (by bdd_omega)

/-- Reading word `j` of the hash value after writing word `k`. -/
theorem readW_writeW_word {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {j k : Nat} (hj : j < 8)
    (hk : k < 8) (h : j ≠ k) :
    (m.writeW (stAddr s₀ k) v).readW (stAddr s₀ j) 32 = m.readW (stAddr s₀ j) 32 := by
  rw [hp.stAddr_eq hj, hp.stAddr_eq hk]
  exact Mem.readW_writeW_sep (word_sep _ hj hk h) (by decide)

theorem stateAt_eq {m : Mem} {s₀ : State} (hp : Pre s₀) {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 8) → m.readW (stAddr s₀ k) 32 = v[k]) :
    stateAt m (State.addr (st s₀)) = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← hp.stAddr_eq hk]; exact h k hk

theorem stateAt_get {s₀ : State} (hp : Pre s₀) (m : Mem) {k : Nat} (hk : k < 8) :
    (stateAt m (State.addr (st s₀)))[k] = m.readW (stAddr s₀ k) 32 := by
  simp only [stateAt, Vector.getElem_ofFn, hp.stAddr_eq hk]

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch buffer. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (State.addr (scr s₀)) s₀.gpr saved

theorem saved_slots : Spill.Slots 68 104 saved := by decide

/-- The hash value `v` is in the working variables' registers. -/
def Regs (s : State) (v : HashValue) : Prop :=
  s.gpr .r4 = v[0] ∧ s.gpr .r5 = v[1] ∧ s.gpr .r6 = v[2] ∧ s.gpr .r7 = v[3] ∧
  s.gpr .r8 = v[4] ∧ s.gpr .r9 = v[5] ∧ s.gpr .r10 = v[6] ∧ s.gpr .r11 = v[7]

theorem Regs.keep {s s' : State} {v : HashValue} (h : Regs s v)
    (e : ∀ r, r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r) : Regs s' v := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨(e _ (by decide) (by decide)).trans h0, (e _ (by decide) (by decide)).trans h1,
    (e _ (by decide) (by decide)).trans h2, (e _ (by decide) (by decide)).trans h3,
    (e _ (by decide) (by decide)).trans h4, (e _ (by decide) (by decide)).trans h5,
    (e _ (by decide) (by decide)).trans h6, (e _ (by decide) (by decide)).trans h7⟩

/-- After the 64 rounds the variables are in the registers they started in. -/
theorem regs_of_vars {s : State} {v : HashValue} (h : Vars 64 s v) : Regs s v :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

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

/-- The loop invariant, at the start of block `i`: the hash value is also in
the registers, and the count of blocks left in the scratch buffer. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  r1 : s.gpr .r1 = blkAddr s₀ i
  cnt : s.mem.readW (cntAddr s₀) 32 = BitVec.ofNat 32 (nb s₀ - i)
  regs : Regs s (stateAt s.mem (State.addr (st s₀)))

/-! ## One block -/

theorem load_eq : load = [
    .ldr .r4 .r0 (4 * 0), .ldr .r5 .r0 (4 * 1), .ldr .r6 .r0 (4 * 2), .ldr .r7 .r0 (4 * 3),
    .ldr .r8 .r0 (4 * 4), .ldr .r9 .r0 (4 * 5), .ldr .r10 .r0 (4 * 6), .ldr .r11 .r0 (4 * 7)] := by
  decide

theorem update_eq : update = [
    .ldr .r12 .r0 (4 * 0), .dp .add .r4 .r4 (.reg .r12), .str .r4 .r0 (4 * 0),
    .ldr .r12 .r0 (4 * 1), .dp .add .r5 .r5 (.reg .r12), .str .r5 .r0 (4 * 1),
    .ldr .r12 .r0 (4 * 2), .dp .add .r6 .r6 (.reg .r12), .str .r6 .r0 (4 * 2),
    .ldr .r12 .r0 (4 * 3), .dp .add .r7 .r7 (.reg .r12), .str .r7 .r0 (4 * 3),
    .ldr .r12 .r0 (4 * 4), .dp .add .r8 .r8 (.reg .r12), .str .r8 .r0 (4 * 4),
    .ldr .r12 .r0 (4 * 5), .dp .add .r9 .r9 (.reg .r12), .str .r9 .r0 (4 * 5),
    .ldr .r12 .r0 (4 * 6), .dp .add .r10 .r10 (.reg .r12), .str .r10 .r0 (4 * 6),
    .ldr .r12 .r0 (4 * 7), .dp .add .r11 .r11 (.reg .r12), .str .r11 .r0 (4 * 7)] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .r4 = v[0] ∧ s.gpr .r5 = v[1] ∧ s.gpr .r6 = v[2] ∧ s.gpr .r7 = v[3] ∧
    s.gpr .r8 = v[4] ∧ s.gpr .r9 = v[5] ∧ s.gpr .r10 = v[6] ∧ s.gpr .r11 = v[7] ∧
    s.gpr .lr = v[1] ^^^ v[2] := Iff.rfl

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hr0 : s.gpr .r0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Regs s₁ (stateAt s.mem (State.addr (st s₀))) ∧
      s₁.gpr .r0 = s.gpr .r0 ∧ s₁.gpr .r1 = s.gpr .r1 ∧ s₁.gpr .r3 = s.gpr .r3 ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  obtain hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  obtain h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  obtain h3 := hin 3 (by decide); have h4 := hin 4 (by decide); have h5 := hin 5 (by decide)
  obtain h6 := hin 6 (by decide); have h7 := hin 7 (by decide)
  apply WP.of_runBlock
  rw [load_eq]
  simp (config := {decide := true}) only [Regs, runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg,
    RegUpd.rd_setReg,
    RegUpd.wr_setReg, State.load32,
    hr0, h0, h1, h2, h3, h4, h5, h6, h7, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  simp only [stateAt_get hp _ (show 0 < 8 by decide), stateAt_get hp _ (show 1 < 8 by decide),
    stateAt_get hp _ (show 2 < 8 by decide), stateAt_get hp _ (show 3 < 8 by decide),
    stateAt_get hp _ (show 4 < 8 by decide), stateAt_get hp _ (show 5 < 8 by decide),
    stateAt_get hp _ (show 6 < 8 by decide), stateAt_get hp _ (show 7 < 8 by decide)]
  exact ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩, trivial⟩

/-- Keeping the block pointer, and `b ⊕ c` for the first round. -/
theorem enter_ok {s₀ : State} {s : State} {v : HashValue} (hr3 : s.gpr .r3 = scr s₀)
    (hout : InRegions s.wr (ptrAddr s₀) 4) (hv : Regs s v) :
    WP isa (.block enter) s fun s' =>
      Vars 0 s' v ∧ s'.mem = s.mem.writeW (ptrAddr s₀) (s.gpr .r1) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r3 = s.gpr .r3 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  simp only [ptrAddr, ptrSlot] at hout ⊢
  apply WP.of_runBlock
  rw [show enter = [.str .r1 .r3 104, .dp .eor .lr .r5 (.reg .r6)] from rfl]
  simp only [vars0, runBlock_cons, runStep_some, runBlock_nil, reduceExec, Op2.eval, isa,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, State.store32, Nat.reduceLT, not_false_eq_true, reduceCtorEq, hr3, hout,
    ite_true, h0, h1, h2, h3, h4, h5, h6, h7, Option.map_some, Option.some.injEq, exists_eq_left',
    and_self]

/-- Eight words written in order to the hash value. -/
def writeState (s₀ : State) (m : Mem) (v : HashValue) : Mem :=
  ((((((((m.writeW (stAddr s₀ 0) v[0]).writeW (stAddr s₀ 1) v[1]).writeW (stAddr s₀ 2) v[2]).writeW
    (stAddr s₀ 3) v[3]).writeW (stAddr s₀ 4) v[4]).writeW (stAddr s₀ 5) v[5]).writeW
    (stAddr s₀ 6) v[6]).writeW (stAddr s₀ 7) v[7])

set_option simprocs false in
theorem stateAt_writeState {s₀ : State} (hp : Pre s₀) (m : Mem) (v : HashValue) :
    stateAt (writeState s₀ m v) (State.addr (st s₀)) = v := by
  apply stateAt_eq hp
  intro k hk
  simp only [writeState]
  rcases (by bdd_omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with h | h | h | h | h | h | h | h <;> subst h <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_writeW_word hp]

theorem frame_writeState {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Frame [stR s₀] m m')
    (v : HashValue) : Frame [stR s₀] m (writeState s₀ m' v) := by
  obtain c : ∀ k, k < 8 → (stR s₀).Contains (stAddr s₀ k) (32 / 8) :=
    fun k hk => contains_sub (by bdd_omega) (by bdd_omega) (hp.stAddr_eq hk)
  simp only [writeState]
  refine (((((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _ (c 6 ?_)).writeW ?_ _ (c 7 ?_) <;>
  simp

/-- The hash value does not change with the memory outside it. -/
theorem stateAt_frame {s₀ : State} (hp : Pre s₀) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r' ∈ rs, (stR s₀).Disjoint r') :
    stateAt m' (State.addr (st s₀)) = stateAt m (State.addr (st s₀)) := by
  apply stateAt_eq hp
  intro k hk
  rw [hf.readW (contains_sub (len := 32) (off := 4 * k) (by bdd_omega) (by bdd_omega) (hp.stAddr_eq hk))
    hd (by decide), ← stateAt_get hp _ hk]

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Regs s V)
    (hr0 : s.gpr .r0 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 8) → s.mem.readW (stAddr s₀ k) 32 = H[k]) :
    WP isa (.block update) s fun s' =>
      s'.mem = writeState s₀ s.mem (Vector.zipWith (· + ·) V H) ∧
      Regs s' (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r3 = s.gpr .r3 ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  obtain hout : ∀ k : Nat, k < 8 → InRegions s.wr (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  obtain i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  obtain i3 := hin 3 (by decide); have i4 := hin 4 (by decide); have i5 := hin 5 (by decide)
  obtain i6 := hin 6 (by decide); have i7 := hin 7 (by decide)
  obtain o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  obtain o3 := hout 3 (by decide); have o4 := hout 4 (by decide); have o5 := hout 5 (by decide)
  obtain o6 := hout 6 (by decide); have o7 := hout 7 (by decide)
  obtain m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  obtain m3 := hH 3 (by decide); have m4 := hH 4 (by decide); have m5 := hH 5 (by decide)
  obtain m6 := hH 6 (by decide); have m7 := hH 7 (by decide)
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp (config := {decide := true}) only [Regs, runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    State.load32, State.store32, hr0,
    i0, i1, i2, i3, i4, i5, i6, i7, o0, o1, o2, o3, o4, o5, o6, o7,
    readW_writeW_word hp,
    m0, m1, m2, m3, m4, m5, m6, m7, v0, v1, v2, v3, v4, v5, v6, v7, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  and_intros
  · simp only [writeState, Vector.getElem_zipWith]
  all_goals first | trivial | simp only [Vector.getElem_zipWith]

/-- The next block's pointer, and the count of the blocks left after this one. -/
theorem advance_ok {s₀ : State} {s : State} {p c : BitVec 32} (hr3 : s.gpr .r3 = scr s₀)
    (ip : InRegions (s.rd ++ s.wr) (ptrAddr s₀) 4) (ic : InRegions (s.rd ++ s.wr) (cntAddr s₀) 4)
    (oc : InRegions s.wr (cntAddr s₀) 4)
    (hp : s.mem.readW (ptrAddr s₀) 32 = p) (hc : s.mem.readW (cntAddr s₀) 32 = c) :
    WP isa (.block advance) s fun s' =>
      s'.gpr .r1 = p + 64 ∧ s'.z = (c - 1 == 0) ∧ s'.mem = s.mem.writeW (cntAddr s₀) (c - 1) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain e64 : encodable (64 : BitVec 32) = true := by decide
  obtain e1 : encodable (1 : BitVec 32) = true := by decide
  simp only [ptrAddr, cntAddr, ptrSlot, cntSlot] at ip ic oc hp hc ⊢
  apply WP.of_runBlock
  simp only [advance, ptrSlot, cntSlot, runBlock_cons, runStep_some, runBlock_nil, reduceExec, Op2.eval,
    isa, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.z_setReg, State.load32, State.store32, subFlags, Nat.reduceLT,
    not_false_eq_true, reduceCtorEq, hr3, ip, ic, oc, hp, hc, e64, e1, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, fun r h1 h2 => ?_, trivial, trivial⟩
  simp only [RegUpd.gpr_setReg_of_ne, h1, h2, not_false_eq_true]

theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [workRegion (scr s₀)] m m' ∨ Frame [stR s₀] m m' ∨ Frame [ctlR s₀] m m') :
    Saved s₀ m' := by
  rcases hf with hf | hf | hf <;> refine h.frame saved_slots hf fun r hr => ?_ <;>
    rw [List.mem_singleton.mp hr]
  · exact Offset.disjoint_base _ (by decide) (by decide)
  · exact Region.Disjoint.sub_left hp.st_scr.symm (Offset.sub_base _ (by decide))
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (hp : Pre s₀) {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    rev (s₀.mem.readW (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 32) = W (blk s₀ i) t := by
  rw [hp.blkAddr_eq hi ht, W_lt _ ht, rev_readW]
  simp only [blk, blockAt, parseBlock]
  generalize State.addr (bp s₀) + BitVec.ofNat 64 (64 * i) = a
  rw [show a + BitVec.ofNat 64 (4 * t) + 1 = a + BitVec.ofNat 64 (4 * t + 1) from Offset.add_add _ _ 1,
    show a + BitVec.ofNat 64 (4 * t + 1) + 1 = a + BitVec.ofNat 64 (4 * t + 2) from Offset.add_add _ _ 1,
    show a + BitVec.ofNat 64 (4 * t + 2) + 1 = a + BitVec.ofNat 64 (4 * t + 3) from Offset.add_add _ _ 1]

theorem work_sub (p : BitVec 32) : Region.Sub (workRegion p) ⟨State.addr p, 112⟩ :=
  Region.sub_prefix (by bdd_omega)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (enter_ok hL.r3 (by rw [hL.wr]; exact hp.out_ptr) hL.regs)
    fun s₁ ⟨hv₁, hm₁, hr0₁, hr1₁, hr3₁, hrd₁, hwr₁⟩ => ?_)
  obtain hf₁ : Frame [ctlR s₀] s.mem s₁.mem := by
    rw [hm₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hp.ptr_contains
  obtain hwin : ∀ r' ∈ [workRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (work_sub _)
  obtain hblk : ∀ m, Frame [workRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      rev (m.readW (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 32) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide),
      hf₁.readW (hp.blk_contains hi ht) hp.blk_ctl (by decide),
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word hp hi ht
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) _ (scr s₀) s₁ hp.scr_fits (hr1₁.trans hL.r1)
    (hr3₁.trans hL.r3)
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 64 (Nat.le_refl _))
    fun s₂ hR => ?_)
  obtain hst : ∀ r' ∈ [workRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (work_sub _)
  obtain hr0₂ : s₂.gpr .r0 = st s₀ := hR.r0.trans (hr0₁.trans hL.r0)
  obtain hr3₂ : s₂.gpr .r3 = scr s₀ := hR.r3.trans (hr3₁.trans hL.r3)
  obtain hrd₂ : s₂.rd = s₀.rd := by rw [hR.rd, hrd₁, hL.rd]
  obtain hwr₂ : s₂.wr = s₀.wr := by rw [hR.wr, hwr₁, hL.wr]
  rw [WP.block_append_iff]
  refine WP.mono (update_ok hp _ (stateAt s.mem (State.addr (st s₀))) (regs_of_vars hR.vars) hr0₂
    hrd₂ hwr₂ fun k hk => ?_) fun s₃ ⟨hm₃, hregs₃, hr0₃, hr3₃, hrd₃, hwr₃⟩ => ?_
  · rw [hR.frame.readW (contains_sub (by bdd_omega) (by bdd_omega) (hp.stAddr_eq hk)) hst (by decide),
      hf₁.readW (contains_sub (by bdd_omega) (by bdd_omega) (hp.stAddr_eq hk)) hp.st_ctl (by decide),
      stateAt_get hp _ hk]
  obtain hf₃ : Frame [stR s₀] s₂.mem s₃.mem := by
    rw [hm₃]; exact frame_writeState hp (Frame.refl _ _) _
  obtain hptr : s₃.mem.readW (ptrAddr s₀) 32 = blkAddr s₀ i := by
    rw [hf₃.readW hp.ptr_contains hp.ctl_st (by decide),
      hR.frame.readW hp.ptr_contains (ctl_work _) (by decide), hm₁, Mem.readW_writeW_self32, hL.r1]
  obtain hcnt : s₃.mem.readW (cntAddr s₀) 32 = BitVec.ofNat 32 (nb s₀ - i) := by
    rw [hf₃.readW hp.cnt_contains hp.ctl_st (by decide),
      hR.frame.readW hp.cnt_contains (ctl_work _) (by decide), hm₁,
      Mem.readW_writeW_sep hp.cnt_ptr_sep (by decide), hL.cnt]
  refine WP.mono (advance_ok (hr3₃.trans hr3₂) (by rw [hrd₃, hwr₃, hrd₂, hwr₂]; exact hp.in_ptr)
    (by rw [hrd₃, hwr₃, hrd₂, hwr₂]; exact hp.in_cnt) (by rw [hwr₃, hwr₂]; exact hp.out_cnt) hptr hcnt)
    fun s₄ ⟨hr1₄, hz₄, hm₄, hk₄, hrd₄, hwr₄⟩ => ?_
  obtain hf₄ : Frame [ctlR s₀] s₃.mem s₄.mem := by
    rw [hm₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hp.cnt_contains
  obtain hnb : nb s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
  obtain hr2 : BitVec.ofNat 32 (nb s₀ - i) - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      Offset.ofNat_sub_ofNat (by bdd_omega), Nat.sub_sub]
  obtain toScr : ∀ {R : Region}, Region.Sub R (scrR s₀) → ∀ {m m' : Mem}, Frame [R] m m' →
      Frame [stR s₀, scrR s₀] m m' := fun hsub _ _ hf =>
    hf.sub fun r hr => ⟨scrR s₀, by simp, by rw [List.mem_singleton.mp hr]; exact hsub⟩
  obtain hframe : Frame [stR s₀, scrR s₀] s₀.mem s₄.mem :=
    (((hL.frame.trans (toScr (ctl_sub _) hf₁)).trans (toScr (work_sub _) hR.frame)).trans
      (hf₃.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)).trans (toScr (ctl_sub _) hf₄)
  obtain hstate₃ : stateAt s₃.mem (State.addr (st s₀)) =
      compressBlocks (H₀ s₀) s₀.mem (State.addr (bp s₀)) (i + 1) := by
    rw [hm₃, stateAt_writeState hp, compressBlocks_succ, ← hL.state]
    rfl
  obtain hstate : stateAt s₄.mem (State.addr (st s₀)) =
      compressBlocks (H₀ s₀) s₀.mem (State.addr (bp s₀)) (i + 1) :=
    (stateAt_frame hp hf₄ hp.st_ctl).trans hstate₃
  obtain hcommon : ∀ j, j = i + 1 → Common s₀ j s₄ := by
    rintro j rfl
    refine ⟨by rw [hk₄ .r0 (by decide) (by decide), hr0₃, hr0₂],
      by rw [hk₄ .r3 (by decide) (by decide), hr3₃, hr3₂],
      by rw [hrd₄, hrd₃, hrd₂], by rw [hwr₄, hwr₃, hwr₂], hframe, hstate, ?_⟩
    exact saved_frame hp (saved_frame hp (saved_frame hp (saved_frame hp hL.saved (.inr (.inr hf₁)))
      (.inl hR.frame)) (.inr (.inl hf₃))) (.inr (.inr hf₄))
  obtain hev : eval .ne s₄ = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, hz₄, hr2]
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
      { hcommon _ rfl with r1 := ?_, cnt := ?_, regs := ?_ }⟩
    · rw [hr1₄]
      exact (Offset.add_add _ _ 64).trans
        (congrArg (bp s₀ + ·) (congrArg (BitVec.ofNat _) (by bdd_omega)))
    · rw [hm₄, Mem.readW_writeW_self32, hr2]
    · rw [stateAt_frame hp hf₄ hp.st_ctl, hm₃, stateAt_writeState hp]
      exact hregs₃.keep hk₄

/-! ## Prologue and epilogue -/

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (State.addr (scr s₀)) s₀.gpr saved

theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save ++ ([.cmp .r2 (.imm 0)] : List Instr))) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.z = (s₀.gpr .r2 - 0 == 0) :=
  Spill.save_slots_ok saved_slots (Nat.le_trans (Nat.add_le_add_left (by decide : 104 ≤ 112) _) hp.scr_fits) (fun _ _ hd => hp.out_save (by bdd_omega))
    (WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩⟩)

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
    rw [(saveMem_frame s₀).readW (contains_sub (len := 32) (off := 4 * k) (by bdd_omega) (by bdd_omega)
      (hp.stAddr_eq hk))
      (by simpa using hp.st_scr) (by decide), ← stateAt_get hp _ hk]
    rfl

/-- Before the first block: the count goes to the scratch buffer and the hash
value to the registers. -/
theorem start_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (hc : Common s₀ 0 s₁)
    (hr1 : s₁.gpr .r1 = bp s₀) (hr2 : s₁.gpr .r2 = s₀.gpr .r2) :
    WP isa (.block start) s₁ (LInv s₀ 0) := by
  obtain hout : InRegions s₁.wr (State.addr (s₁.gpr .r3 + BitVec.ofNat 32 cntSlot)) 4 := by
    rw [hc.wr, hc.r3]; exact hp.out_cnt
  refine WP.block_cons_iff.mpr ⟨_, exec_str (by decide) hout, ?_⟩
  rw [hc.r3, hr2]
  obtain hf : Frame [ctlR s₀] s₁.mem (s₁.mem.writeW (cntAddr s₀) (s₀.gpr .r2)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hp.cnt_contains
  refine WP.mono (load_ok hp (s := { s₁ with mem := s₁.mem.writeW (cntAddr s₀) (s₀.gpr .r2) }) hc.r0
    hc.rd hc.wr) fun s₂ ⟨hregs, hr0, hr1', hr3, hrd, hwr, hm⟩ => ?_
  refine { r0 := hr0.trans hc.r0, r3 := hr3.trans hc.r3, rd := hrd.trans hc.rd, wr := hwr.trans hc.wr,
           frame := ?_, state := ?_, saved := ?_, r1 := ?_, cnt := ?_, regs := ?_ }
  · rw [hm]
    exact hc.frame.trans (hf.sub fun r hr =>
      ⟨scrR s₀, by simp, by rw [List.mem_singleton.mp hr]; exact ctl_sub _⟩)
  · rw [hm]; exact (stateAt_frame hp hf hp.st_ctl).trans hc.state
  · rw [hm]; exact saved_frame hp hc.saved (.inr (.inr hf))
  · rw [hr1', hr1]; simp [blkAddr]
  · rw [hm]
    show (s₁.mem.writeW (cntAddr s₀) (s₀.gpr .r2)).readW (cntAddr s₀) 32 = _
    rw [Mem.readW_writeW_self32]; simp [nb]
  · rw [hm]; exact hregs

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha256.compressArm.post s₀ s' := by
  rw [restore, ← List.append_nil (saved.map _)]
  refine Spill.restore_slots_ok saved_slots (by decide) (g := s₀.gpr) (by rw [hc.r3]; have := hp.scr_fits; omega_using [this])
    (fun _ _ hd => by rw [hc.rd, hc.wr, hc.r3]; exact hp.in_save (by bdd_omega)) (by rw [hc.r3]; exact hc.saved)
    fun s' hs _ hm _ _ _ => WP.block_nil ⟨Spill.restored_of hs (by decide), (congrArg (stateAt · _) hm).trans hc.state⟩

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha256.compressArm.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ ⟨hg, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => restore_ok hp hc)
  obtain hc₀ := common_zero hp hg hrd hwr hm
  refine WP.ite (s₀.gpr .r2 - 0 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    refine WP.seq (WP.mono (start_ok hp hc₀ (by rw [hg]) (by rw [hg])) fun s₂ hL₀ => ?_)
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    obtain hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by bdd_omega, i + 1, rfl, hi', hL'⟩
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
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 112⟩]

/-! ## Constant time

The block pointer and the count of blocks come back from the scratch buffer,
so the taint analysis follows the buffer: the two writable regions, whose
addresses are in `r0` and `r3`. -/

/-- The initial taint: `r0`–`r3` are public, and `r0` and `r3` are the
addresses of the hash value and of the scratch buffer. -/
private def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [32, 112],
    bases := [(.r0, 0), (.r3, 1)] }

private theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega_arith)

private theorem wf₀ {s : State} (hp : Pre s) : VG.Arm.Taint.Wf τ₀ s := by
  obtain hst := hp.st_fits; have hsc := hp.scr_fits
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩, ?_,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega_using [hst, hsc]
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, hp.wr]

private theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha256.compressArm.pre s₁)
    (h₂ : Proof.Sha256.compressArm.pre s₂) (hpub : Proof.Sha256.compressArm.pub s₁ s₂) :
    VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3⟩ := hpub
  obtain hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> first | exact p0 | exact p1 | exact p2 | exact p3
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scrR, st, scr, p0, p3]

theorem compress_verified :
    Verified Arm.target Impl.Sha256.Arm.compress Proof.Sha256.compressArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
      (by taint_decide)
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_, by decide, by decide, by decide⟩ <;>
    first
    | exact Offset.disjoint_of_le (by decide) (by decide)
    | exact Region.Disjoint.symm (Offset.disjoint_of_le (by decide) (by decide))

end VG.Proof.Sha256.Arm
