import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.Gcm.Arm
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Straight
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Bitslice.Sym
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Gcm.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.Arm.Step`. -/
section

/-!
# GHASH on ARMv7: the steps of Algorithm 1

What the instructions of a step (`Impl.Gcm.Arm.step`) compute on the four
words of a 128-bit value, stated on the whole value; a byte of `x` (8 steps);
and the 16 bytes.
-/

namespace VG.Proof.Gcm.Arm

open VG VG.Arm VG.Impl.Gcm.Arm VG.Proof.Gcm
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg op2_lsl wp_mov wp_add wp_sub wp_cmp wp_ldrb)
open VG.Spec.Gcm (Block)

/-! ## Four words as a block -/

/-- Four words, the most significant first. -/
def w4 (a b c d : BitVec 32) : VG.Spec.Gcm.Block := a ++ b ++ c ++ d

theorem getLsbD_w4 (a b c d : BitVec 32) (i : Nat) :
    (VG.Proof.Gcm.Arm.w4 a b c d).getLsbD i =
      if i < 32 then d.getLsbD i else if i < 64 then c.getLsbD (i - 32)
      else if i < 96 then b.getLsbD (i - 64) else a.getLsbD (i - 96) := by
  simp only [VG.Proof.Gcm.Arm.w4, BitVec.getLsbD_append]
  repeat' split
  all_goals first | omega | rfl

/-- `x >>> 31 − 1` is all ones if the top bit of `x` is clear, and zero otherwise. -/
theorem neg_top (x : BitVec 32) :
    x >>> 31 - 1 = if (!x.msb) = true then BitVec.allOnes 32 else 0 := by
  have h : x >>> 31 = if x.msb then 1 else 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_ushiftRight, BitVec.msb_eq_getLsbD_last]
    rcases (by omega : i = 0 ∨ 0 < i) with h | h
    · subst h; cases x.getLsbD (32 - 1) <;> simp
    · simp only [show 31 + i ≥ 32 by omega, BitVec.getLsbD_of_ge]
      split <;> simp [BitVec.getLsbD_one, show i ≠ 0 by omega]
  rw [h]; cases x.msb <;> decide

/-- `((v ∧ 1) ⊕ 1) − 1` is all ones if the lowest bit of `v` is set, and zero otherwise. -/
theorem lsb_mask (v : BitVec 32) :
    (v &&& 1 ^^^ 1) - 1 = if v.getLsbD 0 then BitVec.allOnes 32 else 0 := by
  have h : v &&& 1 = if v.getLsbD 0 then 1 else 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and]
    rcases (by omega : i = 0 ∨ 0 < i) with h | h
    · subst h; cases v.getLsbD 0 <;> simp
    · split <;> simp [BitVec.getLsbD_one, show i ≠ 0 by omega]
  rw [h]; cases v.getLsbD 0 <;> decide

theorem w4_xor (a b c d a' b' c' d' : BitVec 32) :
    VG.Proof.Gcm.Arm.w4 a b c d ^^^ VG.Proof.Gcm.Arm.w4 a' b' c' d' = VG.Proof.Gcm.Arm.w4 (a ^^^ a') (b ^^^ b') (c ^^^ c') (d ^^^ d') := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_xor, VG.Proof.Gcm.Arm.getLsbD_w4, VG.Proof.Gcm.Arm.getLsbD_w4, VG.Proof.Gcm.Arm.getLsbD_w4]
  by_cases h1 : i < 32 <;> by_cases h2 : i < 64 <;> by_cases h3 : i < 96 <;>
    simp [h1, h2, h3, BitVec.getLsbD_xor]

theorem mask_z4 (z0 z1 z2 z3 v0 v1 v2 v3 : BitVec 32) (c : Bool) :
    VG.Proof.Gcm.Arm.w4 (z0 ^^^ (v0 &&& if c then BitVec.allOnes 32 else 0))
        (z1 ^^^ (v1 &&& if c then BitVec.allOnes 32 else 0))
        (z2 ^^^ (v2 &&& if c then BitVec.allOnes 32 else 0))
        (z3 ^^^ (v3 &&& if c then BitVec.allOnes 32 else 0)) =
      if c then VG.Proof.Gcm.Arm.w4 z0 z1 z2 z3 ^^^ VG.Proof.Gcm.Arm.w4 v0 v1 v2 v3 else VG.Proof.Gcm.Arm.w4 z0 z1 z2 z3 := by
  cases c
  · simp
  · simp only [ite_true, BitVec.and_allOnes, VG.Proof.Gcm.Arm.w4_xor]

/-- The shifts and `eor`s of `V` shift the four words right by one bit. -/
theorem shr4 (a b c d : BitVec 32) :
    VG.Proof.Gcm.Arm.w4 (a >>> 1) (b >>> 1 ^^^ a <<< 31) (c >>> 1 ^^^ b <<< 31) (d >>> 1 ^^^ c <<< 31) =
      VG.Proof.Gcm.Arm.w4 a b c d >>> 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, VG.Proof.Gcm.Arm.getLsbD_w4, VG.Proof.Gcm.Arm.getLsbD_w4]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  rcases (by omega : i < 31 ∨ i = 31 ∨ (32 ≤ i ∧ i < 63) ∨ i = 63 ∨ (64 ≤ i ∧ i < 95) ∨ i = 95 ∨
    (96 ≤ i ∧ i < 127) ∨ i = 127) with h | h | h | h | h | h | h | h
  · simp [h, show 1 + i < 32 by omega, show i < 32 by omega]
  · subst h; simp
  · simp [show ¬ i < 32 by omega, show i < 64 by omega, show 1 + i < 64 by omega,
      show ¬ 1 + i < 32 by omega, show i - 32 < 31 by omega, show 1 + (i - 32) = 1 + i - 32 by omega]
  · subst h; simp
  · simp [show ¬ i < 64 by omega, show i < 96 by omega, show 1 + i < 96 by omega,
      show ¬ 1 + i < 64 by omega, show ¬ i < 32 by omega, show ¬ 1 + i < 32 by omega,
      show i - 64 < 31 by omega, show 1 + (i - 64) = 1 + i - 64 by omega]
  · subst h; simp
  · simp [show ¬ i < 96 by omega, show ¬ 1 + i < 96 by omega, show ¬ i < 64 by omega,
      show ¬ 1 + i < 64 by omega, show ¬ i < 32 by omega, show ¬ 1 + i < 32 by omega,
      show 1 + (i - 96) = 1 + i - 96 by omega]
  · subst h; simp

theorem R_eq4 : Spec.Gcm.R = VG.Proof.Gcm.Arm.w4 0xE1000000 0 0 0 := by decide

theorem update_v4 (v0 v1 v2 v3 : BitVec 32) :
    VG.Proof.Gcm.Arm.w4 (v0 >>> 1 ^^^ ((if v3.getLsbD 0 then BitVec.allOnes 32 else 0) &&& 0xE1000000))
        (v1 >>> 1 ^^^ v0 <<< 31) (v2 >>> 1 ^^^ v1 <<< 31) (v3 >>> 1 ^^^ v2 <<< 31) =
      if (VG.Proof.Gcm.Arm.w4 v0 v1 v2 v3).getLsbD 0 then (VG.Proof.Gcm.Arm.w4 v0 v1 v2 v3 >>> 1) ^^^ Spec.Gcm.R
      else VG.Proof.Gcm.Arm.w4 v0 v1 v2 v3 >>> 1 := by
  have h0 : (VG.Proof.Gcm.Arm.w4 v0 v1 v2 v3).getLsbD 0 = v3.getLsbD 0 := by rw [VG.Proof.Gcm.Arm.getLsbD_w4]; rfl
  rw [h0, ← VG.Proof.Gcm.Arm.shr4, VG.Proof.Gcm.Arm.R_eq4]
  cases v3.getLsbD 0
  · simp
  · simp only [ite_true, BitVec.allOnes_and, VG.Proof.Gcm.Arm.w4_xor]
    simp

/-! ## One step -/

/-- `Z` and `V` in a state. -/
def zvOf (s : State) : VG.Spec.Gcm.Block × VG.Spec.Gcm.Block :=
  (VG.Proof.Gcm.Arm.w4 (s.gpr (Z 0)) (s.gpr (Z 1)) (s.gpr (Z 2)) (s.gpr (Z 3)),
   VG.Proof.Gcm.Arm.w4 (s.gpr (V 0)) (s.gpr (V 1)) (s.gpr (V 2)) (s.gpr (V 3)))

/-- The registers a step does not write. -/
def stepKeep : List Reg := [.r1, .r12, .lr]

set_option simprocs false in
theorem step_ok (x : VG.Spec.Gcm.Block) (k : Nat) (s : State) (xr : BitVec 32)
    (hx : s.gpr XR = xr) (hmsb : xr.msb = !(x.getMsbD k)) :
    WP isa (.block VG.Impl.Gcm.Arm.step) s fun s' =>
      s'.gpr XR = xr <<< 1 ∧ VG.Proof.Gcm.Arm.zvOf s' = mulStep x (VG.Proof.Gcm.Arm.zvOf s) k ∧
      (∀ r ∈ VG.Proof.Gcm.Arm.stepKeep, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  subst hx
  simp only [XR] at hmsb ⊢
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Impl.Gcm.Arm.step, XR, Z, V, VG.Impl.Gcm.Arm.M, T, runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, State.setReg, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ?_, trivial⟩
  · simp only [VG.Proof.Gcm.Arm.zvOf, mulStep, Z, V]
    simp (config := {decide := true}) only [ite_true, ite_false]
    rw [VG.Proof.Gcm.Arm.neg_top, hmsb, Bool.not_not, VG.Proof.Gcm.Arm.mask_z4, VG.Proof.Gcm.Arm.lsb_mask, VG.Proof.Gcm.Arm.update_v4]
  · intro r hr
    simp only [VG.Proof.Gcm.Arm.stepKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp (config := {decide := true}) only [ite_false]

/-! ## A byte of `x` -/

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2}
    {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho])
    (k _ (Upd.setReg _ _ _))

theorem ff_bit : ∀ u < 8, (0xFF : BitVec 32).getLsbD u = true := by decide

/-- The top bit of the inverted byte, shifted left by `t`, is the complement of bit `t` of the byte
(from the left). -/
theorem xr_msb (b : BitVec 8) {t : Nat} (ht : t < 8) :
    ((b.setWidth 32 ^^^ 0xFF) <<< 24 <<< t).msb = !(b.getMsbD t) := by
  have e : 32 - 1 - t - 24 = 7 - t := by omega
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, BitVec.getMsbD_eq_getLsbD, e, VG.Proof.Gcm.Arm.ff_bit _ (by omega)]
  simp [show ¬ 32 - 1 < t by omega, show ¬ 32 - 1 - t < 24 by omega, ht,
    show 31 - t < 32 by omega, show 7 - t < 32 by omega]

/-- The block `x` whose bits the steps use: its bytes at `y`. -/
structure Bytes (x : VG.Spec.Gcm.Block) (y : BitVec 32) (sB : State) : Prop where
  fit : y.toNat + 16 ≤ 2 ^ 32
  inr : (⟨State.addr y, 16⟩ : Region) ∈ sB.rd ++ sB.wr
  bits : ∀ j < 16, ∀ t < 8, (sB.mem (State.addr y + BitVec.ofNat 64 j)).getMsbD t = x.getMsbD (8 * j + t)

/-- After the bytes `0 … j − 1` of `x • h`, from the state `sB`. -/
structure Inner (x h : VG.Spec.Gcm.Block) (y : BitVec 32) (sB : State) (j : Nat) (s : State) : Prop where
  zv : VG.Proof.Gcm.Arm.zvOf s = mulSteps x h (8 * j)
  xp : s.gpr XP = y + BitVec.ofNat 32 j
  yp : s.gpr YP = y
  sb : s.gpr SB = sB.gpr SB
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp

theorem zvOf_eq {s s' : State} (h : ∀ r, r ≠ XR → r ≠ XP → r ≠ T → r ≠ VG.Impl.Gcm.Arm.M → s'.gpr r = s.gpr r) :
    VG.Proof.Gcm.Arm.zvOf s' = VG.Proof.Gcm.Arm.zvOf s := by
  simp only [VG.Proof.Gcm.Arm.zvOf, Z, V]
  rw [h .r2 (by decide) (by decide) (by decide) (by decide), h .r3 (by decide) (by decide) (by decide) (by decide),
    h .r4 (by decide) (by decide) (by decide) (by decide), h .r5 (by decide) (by decide) (by decide) (by decide),
    h .r6 (by decide) (by decide) (by decide) (by decide), h .r7 (by decide) (by decide) (by decide) (by decide),
    h .r8 (by decide) (by decide) (by decide) (by decide), h .r9 (by decide) (by decide) (by decide) (by decide)]

theorem beq_16 {j : Nat} (hj : j < 16) :
    (BitVec.ofNat 32 (j + 1) - 16 == 0) = decide (j + 1 = 16) := by
  by_cases h : j + 1 = 16
  · rw [h]; rfl
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro h'
    bv_omega_arith

theorem byte_ok {x h : VG.Spec.Gcm.Block} {y : BitVec 32} {sB : State} (hB : VG.Proof.Gcm.Arm.Bytes x y sB) {j : Nat} (hj : j < 16)
    {s : State} (hs : VG.Proof.Gcm.Arm.Inner x h y sB j s) :
    WP isa (.block steps) s fun s' => VG.Proof.Gcm.Arm.Inner x h y sB (j + 1) s' ∧ s'.z = decide (j + 1 = 16) := by
  have hfit := hB.fit
  rw [steps, WP.block_append_iff, WP.block_append_iff]
  have ha : State.addr (s.gpr XP + BitVec.ofNat 32 0) = State.addr y + BitVec.ofNat 64 j := by
    rw [hs.xp, BitVec.add_zero, addr_add (by omega)]
  have hin : InRegions (s.rd ++ s.wr) (State.addr y + BitVec.ofNat 64 j) 1 := by
    rw [hs.rd, hs.wr, ← addr_add (by omega)]; exact Straight.in_off hB.inr hfit (by omega) (by decide)
  refine wp_ldrb (by decide) ha hin fun s₁ u₁ => ?_
  refine VG.Proof.Gcm.Arm.wp_eor (op2_imm (by decide)) fun s₂ u₂ => wp_mov (op2_lsl (by decide)) fun s₃ u₃ =>
    wp_add (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ?_
  let b : BitVec 8 := sB.mem (State.addr y + BitVec.ofNat 64 j)
  have hx₄ : s₄.gpr XR = (b.setWidth 32 ^^^ 0xFF) <<< 24 := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr, hs.mem]
  have g₄ : ∀ r, r ≠ XR → r ≠ XP → s₄.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₄.other _ h2, u₃.other _ h1, u₂.other _ h1, u₁.other _ h1]
  have xp₄ : s₄.gpr XP = y + BitVec.ofNat 32 (j + 1) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hs.xp]
    bv_omega_arith
  have zv₄ : VG.Proof.Gcm.Arm.zvOf s₄ = VG.Proof.Gcm.Arm.zvOf s := VG.Proof.Gcm.Arm.zvOf_eq fun r h1 h2 _ _ => g₄ r h1 h2
  let Inv : Nat → State → Prop := fun t s' =>
    s'.gpr XR = (b.setWidth 32 ^^^ 0xFF) <<< 24 <<< t ∧ VG.Proof.Gcm.Arm.zvOf s' = mulSteps x h (8 * j + t) ∧
    s'.gpr XP = y + BitVec.ofNat 32 (j + 1) ∧ s'.gpr YP = y ∧ s'.gpr SB = sB.gpr SB ∧
    s'.mem = sB.mem ∧ s'.rd = sB.rd ∧ s'.wr = sB.wr ∧ s'.sp = sB.sp
  have hI₀ : Inv 0 s₄ := by
    refine ⟨by rw [hx₄, BitVec.shiftLeft_zero], by rw [zv₄, hs.zv, Nat.add_zero], xp₄, by rw [g₄ _ (by decide) (by decide), hs.yp],
      by rw [g₄ _ (by decide) (by decide), hs.sb], ?_, ?_, ?_, ?_⟩
    · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.mem]
    · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, hs.rd]
    · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hs.wr]
    · rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, hs.sp]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) Inv (fun t s' ht hI => ?_) 8 (Nat.le_refl _) s₄ hI₀)
    fun s₅ hI₅ => ?_
  · obtain ⟨hx, hzv, hxp, hyp, hsb, hm, hrd, hwr, hsp⟩ := hI
    refine WP.mono (VG.Proof.Gcm.Arm.step_ok x (8 * j + t) s' _ hx ?_) fun s'' ⟨hx', hzv', hk, hm', hrd', hwr', hsp'⟩ => ?_
    · rw [VG.Proof.Gcm.Arm.xr_msb _ ht, ← hB.bits j hj t ht]
    · refine ⟨by rw [hx', BitVec.shiftLeft_add], by rw [hzv', hzv, ← Nat.add_assoc, mulSteps_succ],
        (hk XP (by decide)).trans hxp, (hk YP (by decide)).trans hyp,
        (hk SB (by decide)).trans hsb, hm'.trans hm, hrd'.trans hrd, hwr'.trans hwr,
        hsp'.trans hsp⟩
  · obtain ⟨-, hzv, hxp, hyp, hsb, hm, hrd, hwr, hsp⟩ := hI₅
    refine wp_sub (op2_reg _ _) fun s₆ u₆ => wp_cmp (op2_imm (by decide)) fun s₇ f₇ z₇ => WP.block_nil ?_
    have t₆ : s₆.gpr T = BitVec.ofNat 32 (j + 1) := by
      rw [u₆.gpr, hxp, hyp]; bv_omega_arith
    have g₇ : ∀ r, r ≠ T → s₇.gpr r = s₅.gpr r := fun r hr => by rw [f₇.gpr, u₆.other _ hr]
    refine ⟨⟨?_, by rw [g₇ _ (by decide)]; exact hxp, by rw [g₇ _ (by decide)]; exact hyp,
      by rw [g₇ _ (by decide)]; exact hsb, by rw [f₇.mem, u₆.mem]; exact hm,
      by rw [f₇.rd, u₆.rd]; exact hrd, by rw [f₇.wr, u₆.wr]; exact hwr,
      by rw [f₇.sp, u₆.sp]; exact hsp⟩, ?_⟩
    · rw [VG.Proof.Gcm.Arm.zvOf_eq (fun r _ _ h3 _ => g₇ r h3), hzv, Nat.mul_succ]
    · rw [z₇, t₆, VG.Proof.Gcm.Arm.beq_16 hj]

/-! ## The 128 steps -/

theorem mul_ok {x h : VG.Spec.Gcm.Block} {y : BitVec 32} {sB : State} (hB : VG.Proof.Gcm.Arm.Bytes x y sB) {s : State}
    (hs : VG.Proof.Gcm.Arm.Inner x h y sB 0 s) : WP isa (.loop (.block steps) .ne) s (VG.Proof.Gcm.Arm.Inner x h y sB 16) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = 16 - j ∧ j < 16 ∧ VG.Proof.Gcm.Arm.Inner x h y sB j s)
    (fun m s ⟨j, hm, hj, hs⟩ => WP.mono (VG.Proof.Gcm.Arm.byte_ok hB hj hs) fun s' ⟨hs', hz⟩ => ?_) _ s
    ⟨0, rfl, by decide, hs⟩
  subst hm
  by_cases hl : j + 1 = 16
  · exact .inl ⟨(VG.Proof.MdStream.Arm.eval_ne s').trans (by rw [hz, hl]; rfl), hl ▸ hs'⟩
  · exact .inr ⟨(VG.Proof.MdStream.Arm.eval_ne s').trans (by rw [hz, decide_eq_false hl]; rfl), _,
      by omega, j + 1, rfl, by omega, hs'⟩

end VG.Proof.Gcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.Arm.Ghash`. -/
section

/-!
# GHASH on ARMv7: the whole function

The saves and restores of the callee-saved registers are checked by
evaluation in the naming domain (`Bitslice.names`); a block is `load`
(`Y ⊕ X` over `Y`, and `V := H`), the 16 bytes of steps (`Step.lean`) and
`store`.
-/

namespace VG.Proof.Gcm

open Spec.Gcm

open VG.Arm in
/-- 32-bit ARM contract for `vg_ghash(h = r0, y = r1, data = r2, n = r3,
scratch = [sp])`: replaces the block `Y` at `y` with `GHASH_H` continued from
`Y` over the `n` blocks at `data`, where `H` is the block at `h`.

The code may read `h` (16 bytes), `data` (`16 n` bytes) and the argument on
the stack (4 bytes at `sp`), and read and write `y` (16 bytes) and `scratch`
(256 bytes, whose contents on exit are unspecified). `y` and `scratch` may
not overlap each other, the other buffers or the stack argument, and none
may wrap around the end of the (32-bit) address space. The pointers and `n`
are public; `H`, `Y` and the data are secret. -/
def ghashArm : Contract Arm.isa where
  pre s :=
    let h : Region := ⟨State.addr (s.gpr .r0), 16⟩
    let y : Region := ⟨State.addr (s.gpr .r1), 16⟩
    let data : Region := ⟨State.addr (s.gpr .r2), 16 * (s.gpr .r3).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 256⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [h, data, args] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧
    data.Disjoint scratch ∧ y.Disjoint args ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + 16 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 16 ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + 16 * (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + 256 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' :=
    VG.Spec.Gcm.blockAt s'.mem (State.addr (s.gpr .r1)) =
      ghashFrom (VG.Spec.Gcm.blockAt s.mem (State.addr (s.gpr .r0))) (VG.Spec.Gcm.blockAt s.mem (State.addr (s.gpr .r1)))
        (VG.Spec.Gcm.blocksAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.Gcm

namespace VG.Proof.Gcm.Arm

open VG VG.Arm VG.Impl.Gcm.Arm VG.Proof.Gcm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_sub wp_subs wp_cmp wp_rev
  wp_ldr wp_str wp_ldrSp eval_ne)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## Blocks as words -/

/-- Bit `t` (from the left) of byte `j` of the block at `p`. -/
theorem blockAt_msb (m : Mem) (p : Addr) {j t : Nat} (hj : j < 16) (ht : t < 8) :
    (VG.Spec.Gcm.blockAt m p).getMsbD (8 * j + t) = (m (p + BitVec.ofNat 64 j)).getMsbD t := by
  rw [BitVec.getMsbD_eq_getLsbD, BitVec.getMsbD_eq_getLsbD, decide_eq_true (show 8 * j + t < 128 by omega),
    decide_eq_true ht, Bool.true_and, Bool.true_and,
    show 128 - 1 - (8 * j + t) = 8 * (15 - j) + (8 - 1 - t) by omega,
    Proof.Aes.blockAt_bit m p hj (by omega)]

/-- A block whose word `k` (little-endian) is `rev (W k)`. -/
theorem blockAt_w4 (m : Mem) (p : Addr) (W : Nat → BitVec 32)
    (h : ∀ k < 4, ∀ t < 4, m (p + BitVec.ofNat 64 (4 * k + t)) = (rev (W k)).extractLsb' (8 * t) 8) :
    VG.Spec.Gcm.blockAt m p = VG.Proof.Gcm.Arm.w4 (W 0) (W 1) (W 2) (W 3) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨j, b, hj, hb, rfl⟩ : ∃ j b, j < 16 ∧ b < 8 ∧ i = 8 * (15 - j) + b :=
    ⟨15 - i / 8, i % 8, by omega, by omega, by omega⟩
  rw [Proof.Aes.blockAt_bit m p hj hb]
  obtain ⟨k, t, hk, ht, rfl⟩ : ∃ k t, k < 4 ∧ t < 4 ∧ j = 4 * k + t :=
    ⟨j / 4, j % 4, by omega, by omega, by omega⟩
  rw [h k hk t ht, BitVec.getLsbD_extractLsb', decide_eq_true hb, Bool.true_and, rev_bit _ ht hb,
    VG.Proof.Gcm.Arm.getLsbD_w4]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; congr 1; omega
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]; congr 1; omega
  · rw [ite_eq_right (by omega), ite_eq_left (by omega)]; congr 1; omega
  · rw [ite_eq_left (by omega)]; congr 1; omega

theorem w4_zero : VG.Proof.Gcm.Arm.w4 0 0 0 0 = 0 := by decide

/-- Four loads and `rev`s read a block. -/
theorem blockAt_rev (m : Mem) (p : Addr) :
    VG.Spec.Gcm.blockAt m p = VG.Proof.Gcm.Arm.w4 (rev (m.readW p 32)) (rev (m.readW (p + BitVec.ofNat 64 4) 32))
      (rev (m.readW (p + BitVec.ofNat 64 8) 32)) (rev (m.readW (p + BitVec.ofNat 64 12) 32)) := by
  refine VG.Proof.Gcm.Arm.blockAt_w4 m p (fun k => rev (m.readW (p + BitVec.ofNat 64 (4 * k)) 32)) (fun k hk t ht => ?_)
    |>.trans ?_
  · rw [rev_rev, ← Mem.readW_byte _ _ ht, BitVec.ofNat_add, BitVec.add_assoc]
  · rw [show 4 * 0 = 0 from rfl, BitVec.add_zero]

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev hA : BitVec 32 := s₀.gpr .r0
abbrev yp : BitVec 32 := s₀.gpr .r1
abbrev dp : BitVec 32 := s₀.gpr .r2
abbrev nb : Nat := (s₀.gpr .r3).toNat
abbrev bp : BitVec 32 := stackArg s₀ 0
abbrev hR : Region := ⟨State.addr (VG.Proof.Gcm.Arm.hA s₀), 16⟩
abbrev yR : Region := ⟨State.addr (VG.Proof.Gcm.Arm.yp s₀), 16⟩
abbrev dR : Region := ⟨State.addr (VG.Proof.Gcm.Arm.dp s₀), 16 * VG.Proof.Gcm.Arm.nb s₀⟩
abbrev bR : Region := ⟨State.addr (VG.Proof.Gcm.Arm.bp s₀), 256⟩
abbrev aR : Region := ⟨stackArgAddr s₀ 0, 4⟩
abbrev H₀ : VG.Spec.Gcm.Block := VG.Spec.Gcm.blockAt s₀.mem (State.addr (VG.Proof.Gcm.Arm.hA s₀))
abbrev Y₀ : VG.Spec.Gcm.Block := VG.Spec.Gcm.blockAt s₀.mem (State.addr (VG.Proof.Gcm.Arm.yp s₀))

/-- Block `i`. -/
abbrev blk (i : Nat) : BitVec 32 := VG.Proof.Gcm.Arm.dp s₀ + BitVec.ofNat 32 (16 * i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Gcm.Arm.hR s₀, VG.Proof.Gcm.Arm.dR s₀, VG.Proof.Gcm.Arm.aR s₀]
  wr : s₀.wr = [VG.Proof.Gcm.Arm.yR s₀, VG.Proof.Gcm.Arm.bR s₀]
  dHY : (VG.Proof.Gcm.Arm.hR s₀).Disjoint (VG.Proof.Gcm.Arm.yR s₀)
  dHB : (VG.Proof.Gcm.Arm.hR s₀).Disjoint (VG.Proof.Gcm.Arm.bR s₀)
  dYD : (VG.Proof.Gcm.Arm.yR s₀).Disjoint (VG.Proof.Gcm.Arm.dR s₀)
  dYB : (VG.Proof.Gcm.Arm.yR s₀).Disjoint (VG.Proof.Gcm.Arm.bR s₀)
  dDB : (VG.Proof.Gcm.Arm.dR s₀).Disjoint (VG.Proof.Gcm.Arm.bR s₀)
  dYA : (VG.Proof.Gcm.Arm.yR s₀).Disjoint (VG.Proof.Gcm.Arm.aR s₀)
  dBA : (VG.Proof.Gcm.Arm.bR s₀).Disjoint (VG.Proof.Gcm.Arm.aR s₀)
  fitH : (VG.Proof.Gcm.Arm.hA s₀).toNat + 16 ≤ 2 ^ 32
  fitY : (VG.Proof.Gcm.Arm.yp s₀).toNat + 16 ≤ 2 ^ 32
  fitD : (VG.Proof.Gcm.Arm.dp s₀).toNat + 16 * VG.Proof.Gcm.Arm.nb s₀ ≤ 2 ^ 32
  fitB : (VG.Proof.Gcm.Arm.bp s₀).toNat + 256 ≤ 2 ^ 32
  fitSp : s₀.sp.toNat + 4 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : Proof.Gcm.ghashArm.pre s₀) : VG.Proof.Gcm.Arm.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-! ## Slots of the scratch buffer -/

/-- Slot `k` of the scratch buffer at `B`. -/
abbrev slot (B : Addr) (k : Nat) : Addr := B + BitVec.ofNat 64 (4 * k)

/-- The registers saved in the slots, in order: the callee-saved ones, then
`h`, `data` and `n`. -/
def greg : Nat → Reg
  | 0 => .r4 | 1 => .r5 | 2 => .r6 | 3 => .r7 | 4 => .r8 | 5 => .r9 | 6 => .r10 | 7 => .r11
  | 8 => .lr | 9 => .r0 | 10 => .r2 | _ => .r3

def gCfg : Straight.Cfg := { base := .r12, slots := 12, ext := .r12, exts := 0 }

/-- The stores of the prologue. -/
def gsaves : List Instr :=
  savedRegs.map (fun (r, k) => Instr.str r SB (4 * k)) ++
    [.str .r0 SB (4 * hSlot), .str .r2 SB (4 * dSlot), .str .r3 SB (4 * nSlot)]

/-- The loads of the epilogue. -/
def grestores : List Instr := savedRegs.map fun (r, k) => Instr.ldr r SB (4 * k)

theorem ghash_eq : ghash = .seq (.block (.ldrSp SB 0 :: (VG.Proof.Gcm.Arm.gsaves ++ ([.cmp .r3 (.imm 0)] : List Instr))))
    (.seq (.ite .eq (.block []) (.loop body .ne)) (.block VG.Proof.Gcm.Arm.grestores)) := rfl

def gSaveEnv : Straight.Env Nat :=
  { reg := fun r => (List.range 12).find? (fun i => VG.Proof.Gcm.Arm.greg i == r), slot := fun _ => none }

def gSavePost (e : Straight.Env Nat) : Bool := (List.range 12).all fun i => e.slot i == some i

theorem gsave_check :
    Straight.check (Bitslice.names 32) VG.Proof.Gcm.Arm.gCfg (fun _ => none) VG.Proof.Gcm.Arm.gsaves VG.Proof.Gcm.Arm.gSaveEnv VG.Proof.Gcm.Arm.gSavePost = true := by
  decide +kernel

def gRestoreEnv : Straight.Env Nat :=
  { reg := fun _ => none, slot := fun k => if k < 9 then some k else none }

def gRestorePost (e : Straight.Env Nat) : Bool := (List.range 9).all fun i => e.reg (VG.Proof.Gcm.Arm.greg i) == some i

theorem grestore_check :
    Straight.check (Bitslice.names 32) VG.Proof.Gcm.Arm.gCfg (fun _ => none) VG.Proof.Gcm.Arm.grestores VG.Proof.Gcm.Arm.gRestoreEnv VG.Proof.Gcm.Arm.gRestorePost = true := by
  decide +kernel

theorem gCfg_ok {s : State} {b : BitVec 32} (hw : (⟨State.addr b, 256⟩ : Region) ∈ s.wr)
    (hfit : b.toNat + 256 ≤ 2 ^ 32) (hb : s.gpr .r12 = b) : Straight.Ok VG.Proof.Gcm.Arm.gCfg s :=
  Straight.Ok.of_off (off := 0) hw hfit (by simp [VG.Proof.Gcm.Arm.gCfg, hb]) (by simp [VG.Proof.Gcm.Arm.gCfg]) rfl

theorem slot_addr {b : BitVec 32} (hfit : b.toNat + 256 ≤ 2 ^ 32) {k : Nat} (hk : k < 64) :
    State.addr (b + BitVec.ofNat 32 (4 * k)) = VG.Proof.Gcm.Arm.slot (State.addr b) k := addr_add (by omega)

/-- The callee-saved registers are in slots 0–8. -/
def GSaved (s₀ : State) (B : Addr) (m : Mem) : Prop :=
  ∀ i < 9, m.readW (VG.Proof.Gcm.Arm.slot B i) 32 = s₀.gpr (VG.Proof.Gcm.Arm.greg i)

theorem gsave_ok {s : State} {b : BitVec 32} (hw : (⟨State.addr b, 256⟩ : Region) ∈ s.wr)
    (hfit : b.toNat + 256 ≤ 2 ^ 32) (hb : s.gpr .r12 = b) :
    ∃ s', runBlock isa VG.Proof.Gcm.Arm.gsaves s = some s' ∧
      (∀ i < 12, s'.mem.readW (VG.Proof.Gcm.Arm.slot (State.addr b) i) 32 = s.gpr (VG.Proof.Gcm.Arm.greg i)) ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr b, 48⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := Straight.of_check _ _ _ VG.Proof.Gcm.Arm.gsave_check
  let V : Nat → BitVec 32 := fun i => s.gpr (VG.Proof.Gcm.Arm.greg i)
  have hrel : Straight.Rel (Bitslice.NameRel V) VG.Proof.Gcm.Arm.gCfg (fun _ => none) VG.Proof.Gcm.Arm.gSaveEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ hk _ => by simp [VG.Proof.Gcm.Arm.gCfg] at hk),
      (fun _ _ h => by cases h)⟩
    simp only [VG.Proof.Gcm.Arm.gSaveEnv] at h
    have h1 := List.find?_some h
    simp only [beq_iff_eq] at h1; subst h1; rfl
  obtain ⟨s', hs', p⟩ := Straight.run (Bitslice.names_sound V) (VG.Proof.Gcm.Arm.gCfg_ok hw hfit hb) hrel he
  refine ⟨s', hs', fun i hi => ?_, funext fun r => p.other r ?_, p.rd, p.wr, p.sp, ?_⟩
  · have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at this
    have h := p.rel.slot i i (by simp [VG.Proof.Gcm.Arm.gCfg]; omega) this
    rw [p.base] at h
    simp only [VG.Proof.Gcm.Arm.gCfg, hb] at h
    rw [← VG.Proof.Gcm.Arm.slot_addr hfit (by omega)]
    exact h
  · have : (gsaves.all fun i => dstOf i != some r) = true := by
      simp [VG.Proof.Gcm.Arm.gsaves, savedRegs, dstOf]
    simp [this]
  · have := p.frame
    simpa [Straight.slotRegion, VG.Proof.Gcm.Arm.gCfg, hb] using this

theorem grestore_ok {s₀ s : State} {b : BitVec 32} (hw : (⟨State.addr b, 256⟩ : Region) ∈ s.wr)
    (hfit : b.toNat + 256 ≤ 2 ^ 32) (hb : s.gpr .r12 = b) (hs : VG.Proof.Gcm.Arm.GSaved s₀ (State.addr b) s.mem) :
    ∃ s', runBlock isa VG.Proof.Gcm.Arm.grestores s = some s' ∧ (∀ i < 9, s'.gpr (VG.Proof.Gcm.Arm.greg i) = s₀.gpr (VG.Proof.Gcm.Arm.greg i)) ∧
      Frame [⟨State.addr b, 48⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := Straight.of_check _ _ _ VG.Proof.Gcm.Arm.grestore_check
  let V : Nat → BitVec 32 := fun i => s₀.gpr (VG.Proof.Gcm.Arm.greg i)
  have hrel : Straight.Rel (Bitslice.NameRel V) VG.Proof.Gcm.Arm.gCfg (fun _ => none) VG.Proof.Gcm.Arm.gRestoreEnv s := by
    refine ⟨(fun r a h => by cases h), fun k a hk h => ?_, (fun _ _ hk _ => by simp [VG.Proof.Gcm.Arm.gCfg] at hk),
      (fun _ _ h => by cases h)⟩
    simp only [VG.Proof.Gcm.Arm.gRestoreEnv] at h
    split at h
    · cases h
      rename_i hk'
      have := hs k hk'
      rw [← VG.Proof.Gcm.Arm.slot_addr hfit (by simp [VG.Proof.Gcm.Arm.gCfg] at hk; omega)] at this
      simp only [Bitslice.NameRel, VG.Proof.Gcm.Arm.gCfg, hb]
      exact this
    · cases h
  obtain ⟨s', hs', p⟩ := Straight.run (Bitslice.names_sound V) (VG.Proof.Gcm.Arm.gCfg_ok hw hfit hb) hrel he
  refine ⟨s', hs', fun i hi => ?_, ?_⟩
  · have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at this
    exact p.rel.reg _ i this
  · have := p.frame
    simpa [Straight.slotRegion, VG.Proof.Gcm.Arm.gCfg, hb] using this

/-! ## Addresses -/

theorem r_off (C : Addr) {L x n : Nat} (hL : L < 2 ^ 64) (h : x + n ≤ L) :
    (⟨C, L⟩ : Region).Contains (C + BitVec.ofNat 64 x) n := by
  simp only [Region.Contains]
  rw [show C + BitVec.ofNat 64 x - C = BitVec.ofNat 64 x by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega


namespace Pre
variable {s₀ : State} (hp : VG.Proof.Gcm.Arm.Pre s₀)
include hp

theorem blk_addr {i : Nat} (hi : i < VG.Proof.Gcm.Arm.nb s₀) :
    State.addr (VG.Proof.Gcm.Arm.blk s₀ i) = State.addr (VG.Proof.Gcm.Arm.dp s₀) + BitVec.ofNat 64 (16 * i) := by
  have := hp.fitD; exact addr_add (by omega)

theorem blk_fit {i : Nat} (hi : i < VG.Proof.Gcm.Arm.nb s₀) : (VG.Proof.Gcm.Arm.blk s₀ i).toNat + 16 ≤ 2 ^ 32 := by
  have := hp.fitD
  simp only [VG.Proof.Gcm.Arm.blk]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * i) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem blk_sub {i : Nat} (hi : i < VG.Proof.Gcm.Arm.nb s₀) : Region.Sub ⟨State.addr (VG.Proof.Gcm.Arm.blk s₀ i), 16⟩ (VG.Proof.Gcm.Arm.dR s₀) := by
  have := hp.fitD
  rw [hp.blk_addr hi]; exact VG.Proof.MdStream.Arm.sub_offset (by omega) (by omega)

theorem slot_in {k : Nat} (hk : 4 * k + 4 ≤ 256) :
    InRegions (s₀.rd ++ s₀.wr) (VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) k) 4 :=
  ⟨VG.Proof.Gcm.Arm.bR s₀, by rw [hp.wr]; simp, VG.Proof.Gcm.Arm.r_off _ (by decide) hk⟩

omit hp in
theorem slot_sub {k : Nat} (hk : 4 * k + 4 ≤ 256) :
    Region.Sub ⟨VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) k, 4⟩ (VG.Proof.Gcm.Arm.bR s₀) :=
  VG.Proof.MdStream.Arm.sub_offset (by omega) (by omega)

theorem slot_y {k : Nat} (hk : 4 * k + 4 ≤ 256) :
    Region.Disjoint ⟨VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) k, 4⟩ (VG.Proof.Gcm.Arm.yR s₀) :=
  hp.dYB.symm.sub_left (VG.Proof.Gcm.Arm.Pre.slot_sub hk)

theorem h_frame : ∀ r ∈ [VG.Proof.Gcm.Arm.yR s₀, ⟨State.addr (VG.Proof.Gcm.Arm.bp s₀), 48⟩], Region.Disjoint (VG.Proof.Gcm.Arm.hR s₀) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.dHY
  · exact hp.dHB.sub_right (Region.sub_prefix (by decide))

theorem blk_frame {i : Nat} (hi : i < VG.Proof.Gcm.Arm.nb s₀) :
    ∀ r ∈ [VG.Proof.Gcm.Arm.yR s₀, ⟨State.addr (VG.Proof.Gcm.Arm.bp s₀), 48⟩], Region.Disjoint ⟨State.addr (VG.Proof.Gcm.Arm.blk s₀ i), 16⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.dYD.symm.sub_left (hp.blk_sub hi)
  · exact (hp.dDB.sub_left (hp.blk_sub hi)).sub_right (Region.sub_prefix (by decide))

end Pre

/-! ## The loop invariant -/

/-- Before block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop where
  r1 : s.gpr YP = VG.Proof.Gcm.Arm.yp s₀
  sb : s.gpr SB = VG.Proof.Gcm.Arm.bp s₀
  hs : s.mem.readW (VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) hSlot) 32 = VG.Proof.Gcm.Arm.hA s₀
  ds : s.mem.readW (VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) dSlot) 32 = VG.Proof.Gcm.Arm.blk s₀ i
  ns : s.mem.readW (VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) nSlot) 32 = BitVec.ofNat 32 (VG.Proof.Gcm.Arm.nb s₀ - i)
  saved : VG.Proof.Gcm.Arm.GSaved s₀ (State.addr (VG.Proof.Gcm.Arm.bp s₀)) s.mem
  y : VG.Spec.Gcm.blockAt s.mem (State.addr (VG.Proof.Gcm.Arm.yp s₀)) =
    ghashFrom (VG.Proof.Gcm.Arm.H₀ s₀) (VG.Proof.Gcm.Arm.Y₀ s₀) (VG.Spec.Gcm.blocksAt s₀.mem (State.addr (VG.Proof.Gcm.Arm.dp s₀)) i)
  frame : Frame [VG.Proof.Gcm.Arm.yR s₀, ⟨State.addr (VG.Proof.Gcm.Arm.bp s₀), 48⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-! ## `load`: `Y ⊕ X` over `Y`, and `V := H` -/

/-- After `k` words of `Y ⊕ X` (the block `X` at `d`), from the state `s`. -/
structure XI (s : State) (y b d : BitVec 32) (k : Nat) (s' : State) : Prop where
  yp : s'.gpr YP = y
  sb : s'.gpr SB = b
  m : s'.gpr M = d
  bytes : ∀ j < 16, s'.mem (State.addr y + BitVec.ofNat 64 j) =
    if j < 4 * k then s.mem (State.addr y + BitVec.ofNat 64 j) ^^^ s.mem (State.addr d + BitVec.ofNat 64 j)
    else s.mem (State.addr y + BitVec.ofNat 64 j)
  frame : Frame [⟨State.addr y, 16⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem xor_chunk {s : State} {y b d : BitVec 32} (hyw : (⟨State.addr y, 16⟩ : Region) ∈ s.wr)
    (hfy : y.toNat + 16 ≤ 2 ^ 32)
    (hdin : ∀ k < 4, InRegions (s.rd ++ s.wr) (State.addr d + BitVec.ofNat 64 (4 * k)) 4)
    (hfd : d.toNat + 16 ≤ 2 ^ 32) (hyd : Region.Disjoint ⟨State.addr d, 16⟩ ⟨State.addr y, 16⟩)
    {k : Nat} (hk : k < 4) {s' : State} (hI : VG.Proof.Gcm.Arm.XI s y b d k s') :
    WP isa (.block [.ldr XR YP (4 * k), .ldr T M (4 * k), .dp .eor XR XR (.reg T), .str XR YP (4 * k)])
      s' (VG.Proof.Gcm.Arm.XI s y b d (k + 1)) := by
  have hy4 : State.addr (y + BitVec.ofNat 32 (4 * k)) = State.addr y + BitVec.ofNat 64 (4 * k) :=
    addr_add (by omega)
  have hd4 : State.addr (d + BitVec.ofNat 32 (4 * k)) = State.addr d + BitVec.ofNat 64 (4 * k) :=
    addr_add (by omega)
  refine wp_ldr (by omega) (by rw [hI.yp, hy4])
    (by rw [hI.rd, hI.wr, ← hy4]; exact Straight.in_off (List.mem_append_right _ hyw) hfy (by omega) (by decide))
    fun s₁ u₁ => ?_
  refine wp_ldr (by omega) (by rw [u₁.other _ (by decide), hI.m, hd4])
    (by rw [u₁.rd, u₁.wr, hI.rd, hI.wr]; exact hdin k hk) fun s₂ u₂ => ?_
  refine VG.Proof.Gcm.Arm.wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_str (by omega)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.yp, hy4])
    (by rw [u₃.wr, u₂.wr, u₁.wr, hI.wr, ← hy4]; exact Straight.in_off hyw hfy (by omega) (by decide))
    fun s₄ u₄ => WP.block_nil ?_
  have m₄ : s₄.mem = s'.mem.writeW (State.addr y + BitVec.ofNat 64 (4 * k))
      (s'.mem.readW (State.addr y + BitVec.ofNat 64 (4 * k)) 32 ^^^
        s'.mem.readW (State.addr d + BitVec.ofNat 64 (4 * k)) 32) := by
    rw [u₄.mem, u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₃.mem, u₂.mem, u₁.mem]
  have hD : ∀ j < 16, s'.mem (State.addr d + BitVec.ofNat 64 j) = s.mem (State.addr d + BitVec.ofNat 64 j) :=
    fun j hj => hI.frame.bytes (R := ⟨State.addr d, 16⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hyd) (by simp) hj
  refine ⟨?_, ?_, ?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.yp]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.sb]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.m]
  · rw [m₄]
    by_cases hjk : 4 * k ≤ j ∧ j < 4 * k + 4
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 4 ∧ j = 4 * k + t := ⟨j - 4 * k, by omega, by omega⟩
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, st_byte _ _ _ ht, BitVec.extractLsb'_xor,
        ← Mem.readW_byte _ _ ht, ← Mem.readW_byte _ _ ht, BitVec.add_assoc, BitVec.add_assoc,
        ← BitVec.ofNat_add, hI.bytes _ hj, hD _ hj, ite_eq_right (by omega),
        ite_eq_left (by omega)]
    · rw [writeW32_other _ (off_disjoint _ (by omega) (by omega) (by omega)), hI.bytes j hj]
      by_cases h : j < 4 * k
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega)]
  · rw [m₄]
    exact hI.frame.writeW (r := ⟨State.addr y, 16⟩) (by simp) _ (VG.Proof.Gcm.Arm.r_off _ (by decide) (by omega))
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp]

/-- After `k` words of `H` (at `h`, in the memory `mX`) loaded to `V`. -/
structure VI (mX : Mem) (h y b : BitVec 32) (base : State) (k : Nat) (s' : State) : Prop where
  m : s'.gpr M = h
  yp : s'.gpr YP = y
  sb : s'.gpr SB = b
  v : ∀ k' < k, s'.gpr (V k') = rev (mX.readW (State.addr h + BitVec.ofNat 64 (4 * k')) 32)
  mem : s'.mem = mX
  rd : s'.rd = base.rd
  wr : s'.wr = base.wr
  sp : s'.sp = base.sp

theorem v_regs : ∀ k < 4, V k ≠ M ∧ V k ≠ YP ∧ V k ≠ SB := by decide

theorem v_ne : ∀ k < 4, ∀ k' < 4, k' ≠ k → V k' ≠ V k := by decide

theorem v_chunk {mX : Mem} {h y b : BitVec 32} {base : State}
    (hhin : ∀ k < 4, InRegions (base.rd ++ base.wr) (State.addr (h + BitVec.ofNat 32 (4 * k))) 4)
    {k : Nat} (hk : k < 4) {s' : State} (hfh : h.toNat + 16 ≤ 2 ^ 32) (hI : VG.Proof.Gcm.Arm.VI mX h y b base k s') :
    WP isa (.block [.ldr (V k) M (4 * k), .rev (V k) (V k)]) s' (VG.Proof.Gcm.Arm.VI mX h y b base (k + 1)) := by
  have hv := VG.Proof.Gcm.Arm.v_regs k hk
  refine wp_ldr (by omega) (by rw [hI.m]) (by rw [hI.rd, hI.wr]; exact hhin k hk) fun s₁ u₁ =>
    wp_rev fun s₂ u₂ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, fun k' hk' => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₂.other _ (Ne.symm hv.1), u₁.other _ (Ne.symm hv.1), hI.m]
  · rw [u₂.other _ (Ne.symm hv.2.1), u₁.other _ (Ne.symm hv.2.1), hI.yp]
  · rw [u₂.other _ (Ne.symm hv.2.2), u₁.other _ (Ne.symm hv.2.2), hI.sb]
  · by_cases hkk : k' = k
    · subst hkk
      rw [u₂.gpr, u₁.gpr, hI.mem, addr_add (by omega)]
    · rw [u₂.other _ (VG.Proof.Gcm.Arm.v_ne k hk k' (by omega) hkk), u₁.other _ (VG.Proof.Gcm.Arm.v_ne k hk k' (by omega) hkk),
        hI.v k' (by omega)]
  · rw [u₂.mem, u₁.mem, hI.mem]
  · rw [u₂.rd, u₁.rd, hI.rd]
  · rw [u₂.wr, u₁.wr, hI.wr]
  · rw [u₂.sp, u₁.sp, hI.sp]

/-- `Y ⊕ X` for block `i`. -/
abbrev xblk (s₀ : State) (i : Nat) (s : State) : VG.Spec.Gcm.Block :=
  VG.Spec.Gcm.blockAt s.mem (State.addr (VG.Proof.Gcm.Arm.yp s₀)) ^^^ VG.Spec.Gcm.blockAt s₀.mem (State.addr (VG.Proof.Gcm.Arm.blk s₀ i))

/-- After `load`, from `s`. -/
structure LPost (s₀ : State) (i : Nat) (s s₁ : State) : Prop where
  bytes : VG.Proof.Gcm.Arm.Bytes (VG.Proof.Gcm.Arm.xblk s₀ i s) (VG.Proof.Gcm.Arm.yp s₀) s₁
  inner : VG.Proof.Gcm.Arm.Inner (VG.Proof.Gcm.Arm.xblk s₀ i s) (VG.Proof.Gcm.Arm.H₀ s₀) (VG.Proof.Gcm.Arm.yp s₀) s₁ 0 s₁
  sb : s₁.gpr SB = VG.Proof.Gcm.Arm.bp s₀
  frame : Frame [VG.Proof.Gcm.Arm.yR s₀] s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp

theorem load_eq : load = ([.ldr M SB (4 * dSlot)] : List Instr) ++
    (List.range 4).flatMap (fun k =>
      ([.ldr XR YP (4 * k), .ldr T M (4 * k), .dp .eor XR XR (.reg T), .str XR YP (4 * k)] : List Instr)) ++
    ([.ldr M SB (4 * hSlot)] : List Instr) ++
    (List.range 4).flatMap (fun k => ([.ldr (V k) M (4 * k), .rev (V k) (V k)] : List Instr)) ++
    ([.mov (Z 0) (.imm 0), .mov (Z 1) (.imm 0), .mov (Z 2) (.imm 0), .mov (Z 3) (.imm 0),
      .mov XP (.reg YP)] : List Instr) := rfl

theorem load_ok {s₀ : State} (hp : VG.Proof.Gcm.Arm.Pre s₀) {i : Nat} (hi : i < VG.Proof.Gcm.Arm.nb s₀) {s : State} (hL : VG.Proof.Gcm.Arm.LInv s₀ i s) :
    WP isa (.block load) s (VG.Proof.Gcm.Arm.LPost s₀ i s) := by
  have hfB := hp.fitB; have hfY := hp.fitY; have hfH := hp.fitH
  rw [VG.Proof.Gcm.Arm.load_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine wp_ldr (a := VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) dSlot) (by decide)
    (by rw [hL.sb]; exact VG.Proof.Gcm.Arm.slot_addr hfB (by decide))
    (by rw [hL.rd, hL.wr]; exact hp.slot_in (by decide)) fun s₁ u₁ => WP.block_nil ?_
  have hyw : (⟨State.addr (VG.Proof.Gcm.Arm.yp s₀), 16⟩ : Region) ∈ s₁.wr := by rw [u₁.wr, hL.wr, hp.wr]; simp
  have hdin : ∀ k < 4, InRegions (s₁.rd ++ s₁.wr) (State.addr (VG.Proof.Gcm.Arm.blk s₀ i) + BitVec.ofNat 64 (4 * k)) 4 :=
    fun k hk => by
      have := hp.fitD
      refine ⟨VG.Proof.Gcm.Arm.dR s₀, by rw [u₁.rd, hL.rd, hp.rd]; simp, ?_⟩
      rw [hp.blk_addr hi, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact VG.Proof.Gcm.Arm.r_off _ (by omega) (by omega)
  have hX₀ : VG.Proof.Gcm.Arm.XI s₁ (VG.Proof.Gcm.Arm.yp s₀) (VG.Proof.Gcm.Arm.bp s₀) (VG.Proof.Gcm.Arm.blk s₀ i) 0 s₁ :=
    ⟨by rw [u₁.other _ (by decide), hL.r1], by rw [u₁.other _ (by decide), hL.sb], by rw [u₁.gpr, hL.ds],
      fun j hj => by rw [ite_eq_right (by omega)], Frame.refl _ _, rfl, rfl, rfl⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) (VG.Proof.Gcm.Arm.XI s₁ (VG.Proof.Gcm.Arm.yp s₀) (VG.Proof.Gcm.Arm.bp s₀) (VG.Proof.Gcm.Arm.blk s₀ i))
    (fun k s' hk hI => VG.Proof.Gcm.Arm.xor_chunk hyw hfY hdin (hp.blk_fit hi)
      (hp.dYD.symm.sub_left (hp.blk_sub hi)) hk hI) 4 (Nat.le_refl _) s₁ hX₀) fun s₂ hX => ?_
  refine wp_ldr (a := VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) hSlot) (by decide)
    (by rw [hX.sb]; exact VG.Proof.Gcm.Arm.slot_addr hfB (by decide))
    (by rw [hX.rd, hX.wr, u₁.rd, u₁.wr, hL.rd, hL.wr]; exact hp.slot_in (by decide))
    fun s₃ u₃ => WP.block_nil ?_
  have m₃ : s₃.gpr M = VG.Proof.Gcm.Arm.hA s₀ := by
    rw [u₃.gpr, hX.frame.readW (r := ⟨VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) hSlot, 4⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.slot_y (by decide))
      (by decide), u₁.mem, hL.hs]
  have hhin : ∀ k < 4, InRegions (s.rd ++ s.wr) (State.addr (VG.Proof.Gcm.Arm.hA s₀ + BitVec.ofNat 32 (4 * k))) 4 :=
    fun k hk => by
      rw [hL.rd, hL.wr]; exact Straight.in_off (by rw [hp.rd]; simp) hfH (by omega) (by decide)
  have hV₀ : VG.Proof.Gcm.Arm.VI s₃.mem (VG.Proof.Gcm.Arm.hA s₀) (VG.Proof.Gcm.Arm.yp s₀) (VG.Proof.Gcm.Arm.bp s₀) s 0 s₃ :=
    ⟨m₃, by rw [u₃.other _ (by decide), hX.yp], by rw [u₃.other _ (by decide), hX.sb],
      fun k' h => absurd h (by omega), rfl, by rw [u₃.rd, hX.rd, u₁.rd],
      by rw [u₃.wr, hX.wr, u₁.wr], by rw [u₃.sp, hX.sp, u₁.sp]⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) (VG.Proof.Gcm.Arm.VI s₃.mem (VG.Proof.Gcm.Arm.hA s₀) (VG.Proof.Gcm.Arm.yp s₀) (VG.Proof.Gcm.Arm.bp s₀) s)
    (fun k s' hk hI => VG.Proof.Gcm.Arm.v_chunk hhin hk hfH hI) 4 (Nat.le_refl _) s₃ hV₀) fun s₄ hV => ?_
  refine wp_mov (op2_imm (by decide)) fun s₅ u₅ => wp_mov (op2_imm (by decide)) fun s₆ u₆ =>
    wp_mov (op2_imm (by decide)) fun s₇ u₇ => wp_mov (op2_imm (by decide)) fun s₈ u₈ =>
    wp_mov (op2_reg _ _) fun s₉ u₉ => WP.block_nil ?_
  have mem₉ : s₉.mem = s₂.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, hV.mem, u₃.mem]
  have g₉ : ∀ r, r ≠ Z 0 → r ≠ Z 1 → r ≠ Z 2 → r ≠ Z 3 → r ≠ XP → s₉.gpr r = s₄.gpr r :=
    fun r h0 h1 h2 h3 h4 => by
      rw [u₉.other _ h4, u₈.other _ h3, u₇.other _ h2, u₆.other _ h1, u₅.other _ h0]
  have hDs : ∀ j < 16, s.mem (State.addr (VG.Proof.Gcm.Arm.blk s₀ i) + BitVec.ofNat 64 j) =
      s₀.mem (State.addr (VG.Proof.Gcm.Arm.blk s₀ i) + BitVec.ofNat 64 j) :=
    fun j hj => hL.frame.bytes (R := ⟨State.addr (VG.Proof.Gcm.Arm.blk s₀ i), 16⟩) (hp.blk_frame hi) (by simp) hj
  have hH : VG.Spec.Gcm.blockAt s₃.mem (State.addr (VG.Proof.Gcm.Arm.hA s₀)) = VG.Proof.Gcm.Arm.H₀ s₀ := by
    rw [u₃.mem]
    refine (blockAt_congr (m := s₁.mem) fun j hj => ?_).trans (blockAt_congr (m := s₀.mem) fun j hj => ?_)
    · exact hX.frame.bytes (R := VG.Proof.Gcm.Arm.hR s₀) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.dHY) (by simp) hj
    · rw [u₁.mem]
      exact hL.frame.bytes (R := VG.Proof.Gcm.Arm.hR s₀) hp.h_frame (by simp) hj
  have y₉ : s₉.gpr YP = VG.Proof.Gcm.Arm.yp s₀ := by rw [g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), hV.yp]
  refine ⟨⟨hfY, ?_, fun j hj t ht => ?_⟩, ⟨?_, ?_, y₉, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, hV.rd, hV.wr, hL.rd,
      hL.wr, hp.wr]
    simp
  · rw [mem₉, hX.bytes j hj, ite_eq_left (by omega), u₁.mem, VG.Proof.Gcm.Arm.xblk, BitVec.getMsbD_xor,
      BitVec.getMsbD_xor, VG.Proof.Gcm.Arm.blockAt_msb _ _ hj ht, VG.Proof.Gcm.Arm.blockAt_msb _ _ hj ht, hDs j hj]
  · simp only [VG.Proof.Gcm.Arm.zvOf]
    rw [g₉ (V 0) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₉ (V 1) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₉ (V 2) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₉ (V 3) (by decide) (by decide) (by decide) (by decide) (by decide),
      hV.v 0 (by decide), hV.v 1 (by decide), hV.v 2 (by decide), hV.v 3 (by decide), mulSteps_zero,
      ← hH, VG.Proof.Gcm.Arm.blockAt_rev s₃.mem]
    have z0 : s₉.gpr (Z 0) = 0 := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.gpr]
    have z1 : s₉.gpr (Z 1) = 0 := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]
    have z2 : s₉.gpr (Z 2) = 0 := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]
    have z3 : s₉.gpr (Z 3) = 0 := by rw [u₉.other _ (by decide), u₈.gpr]
    rw [z0, z1, z2, z3, show (4 * 0 : Nat) = 0 from rfl, BitVec.add_zero]
    rw [VG.Proof.Gcm.Arm.w4_zero]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), hV.yp, BitVec.add_zero]
  · rw [g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), hV.sb]
  · rw [mem₉, ← u₁.mem]; exact hX.frame
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, hV.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, hV.wr]
  · rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, hV.sp]

/-! ## `store`: `Y := Z`, and the next block -/

/-- After `k` words of `Z` (of the state `s₂`) stored at `y`. -/
structure ZI (s₂ : State) (y : BitVec 32) (k : Nat) (s' : State) : Prop where
  yp : s'.gpr YP = y
  sb : s'.gpr SB = s₂.gpr SB
  z : ∀ k', k ≤ k' → k' < 4 → s'.gpr (Z k') = s₂.gpr (Z k')
  bytes : ∀ k' < k, ∀ t < 4, s'.mem (State.addr y + BitVec.ofNat 64 (4 * k' + t)) =
    (rev (s₂.gpr (Z k'))).extractLsb' (8 * t) 8
  frame : Frame [⟨State.addr y, 16⟩] s₂.mem s'.mem
  rd : s'.rd = s₂.rd
  wr : s'.wr = s₂.wr
  sp : s'.sp = s₂.sp

theorem z_regs : ∀ k < 4, Z k ≠ YP ∧ Z k ≠ SB := by decide

theorem z_ne : ∀ k < 4, ∀ k' < 4, k' ≠ k → Z k' ≠ Z k := by decide

theorem z_chunk {s₂ : State} {y : BitVec 32} (hyw : (⟨State.addr y, 16⟩ : Region) ∈ s₂.wr)
    (hfy : y.toNat + 16 ≤ 2 ^ 32) {k : Nat} (hk : k < 4) {s' : State} (hI : VG.Proof.Gcm.Arm.ZI s₂ y k s') :
    WP isa (.block [.rev (Z k) (Z k), .str (Z k) YP (4 * k)]) s' (VG.Proof.Gcm.Arm.ZI s₂ y (k + 1)) := by
  have hz := VG.Proof.Gcm.Arm.z_regs k hk
  have hy4 : State.addr (y + BitVec.ofNat 32 (4 * k)) = State.addr y + BitVec.ofNat 64 (4 * k) :=
    addr_add (by omega)
  refine wp_rev fun s₁ u₁ => wp_str (by omega) (by rw [u₁.other _ (Ne.symm hz.1), hI.yp, hy4])
    (by rw [u₁.wr, hI.wr, ← hy4]; exact Straight.in_off hyw hfy (by omega) (by decide))
    fun s₃ u₃ => WP.block_nil ?_
  have m₃ : s₃.mem = s'.mem.writeW (State.addr y + BitVec.ofNat 64 (4 * k)) (rev (s₂.gpr (Z k))) := by
    rw [u₃.mem, u₁.gpr, u₁.mem, hI.z k (Nat.le_refl _) hk]
  refine ⟨?_, ?_, fun k' h1 h2 => ?_, fun k' hk' t ht => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₃.gpr, u₁.other _ (Ne.symm hz.1), hI.yp]
  · rw [u₃.gpr, u₁.other _ (Ne.symm hz.2), hI.sb]
  · rw [u₃.gpr, u₁.other _ (VG.Proof.Gcm.Arm.z_ne k hk k' h2 (by omega)), hI.z k' (by omega) h2]
  · rw [m₃]
    by_cases hkk : k' = k
    · subst hkk
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, st_byte _ _ _ ht]
    · rw [writeW32_other _ (off_disjoint _ (by omega) (by omega) (by omega)), hI.bytes k' (by omega) t ht]
  · rw [m₃]
    exact hI.frame.writeW (r := ⟨State.addr y, 16⟩) (by simp) _ (VG.Proof.Gcm.Arm.r_off _ (by decide) (by omega))
  · rw [u₃.rd, u₁.rd, hI.rd]
  · rw [u₃.wr, u₁.wr, hI.wr]
  · rw [u₃.sp, u₁.sp, hI.sp]

/-- `wp_str`, keeping the flags. -/
theorem wp_strz {is : List Instr} {s : State} {Q : State → Prop} {t n : Reg} {off : Nat} {a : Addr}
    (ho : off < 4096) (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → s'.z = s.z → WP isa (.block is) s' Q) :
    WP isa (.block (.str t n off :: is)) s Q := by
  subst ha
  exact VG.Proof.MdStream.Arm.WP.cons (exec_str ho hout) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

theorem store_eq : store =
    (List.range 4).flatMap (fun k => [.rev (Z k) (Z k), .str (Z k) YP (4 * k)]) ++
    ([.ldr T SB (4 * dSlot), .dp .add T T (.imm 16), .str T SB (4 * dSlot),
      .ldr T SB (4 * nSlot), .subs T T (.imm 1), .str T SB (4 * nSlot)] : List Instr) := rfl

theorem slot_sep {B : Addr} {j k : Nat} (h : j ≠ k) (hj : 4 * j + 4 < 2 ^ 64) (hk : 4 * k + 4 < 2 ^ 64) :
    Mem.Sep (VG.Proof.Gcm.Arm.slot B j) (32 / 8) (VG.Proof.Gcm.Arm.slot B k) (32 / 8) :=
  (off_disjoint B (by omega) hj hk).sep (Region.contains_self _ _) (Region.contains_self _ _)

theorem beq_pred {a : Nat} (h0 : 0 < a) (h : a < 2 ^ 32) :
    (BitVec.ofNat 32 a - 1 == 0) = decide (a - 1 = 0) := by
  rw [show BitVec.ofNat 32 a - 1 = BitVec.ofNat 32 (a - 1) by bv_omega,
    VG.Proof.MdStream.Arm.ofNat_beq_zero (by omega)]

theorem store_ok {s₀ : State} (hp : VG.Proof.Gcm.Arm.Pre s₀) {i : Nat} (hi : i < VG.Proof.Gcm.Arm.nb s₀) {s s₂ : State} (hL : VG.Proof.Gcm.Arm.LInv s₀ i s)
    (hmem : Frame [VG.Proof.Gcm.Arm.yR s₀] s.mem s₂.mem) (hy : s₂.gpr YP = VG.Proof.Gcm.Arm.yp s₀) (hsb : s₂.gpr SB = VG.Proof.Gcm.Arm.bp s₀)
    (hrd : s₂.rd = s.rd) (hwr : s₂.wr = s.wr) (hsp : s₂.sp = s.sp)
    (hz : (VG.Proof.Gcm.Arm.zvOf s₂).1 = ghashFrom (VG.Proof.Gcm.Arm.H₀ s₀) (VG.Proof.Gcm.Arm.Y₀ s₀) (VG.Spec.Gcm.blocksAt s₀.mem (State.addr (VG.Proof.Gcm.Arm.dp s₀)) (i + 1))) :
    WP isa (.block store) s₂ fun s' => s'.z = decide (VG.Proof.Gcm.Arm.nb s₀ - (i + 1) = 0) ∧ VG.Proof.Gcm.Arm.LInv s₀ (i + 1) s' := by
  have hfB := hp.fitB; have hfY := hp.fitY
  have hyw : (⟨State.addr (VG.Proof.Gcm.Arm.yp s₀), 16⟩ : Region) ∈ s₂.wr := by rw [hwr, hL.wr, hp.wr]; simp
  rw [VG.Proof.Gcm.Arm.store_eq, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) (VG.Proof.Gcm.Arm.ZI s₂ (VG.Proof.Gcm.Arm.yp s₀))
    (fun k s' hk hI => VG.Proof.Gcm.Arm.z_chunk hyw hfY hk hI) 4 (Nat.le_refl _) s₂
    ⟨hy, rfl, fun _ _ _ => rfl, fun k' h => absurd h (by omega), Frame.refl _ _, rfl, rfl, rfl⟩)
    fun s₃ hZ => ?_
  have fZ : Frame [VG.Proof.Gcm.Arm.yR s₀] s.mem s₃.mem := hmem.trans hZ.frame
  have rdS : ∀ k, 4 * k + 4 ≤ 256 → s₃.mem.readW (VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) k) 32 =
      s.mem.readW (VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) k) 32 := fun k hk =>
    fZ.readW (r := ⟨VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) k, 4⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.slot_y hk) (by decide)
  have wS : ∀ k, 4 * k + 4 ≤ 256 → InRegions s₀.wr (VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) k) 4 := fun k hk =>
    ⟨VG.Proof.Gcm.Arm.bR s₀, by rw [hp.wr]; simp, VG.Proof.Gcm.Arm.r_off _ (by decide) hk⟩
  have sb₃ : s₃.gpr SB = VG.Proof.Gcm.Arm.bp s₀ := by rw [hZ.sb, hsb]
  refine wp_ldr (a := VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) dSlot) (by decide)
    (by rw [sb₃]; exact VG.Proof.Gcm.Arm.slot_addr hfB (by decide))
    (by rw [hZ.rd, hZ.wr, hrd, hwr, hL.rd, hL.wr]; exact hp.slot_in (by decide)) fun s₄ u₄ => ?_
  refine wp_add (op2_imm (by decide)) fun s₅ u₅ => ?_
  refine wp_str (a := VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) dSlot) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), sb₃]; exact VG.Proof.Gcm.Arm.slot_addr hfB (by decide))
    (by rw [u₅.wr, u₄.wr, hZ.wr, hwr, hL.wr]; exact wS _ (by decide)) fun s₆ u₆ => ?_
  refine wp_ldr (a := VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) nSlot) (by decide)
    (by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), sb₃]; exact VG.Proof.Gcm.Arm.slot_addr hfB (by decide))
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, hZ.rd, hZ.wr, hrd, hwr, hL.rd, hL.wr]
        exact hp.slot_in (by decide)) fun s₇ u₇ => ?_
  refine wp_subs (op2_imm (by decide)) fun s₈ u₈ z₈ => ?_
  refine VG.Proof.Gcm.Arm.wp_strz (a := VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) nSlot) (by decide)
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
          u₄.other _ (by decide), sb₃]; exact VG.Proof.Gcm.Arm.slot_addr hfB (by decide))
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, hZ.wr, hwr, hL.wr]; exact wS _ (by decide))
    fun s₉ u₉ z₉ => WP.block_nil ?_
  have t₄ : s₄.gpr T = VG.Proof.Gcm.Arm.blk s₀ i := by rw [u₄.gpr, rdS _ (by decide), hL.ds]
  have m₆ : s₆.mem = s₃.mem.writeW (VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) dSlot) (VG.Proof.Gcm.Arm.blk s₀ i + 16) := by
    rw [u₆.mem, u₅.gpr, t₄, u₅.mem, u₄.mem]
  have t₇ : s₇.gpr T = BitVec.ofNat 32 (VG.Proof.Gcm.Arm.nb s₀ - i) := by
    rw [u₇.gpr, m₆, Mem.readW_writeW_sep (VG.Proof.Gcm.Arm.slot_sep (by decide) (by decide) (by decide)) (by decide),
      rdS _ (by decide), hL.ns]
  have m₉ : s₉.mem = s₆.mem.writeW (VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) nSlot) (BitVec.ofNat 32 (VG.Proof.Gcm.Arm.nb s₀ - i) - 1) := by
    rw [u₉.mem, u₈.gpr, t₇, u₈.mem, u₇.mem]
  have g₉ : ∀ r, r ≠ T → s₉.gpr r = s₃.gpr r := fun r hr => by
    rw [u₉.gpr, u₈.other _ hr, u₇.other _ hr, u₆.gpr, u₅.other _ hr, u₄.other _ hr]
  have rd₉ : ∀ k, 4 * k + 4 ≤ 256 → k ≠ dSlot → k ≠ nSlot →
      s₉.mem.readW (VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) k) 32 = s.mem.readW (VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) k) 32 :=
    fun k hk h10 h11 => by
      rw [m₉, Mem.readW_writeW_sep (VG.Proof.Gcm.Arm.slot_sep h11 (by omega) (by decide)) (by decide), m₆,
        Mem.readW_writeW_sep (VG.Proof.Gcm.Arm.slot_sep h10 (by omega) (by decide)) (by decide), rdS k hk]
  have hnb : VG.Proof.Gcm.Arm.nb s₀ < 2 ^ 32 := (s₀.gpr .r3).isLt
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [z₉, z₈, t₇, VG.Proof.Gcm.Arm.beq_pred (by omega) (by omega), Nat.sub_sub]
  · rw [g₉ _ (by decide), hZ.yp]
  · rw [g₉ _ (by decide), sb₃]
  · rw [rd₉ _ (by decide) (by decide) (by decide), hL.hs]
  · rw [m₉, Mem.readW_writeW_sep (VG.Proof.Gcm.Arm.slot_sep (by decide) (by decide) (by decide)) (by decide), m₆,
      Mem.readW_writeW_self32]
    simp only [VG.Proof.Gcm.Arm.blk]
    bv_omega
  · rw [m₉, Mem.readW_writeW_self32]
    bv_omega
  · rw [rd₉ _ (by omega) (by simp [dSlot]; omega) (by simp [nSlot]; omega)]
    exact hL.saved j hj
  · have hy₃ : VG.Spec.Gcm.blockAt s₃.mem (State.addr (VG.Proof.Gcm.Arm.yp s₀)) = (VG.Proof.Gcm.Arm.zvOf s₂).1 :=
      VG.Proof.Gcm.Arm.blockAt_w4 _ _ (fun k => s₂.gpr (Z k)) hZ.bytes
    rw [← hz, ← hy₃]
    refine blockAt_congr fun j hj => ?_
    have d : ∀ k, 4 * k + 4 ≤ 256 →
        Region.Disjoint ⟨State.addr (VG.Proof.Gcm.Arm.yp s₀) + BitVec.ofNat 64 j, 1⟩ ⟨VG.Proof.Gcm.Arm.slot (State.addr (VG.Proof.Gcm.Arm.bp s₀)) k, 4⟩ :=
      fun k hk => ((hp.slot_y hk).symm.sub_left (VG.Proof.MdStream.Arm.sub_offset (by omega) (by omega)))
    rw [m₉, writeW32_other _ (d _ (by decide)), m₆, writeW32_other _ (d _ (by decide))]
  · have f₃₉ : Frame [⟨State.addr (VG.Proof.Gcm.Arm.bp s₀), 48⟩] s₃.mem s₉.mem := by
      rw [m₉, m₆]
      exact ((Frame.refl _ _).writeW (r := ⟨State.addr (VG.Proof.Gcm.Arm.bp s₀), 48⟩) (by simp) _
        (VG.Proof.Gcm.Arm.r_off _ (by decide) (by decide))).writeW (r := ⟨State.addr (VG.Proof.Gcm.Arm.bp s₀), 48⟩) (by simp) _
        (VG.Proof.Gcm.Arm.r_off _ (by decide) (by decide))
    exact hL.frame.trans ((fZ.mono (by simp)).trans (f₃₉.mono (by simp)))
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, hZ.rd, hrd, hL.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, hZ.wr, hwr, hL.wr]
  · rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, hZ.sp, hsp, hL.sp]

/-! ## One block, and the loop -/

theorem body_ok {s₀ : State} (hp : VG.Proof.Gcm.Arm.Pre s₀) {i : Nat} (hi : i < VG.Proof.Gcm.Arm.nb s₀) {s : State} (hL : VG.Proof.Gcm.Arm.LInv s₀ i s) :
    WP isa body s fun s' =>
      (VG.Arm.eval .ne s' = some false ∧ VG.Proof.Gcm.Arm.LInv s₀ (VG.Proof.Gcm.Arm.nb s₀) s') ∨
      (VG.Arm.eval .ne s' = some true ∧ i + 1 < VG.Proof.Gcm.Arm.nb s₀ ∧ VG.Proof.Gcm.Arm.LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (VG.Proof.Gcm.Arm.load_ok hp hi hL) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Gcm.Arm.mul_ok h₁.bytes h₁.inner) fun s₂ h₂ => ?_)
  have hz : (VG.Proof.Gcm.Arm.zvOf s₂).1 = ghashFrom (VG.Proof.Gcm.Arm.H₀ s₀) (VG.Proof.Gcm.Arm.Y₀ s₀) (VG.Spec.Gcm.blocksAt s₀.mem (State.addr (VG.Proof.Gcm.Arm.dp s₀)) (i + 1)) := by
    rw [h₂.zv]
    show (mulSteps _ _ 128).1 = _
    rw [← mul_eq, ghashFrom_blocksAt_succ, ← hL.y, ← hp.blk_addr hi]
  refine WP.mono (VG.Proof.Gcm.Arm.store_ok hp hi hL (by rw [h₂.mem]; exact h₁.frame) h₂.yp (h₂.sb.trans h₁.sb)
    (h₂.rd.trans h₁.rd) (h₂.wr.trans h₁.wr) (h₂.sp.trans h₁.sp) hz) fun s₃ ⟨hz₃, hL₃⟩ => ?_
  by_cases hl : i + 1 = VG.Proof.Gcm.Arm.nb s₀
  · refine .inl ⟨(eval_ne s₃).trans (by rw [hz₃, ← hl, Nat.sub_self]; rfl), hl ▸ hL₃⟩
  · refine .inr ⟨(eval_ne s₃).trans (by rw [hz₃, decide_eq_false (by omega)]; rfl), by omega, hL₃⟩

theorem blocks_ok {s₀ : State} (hp : VG.Proof.Gcm.Arm.Pre s₀) (hpos : 0 < VG.Proof.Gcm.Arm.nb s₀) {s : State} (hL : VG.Proof.Gcm.Arm.LInv s₀ 0 s) :
    WP isa (.loop body .ne) s (VG.Proof.Gcm.Arm.LInv s₀ (VG.Proof.Gcm.Arm.nb s₀)) := by
  refine WP.loop (M := isa) (fun m s => ∃ i, m = VG.Proof.Gcm.Arm.nb s₀ - i ∧ i < VG.Proof.Gcm.Arm.nb s₀ ∧ VG.Proof.Gcm.Arm.LInv s₀ i s)
    (fun m s ⟨i, hm, hi, hL⟩ => WP.mono (VG.Proof.Gcm.Arm.body_ok hp hi hL) fun s' h => ?_) _ s ⟨0, rfl, hpos, hL⟩
  rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
  · exact .inl ⟨he, hc⟩
  · exact .inr ⟨he, VG.Proof.Gcm.Arm.nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩

/-! ## The whole function -/

theorem e0 (x : BitVec 32) : x - (0 : BitVec 32) = x := by bv_omega

theorem greg_ne : ∀ i < 9, VG.Proof.Gcm.Arm.greg i ≠ .r12 := by decide

theorem correct {s₀ : State} (hp : VG.Proof.Gcm.Arm.Pre s₀) :
    WP isa ghash s₀ fun s' =>
      (∀ i < 9, s'.gpr (VG.Proof.Gcm.Arm.greg i) = s₀.gpr (VG.Proof.Gcm.Arm.greg i)) ∧ Proof.Gcm.ghashArm.post s₀ s' := by
  have hfB := hp.fitB
  rw [VG.Proof.Gcm.Arm.ghash_eq]
  refine WP.seq ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl
    ⟨VG.Proof.Gcm.Arm.aR s₀, by rw [hp.rd]; simp, Region.contains_self _ _⟩ fun s₁ u₁ => ?_
  rw [WP.block_append_iff]
  obtain ⟨s₂, h₂, sv₂, g₂, rd₂, wr₂, sp₂, f₂⟩ :=
    VG.Proof.Gcm.Arm.gsave_ok (s := s₁) (b := VG.Proof.Gcm.Arm.bp s₀) (by rw [u₁.wr, hp.wr]; simp) hfB u₁.gpr
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  refine wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ?_
  have g₃ : ∀ r, r ≠ .r12 → s₃.gpr r = s₀.gpr r := fun r hr => by
    rw [f₃.gpr, g₂, u₁.other _ hr]
  have m₃ : s₃.mem = s₂.mem := f₃.mem
  have hL₀ : VG.Proof.Gcm.Arm.LInv s₀ 0 s₃ := by
    refine ⟨g₃ _ (by decide), by rw [f₃.gpr, g₂, u₁.gpr]; rfl, ?_, ?_, ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [m₃, sv₂ hSlot (by decide)]; exact u₁.other _ (by decide)
    · rw [m₃, sv₂ dSlot (by decide), u₁.other _ (by decide)]
      simp only [VG.Proof.Gcm.Arm.blk, Nat.mul_zero]; rw [BitVec.add_zero]; rfl
    · rw [m₃, sv₂ nSlot (by decide), u₁.other _ (by decide)]
      simp [VG.Proof.Gcm.Arm.nb]; rfl
    · rw [m₃, sv₂ j (by omega), u₁.other _ (VG.Proof.Gcm.Arm.greg_ne j hj)]
    · rw [ghashFrom_blocksAt_zero, m₃]
      refine blockAt_congr fun j hj => ?_
      rw [f₂.bytes (R := VG.Proof.Gcm.Arm.yR s₀) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.dYB.sub_right (Region.sub_prefix (by decide))) (by simp) hj, u₁.mem]
    · rw [m₃, ← u₁.mem]; exact f₂.mono (by simp)
    · rw [f₃.rd, rd₂, u₁.rd]
    · rw [f₃.wr, wr₂, u₁.wr]
    · rw [f₃.sp, sp₂, u₁.sp]
  refine WP.seq (WP.mono (Q := VG.Proof.Gcm.Arm.LInv s₀ (VG.Proof.Gcm.Arm.nb s₀)) ?_ fun s₄ h₄ => ?_)
  · have hev : isa.eval .eq s₃ = some (s₀.gpr .r3 == 0) := by
      show some s₃.z = _
      rw [z₃, g₂, u₁.other _ (by decide), VG.Proof.Gcm.Arm.e0]
    refine WP.ite _ hev (fun h => WP.block_nil ?_) (fun h => VG.Proof.Gcm.Arm.blocks_ok hp ?_ hL₀)
    · have h0 : VG.Proof.Gcm.Arm.nb s₀ = 0 := by simp at h; simp [VG.Proof.Gcm.Arm.nb, h]
      rw [h0]; exact hL₀
    · simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
  · obtain ⟨s₅, h₅, rg₅, f₅⟩ := VG.Proof.Gcm.Arm.grestore_ok (s₀ := s₀) (b := VG.Proof.Gcm.Arm.bp s₀)
      (by rw [h₄.wr, hp.wr]; simp) hfB h₄.sb h₄.saved
    refine WP.of_runBlock ⟨s₅, h₅, rg₅, ?_⟩
    show VG.Spec.Gcm.blockAt s₅.mem (State.addr (VG.Proof.Gcm.Arm.yp s₀)) =
      ghashFrom (VG.Proof.Gcm.Arm.H₀ s₀) (VG.Proof.Gcm.Arm.Y₀ s₀) (VG.Spec.Gcm.blocksAt s₀.mem (State.addr (VG.Proof.Gcm.Arm.dp s₀)) (VG.Proof.Gcm.Arm.nb s₀))
    rw [← h₄.y]
    exact blockAt_congr fun j hj => f₅.bytes (R := VG.Proof.Gcm.Arm.yR s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.dYB.sub_right (Region.sub_prefix (by decide))) (by simp) hj

theorem ghash_correct (s : State) (hs : Proof.Gcm.ghashArm.pre s) :
    ∃ t s', Exec isa Impl.Gcm.Arm.ghash s t s' ∧ abiPreserved s s' ∧ Proof.Gcm.ghashArm.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Gcm.Arm.correct (VG.Proof.Gcm.Arm.pre_of hs)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by decide)
  · exact h₁ 1 (by decide)
  · exact h₁ 2 (by decide)
  · exact h₁ 3 (by decide)
  · exact h₁ 4 (by decide)
  · exact h₁ 5 (by decide)
  · exact h₁ 6 (by decide)
  · exact h₁ 7 (by decide)
  · exact h₁ 8 (by decide)

/-! ## Constant time -/

/-- The initial taint: the pointers, `n` and the stack argument are public;
`r1` points at `y`, and the stack argument at the scratch buffer. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [16, 256],
    bases := [(.r1, 0)], argLen := 4, argBases := [(0, 1)] }

theorem wf₀ {s : State} (h : Proof.Gcm.ghashArm.pre s) : VG.Arm.Taint.Wf VG.Proof.Gcm.Arm.τ₀ s := by
  have hp := VG.Proof.Gcm.Arm.pre_of h
  have e : (⟨State.addr s.sp, 4⟩ : Region) = VG.Proof.Gcm.Arm.aR s := by simp [VG.Proof.Gcm.Arm.aR, stackArgAddr]
  refine ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Gcm.Arm.τ₀], ?_, ?_⟩, ?_, fun _ => ⟨hp.fitSp, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.dYB
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    have := hp.fitY; have := hp.fitB
    rintro r (rfl | rfl) <;> simp only [VG.Proof.MdStream.Arm.addr_toNat] <;> omega
  · intro p hp'
    simp only [VG.Proof.Gcm.Arm.τ₀, List.mem_singleton] at hp'; subst hp'
    simp [VG.Arm.Taint.region, hp.wr]
  · simp only [VG.Proof.Gcm.Arm.τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.dYA.symm
    · exact hp.dBA.symm
  · intro p hp'
    simp only [VG.Proof.Gcm.Arm.τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Gcm.ghashArm.pre s₁) (h₂ : Proof.Gcm.ghashArm.pre s₂)
    (hpub : Proof.Gcm.ghashArm.pub s₁ s₂) : VG.Arm.Taint.Agree VG.Proof.Gcm.Arm.τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hpub
  have hp₁ := VG.Proof.Gcm.Arm.pre_of h₁; have hp₂ := VG.Proof.Gcm.Arm.pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Gcm.Arm.wf₀ h₁, VG.Proof.Gcm.Arm.wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [VG.Proof.Gcm.Arm.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [VG.Proof.Gcm.Arm.yR, VG.Proof.Gcm.Arm.bR, VG.Proof.Gcm.Arm.yp, VG.Proof.Gcm.Arm.bp, p1, a0]
  · simp only [VG.Proof.Gcm.Arm.τ₀] at hk
    rw [VG.Proof.MdStream.Arm.argByte_eq hp₁.fitSp hk, VG.Proof.MdStream.Arm.argByte_eq hp₂.fitSp hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide)),
      show k / 4 = 0 by omega]
    exact congrArg _ a0

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashArm.pre Proof.Gcm.ghashArm.pub Impl.Gcm.Arm.ghash :=
  VG.Taint.constantTime (A := VG.Arm.taint) VG.Proof.Gcm.Arm.τ₀ (fun _ _ h₁ h₂ hp => VG.Proof.Gcm.Arm.agree₀ h₁ h₂ hp) (by taint_decide)

/-- A state satisfying the precondition (with no blocks, and the scratch buffer at 0). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 16⟩, ⟨0x3000, 0⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 16⟩, ⟨0, 256⟩]

theorem ghash_verified :
    Verified Arm.target Impl.Gcm.Arm.ghash (Spec.Gcm.ghashContract Arm.abi) :=
  Verified.of_correct VG.Proof.Gcm.Arm.ghash_correct VG.Proof.Gcm.Arm.ghash_ct (by
    sig_implies [Spec.Gcm.ghashContract, Spec.Gcm.ghashSig, Proof.Gcm.ghashArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Gcm.Arm.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using Proof.Gcm.Arm.sat)

end VG.Proof.Gcm.Arm

end
