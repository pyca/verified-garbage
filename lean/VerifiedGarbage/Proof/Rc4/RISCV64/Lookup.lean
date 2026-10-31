module

public import VerifiedGarbage.Impl.Rc4.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rc4.Scan64
import VerifiedGarbage.Proof.Rc4.Qword
import VerifiedGarbage.Proof.Rc4.Memory
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Spec.Rc4
public import VerifiedGarbage.TCB.RISCV64.Isa

/-! # RC4 on RISC-V: the table lookup, a doubleword at a time -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

/-- Steps a block of the RC4 code (`mrun`). -/
syntax "rrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rrun) => `(tactic| rrun [])
  | `(tactic| rrun [$ls,*]) => `(tactic| mrun [$ls,*])

/-- An 8-byte aligned offset of an 8-byte aligned base. -/
theorem al_add {p : Addr} (hp : p.toNat % 8 = 0) {d : Nat} (hd : d % 8 = 0) (hd' : d < 2 ^ 64) :
    (p + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) hd']
  have := p.isLt
  omega

/-! ## The row's bit and masks -/

/-- Bit `c` of `q` shifted to the top and arithmetically back: all ones if
it is set. -/
theorem bit_mask (q : BitVec 64) {c : Nat} (hc : c < 64) :
    (q <<< (63 - c)).sshiftRight 63 = if q.getLsbD c then BitVec.allOnes 64 else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last]
  have key : (q <<< (63 - c)).getLsbD 63 = q.getLsbD c := by
    rw [BitVec.getLsbD_shiftLeft]
    simp only [show (63 : Nat) < 64 by decide, decide_true, Bool.true_and,
      show ¬ (63 < 63 - c) by omega, decide_false, Bool.not_false, show 63 - (63 - c) = c by omega]
  rw [show (if 63 + i < 64 then (q <<< (63 - c)).getLsbD (63 + i) else (q <<< (63 - c)).getLsbD (64 - 1)) =
    (q <<< (63 - c)).getLsbD 63 by split; (congr 1; omega); rfl, key]
  cases q.getLsbD c
  · simp
  · simp only [ite_true, BitVec.getLsbD_allOnes, hi, decide_true, show ¬ 64 ≤ i by omega, decide_false,
      Bool.not_false, Bool.and_true]

/-- Doubleword `k`'s mask from the bit of byte `idx`'s doubleword. -/
theorem row_bit (idx : Byte) {k : Nat} (hk : k < 32) :
    (BitVec.twoPow 64 (idx.toNat / 8) <<< (63 - k)).sshiftRight 63 =
      if idx.toNat / 8 = k then BitVec.allOnes 64 else 0#64 := by
  rw [bit_mask _ (by omega), BitVec.getLsbD_twoPow]
  by_cases h : idx.toNat / 8 = k
  · subst h; simp only [ite_true, decide_eq_true (by omega : idx.toNat / 8 < 64), Bool.true_and, decide_true]
  · simp [h]

theorem rowBit_run (s : State) (idx : Byte) (h4 : s.gpr .a4 = idx.setWidth 64) :
    WP isa (.block rowBit) s fun t => t.gpr .t5 = BitVec.twoPow 64 (idx.toNat / 8) ∧ t.mem = s.mem := by
  have := idx.isLt
  unfold rowBit
  rrun [h4]
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show idx.toNat < 2 ^ 64 by omega), show (2 : Nat) ^ 3 = 8 from rfl,
    Nat.mod_eq_of_lt (show idx.toNat / 8 < 64 by omega)]
  rfl

/-- The lane's shift: eight times byte `idx`'s offset in its doubleword. -/
theorem lane_shift (idx : Byte) :
    ((idx.setWidth 64 &&& BitVec.ofNat 64 7) <<< 3).toNat % 64 = 8 * (idx.toNat % 8) := by
  have := Nat.mod_lt idx.toNat (by decide : 8 > 0)
  have hi := idx.isLt
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show idx.toNat < 2 ^ 64 by omega), show 7 % 2 ^ 64 = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mul_comm]

theorem laneShift_run (s : State) (idx : Byte) (h4 : s.gpr .a4 = idx.setWidth 64) :
    WP isa (.block laneShift) s fun t => (t.gpr .t2).toNat % 64 = 8 * (idx.toNat % 8) ∧ t.mem = s.mem := by
  unfold laneShift
  rrun [h4]
  exact lane_shift idx

/-! ## Visiting the doublewords -/

theorem gather_step (s : State) (idx : Byte) {k : Nat} (hk : k < 32)
    (h5 : s.gpr .t5 = BitVec.twoPow 64 (idx.toNat / 8)) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .a7 + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block (gatherStep k)) s fun t =>
      t.gpr .t1 = s.gpr .t1 |||
        (if idx.toNat / 8 = k then s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 (8 * k)) 64 else 0) ∧
      t.gpr .a4 = s.gpr .a4 ∧ t.gpr .t5 = s.gpr .t5 ∧ t.gpr .t6 = s.gpr .t6 ∧ t.gpr .a7 = s.gpr .a7 ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hal' := al_add hal (d := 8 * k) (by omega) (by omega)
  unfold gatherStep rowMask
  rrun [h5, hr, hal', show 8 * k < 2048 by omega, show 63 - k < 64 by omega]
  rw [row_bit idx hk, and_allOnes_ite]; rfl

def GInv (s₀ : State) (idx : Byte) (k : Nat) (t : State) : Prop :=
  t.gpr .t1 = gather s₀.mem (s₀.gpr .a7) idx.toNat k ∧ t.gpr .a4 = s₀.gpr .a4 ∧
    t.gpr .t5 = s₀.gpr .t5 ∧ t.gpr .t6 = s₀.gpr .t6 ∧ t.gpr .a7 = s₀.gpr .a7 ∧ t.mem = s₀.mem ∧
    t.rd = s₀.rd ∧ t.wr = s₀.wr

theorem gather0_run (s : State) (idx : Byte) (h5 : s.gpr .t5 = BitVec.twoPow 64 (idx.toNat / 8))
    (hal : (s.gpr .a7).toNat % 8 = 0) (hr : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256) :
    WP isa (.block gather0) s (GInv s idx 1) := by
  have hr0 : InRegions (s.rd ++ s.wr) (s.gpr .a7) 8 := by
    simpa using region_offset _ _ 256 0 8 (by omega) (by omega) hr
  unfold gather0 rowMask
  rrun [GInv, h5, hr0, hal]
  rw [row_bit idx (k := 0) (by decide), and_allOnes_ite]
  unfold gather
  by_cases h : idx.toNat / 8 = 0
  · rw [ite_eq_left h, ite_eq_left (by omega), h, Nat.mul_zero, BitVec.add_zero]
  · rw [ite_eq_right h, ite_eq_right (by omega)]; rfl

theorem gather_steps (s₀ : State) (idx : Byte) (h5 : s₀.gpr .t5 = BitVec.twoPow 64 (idx.toNat / 8))
    (hal : (s₀.gpr .a7).toNat % 8 = 0)
    (hr : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .a7) 256) :
    ∀ n ≤ 31, ∀ s, GInv s₀ idx 1 s →
      WP isa (.block ((List.range n).flatMap fun k => gatherStep (k + 1))) s (GInv s₀ idx (n + 1)) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun t ht => ?_
    obtain ⟨h1, h4', h5', h6', hp, hm, hrd, hwr⟩ := ht
    have hq : InRegions (t.rd ++ t.wr) (t.gpr .a7 + BitVec.ofNat 64 (8 * (n + 1))) 8 := by
      rw [hrd, hwr, hp]
      exact region_offset _ _ _ _ _ (by omega) (by omega) hr
    refine WP.mono (gather_step t idx (by omega) (h5'.trans h5) (by rw [hp]; exact hal) hq) fun u hu => ?_
    obtain ⟨u1, u4, u5, u6, up, um, urd, uwr⟩ := hu
    refine ⟨?_, u4.trans h4', u5.trans h5', u6.trans h6', up.trans hp, um.trans hm, urd.trans hrd,
      uwr.trans hwr⟩
    rw [u1, h1, hp, hm, gather_succ]

/-! ## The lookup -/

theorem lookup_core (s : State) (idx : Byte) (h4 : s.gpr .a4 = idx.setWidth 64)
    (hal : (s.gpr .a7).toNat % 8 = 0)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256) :
    WP isa (.block lookup) s fun t =>
      t.gpr .a5 = (s.mem (s.gpr .a7 + BitVec.ofNat 64 idx.toNat)).setWidth 64 ∧
      t.gpr .t5 = BitVec.twoPow 64 (idx.toNat / 8) ∧ t.mem = s.mem := by
  have hn := idx.isLt
  simp only [lookup, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t2, .t5] (rowBit_run s idx h4) (by decide +kernel) rfl)
    fun t ⟨⟨t5, tm⟩, tk⟩ => ?_
  have t4 : t.gpr .a4 = s.gpr .a4 := tk.gpr (by decide)
  have tp : t.gpr .a7 = s.gpr .a7 := tk.gpr (by decide)
  have hrt : InRegions (t.rd ++ t.wr) (t.gpr .a7) 256 := by rw [tk.2.1, tk.2.2, tp]; exact hr
  have halt : (t.gpr .a7).toNat % 8 = 0 := by rw [tp]; exact hal
  rw [WP.block_append_iff]
  refine WP.mono (gather0_run t idx t5 halt hrt) fun u hu => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gather_steps t idx t5 halt hrt 31 (by decide) u hu) fun v hv => ?_
  obtain ⟨v1, v4, v5, _, _, vm, _, _⟩ := hv
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t2] (laneShift_run v idx (v4.trans (t4.trans h4))) (by decide +kernel) rfl)
    fun w ⟨⟨w2, wm⟩, wk⟩ => ?_
  have w1 : w.gpr .t1 = v.gpr .t1 := wk.gpr (by decide)
  have w5 : w.gpr .t5 = v.gpr .t5 := wk.gpr (by decide)
  have hL : idx.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  rrun [w2, w1, wm, vm, tm, w5, v5, t5]
  rw [v1, tp]
  unfold gather
  rw [ite_eq_left (by omega), qword_byte _ _ hL, row_lane, tm]

end VG.Proof.Rc4.RISCV64
