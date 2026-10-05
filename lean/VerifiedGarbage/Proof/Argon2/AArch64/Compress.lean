import VerifiedGarbage.Impl.Argon2.AArch64.AddressHeader
import VerifiedGarbage.Impl.Argon2.AArch64.Divide
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.PermuteRows
import VerifiedGarbage.Impl.Argon2.AArch64.Compress
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.Argon2.AArch64.ClearBlock
import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Verified
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Argon2.AArch64.CountCandidates
import VerifiedGarbage.Proof.Argon2.Divide
import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceCount
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Impl.Argon2.AArch64.SelectWindow
import VerifiedGarbage.Impl.Argon2.AArch64.Relative
import VerifiedGarbage.Impl.Argon2.AArch64.Wrap

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.Carry`. -/
section

/-! # Arithmetic facts for ARM64's subtraction carry -/
namespace VG.Proof.Argon2.AArch64

theorem sub_value (a b : BitVec 64) : a + ~~~b + 1#64 = a - b := by
  change a + ~~~b + 1#64 = a - b
  rw [BitVec.add_assoc, ← BitVec.neg_eq_not_add, ← BitVec.sub_eq_add_neg]

theorem sub_carry (a b : BitVec 64) :
    decide (2 ^ 64 ≤ a.toNat + (~~~b).toNat + 1) = decide (b.toNat ≤ a.toNat) := by
  rw [BitVec.toNat_not]
  have hb := b.isLt
  have h : (2 ^ 64 ≤ a.toNat + (2 ^ 64 - 1 - b.toNat) + 1) ↔ b.toNat ≤ a.toNat := by
    simp only [Nat.reducePow] at *
    omega
  simp only [h]

theorem borrow_mask (x : BitVec 64) (b : Bool) :
    x + ~~~x + BitVec.ofNat 64 b.toNat = if b then 0 else -1 := by
  rw [BitVec.not_eq_neg_add, BitVec.sub_eq_add_neg, ← BitVec.add_assoc, ← BitVec.sub_eq_add_neg x x, BitVec.sub_self]
  cases b <;> rfl
end VG.Proof.Argon2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.DivideStep`. -/
section

/-! # One bit of Argon2's fixed-time index division -/

namespace VG.Proof.Argon2.AArch64.Divide

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Divide

/-- All state except the listed registers and arithmetic flags is unchanged. -/
structure Keeps (rs : List Reg) (s t : State) : Prop where
  regs : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem Keeps.mono {rs rs' : List Reg} {s t : State} (h : VG.Proof.Argon2.AArch64.Divide.Keeps rs s t)
    (hh : ∀ r ∈ rs, r ∈ rs') : VG.Proof.Argon2.AArch64.Divide.Keeps rs' s t :=
  ⟨fun r hr => h.regs r (fun hm => hr (hh r hm)), h.mem, h.rd, h.wr, h.sp⟩

theorem Keeps.trans {rs : List Reg} {s t u : State} (h : VG.Proof.Argon2.AArch64.Divide.Keeps rs s t)
    (k : VG.Proof.Argon2.AArch64.Divide.Keeps rs t u) : VG.Proof.Argon2.AArch64.Divide.Keeps rs s u :=
  ⟨fun r hr => (k.regs r hr).trans (h.regs r hr), k.mem.trans h.mem,
    k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp⟩

def mask (b : Bool) : BitVec 64 := if b then -1 else 0

theorem difference_high (a b : BitVec 64) (ha : a.toNat < 2 ^ 63)
    (hb : b.toNat < 2 ^ 63) :
    (a - b) >>> (63 : Nat) = if a.toNat < b.toNat then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight]
  by_cases h : a.toNat < b.toNat
  · rw [ite_eq_left h, BitVec.toNat_sub_of_lt (by rw [BitVec.lt_def]; exact h)]
    simp only [show (1 : BitVec 64).toNat = 1 from rfl, Nat.reducePow] at *
    omega
  · rw [ite_eq_right h, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact Nat.le_of_not_gt h)]
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.reducePow] at *
    omega

theorem subtract_ok (s : State) (j : Nat) (hj : j < 32)
    (ha : (s.gpr .x4).toNat < 2 ^ 32) (hb : (s.gpr .x1).toNat < 2 ^ 32) :
    let v := s.gpr .x4 + s.gpr .x4 +
      (BitVec.ofBool ((s.gpr .x0).getLsbD j)).setWidth 64
    WP isa (.block (subtract j)) s fun t =>
      t.gpr .x4 = v - s.gpr .x1 ∧ t.gpr .x6 = v ∧
      t.gpr .x8 = VG.Proof.Argon2.AArch64.Divide.mask (decide (v.toNat < (s.gpr .x1).toNat)) ∧
      VG.Proof.Argon2.AArch64.Divide.Keeps [.x3, .x4, .x6, .x8, .x9] s t := by
  intro v
  apply WP.of_runBlock
  simp only [subtract, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, RegUpd.gpr_write, Size.bits, show j < 64 by omega,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero, show 0 < 4096 from by decide,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left',
    BitVec.setWidth_eq, BitVec.and_one_eq_setWidth_ofBool_getLsbD,
    BitVec.getLsbD_ushiftRight, show 63 < 64 from by decide,
    show ((1 : BitVec 16).setWidth 64) = 1#64 from rfl,
    show ((0 : BitVec 16).setWidth 64) = 0#64 from rfl, BitVec.add_zero]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · have hv : v.toNat < 2 ^ 63 := by
      have hsum : (s.gpr .x4).toNat + (s.gpr .x4).toNat < 2 ^ 64 := by omega
      have hn := Bool.toNat_le ((s.gpr .x0).getLsbD j)
      simp only [v, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool,
        Nat.mod_eq_of_lt hsum]
      omega
    change (0 : BitVec 64) - ((v - s.gpr .x1) >>> (63 : Nat)) = _
    rw [VG.Proof.Argon2.AArch64.Divide.difference_high _ _ hv (by omega)]
    by_cases h : v.toNat < (s.gpr .x1).toNat <;>
      simp only [VG.Proof.Argon2.AArch64.Divide.mask, h, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] <;> rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
    all_goals rfl

theorem select_value (b : Bool) (reduced original : BitVec 64) :
    reduced ^^^ ((original ^^^ reduced) &&& VG.Proof.Argon2.AArch64.Divide.mask b) =
      if b then original else reduced := by
  cases b
  · apply BitVec.eq_of_toNat_eq
    simp [VG.Proof.Argon2.AArch64.Divide.mask]
  · simp only [VG.Proof.Argon2.AArch64.Divide.mask, ite_true, show (-1 : BitVec 64) = BitVec.allOnes 64 from rfl,
      BitVec.and_allOnes]
    rw [BitVec.xor_comm original reduced, ← BitVec.xor_assoc, BitVec.xor_self,
      BitVec.zero_xor]

theorem select_ok (s : State) (b : Bool) (hm : s.gpr .x8 = VG.Proof.Argon2.AArch64.Divide.mask b) :
    WP isa (.block select) s fun t =>
      t.gpr .x4 = (if b then s.gpr .x6 else s.gpr .x4) ∧
      t.gpr .x5 = (s.gpr .x5 + s.gpr .x5) + (if b then 0 else 1) ∧
      VG.Proof.Argon2.AArch64.Divide.Keeps [.x6, .x4, .x8, .x5] s t := by
  apply WP.of_runBlock
  simp only [select, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, RegUpd.gpr_write,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left',
    BitVec.setWidth_eq, show 1 < 4096 from by decide, hm, VG.Proof.Argon2.AArch64.Divide.select_value]
  refine ⟨trivial, ?_, ?_⟩
  · cases b <;> rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    all_goals rfl

theorem double_bit (x : BitVec 64) (b : Bool) (hx : x.toNat < 2 ^ 32) :
    (x + x + (BitVec.ofBool b).setWidth 64).toNat = 2 * x.toNat + b.toNat := by
  have hsum : x.toNat + x.toNat < 2 ^ 64 := by omega
  cases b <;> simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool,
    Bool.toNat_false, Bool.toNat_true, Nat.zero_mod, Nat.one_mod,
    Nat.mod_eq_of_lt hsum, Nat.add_zero] <;> omega

theorem reduced_value (v d : BitVec 64) :
    (if v.toNat < d.toNat then v else v - d).toNat =
      if v.toNat < d.toNat then v.toNat else v.toNat - d.toNat := by
  split
  · rfl
  · next h =>
    rw [BitVec.toNat_sub]
    have hv := v.isLt
    have hd := d.isLt
    omega

theorem bit_ok (s : State) (j : Nat) (hj : j < 32)
    (hr : (s.gpr .x4).toNat < 2 ^ 32) (hq : (s.gpr .x5).toNat < 2 ^ 32)
    (hd : (s.gpr .x1).toNat < 2 ^ 32) :
    let v := 2 * (s.gpr .x4).toNat + ((s.gpr .x0).getLsbD j).toNat
    let d := (s.gpr .x1).toNat
    WP isa (.block (VG.Impl.Argon2.AArch64.Divide.bit j)) s fun t =>
      (t.gpr .x4).toNat = (if v < d then v else v - d) ∧
      (t.gpr .x5).toNat = 2 * (s.gpr .x5).toNat + (if v < d then 0 else 1) ∧
      VG.Proof.Argon2.AArch64.Divide.Keeps [.x3, .x4, .x6, .x8, .x5, .x9] s t := by
  intro v d
  rw [VG.Impl.Argon2.AArch64.Divide.bit, WP.block_append_iff]
  refine (VG.Proof.Argon2.AArch64.Divide.subtract_ok s j hj hr hd).mono ?_
  rintro u ⟨hu8, hu10, huax, hu⟩
  refine (VG.Proof.Argon2.AArch64.Divide.select_ok u _ huax).mono ?_
  rintro t ⟨ht8, ht9, ht⟩
  have hv := VG.Proof.Argon2.AArch64.Divide.double_bit (s.gpr .x4) ((s.gpr .x0).getLsbD j) hr
  have hu9 := hu.regs .x5 (by decide)
  refine ⟨?_, ?_, (hu.mono (by decide)).trans (ht.mono (by decide))⟩
  · simp only [ht8, hu8, hu10, decide_eq_true_eq]
    rw [VG.Proof.Argon2.AArch64.Divide.reduced_value, hv]
  · simp only [ht9, hu9, hv, decide_eq_true_eq]
    change (s.gpr .x5 + s.gpr .x5 + (if v < d then 0 else 1)).toNat =
      2 * (s.gpr .x5).toNat + (if v < d then 0 else 1)
    by_cases h : v < d
    · simp only [h, ite_true]
      exact VG.Proof.Argon2.AArch64.Divide.double_bit (s.gpr .x5) false hq
    · simp only [h, ite_false]
      exact VG.Proof.Argon2.AArch64.Divide.double_bit (s.gpr .x5) true hq

end VG.Proof.Argon2.AArch64.Divide

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.Mix`. -/
section

/-! # Argon2's modified addition on ARM64 -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Impl.Argon2.AArch64

theorem low32 (x : BitVec 64) :
    (x.setWidth 32).setWidth 64 = x &&& 0xffffffff := by
  rw [BitVec.setWidth_eq_append (by decide)]
  exact (BitVec.and_setWidth_allOnes 32 32 x).symm

theorem addMul_value (a b : BitVec 64) :
    a + b + (a.setWidth 32).setWidth 64 * (b.setWidth 32).setWidth 64 +
      (a.setWidth 32).setWidth 64 * (b.setWidth 32).setWidth 64 =
      Spec.Argon2.addMul a b := by
  rw [VG.Proof.Argon2.AArch64.low32, VG.Proof.Argon2.AArch64.low32, BitVec.add_assoc, ← BitVec.two_mul, Spec.Argon2.addMul,
    BitVec.mul_assoc]
  rfl

theorem addMul_ok {a b : Reg}
    (ha0 : a ≠ .x8) (_ha2 : a ≠ .x9) (ha6 : a ≠ .x10)
    (hb0 : b ≠ .x8) (_hb2 : b ≠ .x9) (hb6 : b ≠ .x10)
    (s : State) :
    WP isa (.block (addMul a b)) s fun t =>
      t.gpr a = Spec.Argon2.addMul (s.gpr a) (s.gpr b) ∧
      (∀ r, r ≠ a → r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [addMul, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    ha0, ha6, hb0, hb6, ha0.symm, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left', BitVec.setWidth_eq, BitVec.or_self]
  refine ⟨VG.Proof.Argon2.AArch64.addMul_value _ _, ?_, trivial, trivial, trivial⟩
  intro r h1 h2 h3 h4
  simp only [h1, h2, h4, ite_false]

/-- A register XOR followed by one of GB's rotations. -/
theorem xorRotate_ok {a d : Reg} (n : Nat)
    (hn : 1 ≤ n) (hn' : n ≤ 63) (s : State) :
    WP isa (.block [.logic .eor .x d d a, .ror .x d d n]) s fun t =>
      t.gpr d = (s.gpr d ^^^ s.gpr a).rotateRight n ∧
      (∀ r, r ≠ d → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  have h64 : n < 64 := by omega
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    h64, ite_true, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.setWidth_eq]
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial, trivial⟩

/-- One half of GB, with all memory and non-working registers preserved. -/
theorem halfGB_ok (r1 r2 : Nat) (h1 : 1 ≤ r1) (h1' : r1 ≤ 63)
    (h2 : 1 ≤ r2) (h2' : r2 ≤ 63) (s : State) :
    let a := Spec.Argon2.addMul (s.gpr .x4) (s.gpr .x5)
    let d := (s.gpr .x7 ^^^ a).rotateRight r1
    let c := Spec.Argon2.addMul (s.gpr .x6) d
    let b := (s.gpr .x5 ^^^ c).rotateRight r2
    WP isa (.block (halfGB r1 r2)) s fun t =>
      t.gpr .x4 = a ∧ t.gpr .x5 = b ∧ t.gpr .x6 = c ∧ t.gpr .x7 = d ∧
      (∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 →
        r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  dsimp only
  rw [halfGB, List.append_assoc, List.append_assoc]
  apply WP.block_append
  refine (VG.Proof.Argon2.AArch64.addMul_ok (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s).mono ?_
  rintro s1 ⟨ha, hk1, hm1, hr1, hw1⟩
  apply WP.block_append
  refine (VG.Proof.Argon2.AArch64.xorRotate_ok r1 h1 h1' s1).mono ?_
  rintro s2 ⟨hd, hk2, hm2, hr2, hw2⟩
  apply WP.block_append
  refine (VG.Proof.Argon2.AArch64.addMul_ok (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s2).mono ?_
  rintro s3 ⟨hc, hk3, hm3, hr3, hw3⟩
  refine (VG.Proof.Argon2.AArch64.xorRotate_ok r2 h2 h2' s3).mono ?_
  rintro s4 ⟨hb, hk4, hm4, hr4, hw4⟩
  have hd' : s2.gpr .x7 =
      (s.gpr .x7 ^^^ Spec.Argon2.addMul (s.gpr .x4) (s.gpr .x5)).rotateRight r1 := by
    rw [hd, ha, hk1 .x7 (by decide) (by decide) (by decide) (by decide)]
  have hc' : s3.gpr .x6 = Spec.Argon2.addMul (s.gpr .x6) (s2.gpr .x7) := by
    rw [hc, hk2 .x6 (by decide), hk1 .x6 (by decide) (by decide) (by decide) (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, hm4.trans (hm3.trans (hm2.trans hm1)),
    hr4.trans (hr3.trans (hr2.trans hr1)), hw4.trans (hw3.trans (hw2.trans hw1))⟩
  · rw [hk4 .x4 (by decide), hk3 .x4 (by decide) (by decide) (by decide) (by decide),
      hk2 .x4 (by decide), ha]
  · rw [hb, hc', hd', hk3 .x5 (by decide) (by decide) (by decide) (by decide),
      hk2 .x5 (by decide), hk1 .x5 (by decide) (by decide) (by decide) (by decide)]
  · rw [hk4 .x6 (by decide), hc', hd']
  · rw [hk4 .x7 (by decide), hk3 .x7 (by decide) (by decide) (by decide) (by decide), hd']
  · intro r h8 h9 h10 h11 h0 hdx hsi
    rw [hk4 r h9, hk3 r h10 h0 hdx hsi, hk2 r h11, hk1 r h8 h0 hdx hsi]

/-- The complete GB operation agrees with the four-word specification. -/
theorem gb_ok (s : State) :
    let v := Proof.Argon2.mix (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
    WP isa (.block gb) s fun t =>
      t.gpr .x4 = v.1 ∧ t.gpr .x5 = v.2.1 ∧
      t.gpr .x6 = v.2.2.1 ∧ t.gpr .x7 = v.2.2.2 ∧
      (∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 →
        r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  dsimp only
  rw [gb]
  apply WP.block_append
  refine (VG.Proof.Argon2.AArch64.halfGB_ok 32 24 (by decide) (by decide) (by decide) (by decide) s).mono ?_
  rintro t ⟨ha, hb, hc, hd, hk, hm, hr, hw⟩
  refine (VG.Proof.Argon2.AArch64.halfGB_ok 16 63 (by decide) (by decide) (by decide) (by decide) t).mono ?_
  rintro u ⟨ha', hb', hc', hd', hk', hm', hr', hw'⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hm'.trans hm, hr'.trans hr, hw'.trans hw⟩
  · rw [ha', ha, hb]; rfl
  · rw [hb', ha, hb, hc, hd]; rfl
  · rw [hc', ha, hb, hc, hd]; rfl
  · rw [hd', ha, hb, hd]; rfl
  · intro r h8 h9 h10 h11 h0 hdx hsi
    exact (hk' r h8 h9 h10 h11 h0 hdx hsi).trans (hk r h8 h9 h10 h11 h0 hdx hsi)

end VG.Proof.Argon2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.Memory`. -/
section

/-! # Argon2 compression working memory -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Impl.Argon2.AArch64

abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d
abbrev word (m : Mem) (p : Addr) (i : Nat) : BitVec 64 := m.readW (VG.Proof.Argon2.AArch64.off p (1024 + 8 * i)) 64

/-- Scratch permissions and its stable base register. -/
structure Scratch (s : State) (p : Addr) : Prop where
  reg : s.gpr .x3 = p
  wr : (⟨p, 4096⟩ : Region) ∈ s.wr

theorem Scratch.write {s : State} {p : Addr} (h : VG.Proof.Argon2.AArch64.Scratch s p) {d n : Nat}
    (hd : d + n ≤ 4096) : InRegions s.wr (VG.Proof.Argon2.AArch64.off p d) n :=
  ⟨_, h.wr, Offset.contains_base p hd (by omega)⟩

theorem Scratch.read {s : State} {p : Addr} (h : VG.Proof.Argon2.AArch64.Scratch s p) {d n : Nat}
    (hd : d + n ≤ 4096) : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.AArch64.off p d) n :=
  ⟨_, List.mem_append_right _ h.wr, Offset.contains_base p hd (by omega)⟩

theorem word_offset (i : Nat) (hi : i < 128) :
    (1024 + 8 * i) % 8 = 0 ∧ 1024 + 8 * i < 32768 := by omega

/-- Load the four words of GB without changing memory or any other register. -/
theorem loadGB_ok (s : State) {p : Addr} (hs : VG.Proof.Argon2.AArch64.Scratch s p) {a b c d : Nat}
    (ha : a < 128) (hb : b < 128) (hc : c < 128) (hd : d < 128) :
    WP isa (.block [
      .ldr .x .x4 .x3 (1024 + 8 * a),
      .ldr .x .x5 .x3 (1024 + 8 * b),
      .ldr .x .x6 .x3 (1024 + 8 * c),
      .ldr .x .x7 .x3 (1024 + 8 * d)]) s fun t =>
      t.gpr .x4 = VG.Proof.Argon2.AArch64.word s.mem p a ∧ t.gpr .x5 = VG.Proof.Argon2.AArch64.word s.mem p b ∧
      t.gpr .x6 = VG.Proof.Argon2.AArch64.word s.mem p c ∧ t.gpr .x7 = VG.Proof.Argon2.AArch64.word s.mem p d ∧
      (∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have la := hs.read (d := 1024 + 8 * a) (n := 8) (by omega)
  have lb := hs.read (d := 1024 + 8 * b) (n := 8) (by omega)
  have lc := hs.read (d := 1024 + 8 * c) (n := 8) (by omega)
  have ld := hs.read (d := 1024 + 8 * d) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_ldr_x (VG.Proof.Argon2.AArch64.word_offset a ha),
    exec_ldr_x (VG.Proof.Argon2.AArch64.word_offset b hb), exec_ldr_x (VG.Proof.Argon2.AArch64.word_offset c hc), exec_ldr_x (VG.Proof.Argon2.AArch64.word_offset d hd),
    hs.reg, la, lb, lc, ld, VG.Proof.Argon2.AArch64.off, VG.Proof.Argon2.AArch64.word, RegUpd.gpr_write,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, reduceCtorEq,
    ite_true, ite_false, Option.some.injEq, exists_eq_left', BitVec.setWidth_eq]
  exact ⟨trivial, trivial, trivial, trivial,
    fun r h1 h2 h3 h4 => by simp only [h1, h2, h3, h4, ite_false], trivial, trivial, trivial⟩

/-- Store the GB result in order, leaving all registers and permissions intact. -/
theorem storeGB_ok (s : State) {p : Addr} (hs : VG.Proof.Argon2.AArch64.Scratch s p) {a b c d : Nat}
    (ha : a < 128) (hb : b < 128) (hc : c < 128) (hd : d < 128) :
    WP isa (.block [
      .str .x .x4 .x3 (1024 + 8 * a),
      .str .x .x5 .x3 (1024 + 8 * b),
      .str .x .x6 .x3 (1024 + 8 * c),
      .str .x .x7 .x3 (1024 + 8 * d)]) s fun t =>
      t.mem = (((s.mem.writeW (VG.Proof.Argon2.AArch64.off p (1024 + 8 * a)) (s.gpr .x4)).writeW
        (VG.Proof.Argon2.AArch64.off p (1024 + 8 * b)) (s.gpr .x5)).writeW
        (VG.Proof.Argon2.AArch64.off p (1024 + 8 * c)) (s.gpr .x6)).writeW
        (VG.Proof.Argon2.AArch64.off p (1024 + 8 * d)) (s.gpr .x7) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have wa := hs.write (d := 1024 + 8 * a) (n := 8) (by omega)
  have wb := hs.write (d := 1024 + 8 * b) (n := 8) (by omega)
  have wc := hs.write (d := 1024 + 8 * c) (n := 8) (by omega)
  have wd := hs.write (d := 1024 + 8 * d) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_str_x (VG.Proof.Argon2.AArch64.word_offset a ha),
    exec_str_x (VG.Proof.Argon2.AArch64.word_offset b hb), exec_str_x (VG.Proof.Argon2.AArch64.word_offset c hc), exec_str_x (VG.Proof.Argon2.AArch64.word_offset d hd),
    hs.reg, wa, wb, wc, wd, VG.Proof.Argon2.AArch64.off, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- Four stores implementing one GB in scratch. -/
def storeMix (m : Mem) (p : Addr) (a b c d : Nat)
    (v : Spec.Argon2.Word × Spec.Argon2.Word × Spec.Argon2.Word × Spec.Argon2.Word) : Mem :=
  (((m.writeW (VG.Proof.Argon2.AArch64.off p (1024 + 8 * a)) v.1).writeW
    (VG.Proof.Argon2.AArch64.off p (1024 + 8 * b)) v.2.1).writeW
    (VG.Proof.Argon2.AArch64.off p (1024 + 8 * c)) v.2.2.1).writeW
    (VG.Proof.Argon2.AArch64.off p (1024 + 8 * d)) v.2.2.2

/-- The complete load/mix/store operation, independently of surrounding words. -/
theorem gbAt_ok (s : State) {p : Addr} (hs : VG.Proof.Argon2.AArch64.Scratch s p) {a b c d : Nat}
    (ha : a < 128) (hb : b < 128) (hc : c < 128) (hd : d < 128) :
    WP isa (gbAt a b c d) s fun t =>
      t.mem = VG.Proof.Argon2.AArch64.storeMix s.mem p a b c d
        (Proof.Argon2.mix (VG.Proof.Argon2.AArch64.word s.mem p a) (VG.Proof.Argon2.AArch64.word s.mem p b)
          (VG.Proof.Argon2.AArch64.word s.mem p c) (VG.Proof.Argon2.AArch64.word s.mem p d)) ∧
      (∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 →
        r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  rw [gbAt]
  apply WP.seq
  refine (VG.Proof.Argon2.AArch64.loadGB_ok s hs ha hb hc hd).mono ?_
  rintro s1 ⟨ha1, hb1, hc1, hd1, hk1, hm1, hr1, hw1⟩
  apply WP.seq
  refine (VG.Proof.Argon2.AArch64.gb_ok s1).mono ?_
  rintro s2 ⟨ha2, hb2, hc2, hd2, hk2, hm2, hr2, hw2⟩
  have hs2 : VG.Proof.Argon2.AArch64.Scratch s2 p := by
    refine ⟨?_, (hw2.trans hw1) ▸ hs.wr⟩
    rw [hk2 .x3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
      hk1 .x3 (by decide) (by decide) (by decide) (by decide), hs.reg]
  refine (VG.Proof.Argon2.AArch64.storeGB_ok s2 hs2 ha hb hc hd).mono ?_
  rintro t ⟨hm3, hk3, hr3, hw3⟩
  refine ⟨?_, ?_, hr3.trans (hr2.trans hr1), hw3.trans (hw2.trans hw1)⟩
  · rw [hm3, ha2, hb2, hc2, hd2, ha1, hb1, hc1, hd1, hm2, hm1]
    rfl
  · intro r h8 h9 h10 h11 h0 hdx hsi
    rw [hk3, hk2 r h8 h9 h10 h11 h0 hdx hsi, hk1 r h8 h9 h10 h11]

end VG.Proof.Argon2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.Words`. -/
section

/-! # The scratch block as a vector of words -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Spec.Argon2

/-- The permuted half of scratch. -/
def working (m : Mem) (p : Addr) : VG.Spec.Argon2.Block := Vector.ofFn fun i => VG.Proof.Argon2.AArch64.word m p i.val

theorem working_get (m : Mem) (p : Addr) (i : Fin 128) :
    (VG.Proof.Argon2.AArch64.working m p)[i] = VG.Proof.Argon2.AArch64.word m p i.val := by
  simp only [VG.Proof.Argon2.AArch64.working, Fin.getElem_fin, Vector.getElem_ofFn]

/-- A write changes exactly the selected word of the block. -/
theorem working_write (m : Mem) (p : Addr) (i : Fin 128) (v : VG.Spec.Argon2.Word) :
    VG.Proof.Argon2.AArch64.working (m.writeW (VG.Proof.Argon2.AArch64.off p (1024 + 8 * i.val)) v) p = (VG.Proof.Argon2.AArch64.working m p).set i v := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Argon2.AArch64.working, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : i.val = j
  · subst j
    simp only [ite_true, VG.Proof.Argon2.AArch64.word, Mem.readW_writeW_self64]
  · simp only [h, ite_false, VG.Proof.Argon2.AArch64.word]
    exact Mem.readW_writeW_sep
      (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

theorem working_storeMix (m : Mem) (p : Addr) (a b c d : Fin 128)
    (v : VG.Spec.Argon2.Word × VG.Spec.Argon2.Word × VG.Spec.Argon2.Word × VG.Spec.Argon2.Word) :
    VG.Proof.Argon2.AArch64.working (VG.Proof.Argon2.AArch64.storeMix m p a.val b.val c.val d.val v) p =
      ((((VG.Proof.Argon2.AArch64.working m p).set a v.1).set b v.2.1).set c v.2.2.1).set d v.2.2.2 := by
  simp only [VG.Proof.Argon2.AArch64.storeMix, VG.Proof.Argon2.AArch64.working_write]

theorem storeMix_frame (m : Mem) (p : Addr) (a b c d : Fin 128)
    (v : VG.Spec.Argon2.Word × VG.Spec.Argon2.Word × VG.Spec.Argon2.Word × VG.Spec.Argon2.Word) :
    Frame [⟨VG.Proof.Argon2.AArch64.off p 1024, 1024⟩] m (VG.Proof.Argon2.AArch64.storeMix m p a.val b.val c.val d.val v) := by
  have inside (i : Fin 128) :
      (⟨VG.Proof.Argon2.AArch64.off p 1024, 1024⟩ : Region).Contains (VG.Proof.Argon2.AArch64.off p (1024 + 8 * i.val)) 8 := by
    exact Offset.contains p (by omega) (by omega) (by omega)
  exact ((((Frame.refl [⟨VG.Proof.Argon2.AArch64.off p 1024, 1024⟩] m).writeW (by simp) v.1 (inside a)).writeW
    (by simp) v.2.1 (inside b)).writeW (by simp) v.2.2.1 (inside c)).writeW
    (by simp) v.2.2.2 (inside d)

/-- GB updates the block vector and only the permuted half of scratch. -/
theorem gbAt_words (s : State) {p : Addr} (hs : VG.Proof.Argon2.AArch64.Scratch s p) (a b c d : Fin 128) :
    WP isa (Impl.Argon2.AArch64.gbAt a.val b.val c.val d.val) s fun t =>
      VG.Proof.Argon2.AArch64.working t.mem p = Proof.Argon2.mixWords (VG.Proof.Argon2.AArch64.working s.mem p) a b c d ∧
      Frame [⟨VG.Proof.Argon2.AArch64.off p 1024, 1024⟩] s.mem t.mem ∧
      (∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 →
        r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  refine (VG.Proof.Argon2.AArch64.gbAt_ok s hs a.isLt b.isLt c.isLt d.isLt).mono ?_
  rintro t ⟨hm, hk, hr, hw⟩
  refine ⟨?_, ?_, hk, hr, hw⟩
  · rw [hm, VG.Proof.Argon2.AArch64.working_storeMix]
    simp only [Proof.Argon2.mixWords, VG.Proof.Argon2.AArch64.working_get]
  · rw [hm]
    exact VG.Proof.Argon2.AArch64.storeMix_frame s.mem p a b c d _

end VG.Proof.Argon2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.Initialize`. -/
section

/-! Merged from `Proof.Argon2.AArch64.Copy`. -/
section
/-! # Initial XOR and final XOR, one word at a time -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Impl.Argon2.AArch64

theorem initWord_ok (s : State) {p : Addr} (hs : VG.Proof.Argon2.AArch64.Scratch s p) (i : Fin 128)
    (hx : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.AArch64.off (s.gpr .x0) (8 * i.val)) 8)
    (hy : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.AArch64.off (s.gpr .x1) (8 * i.val)) 8) :
    let v := s.mem.readW (VG.Proof.Argon2.AArch64.off (s.gpr .x0) (8 * i.val)) 64 ^^^
      s.mem.readW (VG.Proof.Argon2.AArch64.off (s.gpr .x1) (8 * i.val)) 64
    WP isa (.block (initWord i.val)) s fun t =>
      t.mem = (s.mem.writeW (VG.Proof.Argon2.AArch64.off p (8 * i.val)) v).writeW (VG.Proof.Argon2.AArch64.off p (1024 + 8 * i.val)) v ∧
      (∀ r, r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  dsimp only
  have w1 := hs.write (d := 8 * i.val) (n := 8) (by omega)
  have w2 := hs.write (d := 1024 + 8 * i.val) (n := 8) (by omega)
  have e1 : (8 * i.val) % 8 = 0 ∧ 8 * i.val < 32768 := by omega
  have e2 := VG.Proof.Argon2.AArch64.word_offset i.val i.isLt
  apply WP.of_runBlock
  simp only [initWord, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, e1, e2, and_self, ite_true, Option.bind_some,
    State.load, State.store, VG.Proof.Argon2.AArch64.off, hs.reg, hx, hy, w1, w2, State.read,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    Mem.readW, Mem.writeW, reduceCtorEq, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left', BitVec.setWidth_eq]
  exact ⟨trivial, fun r hr hr9 => by simp only [hr, hr9, ite_false], trivial⟩

theorem finishWord_ok (s : State) {p : Addr} (hs : VG.Proof.Argon2.AArch64.Scratch s p) (i : Fin 128)
    (hout : InRegions s.wr (VG.Proof.Argon2.AArch64.off (s.gpr .x2) (8 * i.val)) 8) :
    WP isa (.block (finishWord i.val)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.Argon2.AArch64.off (s.gpr .x2) (8 * i.val))
        (VG.Proof.Argon2.AArch64.word s.mem p i.val ^^^ s.mem.readW (VG.Proof.Argon2.AArch64.off p (8 * i.val)) 64) ∧
      (∀ r, r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have r1 := hs.read (d := 8 * i.val) (n := 8) (by omega)
  have r2 := hs.read (d := 1024 + 8 * i.val) (n := 8) (by omega)
  have e1 : (8 * i.val) % 8 = 0 ∧ 8 * i.val < 32768 := by omega
  have e2 := VG.Proof.Argon2.AArch64.word_offset i.val i.isLt
  apply WP.of_runBlock
  simp only [finishWord, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, e1, e2, and_self, ite_true, Option.bind_some,
    State.load, State.store, VG.Proof.Argon2.AArch64.off, hs.reg, hout, r1, r2, State.read,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    Mem.readW, Mem.writeW, reduceCtorEq, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left', BitVec.setWidth_eq]
  exact ⟨trivial, fun r hr hr9 => by simp only [hr, hr9, ite_false], trivial⟩

end VG.Proof.Argon2.AArch64
end

/-! # Copy X XOR Y into both scratch blocks -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Spec.Argon2

theorem blockAt_get (m : Mem) (p : Addr) (i : Fin 128) :
    (VG.Spec.Argon2.blockAt m p)[i] = m.readW (VG.Proof.Argon2.AArch64.off p (8 * i.val)) 64 := by
  simp only [VG.Spec.Argon2.blockAt, Fin.getElem_fin, Vector.getElem_ofFn, Mem.readW, BitVec.setWidth_eq]

/-- Copying loops change only x8, x9, and memory. -/
def CopyKeeps (s t : State) : Prop :=
  (∀ r, r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem CopyKeeps.refl (s : State) : VG.Proof.Argon2.AArch64.CopyKeeps s s := ⟨fun _ _ _ => rfl, rfl, rfl⟩

theorem CopyKeeps.trans {s t u : State} (h : VG.Proof.Argon2.AArch64.CopyKeeps s t) (h' : VG.Proof.Argon2.AArch64.CopyKeeps t u) : VG.Proof.Argon2.AArch64.CopyKeeps s u :=
  ⟨fun r hr hr9 => (h'.1 r hr hr9).trans (h.1 r hr hr9), h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

theorem Scratch.of_copy {s t : State} {p : Addr} (hs : VG.Proof.Argon2.AArch64.Scratch s p) (h : VG.Proof.Argon2.AArch64.CopyKeeps s t) :
    VG.Proof.Argon2.AArch64.Scratch t p := ⟨(h.1 .x3 (by decide) (by decide)).trans hs.reg, h.2.2 ▸ hs.wr⟩

structure Inputs (s : State) (x y p : Addr) : Prop where
  xreg : s.gpr .x0 = x
  yreg : s.gpr .x1 = y
  xread : (⟨x, 1024⟩ : Region) ∈ s.rd ++ s.wr
  yread : (⟨y, 1024⟩ : Region) ∈ s.rd ++ s.wr
  xsep : (⟨x, 1024⟩ : Region).Disjoint ⟨p, 4096⟩
  ysep : (⟨y, 1024⟩ : Region).Disjoint ⟨p, 4096⟩

theorem Inputs.of_copy {s t : State} {x y p : Addr} (h : VG.Proof.Argon2.AArch64.Inputs s x y p) (hk : VG.Proof.Argon2.AArch64.CopyKeeps s t) :
    VG.Proof.Argon2.AArch64.Inputs t x y p := ⟨(hk.1 .x0 (by decide) (by decide)).trans h.xreg,
      (hk.1 .x1 (by decide) (by decide)).trans h.yreg, by simpa only [hk.2.1, hk.2.2] using h.xread,
      by simpa only [hk.2.1, hk.2.2] using h.yread, h.xsep, h.ysep⟩

theorem input_read {s : State} {x : Addr} (h : (⟨x, 1024⟩ : Region) ∈ s.rd ++ s.wr)
    (i : Fin 128) : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.AArch64.off x (8 * i.val)) 8 :=
  ⟨_, h, Offset.contains_base x (by omega) (by omega)⟩

theorem input_unchanged {m m' : Mem} {x p : Addr} (hf : Frame [⟨p, 4096⟩] m m')
    (hd : (⟨x, 1024⟩ : Region).Disjoint ⟨p, 4096⟩) (i : Fin 128) :
    m'.readW (VG.Proof.Argon2.AArch64.off x (8 * i.val)) 64 = m.readW (VG.Proof.Argon2.AArch64.off x (8 * i.val)) 64 :=
  hf.readW (r := ⟨x, 1024⟩) (Offset.contains_base x (by omega) (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

/-- A prefix of the two scratch copies is initialized. -/
def Initialized (m : Mem) (p : Addr) (r : VG.Spec.Argon2.Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val < n →
    m.readW (VG.Proof.Argon2.AArch64.off p (8 * i.val)) 64 = r[i] ∧ VG.Proof.Argon2.AArch64.word m p i.val = r[i]

theorem init_store_frame (m : Mem) (p : Addr) (i : Fin 128) (v : VG.Spec.Argon2.Word) :
    Frame [⟨p, 4096⟩] m
      ((m.writeW (VG.Proof.Argon2.AArch64.off p (8 * i.val)) v).writeW (VG.Proof.Argon2.AArch64.off p (1024 + 8 * i.val)) v) :=
  ((Frame.refl [⟨p, 4096⟩] m).writeW (r := ⟨p, 4096⟩) (by simp) v (Offset.contains_base p (by omega) (by omega))).writeW (r := ⟨p, 4096⟩)
    (by simp) v (Offset.contains_base p (by omega) (by omega))

theorem initialized_step {m : Mem} {p : Addr} {r : VG.Spec.Argon2.Block} {n : Nat}
    (hn : n < 128) (h : VG.Proof.Argon2.AArch64.Initialized m p r n) :
    VG.Proof.Argon2.AArch64.Initialized ((m.writeW (VG.Proof.Argon2.AArch64.off p (8 * n)) r[n]).writeW
      (VG.Proof.Argon2.AArch64.off p (1024 + 8 * n)) r[n]) p r (n + 1) := by
  intro i hi
  have lower (v : VG.Spec.Argon2.Word) :
      ((m.writeW (VG.Proof.Argon2.AArch64.off p (8 * n)) r[n]).writeW (VG.Proof.Argon2.AArch64.off p (1024 + 8 * n)) v).readW
        (VG.Proof.Argon2.AArch64.off p (8 * i.val)) 64 = (m.writeW (VG.Proof.Argon2.AArch64.off p (8 * n)) r[n]).readW
        (VG.Proof.Argon2.AArch64.off p (8 * i.val)) 64 :=
    Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)
  by_cases he : i.val = n
  · subst n
    simp only [VG.Proof.Argon2.AArch64.word, lower, Mem.readW_writeW_self64]
    exact ⟨rfl, rfl⟩
  · have hi' : i.val < n := by omega
    have sep1 : Mem.Sep (VG.Proof.Argon2.AArch64.off p (8 * i.val)) 8 (VG.Proof.Argon2.AArch64.off p (8 * n)) 8 :=
      Offset.sep p (by omega) (by omega) (by omega)
    have sep2 : Mem.Sep (VG.Proof.Argon2.AArch64.off p (1024 + 8 * i.val)) 8 (VG.Proof.Argon2.AArch64.off p (1024 + 8 * n)) 8 :=
      Offset.sep p (by omega) (by omega) (by omega)
    have sep3 : Mem.Sep (VG.Proof.Argon2.AArch64.off p (1024 + 8 * i.val)) 8 (VG.Proof.Argon2.AArch64.off p (8 * n)) 8 :=
      Offset.sep p (by omega) (by omega) (by omega)
    simp only [VG.Proof.Argon2.AArch64.word, lower, Mem.readW_writeW_sep (w := 64) (w' := 64) sep1 (by decide),
      Mem.readW_writeW_sep (w := 64) (w' := 64) sep2 (by decide), Mem.readW_writeW_sep (w := 64) (w' := 64) sep3 (by decide)]
    exact h i hi'

theorem xorBlock_get (a b : VG.Spec.Argon2.Block) (i : Fin 128) :
    (xorBlock a b)[i] = a[i] ^^^ b[i] := by
  simp only [xorBlock, Fin.getElem_fin, Vector.getElem_zipWith]

/-- Initialize an arbitrary prefix, framing both input blocks. -/
theorem init_prefix (n : Nat) (hn : n ≤ 128) (s : State) {x y p : Addr}
    (hs : VG.Proof.Argon2.AArch64.Scratch s p) (hin : VG.Proof.Argon2.AArch64.Inputs s x y p) :
    WP isa (.block ((List.range n).flatMap Impl.Argon2.AArch64.initWord)) s fun t =>
      VG.Proof.Argon2.AArch64.Initialized t.mem p (xorBlock (VG.Spec.Argon2.blockAt s.mem x) (VG.Spec.Argon2.blockAt s.mem y)) n ∧
      Frame [⟨p, 4096⟩] s.mem t.mem ∧ VG.Proof.Argon2.AArch64.CopyKeeps s t := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨fun i hi => by omega, Frame.refl _ _, CopyKeeps.refl s⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    have hn' : n < 128 := by omega
    have htIn := hin.of_copy hk
    have lx : InRegions (t.rd ++ t.wr) (VG.Proof.Argon2.AArch64.off (t.gpr .x0) (8 * n)) 8 := by
      rw [htIn.xreg]
      exact VG.Proof.Argon2.AArch64.input_read htIn.xread ⟨n, hn'⟩
    have ly : InRegions (t.rd ++ t.wr) (VG.Proof.Argon2.AArch64.off (t.gpr .x1) (8 * n)) 8 := by
      rw [htIn.yreg]
      exact VG.Proof.Argon2.AArch64.input_read htIn.yread ⟨n, hn'⟩
    refine (VG.Proof.Argon2.AArch64.initWord_ok t (hs.of_copy hk) ⟨n, hn'⟩ lx ly).mono ?_
    rintro u ⟨hm, hreg, hr, hw⟩
    have hv : t.mem.readW (VG.Proof.Argon2.AArch64.off x (8 * n)) 64 ^^^ t.mem.readW (VG.Proof.Argon2.AArch64.off y (8 * n)) 64 =
        (xorBlock (VG.Spec.Argon2.blockAt s.mem x) (VG.Spec.Argon2.blockAt s.mem y))[(⟨n, hn'⟩ : Fin 128)] := by
      rw [VG.Proof.Argon2.AArch64.xorBlock_get, VG.Proof.Argon2.AArch64.blockAt_get, VG.Proof.Argon2.AArch64.blockAt_get,
        VG.Proof.Argon2.AArch64.input_unchanged hf hin.xsep ⟨n, hn'⟩, VG.Proof.Argon2.AArch64.input_unchanged hf hin.ysep ⟨n, hn'⟩]
    refine ⟨?_, ?_, hk.trans ⟨hreg, hr, hw⟩⟩
    · rw [hm, htIn.xreg, htIn.yreg, hv]
      exact VG.Proof.Argon2.AArch64.initialized_step hn' ht
    · rw [hm, htIn.xreg, htIn.yreg]
      exact hf.trans (VG.Proof.Argon2.AArch64.init_store_frame t.mem p ⟨n, hn'⟩ _)

/-- The initialized copies both contain X XOR Y. -/
theorem initialized_blocks {m : Mem} {p : Addr} {r : VG.Spec.Argon2.Block} (h : VG.Proof.Argon2.AArch64.Initialized m p r 128) :
    VG.Spec.Argon2.blockAt m p = r ∧ VG.Proof.Argon2.AArch64.working m p = r := by
  constructor
  · apply Vector.ext
    intro i hi
    have he := (h ⟨i, hi⟩ hi).1
    rw [← VG.Proof.Argon2.AArch64.blockAt_get m p ⟨i, hi⟩] at he
    exact he
  · apply Vector.ext
    intro i hi
    have he := (h ⟨i, hi⟩ hi).2
    rw [← VG.Proof.Argon2.AArch64.working_get m p ⟨i, hi⟩] at he
    exact he

end VG.Proof.Argon2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.AddressHeaderWords`. -/
section

/-! Merged from `Proof.Argon2.AArch64.BlockStore`. -/
section
/-! A single matrix or scratch block word write as a vector update. -/

namespace VG.Proof.Argon2.AArch64

open VG VG.Spec.Argon2

theorem blockAt_write (m : Mem) (p : Addr) (i : Fin 128) (v : VG.Spec.Argon2.Word) :
    VG.Spec.Argon2.blockAt (m.writeW (VG.Proof.Argon2.AArch64.off p (8 * i.val)) v) p = (VG.Spec.Argon2.blockAt m p).set i v := by
  apply Vector.ext
  intro j hj
  simp only [VG.Spec.Argon2.blockAt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases eq : i.val = j
  · subst j
    simp only [ite_true]
    change (m.writeW (VG.Proof.Argon2.AArch64.off p (8 * i.val)) v).readW (VG.Proof.Argon2.AArch64.off p (8 * i.val)) 64 = v
    exact Mem.readW_writeW_self64 _ _ _
  · simp only [eq, ite_false]
    change (m.writeW (VG.Proof.Argon2.AArch64.off p (8 * i.val)) v).readW (VG.Proof.Argon2.AArch64.off p (8 * j)) 64 =
      m.readW (VG.Proof.Argon2.AArch64.off p (8 * j)) 64
    exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

theorem blockAt_write_nat (m : Mem) (p : Addr) (i : Nat) (hi : i < 128) (v : VG.Spec.Argon2.Word) :
    VG.Spec.Argon2.blockAt (m.writeW (VG.Proof.Argon2.AArch64.off p (8 * i)) v) p = (VG.Spec.Argon2.blockAt m p).set i v hi :=
  VG.Proof.Argon2.AArch64.blockAt_write m p ⟨i, hi⟩ v

end VG.Proof.Argon2.AArch64
end

/-! Short independent-address input header writes. -/

namespace VG.Proof.Argon2.AArch64.AddressHeader

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressHeader

theorem registerWord_ok (s : State) (i : Nat) (r : Reg)
    (hi : i < 128)
    (hw : InRegions s.wr (VG.Proof.Argon2.AArch64.off (s.gpr .x0) (8 * i)) 8) :
    WP isa (.block (registerWord i r)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.Argon2.AArch64.off (s.gpr .x0) (8 * i)) (s.gpr r) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [VG.Proof.Argon2.AArch64.off] at hw
  have addrBound : (8 * i) % 8 = 0 ∧ 8 * i < 32768 := by omega
  apply WP.of_runBlock
  simp only [registerWord, VG.Impl.Argon2.AArch64.Instructions.store,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, addrBound, hw,
    and_self, ite_true, State.store, State.read, BitVec.setWidth_eq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial⟩

theorem frameWord_ok (s : State) (i offset : Nat) (hi : i < 128)
    (ha : offset % 8 = 0) (hb : offset + 8 ≤ 272)
    (hr : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.AArch64.off (s.gpr .x19) offset) 8)
    (hw : InRegions s.wr (VG.Proof.Argon2.AArch64.off (s.gpr .x0) (8 * i)) 8) :
    WP isa (.block (frameWord i offset)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.Argon2.AArch64.off (s.gpr .x0) (8 * i))
        (s.mem.readW (VG.Proof.Argon2.AArch64.off (s.gpr .x19) offset) 64) ∧
      (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [VG.Proof.Argon2.AArch64.off] at hr hw
  have addrBound : (8 * i) % 8 = 0 ∧ 8 * i < 32768 := by omega
  have offsetBound : offset % 8 = 0 ∧ offset < 32768 := ⟨ha, by omega⟩
  apply WP.of_runBlock
  simp only [frameWord, VG.Impl.Argon2.AArch64.Instructions.store,
    VG.Impl.Argon2.AArch64.Instructions.load,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, addrBound,
    offsetBound, hr, hw, and_self, ite_true, State.store, State.load, State.read,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.setWidth_eq, reduceCtorEq, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, trivial, trivial, rfl⟩
  intro r hr
  simp only [hr, ite_false]

end VG.Proof.Argon2.AArch64.AddressHeader

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitClearMemory`. -/
section

/-! # Zeroing the Argon2 matrix, independently of its initial contents -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit

def clearMem (m : Mem) (p : Addr) : Nat → Mem
  | 0 => m
  | n + 1 => (VG.Proof.Argon2.AArch64.MemoryInit.clearMem m p n).writeW (p + BitVec.ofNat 64 (8 * n)) (0 : BitVec 64)

theorem clearMem_frame (m : Mem) (p : Addr) (n : Nat) (bound : 8 * n < 2 ^ 64) :
    Frame [⟨p, 8 * n⟩] m (VG.Proof.Argon2.AArch64.MemoryInit.clearMem m p n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    have smaller : Frame [⟨p, 8 * (n + 1)⟩] m (VG.Proof.Argon2.AArch64.MemoryInit.clearMem m p n) :=
      (ih (by omega)).sub (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
    exact smaller.writeW (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains_base _ (by omega) (by omega))

theorem clearMem_word (m : Mem) (p : Addr) (n j : Nat)
    (bound : 8 * n < 2 ^ 64) (hj : j < n) :
    (VG.Proof.Argon2.AArch64.MemoryInit.clearMem m p n).readW (p + BitVec.ofNat 64 (8 * j)) 64 = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [VG.Proof.Argon2.AArch64.MemoryInit.clearMem]
    by_cases eq : j = n
    · subst j; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep ?_ (by decide)]
      · exact ih (by omega) (by omega)
      · exact Offset.sep p (by omega) (by omega) (by omega)

end VG.Proof.Argon2.AArch64.MemoryInit

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.ClearBlock`. -/
section

/-! Zero every word, preserving the enclosing loop's registers and memory. -/

namespace VG.Proof.Argon2.AArch64.ClearBlock

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.ClearBlock

theorem word_ok (s : State) (i : Nat) (hi : i < 128)
    (hw : InRegions s.wr (VG.Proof.Argon2.AArch64.off (s.gpr .x0) (8 * i)) 8) :
    WP isa (.block (Impl.Argon2.AArch64.ClearBlock.word i)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.Argon2.AArch64.off (s.gpr .x0) (8 * i)) (s.gpr .x8) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp :=
  AddressHeader.registerWord_ok s i .x8 hi hw

theorem prefix_ok (n : Nat) (hn : n ≤ 128) (s : State) (zero : s.gpr .x8 = 0)
    (write : Covers [⟨s.gpr .x0, 1024⟩] s.wr) :
    WP isa (.block (words n)) s fun t =>
      t.mem = MemoryInit.clearMem s.mem (s.gpr .x0) n ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    simp only [words, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro a ⟨mem, regs, rd, wr, mx⟩
    have hw : InRegions a.wr (VG.Proof.Argon2.AArch64.off (a.gpr .x0) (8 * n)) 8 := by
      rw [regs, wr]
      exact write _ _ ⟨⟨s.gpr .x0, 1024⟩, by simp,
        Offset.contains_base _ (d := 8 * n) (n := 8) (k := 1024) (by omega) (by omega)⟩
    refine (VG.Proof.Argon2.AArch64.ClearBlock.word_ok a n (by omega) hw).mono ?_
    rintro t ⟨mem', regs', rd', wr', mx'⟩
    refine ⟨?_, regs'.trans regs, rd'.trans rd, wr'.trans wr, mx'.trans mx⟩
    rw [mem', regs, zero, mem]
    rfl

theorem zero_ok (s : State) :
    WP isa (.block [VG.Impl.Argon2.AArch64.Instructions.imm .x8 0].flatten) s fun t =>
      t.gpr .x8 = 0 ∧ (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.Instructions.imm,
    show 0 < 65536 from by decide, ite_true, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro r hr
  exact ite_eq_right hr

theorem code_ok (s : State) (write : Covers [⟨s.gpr .x0, 1024⟩] s.wr) :
    WP isa VG.Impl.Argon2.AArch64.ClearBlock.code s fun t => blockAt t.mem (s.gpr .x0) = zeroBlock ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.AArch64.CopyKeeps s t ∧ t.sp = s.sp := by
  unfold VG.Impl.Argon2.AArch64.ClearBlock.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.ClearBlock.zero_ok s).mono ?_)
  rintro a ⟨zero, regs, mem, rd, wr, mx⟩
  have dest : a.gpr .x0 = s.gpr .x0 := regs .x0 (by decide)
  have write' : Covers [⟨a.gpr .x0, 1024⟩] a.wr := by rw [dest, wr]; exact write
  refine (VG.Proof.Argon2.AArch64.ClearBlock.prefix_ok 128 (by decide) a zero write').mono ?_
  rintro t ⟨mem', regs', rd', wr', mx'⟩
  have cleared : t.mem = MemoryInit.clearMem s.mem (s.gpr .x0) 128 := by
    rw [mem', mem, dest]
  refine ⟨?_, ?_, ⟨fun r hr _ => (congrFun regs' r).trans (regs r hr), rd'.trans rd, wr'.trans wr⟩,
    mx'.trans mx⟩
  · rw [cleared]
    apply Vector.ext
    intro i hi
    change (blockAt _ _)[(⟨i, hi⟩ : Fin 128)] = zeroBlock[(⟨i, hi⟩ : Fin 128)]
    rw [VG.Proof.Argon2.AArch64.blockAt_get, MemoryInit.clearMem_word _ _ 128 i (by decide) hi]
    simp only [zeroBlock, Fin.getElem_fin, Vector.getElem_replicate]
  · rw [cleared]
    exact MemoryInit.clearMem_frame _ _ 128 (by decide)

end VG.Proof.Argon2.AArch64.ClearBlock

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.Finish`. -/
section

/-! # XOR the permuted block with R and write the output -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Spec.Argon2

/-- A prefix of the output block has been written. -/
def Written (m : Mem) (out : Addr) (r : VG.Spec.Argon2.Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val < n → m.readW (VG.Proof.Argon2.AArch64.off out (8 * i.val)) 64 = r[i]

theorem written_step {m : Mem} {out : Addr} {r : VG.Spec.Argon2.Block} {n : Nat}
    (hn : n < 128) (h : VG.Proof.Argon2.AArch64.Written m out r n) :
    VG.Proof.Argon2.AArch64.Written (m.writeW (VG.Proof.Argon2.AArch64.off out (8 * n)) r[n]) out r (n + 1) := by
  intro i hi
  by_cases he : i.val = n
  · subst n
    exact Mem.readW_writeW_self64 _ _ _
  · rw [Mem.readW_writeW_sep (Offset.sep out (by omega) (by omega) (by omega)) (by decide)]
    exact h i (by omega)

theorem scratch_unchanged {m m' : Mem} {out p : Addr} (hf : Frame [⟨out, 1024⟩] m m')
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) {d : Nat} (hd' : d + 8 ≤ 4096) :
    m'.readW (VG.Proof.Argon2.AArch64.off p d) 64 = m.readW (VG.Proof.Argon2.AArch64.off p d) 64 :=
  hf.readW (r := ⟨p, 4096⟩) (Offset.contains_base p hd' (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

/-- Finish an arbitrary prefix while preserving the complete scratch allocation. -/
theorem finish_prefix (n : Nat) (hn : n ≤ 128) (s : State) {p out : Addr}
    (hs : VG.Proof.Argon2.AArch64.Scratch s p) (ho : s.gpr .x2 = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) :
    WP isa (.block ((List.range n).flatMap Impl.Argon2.AArch64.finishWord)) s fun t =>
      VG.Proof.Argon2.AArch64.Written t.mem out (xorBlock (VG.Proof.Argon2.AArch64.working s.mem p) (VG.Spec.Argon2.blockAt s.mem p)) n ∧
      Frame [⟨out, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.AArch64.CopyKeeps s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega, Frame.refl _ _, CopyKeeps.refl s⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    have hn' : n < 128 := by omega
    have ho' : t.gpr .x2 = out := (hk.1 .x2 (by decide) (by decide)).trans ho
    have hout : InRegions t.wr (VG.Proof.Argon2.AArch64.off (t.gpr .x2) (8 * n)) 8 := by
      rw [ho', hk.2.2]
      exact ⟨_, hw, Offset.contains_base out (by omega) (by omega)⟩
    refine (VG.Proof.Argon2.AArch64.finishWord_ok t (hs.of_copy hk) ⟨n, hn'⟩ hout).mono ?_
    rintro u ⟨hm, hreg, hr, hw'⟩
    have hv : VG.Proof.Argon2.AArch64.word t.mem p n ^^^ t.mem.readW (VG.Proof.Argon2.AArch64.off p (8 * n)) 64 =
        (xorBlock (VG.Proof.Argon2.AArch64.working s.mem p) (VG.Spec.Argon2.blockAt s.mem p))[(⟨n, hn'⟩ : Fin 128)] := by
      rw [VG.Proof.Argon2.AArch64.xorBlock_get, VG.Proof.Argon2.AArch64.working_get, VG.Proof.Argon2.AArch64.blockAt_get]
      simp only [VG.Proof.Argon2.AArch64.word, VG.Proof.Argon2.AArch64.scratch_unchanged hf hd (d := 1024 + 8 * n) (by omega),
        VG.Proof.Argon2.AArch64.scratch_unchanged hf hd (d := 8 * n) (by omega)]
    refine ⟨?_, ?_, hk.trans ⟨hreg, hr, hw'⟩⟩
    · rw [hm, ho', hv]
      exact VG.Proof.Argon2.AArch64.written_step hn' ht
    · rw [hm, ho']
      exact hf.writeW (r := ⟨out, 1024⟩) (by simp) _
        (Offset.contains_base out (by omega) (by omega))

theorem written_block {m : Mem} {out : Addr} {r : VG.Spec.Argon2.Block} (h : VG.Proof.Argon2.AArch64.Written m out r 128) :
    VG.Spec.Argon2.blockAt m out = r := by
  apply Vector.ext
  intro i hi
  have he := h ⟨i, hi⟩ hi
  rw [← VG.Proof.Argon2.AArch64.blockAt_get m out ⟨i, hi⟩] at he
  exact he

end VG.Proof.Argon2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.Compress`. -/
section

section

/-! Merged from `Proof.Argon2.AArch64.Lit`. -/
section
/-! # Argon2 compression as a checked instruction literal -/

namespace VG.Proof.Argon2.AArch64

materialize_code compress := Impl.Argon2.AArch64.compress

end VG.Proof.Argon2.AArch64
end

/-! Merged from `Proof.Argon2.AArch64.Contract`. -/
section
/-! # A local contract for Argon2 block compression -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Spec.Argon2

def compressLocal : Contract isa where
  pre s :=
    let x : Region := ⟨s.gpr .x0, 1024⟩
    let y : Region := ⟨s.gpr .x1, 1024⟩
    let out : Region := ⟨s.gpr .x2, 1024⟩
    let scratch : Region := ⟨s.gpr .x3, 4096⟩
    s.rd = [x, y] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ x.Disjoint scratch ∧ y.Disjoint scratch
  post s t := VG.Spec.Argon2.blockAt t.mem (s.gpr .x2) =
    VG.Spec.Argon2.compress (VG.Spec.Argon2.blockAt s.mem (s.gpr .x0)) (VG.Spec.Argon2.blockAt s.mem (s.gpr .x1))
  pub s t := s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧ s.sp = t.sp

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x6000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]
  wr := [⟨0x3000, 1024⟩, ⟨0x4000, 4096⟩]

theorem compress_implies : compressLocal.Implies (VG.Spec.Argon2.compressContract AArch64.abi) := by
  sig_implies [VG.Spec.Argon2.compressContract, VG.Spec.Argon2.compressSig, VG.Proof.Argon2.AArch64.compressLocal, AArch64.abi, AArch64.argRegs]
    [satState] using VG.Proof.Argon2.AArch64.satState

end VG.Proof.Argon2.AArch64
end

/-! Constant-time compression: memory contents never determine an address or branch. -/
namespace VG.Proof.Argon2.AArch64
open VG VG.AArch64

def initialTaint : AArch64.Taint.T := Taint.ofRegs [.x0, .x1, .x2, .x3]

theorem initial_agree {s t : State} (hp : compressLocal.pub s t) :
    AArch64.Taint.Agree VG.Proof.Argon2.AArch64.initialTaint s t := by
  obtain ⟨h0, h1, h2, h3, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.Proof.Argon2.AArch64.initialTaint, Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem compress_ct : ConstantTime isa compressLocal.pre compressLocal.pub
    Impl.Argon2.AArch64.compress :=
  VG.Taint.constantTime (A := VG.AArch64.taint) VG.Proof.Argon2.AArch64.initialTaint (fun _ _ _ _ hp => VG.Proof.Argon2.AArch64.initial_agree hp)
    (by taint_decide)
end VG.Proof.Argon2.AArch64

end

/-! Merged from `Proof.Argon2.AArch64.Round`. -/
section
/-! # The row and column permutations in scratch -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Spec.Argon2
open VG.Proof.Argon2

/-- Registers and permissions preserved throughout a scratch permutation. -/
def Keeps (s t : State) : Prop :=
  (∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 →
    r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧
  t.rd = s.rd ∧ t.wr = s.wr

theorem Keeps.refl (s : State) : VG.Proof.Argon2.AArch64.Keeps s s := ⟨fun _ _ _ _ _ _ _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {s t u : State} (h : VG.Proof.Argon2.AArch64.Keeps s t) (h' : VG.Proof.Argon2.AArch64.Keeps t u) : VG.Proof.Argon2.AArch64.Keeps s u :=
  ⟨fun r h8 h9 h10 h11 h0 hdx hsi =>
    (h'.1 r h8 h9 h10 h11 h0 hdx hsi).trans (h.1 r h8 h9 h10 h11 h0 hdx hsi),
    h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

theorem Scratch.of_keeps {s t : State} {p : Addr} (hs : VG.Proof.Argon2.AArch64.Scratch s p)
    (hk : VG.Proof.Argon2.AArch64.Keeps s t) : VG.Proof.Argon2.AArch64.Scratch t p :=
  ⟨(hk.1 .x3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans hs.reg, hk.2.2 ▸ hs.wr⟩

/-- The selected sixteen words and the unchanged words outside them. -/
def Holds (index : Fin 16 → Fin 128) (b : VG.Spec.Argon2.Block) (v : Vector VG.Spec.Argon2.Word 16)
    (m : Mem) (p : Addr) : Prop :=
  gather index (VG.Proof.Argon2.AArch64.working m p) = v ∧
  ∀ k : Fin 128, (∀ j, index j ≠ k) → (VG.Proof.Argon2.AArch64.working m p)[k] = b[k]

theorem holds_self (index : Fin 16 → Fin 128) (m : Mem) (p : Addr) :
    VG.Proof.Argon2.AArch64.Holds index (VG.Proof.Argon2.AArch64.working m p) (gather index (VG.Proof.Argon2.AArch64.working m p)) m p :=
  ⟨rfl, fun _ _ => rfl⟩

/-- One GB advances the selected row or column and preserves its complement. -/
theorem step_ok (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (s : State) {p : Addr} (hs : VG.Proof.Argon2.AArch64.Scratch s p) (base : VG.Spec.Argon2.Block) (v : Vector VG.Spec.Argon2.Word 16)
    (hv : VG.Proof.Argon2.AArch64.Holds index base v s.mem p) (a b c d : Fin 16)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
    WP isa (Impl.Argon2.AArch64.gbAt (index a).val (index b).val (index c).val (index d).val)
      s fun t => VG.Proof.Argon2.AArch64.Holds index base (GB v a b c d) t.mem p ∧
        Frame [⟨VG.Proof.Argon2.AArch64.off p 1024, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.AArch64.Keeps s t := by
  refine (VG.Proof.Argon2.AArch64.gbAt_words s hs (index a) (index b) (index c) (index d)).mono ?_
  rintro t ⟨hw, hf, hk⟩
  refine ⟨⟨?_, ?_⟩, hf, hk⟩
  · rw [hw, gather_mixWords index hi, hv.1, GB_eq_mixWords v hab hac had hbc hbd hcd]
  · intro k hn
    rw [hw]
    have ne (j : Fin 16) : (index j).val ≠ k.val := fun h => hn j (Fin.ext h)
    simp only [mixWords, Fin.getElem_fin, Vector.getElem_set, ne, ite_false]
    exact hv.2 k hn

/-- P on any injectively selected row or column, with a cumulative memory frame. -/
theorem permuteAt_holds (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (s : State) {p : Addr} (hs : VG.Proof.Argon2.AArch64.Scratch s p) (base : VG.Spec.Argon2.Block) (v : Vector VG.Spec.Argon2.Word 16)
    (hv : VG.Proof.Argon2.AArch64.Holds index base v s.mem p) :
    WP isa (Impl.Argon2.AArch64.permuteAt index) s fun t =>
      VG.Proof.Argon2.AArch64.Holds index base (permute v) t.mem p ∧
      Frame [⟨VG.Proof.Argon2.AArch64.off p 1024, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.AArch64.Keeps s t := by
  have advance (t : State) (v' : Vector VG.Spec.Argon2.Word 16)
      (h : VG.Proof.Argon2.AArch64.Holds index base v' t.mem p ∧ Frame [⟨VG.Proof.Argon2.AArch64.off p 1024, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.AArch64.Keeps s t)
      (a b c d : Fin 16)
      (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
      (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
      WP isa (Impl.Argon2.AArch64.gbAt (index a).val (index b).val (index c).val (index d).val)
        t fun u => VG.Proof.Argon2.AArch64.Holds index base (GB v' a b c d) u.mem p ∧
          Frame [⟨VG.Proof.Argon2.AArch64.off p 1024, 1024⟩] s.mem u.mem ∧ VG.Proof.Argon2.AArch64.Keeps s u := by
    refine (VG.Proof.Argon2.AArch64.step_ok index hi t (hs.of_keeps h.2.2) base v' h.1 a b c d
      hab hac had hbc hbd hcd).mono ?_
    rintro u ⟨hu, hf, hk⟩
    exact ⟨hu, h.2.1.trans hf, h.2.2.trans hk⟩
  unfold Impl.Argon2.AArch64.permuteAt
  apply WP.seq
  refine (advance s _ ⟨hv, Frame.refl _ _, Keeps.refl s⟩ 0 4 8 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s1 h1
  apply WP.seq
  refine (advance s1 _ h1 1 5 9 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s2 h2
  apply WP.seq
  refine (advance s2 _ h2 2 6 10 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s3 h3
  apply WP.seq
  refine (advance s3 _ h3 3 7 11 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s4 h4
  apply WP.seq
  refine (advance s4 _ h4 0 5 10 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s5 h5
  apply WP.seq
  refine (advance s5 _ h5 1 6 11 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s6 h6
  apply WP.seq
  refine (advance s6 _ h6 2 7 8 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s7 h7
  exact advance s7 _ h7 3 4 9 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row/column code meets the specification's gather, P, scatter definition. -/
theorem permuteAt_ok (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (s : State) {p : Addr} (hs : VG.Proof.Argon2.AArch64.Scratch s p) :
    WP isa (Impl.Argon2.AArch64.permuteAt index) s fun t =>
      VG.Proof.Argon2.AArch64.working t.mem p = Spec.Argon2.permuteAt index (VG.Proof.Argon2.AArch64.working s.mem p) ∧
      Frame [⟨VG.Proof.Argon2.AArch64.off p 1024, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.AArch64.Keeps s t := by
  refine (VG.Proof.Argon2.AArch64.permuteAt_holds index hi s hs (VG.Proof.Argon2.AArch64.working s.mem p)
    (gather index (VG.Proof.Argon2.AArch64.working s.mem p)) (VG.Proof.Argon2.AArch64.holds_self index s.mem p)).mono ?_
  rintro t ⟨ht, hf, hk⟩
  exact ⟨eq_scatter index hi _ _ _ ht.1 ht.2, hf, hk⟩

/-- Compose a list of row or column permutations without re-executing any GB proof. -/
theorem rounds_ok (index : Fin 8 → Fin 16 → Fin 128)
    (hi : ∀ i, Function.Injective (index i)) (is : List (Fin 8))
    (s : State) {p : Addr} (hs : VG.Proof.Argon2.AArch64.Scratch s p) :
    WP isa (is.foldr (fun i rest => .seq (Impl.Argon2.AArch64.permuteAt (index i)) rest)
      (.block [])) s fun t =>
      VG.Proof.Argon2.AArch64.working t.mem p = is.foldl (fun b i => Spec.Argon2.permuteAt (index i) b) (VG.Proof.Argon2.AArch64.working s.mem p) ∧
      Frame [⟨VG.Proof.Argon2.AArch64.off p 1024, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.AArch64.Keeps s t := by
  induction is generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Frame.refl _ _, Keeps.refl s⟩
  | cons i is ih =>
    apply WP.seq
    refine (VG.Proof.Argon2.AArch64.permuteAt_ok (index i) (hi i) s hs).mono ?_
    rintro t ⟨ht, hf, hk⟩
    refine (ih t (hs.of_keeps hk)).mono ?_
    rintro u ⟨hu, hf', hk'⟩
    refine ⟨?_, hf.trans hf', hk.trans hk'⟩
    simpa only [List.foldl_cons, ht] using hu

end VG.Proof.Argon2.AArch64
end

/-! Correctness, memory safety, ABI preservation, and constant time of ARM64 Argon2 G. -/
namespace VG.Proof.Argon2.AArch64
open VG VG.AArch64 VG.Spec.Argon2

theorem original_preserved {m m' : Mem} {p : Addr}
    (hf : Frame [⟨VG.Proof.Argon2.AArch64.off p 1024, 1024⟩] m m') : VG.Spec.Argon2.blockAt m' p = VG.Spec.Argon2.blockAt m p := by
  apply Vector.ext
  intro i hi
  have he : m'.readW (VG.Proof.Argon2.AArch64.off p (8 * i)) 64 = m.readW (VG.Proof.Argon2.AArch64.off p (8 * i)) 64 :=
    hf.readW (r := ⟨p, 1024⟩) (Offset.contains_base p (by omega) (by omega))
      (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact Offset.base_disjoint p (by decide) (by decide)) (by decide)
  rw [← VG.Proof.Argon2.AArch64.blockAt_get m' p ⟨i, hi⟩, ← VG.Proof.Argon2.AArch64.blockAt_get m p ⟨i, hi⟩] at he
  exact he

theorem round_frame {m m' : Mem} {p out : Addr}
    (hf : Frame [⟨VG.Proof.Argon2.AArch64.off p 1024, 1024⟩] m m') : Frame [⟨out, 1024⟩, ⟨p, 4096⟩] m m' := by
  apply hf.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨p, 4096⟩, by simp, Offset.sub_base p (by decide)⟩

theorem compress_wp (s : State) (hs : compressLocal.pre s) :
    WP isa Impl.Argon2.AArch64.compress s fun t => compressLocal.post s t := by
  obtain ⟨hrd, hwr, hout, hx, hy⟩ := hs
  have scr : VG.Proof.Argon2.AArch64.Scratch s (s.gpr .x3) := ⟨rfl, by simp [hwr]⟩
  have inputs : VG.Proof.Argon2.AArch64.Inputs s (s.gpr .x0) (s.gpr .x1) (s.gpr .x3) :=
    ⟨rfl, rfl, by simp [hrd], by simp [hrd], hx, hy⟩
  unfold Impl.Argon2.AArch64.compress
  apply WP.seq
  refine (VG.Proof.Argon2.AArch64.init_prefix 128 (by decide) s scr inputs).mono ?_
  rintro s1 ⟨hinit, _hf1, hk1⟩
  obtain ⟨horig, hwork⟩ := VG.Proof.Argon2.AArch64.initialized_blocks hinit
  have scr1 := scr.of_copy hk1
  apply WP.seq
  refine (VG.Proof.Argon2.AArch64.rounds_ok rowIndex Proof.Argon2.rowIndex_injective (List.finRange 8) s1 scr1).mono ?_
  rintro s2 ⟨hrow, hf2, hk2⟩
  apply WP.seq
  refine (VG.Proof.Argon2.AArch64.rounds_ok colIndex Proof.Argon2.colIndex_injective (List.finRange 8)
    s2 (scr1.of_keeps hk2)).mono ?_
  rintro s3 ⟨hcol, hf3, hk3⟩
  have hout3 : s3.gpr .x2 = s.gpr .x2 := by
    rw [hk3.1 .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hk2.1 .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hk1.1 .x2 (by decide) (by decide)]
  have hw3 : s3.wr = s.wr := hk3.2.2.trans (hk2.2.2.trans hk1.2.2)
  refine (VG.Proof.Argon2.AArch64.finish_prefix 128 (by decide) s3 ((scr1.of_keeps hk2).of_keeps hk3) hout3
    (by rw [hw3, hwr]; simp) hout.symm).mono ?_
  rintro t ⟨hfinish, _hf4, _hk4⟩
  have ho3 := VG.Proof.Argon2.AArch64.original_preserved (hf2.trans hf3)
  rw [horig] at ho3
  have he := VG.Proof.Argon2.AArch64.written_block hfinish
  rw [hcol, hrow, hwork, ho3] at he
  exact he

theorem compress_correct (s : State) (hs : compressLocal.pre s) :
    ∃ tr t, Exec isa Impl.Argon2.AArch64.compress s tr t ∧ abiPreserved s t ∧
      compressLocal.post s t := by
  obtain ⟨tr, t, he, hp⟩ := VG.Proof.Argon2.AArch64.compress_wp s hs
  refine ⟨tr, t, he, ⟨?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, hp⟩
  intro r hr
  apply Exec.gpr (c := Impl.Argon2.AArch64.compress) (hn := .inl (by decide +kernel)) _ he
  have hk : Impl.Argon2.AArch64.compress.allInstrs (VG.AArch64.keeps (RegSet.ofList preserved)) = true := by
    lit_decide
  intro i hi
  have h := List.all_eq_true.mp (List.all_eq_true.mp (instrs_keeps hk) i hi) r hr
  simpa only [bne_iff_ne] using h

theorem compress_verified : Verified AArch64.target Impl.Argon2.AArch64.compress
    (Spec.Argon2.compressContract AArch64.abi) :=
  Verified.of_correct VG.Proof.Argon2.AArch64.compress_correct VG.Proof.Argon2.AArch64.compress_ct VG.Proof.Argon2.AArch64.compress_implies
end VG.Proof.Argon2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.CountCandidates`. -/
section

/-! # Candidate window arithmetic before selecting the reference lane -/

namespace VG.Proof.Argon2.AArch64.CountCandidates

open VG VG.AArch64 VG.Impl.Argon2.AArch64.CountCandidates
open VG.Impl.Argon2.AArch64

structure Candidates (s t : State) (base : Addr) : Prop where
  same : t.gpr .x2 = base + s.gpr .x23 - 1
  other : t.gpr .x3 = base
  keeps : Divide.Keeps [.x8, .x2, .x3, .x12, .x13, .x14, .x15] s t

theorem first_ok (s : State) : WP isa (.block VG.Impl.Argon2.AArch64.CountCandidates.first) s
    (VG.Proof.Argon2.AArch64.CountCandidates.Candidates s · (s.gpr .x21 * s.gpr .x22)) := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.CountCandidates.first, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.mul, Instructions.add, Instructions.subi,
    Instructions.sub, Instructions.imm, Instructions.mark,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    show 0 < 4096 from by decide, show 1 < 65536 from by decide,
    Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (BitVec.ofNat 16 1).setWidth 64 = 1#64 from rfl,
    BitVec.add_zero, Option.some.injEq, exists_eq_left', Bool.toNat_true, VG.Proof.Argon2.AArch64.sub_value]
  constructor
  · simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, Size.bits,
      BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false, VG.Proof.Argon2.AArch64.sub_value,
      Bool.toNat_true]
    rfl
  · simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, Size.bits,
      BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false, VG.Proof.Argon2.AArch64.sub_value,
      Bool.toNat_true]
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2, ite_false]
  all_goals rfl

theorem later_ok (s : State) : WP isa (.block later) s
    (VG.Proof.Argon2.AArch64.CountCandidates.Candidates s · (s.gpr .x20 - s.gpr .x21)) := by
  apply WP.of_runBlock
  simp only [later, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.add, Instructions.subi,
    Instructions.sub, Instructions.imm, Instructions.mark,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    show 0 < 4096 from by decide, show 1 < 65536 from by decide,
    Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (BitVec.ofNat 16 1).setWidth 64 = 1#64 from rfl,
    BitVec.add_zero, Option.some.injEq, exists_eq_left', Bool.toNat_true, VG.Proof.Argon2.AArch64.sub_value]
  constructor
  · simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, Size.bits,
      BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false, VG.Proof.Argon2.AArch64.sub_value,
      Bool.toNat_true]
    rfl
  · simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, Size.bits,
      BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false, VG.Proof.Argon2.AArch64.sub_value,
      Bool.toNat_true]
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2, ite_false]
  all_goals rfl

structure Adjusted (s t : State) : Prop where
  count : t.gpr .x3 = s.gpr .x3 + Divide.mask (decide ((s.gpr .x23).toNat < 1))
  keeps : Divide.Keeps [.x4, .x5, .x3, .x12, .x15] s t

theorem adjust_ok (s : State) : WP isa (.block adjust) s (VG.Proof.Argon2.AArch64.CountCandidates.Adjusted s) := by
  apply WP.of_runBlock
  simp only [adjust, Instructions.sbb, RegUpd.c_write, RegUpd.c_addWithCarry,
    VG.Proof.Argon2.AArch64.borrow_mask, VG.Proof.Argon2.AArch64.sub_carry, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.add, Instructions.subi,
    Instructions.sub, Instructions.imm, Instructions.mark,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    show 0 < 4096 from by decide, show 1 < 65536 from by decide,
    Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (BitVec.ofNat 16 1).setWidth 64 = 1#64 from rfl,
    BitVec.add_zero, Option.some.injEq, exists_eq_left', Bool.toNat_true, VG.Proof.Argon2.AArch64.sub_value]
  have hm : (if decide (1 ≤ (s.gpr .x23).toNat) then 0 else -1) =
      Divide.mask (decide ((s.gpr .x23).toNat < 1)) := by
    by_cases h : (s.gpr .x23).toNat < 1
    · simp only [Divide.mask, h, Nat.not_le_of_gt h, decide_false, decide_true,
        Bool.false_eq_true, ite_false, ite_true]
    · simp only [Divide.mask, h, Nat.le_of_not_gt h, decide_false, decide_true,
        Bool.false_eq_true, ite_false, ite_true]
  simp only [show (1#64).toNat = 1 from rfl, hm]
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  all_goals rfl

theorem compare_ok (s : State) : WP isa (.block ([Instructions.comparei .x5 0].flatten)) s
    fun t => t.gpr .x15 = s.gpr .x5 ∧ Divide.Keeps [.x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [Instructions.comparei, Instructions.compare, Instructions.imm,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    reduceCtorEq, ite_true, ite_false, show 0 < 65536 from by decide,
    Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceLT,
    BitVec.shiftLeft_zero, Bool.toNat_true, VG.Proof.Argon2.AArch64.sub_value,
    show (BitVec.ofNat 16 0).setWidth 64 = 0#64 from rfl, BitVec.sub_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

def base (s : State) : Addr :=
  if s.gpr .x5 = 0 then s.gpr .x21 * s.gpr .x22 else s.gpr .x20 - s.gpr .x21

def changed : List Reg := [.x8, .x2, .x3, .x4, .x5, .x12, .x13, .x14, .x15]

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.AArch64.CountCandidates.code s fun t =>
    t.gpr .x2 = VG.Proof.Argon2.AArch64.CountCandidates.base s + s.gpr .x23 - 1 ∧
    t.gpr .x3 = VG.Proof.Argon2.AArch64.CountCandidates.base s + Divide.mask (decide ((s.gpr .x23).toNat < 1)) ∧
    Divide.Keeps VG.Proof.Argon2.AArch64.CountCandidates.changed s t := by
  unfold VG.Impl.Argon2.AArch64.CountCandidates.code
  refine WP.seq ((VG.Proof.Argon2.AArch64.CountCandidates.compare_ok s).mono ?_)
  rintro a ⟨flag, keeps⟩
  have branches : WP isa (.ite (.zero .x .x15) (.block VG.Impl.Argon2.AArch64.CountCandidates.first) (.block later)) a
      (VG.Proof.Argon2.AArch64.CountCandidates.Candidates s · (VG.Proof.Argon2.AArch64.CountCandidates.base s)) := by
    refine WP.ite (decide (s.gpr .x5 = 0)) (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag, Bool.beq_eq_decide_eq]) ?_ ?_
    · intro h
      have zero : s.gpr .x5 = 0 := of_decide_eq_true h
      refine (VG.Proof.Argon2.AArch64.CountCandidates.first_ok a).mono ?_
      intro b hb
      refine ⟨?_, ?_, keeps.mono (by decide) |>.trans hb.keeps⟩
      · simpa only [VG.Proof.Argon2.AArch64.CountCandidates.base, zero, ite_true, keeps.regs .x21 (by simp),
          keeps.regs .x22 (by simp), keeps.regs .x23 (by simp)] using hb.same
      · simpa only [VG.Proof.Argon2.AArch64.CountCandidates.base, zero, ite_true, keeps.regs .x21 (by simp),
          keeps.regs .x22 (by simp)] using hb.other
    · intro h
      have nonzero : s.gpr .x5 ≠ 0 := of_decide_eq_false h
      refine (VG.Proof.Argon2.AArch64.CountCandidates.later_ok a).mono ?_
      intro b hb
      refine ⟨?_, ?_, keeps.mono (by decide) |>.trans hb.keeps⟩
      · simpa only [VG.Proof.Argon2.AArch64.CountCandidates.base, nonzero, ite_false, keeps.regs .x20 (by simp),
          keeps.regs .x21 (by simp), keeps.regs .x23 (by simp)] using hb.same
      · simpa only [VG.Proof.Argon2.AArch64.CountCandidates.base, nonzero, ite_false, keeps.regs .x20 (by simp),
          keeps.regs .x21 (by simp)] using hb.other
  refine WP.seq (branches.mono ?_)
  intro b hb
  refine (VG.Proof.Argon2.AArch64.CountCandidates.adjust_ok b).mono ?_
  intro t ht
  refine ⟨?_, ?_, (hb.keeps.mono (by decide)).trans (ht.keeps.mono (by decide))⟩
  · exact (ht.keeps.regs .x2 (by decide)).trans hb.same
  · rw [ht.count, hb.other, hb.keeps.regs .x23 (by decide)]

end VG.Proof.Argon2.AArch64.CountCandidates

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.Divide`. -/
section

/-! # Complete fixed-time division for Argon2's indices -/

namespace VG.Proof.Argon2.AArch64.Divide

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Divide

theorem prefix_step (x : BitVec 64) (j : Nat) :
    x.toNat / 2 ^ j = 2 * (x.toNat / 2 ^ (j + 1)) + (x.getLsbD j).toNat := by
  have h := Nat.mod_add_div (x.toNat / 2 ^ j) 2
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ] at h
  simp only [Nat.succ_eq_add_one] at h
  simp only [← BitVec.testBit_toNat, Nat.toNat_testBit]
  omega

def changed : List Reg := [.x3, .x4, .x6, .x8, .x5, .x9]

/-- The already-consumed prefix equals quotient times divisor plus remainder. -/
structure Invariant (n : Nat) (s : State) : Prop where
  numerator : (s.gpr .x0).toNat < 2 ^ 32
  divisor : 0 < (s.gpr .x1).toNat
  divisorBound : (s.gpr .x1).toNat < 2 ^ 32
  remainder : (s.gpr .x4).toNat < (s.gpr .x1).toNat
  equation : (s.gpr .x0).toNat / 2 ^ n =
    (s.gpr .x5).toNat * (s.gpr .x1).toNat + (s.gpr .x4).toNat

theorem bit_invariant (s : State) (n : Nat) (hn : n < 32) (h : VG.Proof.Argon2.AArch64.Divide.Invariant (n + 1) s) :
    WP isa (.block (VG.Impl.Argon2.AArch64.Divide.bit n)) s fun t => VG.Proof.Argon2.AArch64.Divide.Invariant n t ∧ VG.Proof.Argon2.AArch64.Divide.Keeps VG.Proof.Argon2.AArch64.Divide.changed s t := by
  have hqmul := Nat.le_mul_of_pos_right (s.gpr .x5).toNat h.divisor
  have hprefix := Nat.div_le_self (s.gpr .x0).toNat (2 ^ (n + 1))
  have he := h.equation
  have hb := h.numerator
  have hq : (s.gpr .x5).toNat < 2 ^ 32 := by omega
  have hr : (s.gpr .x4).toNat < 2 ^ 32 := Nat.lt_trans h.remainder h.divisorBound
  refine (VG.Proof.Argon2.AArch64.Divide.bit_ok s n hn hr hq h.divisorBound).mono ?_
  rintro t ⟨ht8, ht9, ht⟩
  have hdi := ht.regs .x0 (by decide)
  have hsi := ht.regs .x1 (by decide)
  have hs := VG.Proof.Argon2.divide_step h.equation h.remainder
    (Bool.toNat_le ((s.gpr .x0).getLsbD n))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ht⟩
  · rw [hdi]; exact h.numerator
  · rw [hsi]; exact h.divisor
  · rw [hsi]; exact h.divisorBound
  · rw [ht8, hsi]; exact hs.2
  · rw [hdi, hsi, ht8, ht9, VG.Proof.Argon2.AArch64.Divide.prefix_step]
    exact hs.1

theorem bits_ok (n : Nat) (hn : n ≤ 32) (s : State) (h : VG.Proof.Argon2.AArch64.Divide.Invariant n s) :
    WP isa (.block ((List.range n).reverse.flatMap VG.Impl.Argon2.AArch64.Divide.bit)) s fun t =>
      VG.Proof.Argon2.AArch64.Divide.Invariant 0 t ∧ VG.Proof.Argon2.AArch64.Divide.Keeps VG.Proof.Argon2.AArch64.Divide.changed s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨h, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.flatMap_cons]
    rw [WP.block_append_iff]
    refine (VG.Proof.Argon2.AArch64.Divide.bit_invariant s n (by omega) h).mono ?_
    rintro t ⟨ht, kt⟩
    refine (ih (by omega) t ht).mono ?_
    rintro u ⟨hu, ku⟩
    exact ⟨hu, kt.trans ku⟩

theorem setup_ok (s : State) (hn : (s.gpr .x0).toNat < 2 ^ 32)
    (hd : 0 < (s.gpr .x1).toNat) (hd' : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa (.block VG.Impl.Argon2.AArch64.Divide.setup) s fun t =>
      VG.Proof.Argon2.AArch64.Divide.Invariant 32 t ∧ VG.Proof.Argon2.AArch64.Divide.Keeps VG.Proof.Argon2.AArch64.Divide.changed s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.Divide.setup, runBlock_cons, runStep_some, runBlock_nil, exec,
    Size.bits,
    ite_true, Option.some.injEq, exists_eq_left',
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero]
  refine ⟨⟨hn, hd, hd', ?_, ?_⟩, ?_⟩
  · exact hd
  · change (s.gpr .x0).toNat / 2 ^ 32 = 0 * (s.gpr .x1).toNat + 0
    rw [Nat.div_eq_of_lt hn, Nat.zero_mul, Nat.zero_add]
  · constructor
    · intro r hr
      simp only [VG.Proof.Argon2.AArch64.Divide.changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.2.1, hr.2.2.2.2.1, ite_false]
    all_goals rfl

theorem code_ok (s : State) (hn : (s.gpr .x0).toNat < 2 ^ 32)
    (hd : 0 < (s.gpr .x1).toNat) (hd' : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa VG.Impl.Argon2.AArch64.Divide.code s fun t =>
      (t.gpr .x5).toNat = (s.gpr .x0).toNat / (s.gpr .x1).toNat ∧
      (t.gpr .x4).toNat = (s.gpr .x0).toNat % (s.gpr .x1).toNat ∧
      VG.Proof.Argon2.AArch64.Divide.Keeps VG.Proof.Argon2.AArch64.Divide.changed s t := by
  rw [VG.Impl.Argon2.AArch64.Divide.code, WP.block_append_iff]
  refine (VG.Proof.Argon2.AArch64.Divide.setup_ok s hn hd hd').mono ?_
  rintro u ⟨hu, ku⟩
  refine (VG.Proof.Argon2.AArch64.Divide.bits_ok 32 (by decide) u hu).mono ?_
  rintro t ⟨ht, kt⟩
  have k := ku.trans kt
  have he := ht.equation
  simp only [Nat.pow_zero, Nat.div_one] at he
  obtain ⟨hq, hr⟩ := VG.Proof.Argon2.divide_result ht.divisor he ht.remainder
  rw [k.regs .x0 (by decide), k.regs .x1 (by decide)] at hq hr
  exact ⟨hq, hr, k⟩

end VG.Proof.Argon2.AArch64.Divide

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.ReferenceCount`. -/
section

/-! Merged from `Proof.Argon2.AArch64.SelectWindow`. -/
section
/-! # Same-lane window selection with no leakage from the equality test -/

namespace VG.Proof.Argon2.AArch64.SelectWindow

open VG VG.AArch64 VG.Impl.Argon2.AArch64.SelectWindow
open VG.Impl.Argon2.AArch64

theorem equality_test (x y : Addr) : (x ^^^ y).toNat < 1 ↔ x = y := by
  constructor
  · intro h
    have zero : x ^^^ y = 0 := by
      apply BitVec.eq_of_toNat_eq
      change (x ^^^ y).toNat = 0
      omega
    exact BitVec.xor_eq_zero_iff.mp zero
  · intro h
    rw [h, BitVec.xor_self]
    decide

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.AArch64.SelectWindow.code s fun t =>
    t.gpr .x4 = (if s.gpr .x0 = s.gpr .x1 then s.gpr .x2 else s.gpr .x3) ∧
    Divide.Keeps [.x8, .x4, .x2, .x12, .x15] s t := by
  unfold VG.Impl.Argon2.AArch64.SelectWindow.code
  apply WP.of_runBlock
  simp only [List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.subi, Instructions.sub, Instructions.sbb,
    Instructions.logic, Instructions.imm, Instructions.mark,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    show 0 < 4096 from by decide, show 1 < 65536 from by decide,
    Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (BitVec.ofNat 16 1).setWidth 64 = 1#64 from rfl,
    show (1#64).toNat = 1 from rfl, BitVec.add_zero,
    Option.some.injEq, exists_eq_left', Bool.toNat_true, VG.Proof.Argon2.AArch64.sub_value, VG.Proof.Argon2.AArch64.sub_carry,
    VG.Proof.Argon2.AArch64.borrow_mask]
  have hm : (if decide (1 ≤ (s.gpr .x0 ^^^ s.gpr .x1).toNat) then 0 else -1) =
      Divide.mask (decide ((s.gpr .x0 ^^^ s.gpr .x1).toNat < 1)) := by
    by_cases h : (s.gpr .x0 ^^^ s.gpr .x1).toNat < 1
    · simp only [Divide.mask, h, Nat.not_le_of_gt h, decide_false, decide_true,
        Bool.false_eq_true, ite_false, ite_true]
    · simp only [Divide.mask, h, Nat.le_of_not_gt h, decide_false, decide_true,
        Bool.false_eq_true, ite_false, ite_true]
  rw [hm, Divide.select_value]
  simp only [decide_eq_true_eq, VG.Proof.Argon2.AArch64.SelectWindow.equality_test]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  all_goals rfl

theorem code_secret_rel : RelCT isa (fun s t => s.sp = t.sp) VG.Impl.Argon2.AArch64.SelectWindow.code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

end VG.Proof.Argon2.AArch64.SelectWindow
end

/-! Merged from `Proof.Argon2.AArch64.CountCandidatesLit`. -/
section
/-! Checked instruction literal for reference-window arithmetic. -/
namespace VG
materialize_code Impl.Argon2.AArch64.CountCandidates.code
end VG
end

/-! Merged from `Proof.Argon2.AArch64.CountCandidatesCT`. -/
section
/-! Only the public pass controls reference-window arithmetic. -/
namespace VG.Proof.Argon2.AArch64.CountCandidates
open VG VG.AArch64 VG.Impl.Argon2.AArch64.CountCandidates

theorem code_rel : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x5 = t.gpr .x5) VG.Impl.Argon2.AArch64.CountCandidates.code
    (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x5])
    (fun _ _ h => ⟨h.1, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h.2⟩) [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)
end VG.Proof.Argon2.AArch64.CountCandidates
end

/-! The selected reference window, with public pass control only. -/

namespace VG.Proof.Argon2.AArch64.ReferenceCount

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceCount

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.AArch64.ReferenceCount.code s fun t =>
    t.gpr .x4 = (if s.gpr .x0 = s.gpr .x1 then
      CountCandidates.base s + s.gpr .x23 - 1 else
      CountCandidates.base s + Divide.mask (decide ((s.gpr .x23).toNat < 1))) ∧
    Divide.Keeps CountCandidates.changed s t := by
  unfold VG.Impl.Argon2.AArch64.ReferenceCount.code
  refine WP.seq ((CountCandidates.code_ok s).mono ?_)
  rintro a ⟨same, other, keeps⟩
  refine (SelectWindow.code_ok a).mono ?_
  rintro t ⟨out, tail⟩
  refine ⟨?_, keeps.trans (tail.mono (by decide))⟩
  rw [out, keeps.regs .x0 (by decide), keeps.regs .x1 (by decide), same, other]

theorem same_word (b i : Nat) (positive : 0 < b + i) :
    BitVec.ofNat 64 b + BitVec.ofNat 64 i - (1 : Addr) =
      BitVec.ofNat 64 (b + i - 1) := by
  rw [← BitVec.ofNat_add]
  change BitVec.ofNat 64 (b + i) - BitVec.ofNat 64 1 = _
  exact Offset.ofNat_sub_ofNat (by omega)

theorem other_word (b i : Nat) (bound : i < 2 ^ 64) (positive : i = 0 → 0 < b) :
    BitVec.ofNat 64 b + Divide.mask (decide ((BitVec.ofNat 64 i).toNat < 1)) =
      BitVec.ofNat 64 (b - (if i = 0 then 1 else 0)) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  by_cases zero : i = 0
  · simp only [zero, show decide ((0 : Nat) < 1) = true from rfl, Divide.mask, ite_true]
    rw [BitVec.add_neg_eq_sub]
    change BitVec.ofNat 64 b - BitVec.ofNat 64 1 = _
    exact Offset.ofNat_sub_ofNat (by have := positive zero; omega)
  · have notSmall : ¬i < 1 := by omega
    simp only [notSmall, decide_false, Divide.mask, Bool.false_eq_true, ite_false,
      zero, Nat.sub_zero]
    change BitVec.ofNat 64 b + 0#64 = BitVec.ofNat 64 b
    rw [BitVec.add_zero]

theorem selected_word (b i : Nat) (same : Bool) (bound : i < 2 ^ 64)
    (positive : 0 < b + i) (atZero : i = 0 → 0 < b) :
    (if same then BitVec.ofNat 64 b + BitVec.ofNat 64 i - (1 : Addr) else
      BitVec.ofNat 64 b + Divide.mask (decide ((BitVec.ofNat 64 i).toNat < 1))) =
      BitVec.ofNat 64 (if same then b + i - 1 else b - (if i = 0 then 1 else 0)) := by
  cases same
  · exact VG.Proof.Argon2.AArch64.ReferenceCount.other_word b i bound atZero
  · exact VG.Proof.Argon2.AArch64.ReferenceCount.same_word b i positive

theorem spec_count (p : Spec.Argon2.Params) (pass slice index : Nat) (same : Bool) :
    Spec.Argon2.referenceCount p pass slice index same =
      let b := if pass = 0 then slice * p.segmentLen else p.laneLen - p.segmentLen
      if same then b + index - 1 else b - (if index = 0 then 1 else 0) := by
  unfold Spec.Argon2.referenceCount
  by_cases firstPass : pass = 0 <;> cases same <;>
    simp only [firstPass, ite_true, ite_false, Bool.false_eq_true]

def windowBase (p : Spec.Argon2.Params) (pass slice : Nat) : Nat :=
  if pass = 0 then slice * p.segmentLen else p.laneLen - p.segmentLen

theorem base_nat (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (passReg : (s.gpr .x5).toNat = pass)
    (laneReg : s.gpr .x20 = BitVec.ofNat 64 p.laneLen)
    (segmentReg : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen)
    (sliceReg : s.gpr .x22 = BitVec.ofNat 64 slice)
    (segmentBound : p.segmentLen ≤ p.laneLen) :
    CountCandidates.base s = BitVec.ofNat 64 (VG.Proof.Argon2.AArch64.ReferenceCount.windowBase p pass slice) := by
  have isZero : s.gpr .x5 = 0 ↔ pass = 0 := by
    rw [← passReg]
    constructor
    · intro h; rw [h]; rfl
    · intro h
      apply BitVec.eq_of_toNat_eq
      exact h
  unfold CountCandidates.base VG.Proof.Argon2.AArch64.ReferenceCount.windowBase
  by_cases firstPass : pass = 0
  · simp only [isZero, firstPass, ite_true]
    rw [segmentReg, sliceReg, ← BitVec.ofNat_mul, Nat.mul_comm]
  · simp only [isZero, firstPass, ite_false]
    rw [laneReg, segmentReg]
    exact Offset.ofNat_sub_ofNat segmentBound

theorem code_nat_ok (s : State) (p : Spec.Argon2.Params) (pass slice index : Nat)
    (passReg : (s.gpr .x5).toNat = pass)
    (laneReg : s.gpr .x20 = BitVec.ofNat 64 p.laneLen)
    (segmentReg : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen)
    (sliceReg : s.gpr .x22 = BitVec.ofNat 64 slice)
    (indexReg : s.gpr .x23 = BitVec.ofNat 64 index)
    (segmentBound : p.segmentLen ≤ p.laneLen) (indexBound : index < 2 ^ 64)
    (positive : 0 < VG.Proof.Argon2.AArch64.ReferenceCount.windowBase p pass slice + index)
    (atZero : index = 0 → 0 < VG.Proof.Argon2.AArch64.ReferenceCount.windowBase p pass slice) :
    WP isa VG.Impl.Argon2.AArch64.ReferenceCount.code s fun t =>
      t.gpr .x4 = BitVec.ofNat 64 (Spec.Argon2.referenceCount p pass slice index
        (decide (s.gpr .x0 = s.gpr .x1))) ∧
      Divide.Keeps CountCandidates.changed s t := by
  refine (VG.Proof.Argon2.AArch64.ReferenceCount.code_ok s).mono ?_
  rintro t ⟨out, keeps⟩
  refine ⟨out.trans ?_, keeps⟩
  rw [VG.Proof.Argon2.AArch64.ReferenceCount.base_nat s p pass slice passReg laneReg segmentReg sliceReg segmentBound, indexReg,
    VG.Proof.Argon2.AArch64.ReferenceCount.spec_count]
  simpa only [decide_eq_true_eq, VG.Proof.Argon2.AArch64.ReferenceCount.windowBase] using
    VG.Proof.Argon2.AArch64.ReferenceCount.selected_word (VG.Proof.Argon2.AArch64.ReferenceCount.windowBase p pass slice) index
      (decide (s.gpr .x0 = s.gpr .x1)) indexBound positive atZero

theorem code_rel : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x5 = t.gpr .x5) VG.Impl.Argon2.AArch64.ReferenceCount.code
    (fun s t => s.sp = t.sp) :=
  CountCandidates.code_rel.seq SelectWindow.code_secret_rel

end VG.Proof.Argon2.AArch64.ReferenceCount

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.Relative`. -/
section

/-! # The baseline reference-window mapping is fixed time and preserves memory -/

namespace VG.Proof.Argon2.AArch64.Relative

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Relative
open VG.Impl.Argon2.AArch64

def value (random count : Addr) : Addr :=
  let j := random &&& 0xffffffff
  let x := (j * j) >>> 32
  let y := (x * count) >>> 32
  count - 1 - y

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.AArch64.Relative.code s fun t =>
    t.gpr .x8 = VG.Proof.Argon2.AArch64.Relative.value (s.gpr .x0) (s.gpr .x1) ∧
    (∀ r, r ≠ .x8 → r ≠ .x2 → r ≠ .x3 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
    t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold VG.Impl.Argon2.AArch64.Relative.code
  apply WP.of_runBlock
  simp only [List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.mov32, Instructions.mul, Instructions.shr,
    Instructions.subi, Instructions.sub, Instructions.imm, Instructions.mark,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.mem_addWithCarry, RegUpd.rd_addWithCarry, RegUpd.wr_addWithCarry,
    BitVec.setWidth_eq, BitVec.or_self, reduceCtorEq, ite_true, ite_false,
    show 0 < 4096 from by decide, show 1 < 65536 from by decide,
    Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (BitVec.ofNat 16 1).setWidth 64 = 1#64 from rfl,
    show 32 < 64 from by decide, BitVec.add_zero, Option.some.injEq,
    exists_eq_left', Bool.toNat_true, VG.Proof.Argon2.AArch64.sub_value]
  refine ⟨?_, ?_, trivial, trivial, trivial⟩
  · rw [VG.Proof.Argon2.AArch64.low32]; rfl
  · intro r h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, ite_false]

theorem mul_shift_toNat (x y : Addr) (bound : x.toNat * y.toNat < 2 ^ 64) :
    ((x * y) >>> 32).toNat = x.toNat * y.toNat / 2 ^ 32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul,
    Nat.mod_eq_of_lt bound]

theorem value_nat (random count : Addr) (lo : 0 < count.toNat)
    (bound : count.toNat < 2 ^ 32) :
    VG.Proof.Argon2.AArch64.Relative.value random count = BitVec.ofNat 64
      (count.toNat - 1 - count.toNat * ((random &&& 0xffffffff).toNat *
        (random &&& 0xffffffff).toNat / 2 ^ 32) / 2 ^ 32) := by
  let j := random &&& 0xffffffff
  have hj : j.toNat < 2 ^ 32 := by
    have h32 := (random.setWidth 32).isLt
    rw [show j = (random.setWidth 32).setWidth 64 from (VG.Proof.Argon2.AArch64.low32 random).symm,
      BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    exact h32
  have hx := VG.Proof.Argon2.AArch64.Relative.mul_shift_toNat j j (Proof.Argon2.reference_square_bound _ hj)
  have product : ((j * j) >>> 32).toNat * count.toNat < 2 ^ 64 := by
    rw [hx, Nat.mul_comm]
    exact Proof.Argon2.reference_product_bound _ _ bound hj
  have hy := VG.Proof.Argon2.AArch64.Relative.mul_shift_toNat ((j * j) >>> 32) count product
  rw [hx, Nat.mul_comm] at hy
  have hyBound : count.toNat * (j.toNat * j.toNat / 2 ^ 32) / 2 ^ 32 < count.toNat :=
    Proof.Argon2.reference_scale_lt_count _ _ lo hj
  have hyWord : (((j * j) >>> 32) * count) >>> 32 = BitVec.ofNat 64
      (count.toNat * (j.toNat * j.toNat / 2 ^ 32) / 2 ^ 32) := by
    apply BitVec.eq_of_toNat_eq
    rw [hy, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold VG.Proof.Argon2.AArch64.Relative.value
  change count - 1 - ((((j * j) >>> 32) * count) >>> 32) = _
  rw [hyWord]
  change count - (1 : Addr) - BitVec.ofNat 64
    (count.toNat * (j.toNat * j.toNat / 2 ^ 32) / 2 ^ 32) = _
  have countWord : count = BitVec.ofNat 64 count.toNat := by
    exact (BitVec.ofNat_toNat 64 count).symm
  have countSub : count - 1 = BitVec.ofNat 64 (count.toNat - 1) := by
    calc
      count - 1 = BitVec.ofNat 64 count.toNat - BitVec.ofNat 64 1 :=
        congrArg (fun x : Addr => x - 1) countWord
      _ = _ := Offset.ofNat_sub_ofNat (by omega)
  rw [countSub, Offset.ofNat_sub_ofNat (by omega)]

theorem code_nat_ok (s : State) (lo : 0 < (s.gpr .x1).toNat)
    (bound : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa VG.Impl.Argon2.AArch64.Relative.code s fun t =>
      t.gpr .x8 = BitVec.ofNat 64
        ((s.gpr .x1).toNat - 1 - (s.gpr .x1).toNat *
          ((s.gpr .x0 &&& 0xffffffff).toNat * (s.gpr .x0 &&& 0xffffffff).toNat / 2 ^ 32) /
          2 ^ 32) ∧
      (∀ r, r ≠ .x8 → r ≠ .x2 → r ≠ .x3 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  (VG.Proof.Argon2.AArch64.Relative.code_ok s).mono (fun _ h => ⟨h.1.trans (VG.Proof.Argon2.AArch64.Relative.value_nat _ _ lo bound), h.2⟩)

theorem code_secret_rel : RelCT isa (fun s t => s.sp = t.sp) VG.Impl.Argon2.AArch64.Relative.code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

end VG.Proof.Argon2.AArch64.Relative

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.Wrap`. -/
section

/-! # Masked subtraction agrees with wrapping the reference column -/

namespace VG.Proof.Argon2.AArch64.Wrap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Wrap
open VG.Impl.Argon2.AArch64

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.AArch64.Wrap.code s fun t =>
    t.gpr .x0 = (if (s.gpr .x0).toNat < (s.gpr .x1).toNat
      then s.gpr .x0 else s.gpr .x0 - s.gpr .x1) ∧
    Divide.Keeps [.x0, .x6, .x8, .x15] s t := by
  unfold VG.Impl.Argon2.AArch64.Wrap.code
  apply WP.of_runBlock
  simp only [List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.sub, Instructions.sbb, Instructions.logic,
    Instructions.mark, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    show 0 < 4096 from by decide, BitVec.add_zero,
    Option.some.injEq, exists_eq_left', Bool.toNat_true, VG.Proof.Argon2.AArch64.sub_value, VG.Proof.Argon2.AArch64.sub_carry,
    VG.Proof.Argon2.AArch64.borrow_mask]
  have hm : (if decide ((s.gpr .x1).toNat ≤ (s.gpr .x0).toNat) then 0 else -1) =
      Divide.mask (decide ((s.gpr .x0).toNat < (s.gpr .x1).toNat)) := by
    by_cases h : (s.gpr .x0).toNat < (s.gpr .x1).toNat <;>
      simp [Divide.mask, h, Nat.le_of_not_gt, Nat.not_le_of_gt]
  rw [hm, Divide.select_value]
  simp only [decide_eq_true_eq]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem wrap_nat (x q : Addr) (bound : x.toNat < 2 * q.toNat) :
    (if x.toNat < q.toNat then x else x - q) = BitVec.ofNat 64 (x.toNat % q.toNat) := by
  rw [Proof.Argon2.reference_wrap _ _ bound]
  by_cases small : x.toNat < q.toNat
  · rw [ite_eq_left small, ite_eq_left small]
    exact (BitVec.ofNat_toNat 64 x).symm
  · rw [ite_eq_right small, ite_eq_right small]
    calc
      x - q = BitVec.ofNat 64 x.toNat - BitVec.ofNat 64 q.toNat := by
        simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = _ := Offset.ofNat_sub_ofNat (by omega)

theorem code_nat_ok (s : State) (bound : (s.gpr .x0).toNat < 2 * (s.gpr .x1).toNat) :
    WP isa VG.Impl.Argon2.AArch64.Wrap.code s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 ((s.gpr .x0).toNat % (s.gpr .x1).toNat) ∧
      Divide.Keeps [.x0, .x6, .x8, .x15] s t :=
  (VG.Proof.Argon2.AArch64.Wrap.code_ok s).mono (fun _ h => ⟨h.1.trans (VG.Proof.Argon2.AArch64.Wrap.wrap_nat _ _ bound), h.2⟩)

theorem code_secret_rel : RelCT isa (fun s t => s.sp = t.sp) VG.Impl.Argon2.AArch64.Wrap.code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

end VG.Proof.Argon2.AArch64.Wrap

end
