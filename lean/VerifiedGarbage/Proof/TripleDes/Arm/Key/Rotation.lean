module

import VerifiedGarbage.Proof.TripleDes.KeySchedule
public import VerifiedGarbage.Proof.Rc2.Arm.Lookup
public import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
import VerifiedGarbage.Proof.Rc2.Arm.KeySteps
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `TripleDes.Arm.KeySteps`, which this module and modules that import it used -/

section

/-! ### `TripleDes.Arm.Word`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.Arm

theorem mask28 (x : BitVec 32) : x &&& 0x0fffffff = (x.setWidth 28).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change x.toNat &&& (2 ^ 28 - 1) = x.toNat % 268435456 % 4294967296
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega_using []

theorem rotate28_word (x : BitVec 28) (n : Nat) (hn : 1 ≤ n) (hn' : n < 5) :
    ((x.setWidth 32).rotateRight (32 - n) ^^^ (x.setWidth 32) >>> (28 - n)) &&& 0x0fffffff =
      (x.rotateLeft n).setWidth 32 := by
  rw [mask28]
  apply congrArg (BitVec.setWidth 32)
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateLeft]
  have n32 : (32 - n) % 32 = 32 - n := Nat.mod_eq_of_lt (by omega_using [hn])
  have n28 : n % 28 = n := Nat.mod_eq_of_lt (by omega_using [hn'])
  rw [n32, n28]
  rw [show 32 - (32 - n) = n by omega_using [hn']]
  by_cases h : j < n
  · simp (disch := omega) [h, hj,
      show j + (28 - n) < 32 by omega_using [hn', h], BitVec.getLsbD_of_ge, Nat.add_comm]
  · simp (disch := omega) [h, hj, show j < 32 by omega_using [hj],
      show j - n < 32 by omega_using [hj], BitVec.getLsbD_of_ge]


theorem mask_word (x : BitVec 32) (n : Nat) (hn : 0 < n) (hn32 : n ≤ 32) :
    (x <<< (32 - n)) >>> (32 - n) = (x.setWidth n).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j < n
  · have hi : 32 - n + j < 32 := by omega
    have hlo : ¬32 - n + j < 32 - n := by omega_using []
    simp only [hi, hlo, h, hj, decide_true, decide_false, Bool.not_false,
      Bool.true_and, show 32 - n + j - (32 - n) = j by omega_using []]
  · have ho : ¬32 - n + j < 32 := by omega_using [h]
    simp only [ho, h, hj, decide_true, decide_false, Bool.false_and, Bool.true_and]

theorem packed48 (x : BitVec 48) :
    ((x >>> 32).setWidth 16).setWidth 32 ++ x.setWidth 32 = x.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    hi, decide_true, Bool.true_and]
  by_cases hlo : i < 32
  · simp only [hlo, ite_true, decide_true, Bool.true_and]
  · simp (disch := omega) only [hlo, ite_false, decide_true, Bool.true_and,
      show i - 32 < 32 by omega_using [hi], show 32 + (i - 32) = i by omega_using [hlo]]
    by_cases h48 : i < 48
    · simp only [show i - 32 < 16 by omega_using [h48], decide_true, Bool.true_and]
    · simp only [show ¬i - 32 < 16 by omega_using [h48], decide_false, Bool.false_and,
        BitVec.getLsbD_of_ge x i (by omega_using [h48])]

end VG.Proof.TripleDes.Arm

end

end

@[expose] public section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm

theorem rotate28_ok (s : State) (r : Reg) (hr : r ≠ .r4)
    (x : BitVec 28) (hx : s.gpr r = x.setWidth 32)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 5) :
    ∃ s', runBlock isa (Key.rotate28 r n) s = some s' ∧
      s'.gpr r = (x.rotateLeft n).setWidth 32 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r', r' ≠ r → r' ≠ .r4 → s'.gpr r' = s.gpr r') := by
  have hleft : 1 ≤ 32 - n ∧ 32 - n ≤ 31 := by omega_using [hn, hn']
  have hright : 1 ≤ 28 - n ∧ 28 - n ≤ 31 := by omega_using [hn']
  refine ⟨_, by
    simp only [Key.rotate28, mask, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, hleft.1, hleft.2, hright.1, hright.2,
      show 1 ≤ (4 : Nat) from by decide, show (4 : Nat) ≤ 31 from by decide, and_self, ite_true, Option.map_some,
      hr, Ne.symm hr, gpr_setReg, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, hr, ite_false]
    rw [hx, mask_word _ 28 (by decide) (by decide)]
    exact (mask28 _).symm.trans (rotate28_word x n hn hn')
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · simp only [sp_setReg]
  · intro r' h1 h2; simp only [gpr_setReg, h1, h2, ite_false]
end VG.Proof.TripleDes.Arm

end

end

@[expose] public section

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (Keep)

structure RotatePost (c d : BitVec 28) (n : Nat) (s s' : State) : Prop where
  c : s'.gpr .r10 = (c.rotateLeft n).setWidth 32
  d : s'.gpr .r11 = (d.rotateLeft n).setWidth 32
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .r4 → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r

theorem rotate_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .r10 = c.setWidth 32) (hd : s.gpr .r11 = d.setWidth 32)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 5) :
    WP isa (Impl.TripleDes.Arm.Key.rotate n) s (RotatePost c d n s) := by
  rw [Impl.TripleDes.Arm.Key.rotate, WP.block_append_iff]
  obtain ⟨s₁, run₁, c₁, mem₁, rd₁, wr₁, _, reg₁⟩ := rotate28_ok s .r10 (by decide) c hc n hn hn'
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have d₁ : s₁.gpr .r11 = d.setWidth 32 := (reg₁ .r11 (by decide) (by decide)).trans hd
  obtain ⟨s₂, run₂, d₂, mem₂, rd₂, wr₂, _, reg₂⟩ := rotate28_ok s₁ .r11 (by decide) d d₁ n hn hn'
  refine WP.of_runBlock ⟨s₂, run₂, ⟨(reg₂ .r10 (by decide) (by decide)).trans c₁, d₂,
    mem₂.trans mem₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩⟩
  intro r ha hc hd
  exact (reg₂ r hd ha).trans (reg₁ r hc ha)

theorem comparison_values : ∀ j < 16, ∀ k < 16,
    ((BitVec.ofNat 32 j >>> 1) == (0 : BitVec 32)) = decide (j < 2) ∧
    ((BitVec.ofNat 32 j - BitVec.ofNat 32 k) == (0 : BitVec 32)) = decide (j = k) := by
  decide

theorem lowTest_ok (s : State) (j : Nat) (hj : j < 16)
    (hv : s.gpr .r9 = BitVec.ofNat 32 j) :
    ∃ s', runBlock isa [.mov .r4 (.shifted .r9 .lsr 1), .cmp .r4 (.imm 0)] s = some s' ∧
      isa.eval .eq s' = some (decide (j < 2)) ∧ Keep [.r4] s s' := by
  refine ⟨_, by
    simp only [↓reduceIte, Nat.reduceLeDiff, and_self, runBlock_cons, runStep_some, 
      exec, Op2.eval, Option.map_some, gpr_setReg]
    rfl, ?_, ?_⟩
  · change some (((s.gpr .r9 >>> 1) - 0) == 0) = _
    have hz : (s.gpr .r9 >>> 1) - (0 : BitVec 32) = s.gpr .r9 >>> 1 := by bv_omega
    rw [hz, hv]
    exact congrArg some (comparison_values j hj 0 (by decide)).1
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      simp only [List.mem_singleton] at hr
      simp only [VG.Proof.Rc2.Arm.gpr_subFlags, gpr_setReg, hr, ite_false]
    · rfl
    · rfl
    · rfl

theorem eqTest_ok (s : State) (j k : Nat) (hj : j < 16) (hk : k < 16)
    (hv : s.gpr .r9 = BitVec.ofNat 32 j) :
    ∃ s', runBlock isa [.cmp .r9 (.imm (BitVec.ofNat 32 k))] s = some s' ∧
      isa.eval .eq s' = some (decide (j = k)) ∧ Keep [.r4] s s' := by
  have henc : encodable (BitVec.ofNat 32 k) = true := by
    have hfinite : ∀ k < 16, encodable (BitVec.ofNat 32 k) = true := by decide
    exact hfinite k hk
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
      henc, ite_true, Option.map_some]
    rfl, ?_, ?_⟩
  · change some ((s.gpr .r9 - BitVec.ofNat 32 k) == 0) = _
    rw [hv]
    exact congrArg some (comparison_values j hj k hk).2
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem rotation_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r10 = c.setWidth 32) (hd : s.gpr .r11 = d.setWidth 32)
    (hjreg : s.gpr .r9 = BitVec.ofNat 32 j) :
    WP isa Impl.TripleDes.Arm.Key.rotation s
      (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
  rw [Impl.TripleDes.Arm.Key.rotation]
  apply WP.seq
  obtain ⟨s₁, run₁, cond₁, keep₁⟩ := lowTest_ok s j hj hjreg
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hrot (s' : State) (h : Keep [.r4] s s') (n : Nat) (hn : 1 ≤ n) (hn' : n < 5)
      (hv : Spec.TripleDes.rotations.getD j 0 = n) :
      WP isa (Impl.TripleDes.Arm.Key.rotate n) s' (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
    apply WP.mono (rotate_ok s' c d ((h.reg .r10 (by simp)).trans hc)
      ((h.reg .r11 (by simp)).trans hd) n hn hn')
    intro t ht
    rw [hv]
    exact ⟨ht.c, ht.d, ht.mem.trans h.mem, ht.rd.trans h.rd, ht.wr.trans h.wr,
      fun r ha hc hd => (ht.reg r ha hc hd).trans (h.reg r (by simpa only [List.mem_singleton] using ha))⟩
  have combine {a b : State} (ha : Keep [.r4] s a) (hb : Keep [.r4] a b) : Keep [.r4] s b :=
    ⟨fun r hr => (hb.reg r hr).trans (ha.reg r hr), hb.mem.trans ha.mem,
      hb.rd.trans ha.rd, hb.wr.trans ha.wr⟩
  by_cases h2 : j < 2
  · apply WP.ite true (by simpa only [h2, decide_true] using cond₁)
    · intro _
      exact hrot s₁ keep₁ 1 (by decide) (by decide)
        (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inl h2)])
    · simp
  · apply WP.ite false (by simpa only [h2, decide_false] using cond₁)
    · simp
    · intro _
      apply WP.seq
      obtain ⟨s₂, run₂, cond₂, keep₂⟩ := eqTest_ok s₁ j 8 hj (by decide)
        ((keep₁.reg .r9 (by simp)).trans hjreg)
      refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
      have keep₂' := combine keep₁ keep₂
      by_cases h8 : j = 8
      · apply WP.ite true (by simpa only [h8, decide_true] using cond₂)
        · intro _
          exact hrot s₂ keep₂' 1 (by decide) (by decide)
            (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inl h8))])
        · simp
      · apply WP.ite false (by simpa only [h8, decide_false] using cond₂)
        · simp
        · intro _
          apply WP.seq
          obtain ⟨s₃, run₃, cond₃, keep₃⟩ := eqTest_ok s₂ j 15 hj (by decide)
            ((keep₂'.reg .r9 (by simp)).trans hjreg)
          refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
          have keep₃' := combine keep₂' keep₃
          by_cases h15 : j = 15
          · apply WP.ite true (by simpa only [h15, decide_true] using cond₃)
            · intro _
              exact hrot s₃ keep₃' 1 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inr h15))])
            · simp
          · apply WP.ite false (by simpa only [h15, decide_false] using cond₃)
            · simp
            · intro _
              exact hrot s₃ keep₃' 2 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_right (by simp only [h2, h8, h15, or_self, not_false_eq_true])])

end VG.Proof.TripleDes.Arm.Key
