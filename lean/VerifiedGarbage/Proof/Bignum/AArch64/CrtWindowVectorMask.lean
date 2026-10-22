module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorLoad
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract

/-! A 128-byte table row: a mask from a scalar comparison of the row counter
with the digit, and eight load/BIT pairs. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowSelectVector (innerWide)

def maskWide : List Instr :=
  [.subs .x .x9 .x14 .x5, .cselc .x .x9 .x7 .x8 .eq, .vop (.dup .d2 .v20 .x9)]

theorem innerWide_eq : innerWide =
    maskWide ++ loadBits 8 ++ ([.add .x .x16 .x16 .x6] : List Instr) := rfl

theorem sub_zero_iff (a b : BitVec 64) :
    a + ~~~b + BitVec.ofNat 64 (true.toNat) = 0 ↔ a = b := by
  rw [show BitVec.ofNat 64 (true.toNat) = 1#64 from rfl, BitVec.add_assoc,
    ← BitVec.neg_eq_not_add, ← BitVec.sub_eq_add_neg]
  constructor
  · intro h
    have e := BitVec.sub_add_cancel a b
    rw [h] at e
    exact e.symm.trans (BitVec.zero_add b)
  · intro h
    rw [h, BitVec.sub_self]
    rfl

theorem count_eq_iff {j v : Nat} (hj : j < 32) (hv : v < 32) :
    BitVec.ofNat 64 (32 - j) = BitVec.ofNat 64 (32 - v) ↔ j = v := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    omega
  · intro h; rw [h]

theorem dup2_mask (c : Prop) [Decidable c] :
    ofVDwords (if c then BitVec.allOnes 64 else 0) (if c then BitVec.allOnes 64 else 0) =
      if c then BitVec.allOnes 128 else 0 := by
  by_cases h : c
  · simp only [h, ite_true]; decide
  · simp only [h, ite_false]; decide

theorem exec_cselc_eq {s : State} {d n m : Reg} :
    exec (.cselc .x d n m .eq) s =
      some (s.write .x d (if s.zf then s.gpr n else s.gpr m)) := rfl

theorem exec_dup_d2 {s : State} {d : VReg} {n : Reg} :
    exec (.vop (.dup .d2 d n)) s = some (s.setV d (ofVDwords (s.gpr n) (s.gpr n))) := rfl

/-- The mask is all ones in exactly the row `j = v`, from `x14 = 32 - j` and
`x5 = 32 - v`. Only `x9`, the flags and `v20` change. -/
theorem mask_ok {s : State} {j v : Nat} (hj : j < 32) (hv : v < 32)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 (32 - j)) (h5 : s.gpr .x5 = BitVec.ofNat 64 (32 - v))
    (h7 : s.gpr .x7 = BitVec.allOnes 64) (h8 : s.gpr .x8 = 0) :
    WP isa (.block maskWide) s fun t =>
      t.v .v20 = (if j = v then BitVec.allOnes 128 else 0) ∧ t.mem = s.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .x16 = s.gpr .x16 ∧ t.gpr .x6 = s.gpr .x6 ∧
      ∀ r, r ≠ .v20 → t.v r = s.v r := by
  apply WP.of_runBlock
  simp only [maskWide, runBlock_cons, runStep_some, runBlock_nil, exec_subs_x, exec_cselc_eq,
    exec_dup_d2, Option.some.injEq, exists_eq_left']
  generalize hA : s.addWithCarry .x .x9 (s.gpr .x14) (~~~s.gpr .x5) true = A
  have hz : A.zf = decide (j = v) := by
    subst hA
    change decide (_ = 0) = _
    simp only [Size.bits, h14, h5]
    exact decide_eq_decide.mpr ((sub_zero_iff _ _).trans (count_eq_iff hj hv))
  have hg : ∀ r, r ≠ .x9 → A.gpr r = s.gpr r := fun r hr => by
    subst hA
    simp only [gpr_addWithCarry_x, hr, ite_false]
  have hm : A.mem = s.mem := by subst hA; rfl
  have hrd : A.rd = s.rd := by subst hA; rfl
  have hwr : A.wr = s.wr := by subst hA; rfl
  have hv' : A.v = s.v := by subst hA; rfl
  simp only [RegUpd.gpr_write_self, hz, hg _ (show Reg.x7 ≠ .x9 by decide),
    hg _ (show Reg.x8 ≠ .x9 by decide), h7, h8, Size.bits, BitVec.setWidth_eq,
    decide_eq_true_eq, RegUpd.v_setV_self, RegUpd.mem_setV, RegUpd.mem_write, hm,
    RegUpd.rd_setV, RegUpd.rd_write, hrd, RegUpd.wr_setV, RegUpd.wr_write, hwr,
    RegUpd.gpr_setV, RegUpd.gpr_write_of_ne (h := show ¬Reg.x16 = .x9 by decide),
    RegUpd.gpr_write_of_ne (h := show ¬Reg.x6 = .x9 by decide),
    hg _ (show Reg.x16 ≠ .x9 by decide), hg _ (show Reg.x6 ≠ .x9 by decide), dup2_mask]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, fun r hr => ?_⟩
  rw [RegUpd.v_setV_of_ne _ _ hr, RegUpd.v_write, hv']

theorem add16_ok (s : State) :
    WP isa (.block [.add .x .x16 .x16 .x6]) s fun t =>
      t = s.write .x .x16 (s.gpr .x16 + s.gpr .x6) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add_x, Option.some.injEq,
    exists_eq_left']

theorem innerWide_ok {s : State} {j v : Nat} (hj : j < 32) (hv : v < 32)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 (32 - j)) (h5 : s.gpr .x5 = BitVec.ofNat 64 (32 - v))
    (h7 : s.gpr .x7 = BitVec.allOnes 64) (h8 : s.gpr .x8 = 0)
    (hld : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block innerWide) s fun t =>
      ((∀ i < 8, t.v (acc i) = if j = v then
        s.mem.read (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16 else s.v (acc i)) ∧
      t.gpr .x16 = s.gpr .x16 + s.gpr .x6 ∧ t.mem = s.mem) ∧ Keep [.x9, .x16] s t := by
  refine WP.keep [.x9, .x16] ?_ (by decide) (by decide) (by decide +kernel)
  rw [innerWide_eq, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (mask_ok hj hv h14 h5 h7 h8) fun a ⟨hm, am, ard, awr, a16, a6, av⟩ => ?_
  refine WP.mono (loadBits_ok (choose := j = v) 8 (Nat.le_refl _) hm
    (fun i hi => by rw [ard, awr, a16]; exact hld i hi)) fun b ⟨hb, kb⟩ => ?_
  refine WP.mono (add16_ok b) fun t ht => ?_
  subst t
  refine ⟨fun i hi => ?_, ?_, kb.mem.trans am⟩
  · rw [RegUpd.v_write, hb i hi, am, a16, av _ (acc_facts i hi).1]
    simp only [hi, true_and]
  · simp only [RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, kb.gpr, a16, a6]

end VG.Proof.Bignum.AArch64.WindowVector
