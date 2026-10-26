module

public import VerifiedGarbage.Proof.Argon2.Spec
public import VerifiedGarbage.Impl.Argon2.AArch64.Compress
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! # Argon2's modified addition and GB on ARM64 registers -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Impl.Argon2.AArch64

theorem low32 (x : BitVec 64) :
    (x.setWidth 32).setWidth 64 = x &&& 0xffffffff := by
  rw [BitVec.setWidth_eq_append (by decide)]
  exact (BitVec.and_setWidth_allOnes 32 32 x).symm

theorem addMul_value (a b : BitVec 64) :
    a + (a.setWidth 32).setWidth 64 * (b.setWidth 32).setWidth 64 +
      (b + (a.setWidth 32).setWidth 64 * (b.setWidth 32).setWidth 64) =
      Spec.Argon2.addMul a b := by
  rw [low32, low32, Spec.Argon2.addMul, BitVec.mul_assoc]
  generalize (a &&& 0xffffffff) * (b &&& 0xffffffff) = p
  grind

/-- GB's four registers and its temporary are distinct. -/
structure Distinct (a b c d t : Reg) : Prop where
  ab : a ≠ b
  ac : a ≠ c
  ad : a ≠ d
  a_t : a ≠ t
  bc : b ≠ c
  bd : b ≠ d
  b_t : b ≠ t
  cd : c ≠ d
  c_t : c ≠ t
  d_t : d ≠ t

theorem addMul_ok {a b t : Reg} (hat : a ≠ t) (hbt : b ≠ t) (s : State) :
    WP isa (.block (addMul a b t)) s fun u =>
      u.gpr a = Spec.Argon2.addMul (s.gpr a) (s.gpr b) ∧
      (∀ r, r ≠ a → r ≠ t → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v := by
  apply WP.of_runBlock
  simp only [addMul, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ _ hat.symm, RegUpd.gpr_write_of_ne _ _ _ hat,
    RegUpd.gpr_write_of_ne _ _ _ hbt, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.v_write,
    Option.some.injEq, exists_eq_left', BitVec.setWidth_eq]
  refine ⟨addMul_value _ _, ?_, trivial, trivial, trivial, trivial⟩
  intro r h1 h2
  rw [RegUpd.gpr_write_of_ne _ _ _ h1, RegUpd.gpr_write_of_ne _ _ _ h1,
    RegUpd.gpr_write_of_ne _ _ _ h2]

theorem addMulOnce_value (a b : BitVec 64) :
    a + b + (a.setWidth 32).setWidth 64 * (b.setWidth 32).setWidth 64 +
      (a.setWidth 32).setWidth 64 * (b.setWidth 32).setWidth 64 =
      Spec.Argon2.addMul a b := by
  rw [low32, low32, Spec.Argon2.addMul, BitVec.mul_assoc]
  generalize (a &&& 0xffffffff) * (b &&& 0xffffffff) = p
  grind

/-- The single-product form has the same modular arithmetic and frame. -/
theorem addMulOnce_ok {a b t : Reg} (hat : a ≠ t) (hbt : b ≠ t) (s : State) :
    WP isa (.block (addMulOnce a b t)) s fun u =>
      u.gpr a = Spec.Argon2.addMul (s.gpr a) (s.gpr b) ∧
      (∀ r, r ≠ a → r ≠ t → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v := by
  apply WP.of_runBlock
  simp only [addMulOnce, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ _ hat.symm, RegUpd.gpr_write_of_ne _ _ _ hat,
    RegUpd.gpr_write_of_ne _ _ _ hbt, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.v_write,
    Option.some.injEq, exists_eq_left', BitVec.setWidth_eq]
  refine ⟨addMulOnce_value _ _, ?_, trivial, trivial, trivial, trivial⟩
  intro r h1 h2
  rw [RegUpd.gpr_write_of_ne _ _ _ h1, RegUpd.gpr_write_of_ne _ _ _ h1,
    RegUpd.gpr_write_of_ne _ _ _ h1, RegUpd.gpr_write_of_ne _ _ _ h2]

/-- A register XOR followed by one of GB's rotations. -/
theorem xorRotate_ok {a d : Reg} (n : Nat)
    (hn : 1 ≤ n) (hn' : n ≤ 63) (s : State) :
    WP isa (.block [.logic .eor .x d d a, .ror .x d d n]) s fun t =>
      t.gpr d = (s.gpr d ^^^ s.gpr a).rotateRight n ∧
      (∀ r, r ≠ d → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.v = s.v := by
  apply WP.of_runBlock
  have h64 : n < 64 := by omega
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    h64, ite_true, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.v_write,
    BitVec.setWidth_eq]
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial, trivial, trivial⟩

/-- One half of GB, with all memory and the other registers preserved. -/
theorem halfGB_ok {a b c d t : Reg} (h : Distinct a b c d t) (r1 r2 : Nat)
    (h1 : 1 ≤ r1) (h1' : r1 ≤ 63) (h2 : 1 ≤ r2) (h2' : r2 ≤ 63) (s : State) :
    let va := Spec.Argon2.addMul (s.gpr a) (s.gpr b)
    let vd := (s.gpr d ^^^ va).rotateRight r1
    let vc := Spec.Argon2.addMul (s.gpr c) vd
    let vb := (s.gpr b ^^^ vc).rotateRight r2
    WP isa (.block (halfGB a b c d t r1 r2)) s fun u =>
      u.gpr a = va ∧ u.gpr b = vb ∧ u.gpr c = vc ∧ u.gpr d = vd ∧
      (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → r ≠ t → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v := by
  dsimp only
  rw [halfGB, List.append_assoc, List.append_assoc]
  apply WP.block_append
  refine (addMul_ok h.a_t h.b_t s).mono ?_
  rintro s1 ⟨ha, hk1, hm1, hr1, hw1, hv1⟩
  apply WP.block_append
  refine (xorRotate_ok (a := a) (d := d) r1 h1 h1' s1).mono ?_
  rintro s2 ⟨hd, hk2, hm2, hr2, hw2, hv2⟩
  apply WP.block_append
  refine (addMul_ok h.c_t h.d_t s2).mono ?_
  rintro s3 ⟨hc, hk3, hm3, hr3, hw3, hv3⟩
  refine (xorRotate_ok (a := c) (d := b) r2 h2 h2' s3).mono ?_
  rintro s4 ⟨hb, hk4, hm4, hr4, hw4, hv4⟩
  have hd' : s2.gpr d = (s.gpr d ^^^ Spec.Argon2.addMul (s.gpr a) (s.gpr b)).rotateRight r1 := by
    rw [hd, ha, hk1 d h.ad.symm h.d_t]
  have hc' : s3.gpr c = Spec.Argon2.addMul (s.gpr c) (s2.gpr d) := by
    rw [hc, hk2 c h.cd, hk1 c h.ac.symm h.c_t]
  refine ⟨?_, ?_, ?_, ?_, ?_, hm4.trans (hm3.trans (hm2.trans hm1)),
    hr4.trans (hr3.trans (hr2.trans hr1)), hw4.trans (hw3.trans (hw2.trans hw1)),
    hv4.trans (hv3.trans (hv2.trans hv1))⟩
  · rw [hk4 a h.ab, hk3 a h.ac h.a_t, hk2 a h.ad, ha]
  · rw [hb, hc', hd', hk3 b h.bc h.b_t, hk2 b h.bd, hk1 b h.ab.symm h.b_t]
  · rw [hk4 c h.bc.symm, hc', hd']
  · rw [hk4 d h.bd.symm, hk3 d h.cd.symm h.d_t, hd']
  · intro r ra rb rc rd rt
    rw [hk4 r rb, hk3 r rc rt, hk2 r rd, hk1 r ra rt]

/-- The complete GB operation agrees with the four-word specification. -/
theorem gb_ok {a b c d t : Reg} (h : Distinct a b c d t) (s : State) :
    let v := Proof.Argon2.mix (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d)
    WP isa (.block (gb a b c d t)) s fun u =>
      u.gpr a = v.1 ∧ u.gpr b = v.2.1 ∧ u.gpr c = v.2.2.1 ∧ u.gpr d = v.2.2.2 ∧
      (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → r ≠ t → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v := by
  dsimp only
  rw [gb]
  apply WP.block_append
  refine (halfGB_ok h 32 24 (by decide) (by decide) (by decide) (by decide) s).mono ?_
  rintro u ⟨ha, hb, hc, hd, hk, hm, hr, hw, hv⟩
  refine (halfGB_ok h 16 63 (by decide) (by decide) (by decide) (by decide) u).mono ?_
  rintro w ⟨ha', hb', hc', hd', hk', hm', hr', hw', hv'⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hm'.trans hm, hr'.trans hr, hw'.trans hw, hv'.trans hv⟩
  · rw [ha', ha, hb]; rfl
  · rw [hb', ha, hb, hc, hd]; rfl
  · rw [hc', ha, hb, hc, hd]; rfl
  · rw [hd', ha, hb, hd]; rfl
  · intro r ra rb rc rd rt
    exact (hk' r ra rb rc rd rt).trans (hk r ra rb rc rd rt)

end VG.Proof.Argon2.AArch64
