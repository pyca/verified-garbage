module

public import VerifiedGarbage.Proof.Rc4.PPC64LE.Lookup
import VerifiedGarbage.Proof.Rc4.Memory
import VerifiedGarbage.Proof.Rc4.Qword
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # RC4 on PPC64LE: replacing a secret-indexed byte of the table

The difference is XORed into each of the table's 16 vectors under a mask
that is the difference in one lane of one vector: `vperm` of one-hot
vectors that conditional rotations (`rotStep_run`) move to the lane and
to the vector (`chain_bytes`). A vector's store then changes only that
byte (`write_xor`).
-/

@[expose] public section

namespace VG.Proof.Rc4.PPC64LE
open VG VG.PPC64LE VG.Impl.Rc4.PPC64LE VG.Proof.Rc4

theorem byte_addr (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem xor_byte (a b : Byte) : a.setWidth 64 ^^^ b.setWidth 64 = (a ^^^ b).setWidth 64 := by
  rw [BitVec.setWidth_xor]

theorem hi64 (a b : BitVec 64) : (a ++ b).extractLsb' 64 64 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show ¬ 64 + i < 64 by omega, ite_false, Nat.add_sub_cancel_left]

theorem lo64 (a b : BitVec 64) : (a ++ b).extractLsb' 0 64 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    Nat.zero_add, ite_true]

/-! ## Rotations -/

/-- `vsldoi d x x n`: `x` rotated left by `n` bytes. -/
def rotl (x : BitVec 128) (n : Nat) : BitVec 128 := BitVec.extractLsb' 128 128 ((x ++ x) <<< (8 * n))

theorem vbyte_zero (i : Nat) : vbyte 0#128 i = 0#8 := by simp [vbyte]

theorem ofVBytes_const_ite (c : Prop) [Decidable c] :
    (ofVBytes fun _ => if c then 255#8 else 0#8) = if c then BitVec.allOnes 128 else 0#128 := by
  by_cases h : c
  · simp only [h, ite_true]; decide
  · simp only [h, ite_false]; decide

theorem sel_ite (a b : BitVec 128) (c : Prop) [Decidable c] :
    (a &&& ~~~(if c then BitVec.allOnes 128 else 0#128)) ||| (b &&& (if c then BitVec.allOnes 128 else 0#128)) =
      if c then b else a := by
  by_cases h : c
  · simp only [h, ite_true, BitVec.not_allOnes, BitVec.and_zero, BitVec.zero_or, BitVec.and_allOnes]
  · simp only [h, ite_false, BitVec.not_zero, BitVec.and_allOnes, BitVec.and_zero, BitVec.or_zero]

/-- A splat of a bit's mask: all ones if bit `c` of `q` is set. -/
theorem splat_mask (q u : BitVec 64) {c : Nat} (hc : c < 64) :
    (ofVBytes fun i => if (vbyte 0#128 i).toNat % 32 < 16 then
        vbyte ((0#64 - (q <<< (63 - c)) >>> 63) ++ u) ((vbyte 0#128 i).toNat % 32)
      else vbyte ((0#64 - (q <<< (63 - c)) >>> 63) ++ u) ((vbyte 0#128 i).toNat % 32 - 16)) =
      if q.getLsbD c = true then BitVec.allOnes 128 else 0#128 := by
  simp only [vbyte_zero, BitVec.toNat_zero, Nat.zero_mod, show (0 : Nat) < 16 by decide, ite_true,
    vbyte_mask _ _ hc (show 0 < 8 by decide)]
  exact ofVBytes_const_ite _

theorem rotStep_run (u : State) {v w : VReg} (hv : (v = .v0 ∧ w = .v1) ∨ (v = .v1 ∧ w = .v0)) {b : Nat}
    (hb : b < 4) (hz : u.vpr .v14 = 0#128) (h8 : u.gpr .r8 = 0) :
    WP isa (.block (rotStep v b)) u fun t =>
      t.vpr v = (if (u.gpr .r0).getLsbD b = true then rotl (u.vpr v) (2 ^ b) else u.vpr v) ∧
      t.vpr .v14 = u.vpr .v14 ∧ t.vpr .v15 = u.vpr .v15 ∧ t.vpr w = u.vpr w ∧ t.mem = u.mem := by
  rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
  · unfold rotStep vperm
    rrun [reduceVOpEval, vRotM, vRot, vZ, vpr_writeV, gpr_writeV, mem_writeV, hz, h8,
      splat_mask _ _ (show 0 < 64 by decide), splat_mask _ _ (show 1 < 64 by decide),
      splat_mask _ _ (show 2 < 64 by decide), splat_mask _ _ (show 3 < 64 by decide), sel_ite, rotl]

/-- Byte 0's one-hot vector. -/
abbrev oh0 : BitVec 128 := 0xFF000000000000000000000000000000#128

/-- The four conditional rotations, by the bits of `n`. -/
def chain (n : Nat) (x : BitVec 128) : BitVec 128 :=
  let x1 := if n.testBit 0 = true then rotl x 1 else x
  let x2 := if n.testBit 1 = true then rotl x1 2 else x1
  let x3 := if n.testBit 2 = true then rotl x2 4 else x2
  if n.testBit 3 = true then rotl x3 8 else x3

theorem chain_bytes : ∀ n < 16, ∀ t < 16, vbyte (chain n oh0) t = if t = (16 - n) % 16 then 255#8 else 0#8 := by
  decide

theorem oneHot0_run (u : State) {v : VReg} (hv : v = .v0 ∨ v = .v1) (hz : u.vpr .v14 = 0#128) :
    WP isa (.block (oneHot0 v)) u fun t =>
      t.vpr v = oh0 ∧ t.vpr .v14 = u.vpr .v14 ∧ t.vpr .v15 = u.vpr .v15 ∧
      (∀ w, w ≠ v → w ≠ .v14 → t.vpr w = u.vpr w) ∧ t.mem = u.mem := by
  rcases hv with rfl | rfl <;>
  · unfold oneHot0
    rrun [reduceVOpEval, vZ, vpr_writeV, gpr_writeV, mem_writeV, hz, sldoi8_eq, hi64, lo64]
    refine ⟨by decide, fun w h1 _ => ?_⟩
    simp [h1]

theorem getLsbD_testBit (x : BitVec 64) (b : Nat) : x.getLsbD b = x.toNat.testBit b := rfl

theorem oneHot_run (u : State) {v w : VReg} (hv : (v = .v0 ∧ w = .v1) ∨ (v = .v1 ∧ w = .v0))
    (hz : u.vpr .v14 = 0#128) (h8 : u.gpr .r8 = 0) (hn : (u.gpr .r0).toNat < 16) :
    WP isa (.block (oneHot v)) u fun t =>
      (∀ i < 16, vbyte (t.vpr v) i = if i = (16 - (u.gpr .r0).toNat) % 16 then 255#8 else 0#8) ∧
      t.vpr .v14 = u.vpr .v14 ∧ t.vpr .v15 = u.vpr .v15 ∧ t.vpr w = u.vpr w ∧ t.mem = u.mem ∧
      Keep [.r12] u t := by
  have hv' : v = .v0 ∨ v = .v1 := by rcases hv with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hwv : w ≠ v := by rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2 <;> decide
  have hw14 : w ≠ .v14 := by rcases hv with ⟨_, h2⟩ | ⟨_, h2⟩ <;> subst h2 <;> decide
  unfold oneHot
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (oneHot0_run u hv' hz) (by rcases hv' with h | h <;> subst h <;> decide) (by
    rcases hv' with h | h <;> subst h <;> decide)) fun t₀ ⟨⟨a0, z0, d0, o0, m0⟩, k0⟩ => ?_
  have g0 : t₀.gpr .r0 = u.gpr .r0 := k0.gpr (by decide)
  have e0 : t₀.gpr .r8 = 0 := by rw [k0.gpr (by decide), h8]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (rotStep_run t₀ hv (b := 0) (by decide) (by rw [z0, hz]) e0)
    (by rcases hv' with h | h <;> subst h <;> decide) (by rcases hv' with h | h <;> subst h <;> decide))
    fun t₁ ⟨⟨a1, z1, d1, o1, m1⟩, k1⟩ => ?_
  have g1 : t₁.gpr .r0 = u.gpr .r0 := (k1.gpr (by decide)).trans g0
  have e1 : t₁.gpr .r8 = 0 := by rw [k1.gpr (by decide), e0]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (rotStep_run t₁ hv (b := 1) (by decide) (by rw [z1, z0, hz]) e1)
    (by rcases hv' with h | h <;> subst h <;> decide) (by rcases hv' with h | h <;> subst h <;> decide))
    fun t₂ ⟨⟨a2, z2, d2, o2, m2⟩, k2⟩ => ?_
  have g2 : t₂.gpr .r0 = u.gpr .r0 := (k2.gpr (by decide)).trans g1
  have e2 : t₂.gpr .r8 = 0 := by rw [k2.gpr (by decide), e1]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (rotStep_run t₂ hv (b := 2) (by decide) (by rw [z2, z1, z0, hz]) e2)
    (by rcases hv' with h | h <;> subst h <;> decide) (by rcases hv' with h | h <;> subst h <;> decide))
    fun t₃ ⟨⟨a3, z3, d3, o3, m3⟩, k3⟩ => ?_
  have g3 : t₃.gpr .r0 = u.gpr .r0 := (k3.gpr (by decide)).trans g2
  have e3 : t₃.gpr .r8 = 0 := by rw [k3.gpr (by decide), e2]
  refine WP.mono (WP.keep [.r12] (rotStep_run t₃ hv (b := 3) (by decide) (by rw [z3, z2, z1, z0, hz]) e3)
    (by rcases hv' with h | h <;> subst h <;> decide) (by rcases hv' with h | h <;> subst h <;> decide))
    fun t₄ ⟨⟨a4, z4, d4, o4, m4⟩, k4⟩ => ?_
  refine ⟨fun i hi => ?_, by rw [z4, z3, z2, z1, z0], by rw [d4, d3, d2, d1, d0],
    by rw [o4, o3, o2, o1, o0 w hwv hw14], by rw [m4, m3, m2, m1, m0],
    (((k0.trans k1).trans k2).trans (k3.trans k4)).mono (by decide)⟩
  have := chain_bytes _ hn i hi
  rw [← this, a4, g3, a3, g2, a2, g1, a1, g0, a0]
  simp only [chain, getLsbD_testBit]

/-! ## The masks -/

theorem vbyte_top (x u : BitVec 64) : vbyte (x <<< 56 ++ u) 0 = x.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  simp only [show ¬ 8 * (15 - 0) + i < 64 by omega, ite_false, show 8 * (15 - 0) + i - 64 < 64 by omega,
    decide_true, Bool.true_and, show ¬ 8 * (15 - 0) + i - 64 < 56 by omega, decide_false, Bool.not_false]
  congr 1; omega

/-- The lane's rotation: `(16 - ((index mod 16) XOR 7)) mod 16`. -/
theorem laneRot (b : Byte) :
    (((0#64 - ((b.setWidth 64 <<< 60 >>> 60) ^^^ 7#64)) <<< 60) >>> 60).toNat = (16 - ((b.toNat % 16) ^^^ 7)) % 16 := by
  have : ∀ b : Byte, (((0#64 - ((b.setWidth 64 <<< 60 >>> 60) ^^^ 7#64)) <<< 60) >>> 60).toNat =
      (16 - ((b.toNat % 16) ^^^ 7)) % 16 := by decide
  exact this b

/-- The vector's rotation: `(16 - index / 16) mod 16`. -/
theorem vecRot (b : Byte) : (((0#64 - b.setWidth 64 >>> 4) <<< 60) >>> 60).toNat = (16 - b.toNat / 16) % 16 := by
  have : ∀ b : Byte, (((0#64 - b.setWidth 64 >>> 4) <<< 60) >>> 60).toNat = (16 - b.toNat / 16) % 16 := by decide
  exact this b

theorem rot_back {p : Nat} (hp : p < 16) : (16 - (16 - p) % 16) % 16 = p := by omega

theorem and_ff (d : Byte) (c : Prop) [Decidable c] : (if c then 255#8 else 0#8) &&& d = if c then d else 0#8 := by
  by_cases h : c
  · simp only [h, ite_true, show (255#8 : Byte) = BitVec.allOnes 8 by decide, BitVec.allOnes_and]
  · simp [h]

theorem replaceStart_run (u : State) (idx d : Byte) (h9 : u.gpr .r9 = idx.setWidth 64) (h8 : u.gpr .r8 = 0)
    (h0 : u.gpr .r0 = d.setWidth 64) :
    WP isa (.block replaceStart) u fun t =>
      (∀ i < 16, vbyte (t.vpr .v0) i = if i = (idx.toNat % 16) ^^^ 7 then d else 0#8) ∧
      (∀ i < 16, vbyte (t.vpr .v1) i = if i = idx.toNat / 16 then 255#8 else 0#8) ∧
      t.vpr .v14 = 0#128 ∧ t.gpr .r11 = u.gpr .r3 ∧ t.mem = u.mem ∧ Keep [.r0, .r11, .r12] u t := by
  unfold replaceStart
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r12] (Q := fun t => t.vpr .v14 = 0#128 ∧ (∀ i < 16, vbyte (t.vpr .v15) i = d) ∧
      (t.gpr .r0).toNat = (16 - ((idx.toNat % 16) ^^^ 7)) % 16 ∧ t.mem = u.mem) (by
    unfold laneStart vperm
    rrun [reduceVOpEval, vZ, vDiff, vpr_writeV, gpr_writeV, mem_writeV, h0, h9, h8, BitVec.xor_self]
    refine ⟨fun i hi => ?_, laneRot idx⟩
    rw [vbyte_packed _ hi]
    simp only [vbyte_zero, BitVec.toNat_zero, Nat.zero_mod, show (0 : Nat) < 16 by decide, ite_true, vbyte_top]
    apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]) (by decide) rfl) fun t₁ ⟨⟨z1, d1, r1, m1⟩, k1⟩ => ?_
  have e8 : t₁.gpr .r8 = 0 := by rw [k1.gpr (by decide), h8]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (oneHot_run t₁ (v := .v0) (w := .v1) (.inl ⟨rfl, rfl⟩) z1 e8 (by rw [r1]; omega))
    (by decide) rfl) fun t₂ ⟨⟨a2, z2, d2, _, m2, _⟩, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r12] (Q := fun t => (∀ i < 16, vbyte (t.vpr .v0) i =
      if i = (idx.toNat % 16) ^^^ 7 then d else 0#8) ∧ t.vpr .v14 = 0#128 ∧
      (t.gpr .r0).toNat = (16 - idx.toNat / 16) % 16 ∧ t.mem = u.mem) (by
    unfold vecStart
    rrun [reduceVOpEval, vLane, vDiff, vpr_writeV, gpr_writeV, mem_writeV, z2, z1, m2, m1,
      show t₂.gpr .r9 = idx.setWidth 64 by rw [k2.gpr (by decide), k1.gpr (by decide), h9],
      show t₂.gpr .r8 = 0 by rw [k2.gpr (by decide), e8]]
    refine ⟨fun i hi => ?_, vecRot idx⟩
    rw [vbyte_and, a2 i hi, d2, d1 i hi, r1, rot_back (Nat.xor_lt_two_pow (n := 4) (Nat.mod_lt _ (by decide))
      (by decide)), and_ff]) (by decide) rfl)
    fun t₃ ⟨⟨a3, z3, r3, m3⟩, k3⟩ => ?_
  have e8' : t₃.gpr .r8 = 0 := by rw [k3.gpr (by decide), k2.gpr (by decide), e8]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (oneHot_run t₃ (v := .v1) (w := .v0) (.inr ⟨rfl, rfl⟩) z3 e8' (by rw [r3]; omega))
    (by decide) rfl) fun t₄ ⟨⟨a4, z4, _, o4, m4, _⟩, k4⟩ => ?_
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = t₄.gpr .r3 ∧ t.vpr = t₄.vpr ∧ t.mem = t₄.mem)
    (by rrun [BitVec.or_self]) (by decide) rfl) fun t ⟨⟨t11, tv, tm⟩, tk⟩ => ?_
  refine ⟨fun i hi => by rw [tv, o4]; exact a3 i hi, fun i hi => by
    rw [tv, a4 i hi, r3, show (16 - (16 - idx.toNat / 16) % 16) % 16 = idx.toNat / 16 by have := idx.isLt; omega],
    by rw [tv, z4, z3], by rw [t11, k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide)],
    by rw [tm, m4, m3], (((k1.trans k2).trans k3).trans (k4.trans tk)).mono (by decide)⟩

/-! ## The stores -/

theorem swapDwords_xor (a b : BitVec 128) : swapDwords (a ^^^ b) = swapDwords a ^^^ swapDwords b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_swapDwords _ hi, BitVec.getLsbD_xor, BitVec.getLsbD_xor, getLsbD_swapDwords _ hi,
    getLsbD_swapDwords _ hi]

theorem extract_xor (a b : BitVec 128) (j : Nat) :
    (a ^^^ b).extractLsb' (8 * j) 8 = a.extractLsb' (8 * j) 8 ^^^ b.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

/-- Byte `x` of a vector's store of its load XORed with `W`. -/
theorem write_xor (m : Mem) (a : Addr) (W : BitVec 128) (x : Addr) :
    (m.write a 16 (swapDwords (swapDwords (m.readW a 128) ^^^ W))) x =
      if (x - a).toNat < 16 then m x ^^^ vbyte W ((x - a).toNat ^^^ 7) else m x := by
  unfold Mem.write
  split
  · rename_i h
    rw [swapDwords_xor, swapDwords_involutive, extract_xor]
    have e1 : (m.readW a 128).extractLsb' (8 * (x - a).toNat) 8 = m x := by
      rw [Mem.readW, BitVec.setWidth_eq]
      rw [show (m.read a (128 / 8)) = m.read a 16 from rfl, Mem.extractLsb'_read m a h, BitVec.ofNat_toNat,
        BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    have e2 : ∀ (X : BitVec 128) (j : Nat), j < 16 → (swapDwords X).extractLsb' (8 * j) 8 = vbyte X (j ^^^ 7) := by
      intro X j hj
      have f : ∀ j < 16, (if 15 - j < 8 then 15 - j + 8 else 15 - j - 8) = j ^^^ 7 := by decide
      rw [← f j hj, ← vbyte_swapDwords _ (by omega), vbyte, show 15 - (15 - j) = j by omega]
    rw [e1, e2 W _ h]
  · rfl

/-- The scatter's state after `k` of the table's vectors, from `s₀`: the
replaced byte `x` (with value `nv`) is in place if its vector is done. -/
structure SInv (s₀ : State) (T : Addr) (x : Nat) (dd nv : Byte) (k : Nat) (u : State) : Prop where
  le : k ≤ 16
  lane : ∀ i < 16, vbyte (u.vpr .v0) i = if i = (x % 16) ^^^ 7 then dd else 0#8
  hot : ∀ i < 16, vbyte (u.vpr .v1) i = if (i + k) % 16 = x / 16 then 255#8 else 0#8
  z : u.vpr .v14 = 0#128
  r11 : u.gpr .r11 = T + BitVec.ofNat 64 (16 * k)
  r8 : u.gpr .r8 = 0
  mem : ∀ y, u.mem y = if (y - T).toNat < 16 * k ∧ (y - T).toNat = x then nv else s₀.mem y
  keep : Keep [.r11] s₀ u

theorem vbyte_rotl1 (H : BitVec 128) {t : Nat} (ht : t < 16) :
    vbyte (BitVec.extractLsb' 128 128 ((H ++ H) <<< 8)) t = vbyte H ((t + 1) % 16) := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, hr,
    decide_true, Bool.true_and, show 128 + (8 * (15 - t) + r) < 128 + 128 by omega,
    show ¬ 128 + (8 * (15 - t) + r) < 8 by omega, decide_false, Bool.not_false]
  by_cases h : t = 15
  · subst h
    rw [ite_eq_left (show 128 + (8 * (15 - 15) + r) - 8 < 128 by omega),
      decide_eq_true (show 8 * (15 - 15) + r < 128 by omega), Bool.true_and]
    exact congrArg H.getLsbD (by omega)
  · rw [ite_eq_right (show ¬ 128 + (8 * (15 - t) + r) - 8 < 128 by omega),
      decide_eq_true (show 8 * (15 - t) + r < 128 by omega), Bool.true_and]
    exact congrArg H.getLsbD (by omega)

theorem scatter_run (u : State) (hz : u.vpr .v14 = 0#128) (h8 : u.gpr .r8 = 0) {a : Addr} (h11 : u.gpr .r11 = a)
    (hr : InRegions (u.rd ++ u.wr) a 16) (hw : InRegions u.wr a 16) :
    WP isa (.block scatterStep) u fun t =>
      t.mem = u.mem.write a 16 (swapDwords (swapDwords (u.mem.readW a 128) ^^^ (u.vpr .v0 &&&
        ofVBytes fun _ => vbyte (u.vpr .v1) 0))) ∧
      t.vpr .v1 = BitVec.extractLsb' 128 128 ((u.vpr .v1 ++ u.vpr .v1) <<< 8) ∧
      t.vpr .v0 = u.vpr .v0 ∧ t.vpr .v14 = u.vpr .v14 ∧ t.gpr .r11 = a + 16#64 ∧ t.rd = u.rd ∧ t.wr = u.wr := by
  unfold scatterStep vperm
  rrun [reduceVOpEval, vMask, vHot, vLane, vS, vZ, vpr_writeV, gpr_writeV, mem_writeV, rd_writeV, wr_writeV,
    ↓read_sixteen, addrX, hz, h8, h11, hr, hw, State.store, vbyte_zero, BitVec.toNat_ofNat, Nat.zero_mod]

theorem sub_off (y T : Addr) (c : Nat) (hc : c < 2 ^ 64) :
    (y - (T + BitVec.ofNat 64 c)).toNat = ((y - T).toNat + (2 ^ 64 - c)) % 2 ^ 64 := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem xor7_inj : ∀ j < 16, ∀ q < 16, (j ^^^ 7 = q ^^^ 7 ↔ j = q) := by decide

theorem xor7_lt : ∀ j < 16, j ^^^ 7 < 16 := by decide

theorem eq_off (y T : Addr) : y = T + BitVec.ofNat 64 (y - T).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

theorem scatter_step {s₀ : State} {T : Addr} {x : Nat} {dd nv : Byte} (hw : InRegions s₀.wr T 256)
    (hnv : nv = s₀.mem (T + BitVec.ofNat 64 x) ^^^ dd) {k : Nat} (hk : k < 16) {u : State}
    (I : SInv s₀ T x dd nv k u) :
    WP isa (.block scatterStep) u (SInv s₀ T x dd nv (k + 1)) := by
  have hwu : u.wr = s₀.wr := I.keep.2.2
  have hwa : InRegions u.wr (T + BitVec.ofNat 64 (16 * k)) 16 := by
    rw [hwu]; exact region_offset _ _ _ _ _ (by omega) (by omega) hw
  have hra : InRegions (u.rd ++ u.wr) (T + BitVec.ofNat 64 (16 * k)) 16 := by
    obtain ⟨r, hr, hc⟩ := hwa; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep [.r11] (scatter_run u I.z I.r8 I.r11 hra hwa) (by decide) rfl)
    fun t ⟨⟨tm, t1, t0, t14, t11, trd, twr⟩, tk⟩ => ?_
  have hM : (ofVBytes fun _ => vbyte (u.vpr .v1) 0) = if k = x / 16 then BitVec.allOnes 128 else 0#128 := by
    rw [I.hot 0 (by decide), show (0 + k) % 16 = k by omega]
    exact ofVBytes_const_ite _
  have hW : ∀ j < 16, vbyte (u.vpr .v0 &&& ofVBytes fun _ => vbyte (u.vpr .v1) 0) (j ^^^ 7) =
      if k = x / 16 ∧ j = x % 16 then dd else 0#8 := by
    intro j hj
    rw [hM, vbyte_and, I.lane _ (xor7_lt j hj)]
    by_cases e : k = x / 16
    · rw [ite_eq_left e, show vbyte (BitVec.allOnes 128) (j ^^^ 7) = 255#8 by
        have : ∀ j < 16, vbyte (BitVec.allOnes 128) j = 255#8 := by decide
        exact this _ (xor7_lt j hj)]
      have := xor7_inj j hj (x % 16) (by omega)
      by_cases e2 : j = x % 16
      · rw [ite_eq_left (this.mpr e2), ite_eq_left ⟨e, e2⟩, show (255#8 : Byte) = BitVec.allOnes 8 by decide,
          BitVec.and_allOnes]
      · rw [ite_eq_right (fun h => e2 (this.mp h)), ite_eq_right (fun h => e2 h.2), BitVec.zero_and]
    · rw [ite_eq_right e, vbyte_zero, BitVec.and_zero, ite_eq_right (fun h => e h.1)]
  refine ⟨by omega, fun i hi => by rw [t0]; exact I.lane i hi, fun i hi => ?_, by rw [t14]; exact I.z, ?_,
    by rw [tk.gpr (by decide)]; exact I.r8, fun y => ?_, I.keep.trans tk |>.mono (by decide)⟩
  · rw [t1, vbyte_rotl1 _ hi, I.hot _ (Nat.mod_lt _ (by decide)), show ((i + 1) % 16 + k) % 16 = (i + (k + 1)) % 16 by
      omega]
  · rw [t11, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add]; congr 2
  · rw [tm, write_xor, sub_off _ _ _ (by omega)]
    have ho := (y - T).isLt
    generalize ho' : (y - T).toNat = o at ho
    split
    · rename_i hin
      have h1 : 16 * k ≤ o ∧ o < 16 * k + 16 := by omega
      rw [show (o + (2 ^ 64 - 16 * k)) % 2 ^ 64 = o - 16 * k by omega, hW _ (by omega), I.mem y, ho',
        ite_eq_right (show ¬ (o < 16 * k ∧ o = x) by omega)]
      by_cases e : o = x
      · rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left ⟨by omega, by omega⟩, hnv, eq_off y T, ho', e]
      · rw [ite_eq_right (fun h => e (by omega)), ite_eq_right (fun h => e h.2), BitVec.xor_zero]
    · rename_i hout
      rw [I.mem y, ho']
      by_cases e : o < 16 * k
      · simp only [show (o < 16 * k ∧ o = x) ↔ (o < 16 * (k + 1) ∧ o = x) by omega]
      · rw [ite_eq_right (show ¬ (o < 16 * k ∧ o = x) by omega), ite_eq_right (show ¬ (o < 16 * (k + 1) ∧ o = x) by omega)]

theorem scatter_all {s₀ : State} {T : Addr} {x : Nat} {dd nv : Byte} (hw : InRegions s₀.wr T 256)
    (hnv : nv = s₀.mem (T + BitVec.ofNat 64 x) ^^^ dd) :
    ∀ k ≤ 16, ∀ u, SInv s₀ T x dd nv 0 u →
      WP isa (.block ((List.range k).flatMap fun _ => scatterStep)) u (SInv s₀ T x dd nv k)
  | 0, _, u, I => WP.block_nil I
  | k + 1, hk, u, I => by
    rw [flatMap_succ, WP.block_append_iff]
    exact WP.mono (scatter_all hw hnv k (by omega) u I) fun v V => scatter_step hw hnv (by omega) V

/-! ## The replacement -/

theorem replace_core (s : State) (idx ii : Byte) (h9 : s.gpr .r9 = idx.setWidth 64)
    (h8 : s.gpr .r8 = 0) (hcx : s.gpr .r6 = ii.setWidth 64)
    (hw : InRegions s.wr (s.gpr .r3) 256) :
    WP isa (.block replace) s fun t =>
      t.gpr .r10 = (s.mem (s.gpr .r3 + BitVec.ofNat 64 idx.toNat)).setWidth 64 ∧
      t.mem = s.mem.write (s.gpr .r3 + BitVec.ofNat 64 idx.toNat) 1
        (s.mem (s.gpr .r3 + BitVec.ofNat 64 ii.toNat)) := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .r3) 256 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain ⟨T, hT⟩ : ∃ T, s.gpr .r3 = T := ⟨_, rfl⟩
  let b := s.mem (T + BitVec.ofNat 64 idx.toNat)
  let v := s.mem (T + BitVec.ofNat 64 ii.toNat)
  simp only [replace, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r10, .r11, .r12] (lookup_core s idx h9 h8 hr) (by decide))
    fun t ⟨⟨t10, tm⟩, tk⟩ => ?_
  rw [WP.block_append_iff]
  have hi : InRegions (t.rd ++ t.wr) (T + ii.setWidth 64) 1 := by
    rw [tk.2.1, tk.2.2, byte_addr, ← hT]
    exact region_offset _ _ _ _ _ (by have := ii.isLt; omega) (by have := ii.isLt; omega) hr
  refine WP.mono (WP.keep [.r0, .r12] (Q := fun u => u.gpr .r0 = v.setWidth 64 ∧ u.mem = s.mem) (by
    unfold loadI
    rrun [show t.gpr .r3 = T by rw [tk.gpr (by decide), hT], show t.gpr .r6 = ii.setWidth 64 by
      rw [tk.gpr (by decide), hcx], hi, tm]
    show _ = (s.mem (T + BitVec.ofNat 64 ii.toNat)).setWidth 64
    rw [← byte_addr ii]) (by decide) rfl) fun u ⟨⟨u0, um⟩, uk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0] (Q := fun w => w.gpr .r0 = (v ^^^ b).setWidth 64 ∧ w.mem = s.mem ∧ w.vpr = u.vpr)
    (by rrun [u0, show u.gpr .r10 = b.setWidth 64 by rw [uk.gpr (by decide), t10, hT], um, xor_byte])
    (by decide) rfl) fun w ⟨⟨w0, wm, _⟩, wk⟩ => ?_
  have K : Keep [.r0, .r10, .r11, .r12] s w := ((tk.trans uk).trans wk).mono (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (replaceStart_run w idx (v ^^^ b) (by rw [K.gpr (by decide), h9])
    (by rw [K.gpr (by decide), h8]) w0) fun z ⟨zl, zh, zz, z11, zm, zk⟩ => ?_
  have K2 : Keep [.r0, .r10, .r11, .r12] s z := (K.trans zk).mono (by decide)
  have hwz : InRegions z.wr T 256 := by rw [K2.2.2, ← hT]; exact hw
  have I0 : SInv z T idx.toNat (v ^^^ b) v 0 z := ⟨by decide, zl, fun i hi => by rw [zh i hi, Nat.add_zero,
      Nat.mod_eq_of_lt hi], zz, by rw [z11, K.gpr (by decide), hT]; simp,
    by rw [K2.gpr (by decide), h8], fun y => by simp, Keep.refl _ _⟩
  have hnv : v = z.mem (T + BitVec.ofNat 64 idx.toNat) ^^^ (v ^^^ b) := by
    rw [zm, wm, show s.mem (T + BitVec.ofNat 64 idx.toNat) = b from rfl, BitVec.xor_comm v b,
      ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  refine WP.mono (scatter_all hwz hnv 16 (by decide) z I0) fun f F => ⟨?_, ?_⟩
  · rw [F.keep.gpr (by decide), zk.gpr (by decide), wk.gpr (by decide), uk.gpr (by decide), t10, hT]
  · funext y
    rw [F.mem y, zm, wm, hT]
    unfold Mem.write
    have ho := (y - T).isLt
    rw [sub_off _ _ _ (by have := idx.isLt; omega)]
    by_cases e : (y - T).toNat = idx.toNat
    · rw [ite_eq_left ⟨by have := idx.isLt; omega, e⟩, ite_eq_left (by rw [e]; omega)]
      rw [e, show (idx.toNat + (2 ^ 64 - idx.toNat)) % 2 ^ 64 = 0 by omega]
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
      show (s.mem (T + BitVec.ofNat 64 ii.toNat))[i] = _
      rw [← byte_addr ii]
    · rw [ite_eq_right (fun h => e h.2), ite_eq_right (by omega)]

end VG.Proof.Rc4.PPC64LE
