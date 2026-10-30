module

public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

/-!
# ML-KEM on AArch64: the lanes of the vector codecs

The words of the vector compression and decompression (`Impl/MlKem/AArch64/Compress.lean`),
as numbers (`Lanes`): `Compress_d` (`cmpV_ok`) and `Decompress_d` (`decV_ok`) of each, and
pairs of lanes into one (`pairV_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem

theorem lanes_ushr {x : BitVec 128} {f : Nat → Nat} (hx : Lanes x f) (sh : Nat) (y : BitVec 128) :
    Lanes (VArr.s4.map2 (fun w a b => VShiftOp.eval .ushr sh w a b) y x) fun e => f e / 2 ^ sh :=
  fun e he => by
    rw [vword_map2 _ _ _ he]
    simp only [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hx e he]

theorem lanes_shl {x : BitVec 128} {f : Nat → Nat} (hx : Lanes x f) (sh : Nat) (y : BitVec 128) :
    Lanes (VArr.s4.map2 (fun w a b => VShiftOp.eval .shl sh w a b) y x) fun e => f e * 2 ^ sh % 2 ^ 32 :=
  fun e he => by
    rw [vword_map2 _ _ _ he]
    simp only [VShiftOp.eval, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hx e he]

theorem vword_and' (x y : BitVec 128) (e : Nat) : vword (x &&& y) e = vword x e &&& vword y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vword, hi]

theorem vword_or' (x y : BitVec 128) (e : Nat) : vword (x ||| y) e = vword x e ||| vword y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vword, hi]

theorem lanes_mask {x y : BitVec 128} {f : Nat → Nat} {k : Nat} (hx : Lanes x f)
    (hy : Lanes y fun _ => 2 ^ k - 1) : Lanes (x &&& y) fun e => f e % 2 ^ k := fun e he => by
  rw [vword_and', BitVec.toNat_and, hx e he, hy e he, Nat.and_two_pow_sub_one_eq_mod]

theorem or_shift {a b k : Nat} (ha : a < 2 ^ k) : a ||| b * 2 ^ k = a + b * 2 ^ k := by
  rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.add_comm]

theorem lanes_or {x y : BitVec 128} {f g : Nat → Nat} {k : Nat} (hx : Lanes x f)
    (hy : Lanes y fun e => g e * 2 ^ k) (hf : ∀ e < 4, f e < 2 ^ k) :
    Lanes (x ||| y) fun e => f e + g e * 2 ^ k := fun e he => by
  rw [vword_or', BitVec.toNat_or, hx e he, hy e he, or_shift (hf e he)]

theorem lanes_uzp1 {x y : BitVec 128} {f : Nat → Nat} (hx : Lanes x f) (hy : Lanes y fun e => f (4 + e)) :
    Lanes (VPermOp.eval .uzp1 .s4 x y) fun e => f (2 * e) := fun e he => by
  rw [vword_uzp1_s4 _ _ he]
  split
  · exact hx _ (by omega_arith)
  · rw [hy _ (by omega_arith)]; dsimp only; congr 1; omega_arith

theorem lanes_uzp2 {x y : BitVec 128} {f : Nat → Nat} (hx : Lanes x f) (hy : Lanes y fun e => f (4 + e)) :
    Lanes (VPermOp.eval .uzp2 .s4 x y) fun e => f (2 * e + 1) := fun e he => by
  rw [vword_uzp2_s4 _ _ he]
  split
  · exact hx _ (by omega_arith)
  · rw [hy _ (by omega_arith)]; dsimp only; congr 1; omega_arith

theorem lanes_get {s s' : State} {d : VReg} {x : BitVec 128} (h : VUpd s s' d x) {r : VReg} (hr : r ≠ d)
    {f : Nat → Nat} (hf : Lanes (s.v r) f) : Lanes (s'.v r) f := by rw [h.get r hr]; exact hf

theorem eval_shift {s : State} {op : VShiftOp} {a : VArr} {d n : VReg} {sh : Nat}
    (h : op.ok a.esize sh = true) :
    VOp.eval s (.shift op a d n sh) = some (d, a.map2 (fun w x y => op.eval sh w x y) (s.v d) (s.v n)) := by
  simp only [reduceVOpEval, h, ite_true]

/-- `Compress_d` of the lanes of `v`. -/
theorem cmpV_ok {s : State} {v : VReg} {d M A : Nat} (hM : M ≤ 322542) (hA : A < 2 ^ 19)
    (h16 : Lanes (s.v .v16) fun _ => M) (h17 : Lanes (s.v .v17) fun _ => A)
    (h18 : Lanes (s.v .v18) fun _ => 2 ^ d - 1) (hv17 : v ≠ .v17) (hv18 : v ≠ .v18)
    {f : Nat → Nat} (hx : Lanes (s.v v) f) (hf : ∀ e < 4, f e < 3329) :
    WP isa (.block (cmpV v)) s fun t => VChg [v] s t ∧
      Lanes (t.v v) fun e => (f e * M + A) / 2 ^ 19 % 2 ^ d := by
  unfold cmpV
  refine wp_vop rfl fun s1 h1 => wp_vop rfl fun s2 h2 =>
    wp_vop (eval_shift (by decide)) fun s3 h3 => wp_vop rfl fun s4 h4 => wp_nil ⟨?_, ?_⟩
  · exact (((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).mono (by intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at hr ⊢; exact hr)
  have l1 := lanes_mul hx h16
  rw [← h1.v] at l1
  have l2 := lanes_add l1 (lanes_get h1 (Ne.symm hv17) h17)
  rw [← h2.v] at l2
  have l3 := lanes_ushr l2 19 (s2.v v)
  rw [← h3.v] at l3
  have l4 := lanes_mask l3 (lanes_get h3 (Ne.symm hv18) (lanes_get h2 (Ne.symm hv18)
    (lanes_get h1 (Ne.symm hv18) h18)))
  rw [h4.v]
  refine l4.congr fun e he => ?_
  have := hf e he
  have hm : f e * M < 2 ^ 31 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_of_lt this) hM) (by decide)
  have h1 : f e * M < 2 ^ 32 := by omega_arith
  rw [Nat.mod_eq_of_lt h1]
  have h2 : f e * M + A < 2 ^ 32 := by omega_arith
  rw [Nat.mod_eq_of_lt h2]

/-- The lanes of `x` and `y`, less than `2ᵇ`, in pairs. -/
theorem pairV_ok {s : State} {b : Nat} {d x y : VReg} (hb : b < 16) (hx19 : x ≠ .v19) (hy19 : y ≠ .v19)
    (hd19 : d ≠ .v19) {f : Nat → Nat} (hx : Lanes (s.v x) f) (hy : Lanes (s.v y) fun e => f (4 + e))
    (hf : ∀ e < 8, f e < 2 ^ b) :
    WP isa (.block (pairV b d x y)) s fun t => VChg [.v19, d] s t ∧
      Lanes (t.v d) fun e => f (2 * e) + f (2 * e + 1) * 2 ^ b := by
  unfold pairV
  refine wp_vop rfl fun s1 h1 => wp_vop rfl fun s2 h2 =>
    wp_vop (eval_shift (by simp only [VShiftOp.ok, VArr.esize]; simp; omega_arith)) fun s3 h3 => wp_vop rfl fun s4 h4 =>
      wp_nil ⟨?_, ?_⟩
  · exact (((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).mono (by
      intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with ((h | h) | h) | h <;> simp [h])
  have l1 := lanes_uzp2 hx hy
  rw [← h1.v] at l1
  have l2 := lanes_uzp1 (lanes_get h1 hx19 hx) (lanes_get h1 hy19 hy)
  rw [← h2.v] at l2
  have l3 := lanes_shl (lanes_get h2 (Ne.symm hd19) l1) b (s2.v .v19)
  rw [← h3.v] at l3
  have l4 := lanes_or (lanes_get h3 hd19 l2) (k := b) (g := fun e => f (2 * e + 1))
    (l3.congr fun e he => Nat.mod_eq_of_lt (by
      have := hf (2 * e + 1) (by omega_arith)
      calc f (2 * e + 1) * 2 ^ b < 2 ^ b * 2 ^ b := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos b)
        _ = 2 ^ (b + b) := (Nat.pow_add 2 b b).symm
        _ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega_arith)))
    fun e he => hf _ (by omega_arith)
  rw [h4.v]
  exact l4

/-- `Decompress_d` of the lanes of `v`. -/
theorem decV_ok {s : State} {v : VReg} {d : Nat} (hd : 0 < d) (hd' : d ≤ 11)
    (h16 : Lanes (s.v .v16) fun _ => 3329) (h17 : Lanes (s.v .v17) fun _ => 2 ^ (d - 1))
    (hv17 : v ≠ .v17)
    {f : Nat → Nat} (hx : Lanes (s.v v) f) (hf : ∀ e < 4, f e < 2 ^ d) :
    WP isa (.block (decV d v)) s fun t => VChg [v] s t ∧
      Lanes (t.v v) fun e => (3329 * f e + 2 ^ (d - 1)) / 2 ^ d := by
  unfold decV
  refine wp_vop rfl fun s1 h1 => wp_vop rfl fun s2 h2 =>
    wp_vop (eval_shift (by simp only [VShiftOp.ok, VArr.esize]; simp; omega_arith)) fun s3 h3 => wp_nil ⟨?_, ?_⟩
  · exact ((h1.chg.trans h2.chg).trans h3.chg).mono (by intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at hr ⊢; exact hr)
  have l1 := lanes_mul hx h16
  rw [← h1.v] at l1
  have l2 := lanes_add l1 (lanes_get h1 (Ne.symm hv17) h17)
  rw [← h2.v] at l2
  have l3 := lanes_ushr l2 d (s2.v v)
  rw [← h3.v] at l3
  refine l3.congr fun e he => ?_
  have := hf e he
  have h11 : 2 ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hd'
  have h10 : 2 ^ (d - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  rw [show (2 : Nat) ^ 11 = 2048 from rfl] at h11 h10
  have b0 : f e * 3329 ≤ 2048 * 3329 := Nat.mul_le_mul_right _ (by omega_arith)
  have b1 : f e * 3329 < 2 ^ 32 := Nat.lt_of_le_of_lt b0 (by decide)
  rw [Nat.mod_eq_of_lt b1]
  have b2 : f e * 3329 + 2 ^ (d - 1) < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.add_le_add b0 h10) (by decide)
  rw [Nat.mod_eq_of_lt b2, Nat.mul_comm (f e)]

end VG.Proof.MlKem.AArch64.CodecV
