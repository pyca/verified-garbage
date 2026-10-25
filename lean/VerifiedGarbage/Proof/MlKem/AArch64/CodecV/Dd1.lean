module
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdLoop

import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Framework.Block

/-!
# ML-KEM on AArch64: an iteration of `dd1Body`

Byte `j` of a vector broadcast (`dupE`), its bit `i` masked in word `i` (AND), compared with zero
(CMEQ) and turned into `0` or `1665` (BIC): `Decompress₁` of the bit (`dd1Byte_ok`). Sixteen bytes
of the input to coefficients `128 k … 128 k + 127` of the output (`step1`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Spec.MlKem

theorem vword_bytes' (x : BitVec 128) (j : Nat) :
    vword x j = vbyte x (4*j+3) ++ vbyte x (4*j+2) ++ vbyte x (4*j+1) ++ vbyte x (4*j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [vword, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true, Bool.true_and]
  by_cases h0 : b < 8
  · simp only [h0, ite_true, decide_true, Bool.true_and]
    congr 1; omega_arith
  by_cases h1 : b < 16
  · simp only [h0, ite_false, show b-8<8 by omega_arith, ite_true, decide_true, Bool.true_and]
    congr 1; omega_arith
  by_cases h2 : b < 24
  · simp only [h0, ite_false, show ¬ b-8<8 by omega_arith, show b-8-8<8 by omega_arith,
      ite_true, decide_true, Bool.true_and]
    congr 1 <;> omega_arith
  · simp only [h0, ite_false, show ¬ b-8<8 by omega_arith, show ¬ b-8-8<8 by omega_arith,
      show b-8-8-8<8 by omega_arith, decide_true, Bool.true_and]
    congr 1; omega_arith

/-- A bit of a broadcast byte, as `Decompress₁` computes it. -/
theorem bit1665 : ∀ n < 256, ∀ i < 8,
    (1665#32 &&& ~~~(if (BitVec.ofNat 8 n ++ BitVec.ofNat 8 n ++ BitVec.ofNat 8 n ++ BitVec.ofNat 8 n) &&&
      BitVec.ofNat 32 (2 ^ i) = 0#32 then BitVec.allOnes 32 else 0#32)).toNat = 1665 * (n / 2 ^ i % 2) := by
  decide +kernel

theorem vword_not' (x : BitVec 128) (e : Nat) (he : e < 4) : vword (~~~x) e = ~~~vword x e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vword, hi, show 32 * e + i < 128 by omega_arith]

/-- A word of the result of `dd1Byte`. -/
theorem lane1665 {x m c z : BitVec 128} {e : Nat} (he : e < 4) {i : Nat} (hi : i < 8) {b : BitVec 8}
    (hx : vword x e = b ++ b ++ b ++ b) (hm : vword m e = BitVec.ofNat 32 (2 ^ i)) (hc : vword c e = 1665#32)
    (hz : vword z e = 0#32) :
    (vword (c &&& ~~~(VArr.s4.map2 (fun w x y => if x = y then BitVec.allOnes w else 0) (x &&& m) z)) e).toNat =
      1665 * (b.toNat / 2 ^ i % 2) := by
  rw [vword_and', vword_not' _ _ he, vword_map2 _ _ _ he, vword_and', hx, hm, hc, hz]
  have h := bit1665 b.toNat b.isLt i hi
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  exact h

/-- The state through the bytes of `dd1Body`. -/
structure BInv (s : State) (p : Addr) (m₀ : Mem) (t : Nat) (Gf old : Nat → BitVec 32) (j : Nat)
    (u : State) : Prop where
  gpr : u.gpr = s.gpr
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  sp : u.sp = s.sp
  v : ∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → u.v r = s.v r
  out : CoeffsUpTo u.mem p (t + 8 * j) Gf old
  frame : Frame [polyRegion p] m₀ u.mem

theorem dd1Byte_ok {s : State} {p : Addr} {m₀ : Mem} {t : Nat} {Gf old : Nat → BitVec 32}
    (hw : ∀ i, i + 4 ≤ 256 → InRegions s.wr (coeffAddr p i) 16)
    (h3 : ∀ j, s.gpr .x3 + BitVec.ofNat 64 (32 * j) = coeffAddr p (t + 8 * j)) (ht : t + 128 ≤ 256)
    (h18 : ∀ e < 4, vword (s.v .v18) e = BitVec.ofNat 32 (2 ^ e))
    (h19 : ∀ e < 4, vword (s.v .v19) e = BitVec.ofNat 32 (2 ^ (4 + e)))
    (h20 : ∀ e < 4, vword (s.v .v20) e = 1665#32) (h21 : s.v .v21 = 0)
    (hG : ∀ j < 16, ∀ e < 8, Gf (t + 8 * j + e) =
      BitVec.ofNat 32 (1665 * ((vbyte (s.v .v22) j).toNat / 2 ^ e % 2)))
    {j : Nat} (hj : j < 16) {u : State} (hu : BInv s p m₀ t Gf old j u) :
    WP isa (.block (dd1Byte j)) u (BInv s p m₀ t Gf old (j + 1)) := by
  unfold dd1Byte
  refine wp_vop (by simp only [VOp.eval, VArr.esize, show j < 128 / 8 from hj, ite_true]; rfl) fun a1 h1 =>
    wp_vop rfl fun a2 h2 => wp_vop rfl fun a3 h3' => wp_vop rfl fun a4 h4 => wp_vop rfl fun a5 h5 =>
    wp_vop rfl fun a6 h6 => wp_vop rfl fun a7 h7 => ?_
  have uv (r : VReg) (h0 : r ≠ .v0) (h1' : r ≠ .v1) (h2' : r ≠ .v2) : a7.v r = s.v r := by
    rw [h7.get r h2', h6.get r h1', h5.get r h2', h4.get r h1', h3'.get r h2', h2.get r h1', h1.get r h0,
      hu.v r h0 h1' h2']
  have hb : ∀ e < 4, vword (a1.v .v0) e = vbyte (s.v .v22) j ++ vbyte (s.v .v22) j ++ vbyte (s.v .v22) j ++
      vbyte (s.v .v22) j := fun e he => by
    rw [h1.v, vword_bytes', Rc4.AArch64.vbyte_map2 _ _ _ (by omega_arith), Rc4.AArch64.vbyte_map2 _ _ _ (by omega_arith),
      Rc4.AArch64.vbyte_map2 _ _ _ (by omega_arith), Rc4.AArch64.vbyte_map2 _ _ _ (by omega_arith),
      hu.v .v22 (by decide) (by decide) (by decide)]
    rfl
  have z0 : ∀ e < 4, vword (a3.v .v21) e = 0#32 := fun e _ => by
    rw [h3'.get .v21 (by decide), h2.get .v21 (by decide), h1.get .v21 (by decide),
      hu.v .v21 (by decide) (by decide) (by decide), h21]; simp [vword]
  have w1 : ∀ e < 4, (vword (a7.v .v1) e).toNat = 1665 * ((vbyte (s.v .v22) j).toNat / 2 ^ e % 2) :=
    fun e he => by
      rw [h7.get .v1 (by decide), h6.v, h5.get .v1 (by decide), h5.get .v20 (by decide), h4.v,
        h4.get .v20 (by decide), h3'.get .v1 (by decide), h3'.get .v20 (by decide), h2.v,
        h2.get .v20 (by decide), h1.get .v18 (by decide), h1.get .v20 (by decide)]
      dsimp only
      exact lane1665 he (by omega_arith) (hb e he) (by rw [hu.v .v18 (by decide) (by decide) (by decide)]; exact h18 e he)
        (by rw [hu.v .v20 (by decide) (by decide) (by decide)]; exact h20 e he) (z0 e he)
  have w2 : ∀ e < 4, (vword (a7.v .v2) e).toNat = 1665 * ((vbyte (s.v .v22) j).toNat / 2 ^ (4 + e) % 2) :=
    fun e he => by
      rw [h7.v, h6.get .v2 (by decide), h6.get .v20 (by decide), h5.v, h5.get .v20 (by decide),
        h4.get .v2 (by decide), h4.get .v21 (by decide), h4.get .v20 (by decide), h3'.v,
        h3'.get .v20 (by decide), h2.get .v0 (by decide), h2.get .v19 (by decide), h2.get .v20 (by decide),
        h1.get .v19 (by decide), h1.get .v20 (by decide)]
      dsimp only
      exact lane1665 he (by omega_arith) (hb e he)
        (by rw [hu.v .v19 (by decide) (by decide) (by decide)]; exact h19 e he)
        (by rw [hu.v .v20 (by decide) (by decide) (by decide)]; exact h20 e he) (z0 e he)
  have g7 : a7.gpr = s.gpr := by
    rw [h7.gpr, h6.gpr, h5.gpr, h4.gpr, h3'.gpr, h2.gpr, h1.gpr, hu.gpr]
  have m7 : a7.mem = u.mem := by
    rw [h7.mem, h6.mem, h5.mem, h4.mem, h3'.mem, h2.mem, h1.mem]
  have wr7 : a7.wr = s.wr := by
    rw [h7.wr, h6.wr, h5.wr, h4.wr, h3'.wr, h2.wr, h1.wr, hu.wr]
  refine wp_strq2 (o := 32 * j) (by rw [wr7]; exact hw) (by rw [g7]; exact h3 j) ⟨by omega_arith, by omega_arith⟩
    (by omega_arith) (by rw [m7]; exact hu.out) (by rw [m7]; exact hu.frame)
    (vword_G w1 fun e he => by rw [hG j hj e (by omega_arith)])
    (vword_G w2 fun e he => by rw [Nat.add_assoc, hG j hj (4 + e) (by omega_arith)])
    fun s' st o f => wp_nil ⟨by rw [st.gpr, g7], by rw [st.rd, h7.rd, h6.rd, h5.rd, h4.rd, h3'.rd, h2.rd,
      h1.rd, hu.rd], by rw [st.wr, wr7], by rw [st.sp, h7.sp, h6.sp, h5.sp, h4.sp, h3'.sp, h2.sp, h1.sp, hu.sp],
      fun r a b c => by rw [st.v, uv r a b c], by rw [show t + 8 * (j + 1) = t + 8 * j + 8 by omega_arith]; exact o, f⟩

end VG.Proof.MlKem.AArch64.DD

namespace VG.Proof.MlKem.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Spec.MlKem

/-- The constants of `dd1Body` besides those of `decV`. -/
abbrev K1 (s : State) : Prop := (∀ e < 4, vword (s.v .v18) e = BitVec.ofNat 32 (2 ^ e)) ∧
  (∀ e < 4, vword (s.v .v19) e = BitVec.ofNat 32 (2 ^ (4 + e))) ∧ (∀ e < 4, vword (s.v .v20) e = 1665#32) ∧
  s.v .v21 = 0

theorem K1.of_v {s t : State} (h : K1 s) (hv : ∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v22 → t.v r = s.v r) :
    K1 t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hv .v18 (by decide) (by decide) (by decide) (by decide)]; exact h.1
  · rw [hv .v19 (by decide) (by decide) (by decide) (by decide)]; exact h.2.1
  · rw [hv .v20 (by decide) (by decide) (by decide) (by decide)]; exact h.2.2.1
  · rw [hv .v21 (by decide) (by decide) (by decide) (by decide)]; exact h.2.2.2

/-- Coefficient `8 g + e` of the output for `d = 1`. -/
theorem G1 (s₀ : State) {g e : Nat} (hg : g < 32) (he : e < 8) :
    DD.G width1 s₀ (8 * g + e) = BitVec.ofNat 32 (1665 * (byte width1 s₀ g / 2 ^ e % 2)) := by
  rw [show 8 * g + e = width1.c * g + e from rfl, G_eq width1_ok s₀ (by simp [width1]; omega_arith) he,
    show width1.nb = 1 from rfl, num1 rfl]
  simp only [show width1.d = 1 from rfl, Nat.one_mul, Nat.sub_self, Nat.pow_zero, Nat.pow_one]
  have : byte width1 s₀ g / 2 ^ e % 2 < 2 := Nat.mod_lt _ (by decide)
  congr 1
  show (3329 * _ + 1) / 2 = _
  omega_arith

theorem step1 {s₀ : State} (hp : Pre width1 s₀) {k : Nat} (hk : k < 2) {s : State}
    (h : DInv width1 16 K1 s₀ k s) :
    WP isa (.block dd1Body) s fun t =>
      DInv width1 16 K1 s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 2) := by
  have e0 : s.gpr .x0 + BitVec.ofNat 64 0 = bP s₀ + BitVec.ofNat 64 (16 * k) := by
    rw [ptr_zero, h.x0]; rfl
  unfold dd1Body
  simp only [List.cons_append]
  refine wp_ldrq (by decide) e0 (h.in16 width1_ok hp (by simp [width1]; omega_arith)) fun s1 h1 => ?_
  have b1 : ∀ j < 16, (vbyte (s1.v .v22) j).toNat = byte width1 s₀ (16 * k + j) := fun j hj => by
    rw [h1.v]; exact vbyte_input width1_ok hp h.frame (by simp [width1]; omega_arith) hj
  have x3 : ∀ j, s1.gpr .x3 + BitVec.ofNat 64 (32 * j) = coeffAddr (fP s₀) (128 * k + 8 * j) := fun j => by
    rw [h1.gpr, h.x3, show width1.c * 16 * k = 128 * k by simp [width1],
      show 32 * j = 4 * (8 * j) by omega_arith, coeffAddr_off]
  have K : K1 s1 := ⟨by rw [h1.get .v18 (by decide)]; exact h.K.1, by rw [h1.get .v19 (by decide)]; exact h.K.2.1,
    by rw [h1.get .v20 (by decide)]; exact h.K.2.2.1, by rw [h1.get .v21 (by decide)]; exact h.K.2.2.2⟩
  have out0 : CoeffsUpTo s1.mem (fP s₀) (128 * k + 8 * 0) (DD.G width1 s₀) (old s₀) := by
    rw [h1.mem, Nat.mul_zero, Nat.add_zero, show 128 * k = width1.c * 16 * k by simp [width1]]
    exact h.out
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (BInv s1 (fP s₀) s₀.mem (128 * k) (DD.G width1 s₀) (old s₀))
    (fun j u hj hu => dd1Byte_ok (fun i hi => by rw [h1.wr]; exact h.out16 hp hi) x3 (by omega_arith) K.1 K.2.1
      K.2.2.1 K.2.2.2 (fun j hj e he => by
        rw [b1 j hj, show 128 * k + 8 * j + e = 8 * (16 * k + j) + e by omega_arith, G1 s₀ (by omega_arith) he]) hj hu)
    16 (Nat.le_refl _) s1 ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl, out0, by rw [h1.mem]; exact h.frame⟩)
    fun s2 b2 => ?_
  have k4 : k < 256 / (width1.c * 16) := by simp [width1]; omega_arith
  refine WP.mono (dtail_ok (w := width1) (Ng := 16) (s₀ := s₀) k4 (by rw [b2.gpr, h1.gpr, h.x0])
    (by rw [b2.gpr, h1.gpr, h.x3]) (by rw [b2.gpr, h1.gpr, h.x11]) (by decide) (by decide))
    fun u ⟨o, uv, u0, u3, u11, uc⟩ => ?_
  have hv : ∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v22 → u.v r = s.v r := fun r a b c d => by
    rw [uv, b2.v r a b c, h1.get r d]
  refine ⟨⟨by rw [o.rd, b2.rd, h1.rd, h.rd], by rw [o.wr, b2.wr, h1.wr, h.wr],
    by rw [o.sp, b2.sp, h1.sp, h.sp], u0, u3, u11, ?_, h.K.of_v hv, ?_, ?_⟩,
    by rw [show 256 / (width1.c * 16) = 2 from rfl] at uc; exact uc⟩
  · exact ⟨by rw [hv .v16 (by decide) (by decide) (by decide) (by decide)]; exact h.cs.q,
      by rw [hv .v17 (by decide) (by decide) (by decide) (by decide)]; exact h.cs.h⟩
  · rw [o.mem, show width1.c * 16 * (k + 1) = 128 * k + 8 * 16 by simp [width1]; omega_arith]
    exact b2.out
  · rw [o.mem]; exact b2.frame

end VG.Proof.MlKem.AArch64.DD
