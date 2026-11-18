module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd10Step
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd10Step
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
meta import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.Encode

/-! ### `MlKem.AArch64.CodecV.Dd4Step`, which only this module used -/

section

/-!
# ML-KEM on AArch64: an iteration of `dd4Body`

Bytes `16 k … 16 k + 15` of the input to coefficients `32 k … 32 k + 31` of the output.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Spec.MlKem

/-- The constants of `dd4Body` besides those of `decV`. -/
abbrev K4 (s : State) : Prop := (∀ j < 16, (vbyte (s.v .v18) j).toNat = 15) ∧ s.v .v19 = 0

/-- Coefficient `32 k + m` of the output for `d = 4`. -/
theorem G4 (s₀ : State) {k m : Nat} (hk : k < 8) (hm : m < 32) :
    DD.G width4 s₀ (32 * k + m) =
      BitVec.ofNat 32 (df 4 (nib (fun j => byte width4 s₀ (16 * k + j)) m)) := by
  rw [show 32 * k + m = width4.c * (16 * k + m / 2) + m % 2 by simp [width4]; omega_using [],
    G_eq width4_ok s₀ (by simp [width4]; omega_using [hk, hm]) (by simp [width4]; omega_using []), show width4.nb = 1 from rfl, num1 rfl]
  simp only [show width4.d = 4 from rfl, df, nib, show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_mul]

theorem step4 {s₀ : State} (hp : Pre width4 s₀) {k : Nat} (hk : k < 8) {s : State}
    (h : DInv width4 16 K4 s₀ k s) :
    WP isa (.block dd4Body) s fun t =>
      DInv width4 16 K4 s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 8) := by
  have e0 : s.gpr .x0 + BitVec.ofNat 64 0 = bP s₀ + BitVec.ofNat 64 (16 * k) := by
    rw [ptr_zero, h.x0]; rfl
  unfold dd4Body
  simp only [List.cons_append]
  refine wp_ldrq (by decide) e0 (h.in16 width4_ok hp (by simp [width4]; omega_using [hk])) fun s1 h1 => ?_
  let B : Nat → Nat := fun j => byte width4 s₀ (16 * k + j)
  rw [WP.block_append_iff]
  refine WP.mono (dd4Math_ok (h.cs.chg h1.chg) (by rw [h1.get .v18 (by decide)]; exact h.K.1)
    (by rw [h1.get .v19 (by decide)]; exact h.K.2) (B := B)
    (fun j hj => by rw [h1.v]; exact vbyte_input width4_ok hp h.frame (by simp [width4]; omega_using [hk]) hj)
    (fun j _ => byte_lt _)) fun s2 ⟨c2, r0, r1, r2, r3, r6, r7, r20, r21⟩ => ?_
  have g2 : s2.gpr = s.gpr := by rw [c2.gpr, h1.gpr]
  have hw2 : ∀ i, i + 4 ≤ 256 → InRegions s2.wr (coeffAddr (fP s₀) i) 16 := fun i hi => by
    rw [c2.wr, h1.wr]; exact h.out16 hp hi
  have a3 : ∀ i, s2.gpr .x3 + BitVec.ofNat 64 (16 * i) = coeffAddr (fP s₀) (32 * k + 4 * i) := fun i => by
    rw [g2, h.x3, show width4.c * 16 * k = 32 * k from by simp [width4], show 16 * i = 4 * (4 * i) by omega_using [],
      coeffAddr_off]
  have out2 : CoeffsUpTo s2.mem (fP s₀) (32 * k) (DD.G width4 s₀) (old s₀) := by
    rw [c2.mem, h1.mem, show 32 * k = width4.c * 16 * k by simp [width4]]; exact h.out
  have f2 : Frame [polyRegion (fP s₀)] s₀.mem s2.mem := by rw [c2.mem, h1.mem]; exact h.frame
  have v (r : VReg) (o : Nat) (hr : Lanes (s2.v r) fun e => df 4 (nib B (o + e))) (ho : o + 4 ≤ 32) :
      ∀ e < 4, vword (s2.v r) e = DD.G width4 s₀ (32 * k + o + e) :=
    vword_G hr fun e he => by rw [Nat.add_assoc, G4 s₀ hk (by omega_using [ho, he])]
  refine wp_strq2 (o := 0) hw2 (a3 0) (by decide) (by omega_using [hk]) out2 f2 (v _ 0 (r0.congr fun _ _ => by
    rw [Nat.zero_add]) (by decide)) (v _ 4 r1 (by decide)) fun s3 t3 o3 f3 => ?_
  refine wp_strq2 (o := 32) (by rw [t3.wr]; exact hw2) (by rw [t3.gpr]; exact a3 2) (by decide) (by omega_using [hk]) o3 f3
    (by rw [t3.v]; exact v _ 8 r2 (by decide)) (by rw [t3.v]; exact v _ 12 r3 (by decide))
    fun s4 t4 o4 f4 => ?_
  refine wp_strq2 (o := 64) (by rw [t4.wr, t3.wr]; exact hw2) (by rw [t4.gpr, t3.gpr]; exact a3 4) (by decide)
    (by omega_using [hk]) o4 f4 (by rw [t4.v, t3.v]; exact v _ 16 r6 (by decide))
    (by rw [t4.v, t3.v]; exact v _ 20 r7 (by decide)) fun s5 t5 o5 f5 => ?_
  refine wp_strq2 (o := 96) (by rw [t5.wr, t4.wr, t3.wr]; exact hw2) (by rw [t5.gpr, t4.gpr, t3.gpr]; exact a3 6)
    (by decide) (by omega_using [hk]) o5 f5 (by rw [t5.v, t4.v, t3.v]; exact v _ 24 r20 (by decide))
    (by rw [t5.v, t4.v, t3.v]; exact v _ 28 r21 (by decide)) fun s6 t6 o6 f6 => ?_
  have t := ((t3.trans t4).trans t5).trans t6
  have k4 : k < 256 / (width4.c * 16) := by simp [width4]; omega_using [hk]
  refine WP.mono (dtail_ok (w := width4) (Ng := 16) (s₀ := s₀) k4 (by rw [t.gpr, g2, h.x0])
    (by rw [t.gpr, g2, h.x3]) (by rw [t.gpr, g2, h.x11]) (by decide) (by decide))
    fun u ⟨o, uv, u0, u3, u11, uc⟩ => ?_
  have hv : u.v = s2.v := by rw [uv, t.v]
  refine ⟨⟨by rw [o.rd, t.rd, c2.rd, h1.rd, h.rd], by rw [o.wr, t.wr, c2.wr, h1.wr, h.wr],
    by rw [o.sp, t.sp, c2.sp, h1.sp, h.sp], u0, u3, u11, ?_, ?_, ?_, ?_⟩,
    by rw [show 256 / (width4.c * 16) = 8 from rfl] at uc; exact uc⟩
  · have := (h.cs.chg h1.chg).chg c2
    exact ⟨by rw [hv]; exact this.q, by rw [hv]; exact this.h⟩
  · exact ⟨fun j hj => by rw [hv, c2.get .v18 (by decide), h1.get .v18 (by decide)]; exact h.K.1 j hj,
      by rw [hv, c2.get .v19 (by decide), h1.get .v19 (by decide)]; exact h.K.2⟩
  · rw [o.mem, show width4.c * 16 * (k + 1) = 32 * k + 8 + 8 + 8 + 8 by simp [width4]; omega_using []]; exact o6
  · rw [o.mem]; exact f6

end VG.Proof.MlKem.AArch64.DD

end

end

/-! ### `MlKem.AArch64.CodecV.Dd1`, which only this module used -/

section

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

end

end

/-!
# ML-KEM on AArch64: `vg_mlkem_decode_decompress`

The contract, the dispatch on `len` to the loop of each width (`loop1_ok`, `loop4_ok`,
`loop10_ok`, from `Proof/MlKem/AArch64/CodecV/`), and constant time: every address and branch
depends only on the pointers and `len`.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `vg_mlkem_decode_decompress(b = x0, len = x1, d = w2,
f = x3)`: if `d` is 1, 4 or 10 and `len = 32 d`, writes
`Decompress_d(ByteDecode_d(B))` of the `len` bytes `B` at `b` to `f`, reduced.
The code may read `b` and write `f`, which do not overlap. -/
def decodeDecompressAArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩] ∧ s.wr = [⟨s.gpr .x3, 1024⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ ⟨s.gpr .x3, 1024⟩ ∧
    ((s.gpr .x2).setWidth 32).toNat ∈ compressWidths ∧
    (s.gpr .x1).toNat = 32 * ((s.gpr .x2).setWidth 32).toNat
  post s s' := PolyIs s'.mem (s.gpr .x3)
    (decodeDecompress ((s.gpr .x2).setWidth 32).toNat (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Proof.MlKem.AArch64.CE (GFr wp_dupW wp_bytesVec wp_movImm9)
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- One width, from the state after the dispatch. -/
theorem width_ok {w : Width} {c : Prog isa} {s₀ s : State} (hs : decodeDecompressAArch64.pre s₀)
    (hd : ((s₀.gpr .x2).setWidth 32).toNat = w.d) (hk : Keep [.x9] s₀ s) (hm : s.mem = s₀.mem)
    (hl : ∀ s, Pre w s → WP isa c s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (fP s) (decodeDecompress w.d (B w s))) :
    WP isa c s fun s' => s'.sp = s₀.sp ∧ decodeDecompressAArch64.post s₀ s' := by
  obtain ⟨h1, h2, h3, -, hlen⟩ := hs
  rw [hd] at hlen
  have e0 : bP s = s₀.gpr .x0 := hk.get .x0
  have e3 : fP s = s₀.gpr .x3 := hk.get .x3
  have hp : Pre w s :=
    ⟨by rw [hk.rd, h1, bR, e0, hlen], by rw [hk.wr, h2, e3], by rw [e3, bR, e0, ← hlen]; exact h3⟩
  refine WP.mono (hl s hp) fun s' ⟨_, _, sp, e⟩ => ⟨by rw [sp, hk.sp], ?_⟩
  show PolyIs s'.mem (s₀.gpr .x3) (decodeDecompress ((s₀.gpr .x2).setWidth 32).toNat
    (bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat))
  rw [hlen, hd, ← e3, ← e0, ← hm]
  exact e

theorem dd1idx18 : setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (([1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 8, 0, 0, 0] : List Nat).getD (0 + i) 255) * 2 ^ (8 * i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (([1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 8, 0, 0, 0] : List Nat).getD (0 + i) 255) * 2 ^ (8 * i)) 0)))
    64 1 (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (([1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 8, 0, 0, 0] : List Nat).getD (8 + i) 255) * 2 ^ (8 * i)) 0)) =
      ofVWords 1#32 2#32 4#32 8#32 := by decide +kernel

theorem dd1idx19 : setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (([16, 0, 0, 0, 32, 0, 0, 0, 64, 0, 0, 0, 128, 0, 0, 0] : List Nat).getD (0 + i) 255) * 2 ^ (8 * i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (([16, 0, 0, 0, 32, 0, 0, 0, 64, 0, 0, 0, 128, 0, 0, 0] : List Nat).getD (0 + i) 255) * 2 ^ (8 * i)) 0)))
    64 1 (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (([16, 0, 0, 0, 32, 0, 0, 0, 64, 0, 0, 0, 128, 0, 0, 0] : List Nat).getD (8 + i) 255) * 2 ^ (8 * i)) 0)) =
      ofVWords 16#32 32#32 64#32 128#32 := by decide +kernel

theorem dd10idx : setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (dd10Idx.getD (0 + i) 255) * 2 ^ (8 * i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (dd10Idx.getD (0 + i) 255) * 2 ^ (8 * i)) 0))) 64 1
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (dd10Idx.getD (8 + i) 255) * 2 ^ (8 * i)) 0)) =
      idxVec dd10Idx := by decide +kernel

theorem dd10idxHi : setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (dd10IdxHi.getD (0 + i) 255) * 2 ^ (8 * i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (dd10IdxHi.getD (0 + i) 255) * 2 ^ (8 * i)) 0))) 64 1
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (dd10IdxHi.getD (8 + i) 255) * 2 ^ (8 * i)) 0)) =
      idxVec dd10IdxHi := by decide +kernel

theorem vword_ofVWords4 (a b c d : BitVec 32) : ∀ e < 4, vword (ofVWords a b c d) e = [a, b, c, d][e]! := by
  intro e he
  rw [vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega_using [he]) with rfl | rfl | rfl | rfl <;> rfl

theorem loop1_ok {s₀ : State} (hp : Pre width1 s₀) :
    WP isa (ddLoop 1 2 (bytesVec .v18 [1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 8, 0, 0, 0] ++
      bytesVec .v19 [16, 0, 0, 0, 32, 0, 0, 0, 64, 0, 0, 0, 128, 0, 0, 0] ++ dupW .v20 1665 ++
      ([.vop (.movi0 .v21)] : List Instr)) dd1Body) s₀ fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
        PolyIs s'.mem (fP s₀) (decodeDecompress width1.d (B width1 s₀)) :=
  dloop_ok width1_ok (Ng := 16) (K := K1) rfl (by decide) rfl
    (fun s => by
      simp only [List.append_assoc]
      exact wp_bytesVec fun s1 g1 v1 e1 => wp_bytesVec fun s2 g2 v2 e2 => wp_dupW (by decide) fun s3 g3 v3 e3 =>
        wp_vop rfl fun s4 h4 => wp_nil ⟨(g1.trans g2).trans (g3.trans (.of_upd h4)),
          fun r a b c d _ _ => by rw [h4.get r d, v3 r c, v2 r b, v1 r a],
          ⟨by rw [h4.get .v18 (by decide), v3 .v18 (by decide), v2 .v18 (by decide), e1, dd1idx18]
              exact fun e he => by rw [vword_ofVWords4 _ _ _ _ e he]
                                   rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega_using [he]) with rfl | rfl | rfl | rfl <;> rfl,
           by rw [h4.get .v19 (by decide), v3 .v19 (by decide), e2, dd1idx19]
              exact fun e he => by rw [vword_ofVWords4 _ _ _ _ e he]
                                   rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega_using [he]) with rfl | rfl | rfl | rfl <;> rfl,
           fun e he => by
             rw [h4.get .v20 (by decide)]
             apply BitVec.eq_of_toNat_eq; rw [e3 e he]; rfl,
           by rw [h4.v]⟩⟩)
    (fun _ _ hv hk => by rw [K1, hv]; exact hk)
    fun _ hk _ h => step1 hp hk h

theorem loop4_ok {s₀ : State} (hp : Pre width4 s₀) :
    WP isa (ddLoop 4 8 (movImm .x9 15 ++ ([.vop (.dup .b16 .v18 .x9), .vop (.movi0 .v19)] : List Instr)) dd4Body) s₀
      fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
        PolyIs s'.mem (fP s₀) (decodeDecompress width4.d (B width4 s₀)) :=
  dloop_ok width4_ok (Ng := 16) (K := K4) rfl (by decide) rfl
    (fun s => wp_movImm9 fun s1 g1 v1 e1 => wp_vop rfl fun s2 h2 => wp_vop rfl fun s3 h3 => wp_nil
      ⟨g1.trans ((GFr.of_upd h2).trans (.of_upd h3)), fun r a b _ _ _ _ => by rw [h3.get r b, h2.get r a, v1],
        fun j hj => by
          rw [h3.get .v18 (by decide), h2.v, vbyte_ofVBytes _ hj, e1]; rfl,
        by rw [h3.v]⟩)
    (fun _ _ hv hk => by rw [K4, hv]; exact hk)
    fun _ hk _ h => step4 hp hk h

theorem loop10_ok {s₀ : State} (hp : Pre width10 s₀) :
    WP isa (ddLoop 10 16 (dupW .v18 (2 ^ 20 - 1) ++ dupW .v19 1023 ++ bytesVec .v20 dd10Idx ++
      bytesVec .v21 dd10IdxHi) dd10Body) s₀ fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
        PolyIs s'.mem (fP s₀) (decodeDecompress width10.d (B width10 s₀)) :=
  dloop_ok width10_ok (Ng := 4) (K := K10) rfl (by decide) rfl
    (fun s => by
      simp only [List.append_assoc]
      rw [← List.append_nil (bytesVec .v21 _)]
      exact wp_dupW (by decide) fun s1 g1 v1 l1 => wp_dupW (by decide) fun s2 g2 v2 l2 =>
        wp_bytesVec fun s3 g3 v3 e3 => wp_bytesVec fun s4 g4 v4 e4 => wp_nil
          ⟨((g1.trans g2).trans g3).trans g4, fun r a b c d _ _ => by rw [v4 r d, v3 r c, v2 r b, v1 r a],
            by rw [v4 .v18 (by decide), v3 .v18 (by decide), v2 .v18 (by decide)]; exact l1,
            by rw [v4 .v19 (by decide), v3 .v19 (by decide)]; exact l2,
            by rw [v4 .v20 (by decide), e3, dd10idx], by rw [e4, dd10idxHi]⟩)
    (fun _ _ hv hk => by rw [K10, hv]; exact hk)
    fun _ hk _ h => step10 hp hk h

theorem correct (s : State) (hs : decodeDecompressAArch64.pre s) :
    ∃ t s', Exec isa decodeDecompress s t s' ∧ abiPreserved s s' ∧
      decodeDecompressAArch64.post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, hd, hlen⟩ := hs'
  suffices h : WP isa decodeDecompress s fun s' => s'.sp = s.sp ∧ decodeDecompressAArch64.post s s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hpost⟩
  refine WP.seq ?_
  refine wp_subImm (by decide) fun s₂ h₂ e₂ => wp_nil ?_
  have k₂ : Keep [.x9] s s₂ := h₂.keep
  have m₂ : s₂.mem = s.mem := h₂.mem
  have z₂ : isa.eval (.zero .x .x9) s₂ = some (decide ((s.gpr .x1).toNat = 32)) := by
    rw [eval_zero, eq_zero_iff, e₂, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    congr 1
    apply decide_eq_decide.mpr
    rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega_using []
  refine WP.ite _ z₂ (fun hb => ?_) (fun hb => ?_)
  · have e : ((s.gpr .x2).setWidth 32).toNat = 1 := by simp at hb; omega_using [hlen, hb]
    exact width_ok (w := width1) hs e k₂ m₂ fun _ hp => loop1_ok hp
  refine WP.seq (wp_subImm (by decide) fun s₃ h₃ e₃ => wp_nil ?_)
  have k₃ : Keep [.x9] s s₃ := (k₂.trans h₃.keep).mono
  have z₃ : isa.eval (.zero .x .x9) s₃ = some (decide ((s.gpr .x1).toNat = 128)) := by
    rw [eval_zero, eq_zero_iff, e₃, k₂.get .x1, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    congr 1
    apply decide_eq_decide.mpr
    rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega_using []
  refine WP.ite _ z₃ (fun hb' => ?_) (fun hb' => ?_)
  · have e : ((s.gpr .x2).setWidth 32).toNat = 4 := by simp at hb'; omega_using [hlen, hb']
    exact width_ok (w := width4) hs e k₃ (by rw [h₃.mem, m₂]) fun _ hp => loop4_ok hp
  · have e : ((s.gpr .x2).setWidth 32).toNat = 10 := by
      simp at hb hb'
      rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega
    exact width_ok (w := width10) hs e k₃ (by rw [h₃.mem, m₂]) fun _ hp => loop10_ok hp

end VG.Proof.MlKem.AArch64.DD
