module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Gs
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Last
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ML-KEM's 16-bit inverse NTT on AArch64: lanes by index

As `Idx.lean` for the inverse: lane `e` of a register is coefficient
`base + o[e]` after `j` layers of `NTT⁻¹` (`IRepI`), less than `B` in
absolute value (sums grow, products are less than `q`). `irepI_gs`: an
inverse butterfly advances a layer when the offsets are the layer's pairs
and the zetas its own (`okGs`); `firstTwo_ok`: the first two layers of 16
coefficients, around their transposes (`okFirst`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

/-- Lane `e` of `x` is coefficient `base + o[e]` of `P` after `j` layers of `NTT⁻¹`, less than
`B` in absolute value. -/
def IRepI (P : Poly) (j base : Nat) (o : List Nat) (B : Nat) (x : BitVec 128) : Prop :=
  Rep x (fun e => (nttInvL j P)[base + o.getD e 0]!) B

theorem IRepI.mono {P : Poly} {j base B B' : Nat} {o : List Nat} {x : BitVec 128}
    (h : IRepI P j base o B x) (hB : B ≤ B') : IRepI P j base o B' x := Rep.mono h hB

theorem irepI_perm {P : Poly} {j base B : Nat} {ox oy o : List Nat} {r x y : BitVec 128}
    {c : Nat → Bool} {i₁ i₂ : Nat → Nat} (hs : Src r x y c i₁ i₂)
    (hi : ∀ e < 8, (if c e then i₁ e else i₂ e) < 8)
    (hx : IRepI P j base ox B x) (hy : IRepI P j base oy B y) (ho : permO ox oy c i₁ i₂ o = true) :
    IRepI P j base o B r := fun e he => by
  simp only [permO, List.all_eq_true, List.mem_range, beq_iff_eq] at ho
  dsimp only
  rw [hs e he, ho e he]
  have hi' := hi e he
  by_cases h : c e
  · simp only [h, ite_true] at hi' ⊢; exact hx _ hi'
  · simp only [h, ite_false, Bool.false_eq_true] at hi' ⊢; exact hy _ hi'

/-- The lanes `ox`, `oy` are the pairs of inverse butterflies of layer `j + 1`
(`len = 2 <<< j`) in a block of 32 coefficients, with zetas `zeta (K₀ + kz[e])`, `K₀` the
smallest zeta of the block. -/
def okGs (j : Nat) (ox oy kz : List Nat) : Bool :=
  let len := 2 <<< j
  j < 7 && 32 % (2 * len) == 0 && (List.range 8).all fun e =>
    ox.getD e 0 < 32 && oy.getD e 0 < 32 && decide (ox.getD e 0 % (2 * len) < len) &&
      oy.getD e 0 == ox.getD e 0 + len && kz.getD e 0 + ox.getD e 0 / (2 * len) + 1 == 32 / (2 * len)

private theorem mod_div_base' {d base o : Nat} (hd : 0 < d) (h : base % d = 0) :
    (base + o) % d = o % d ∧ (base + o) / d = base / d + o / d := by
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  exact ⟨by rw [Nat.mul_add_mod], by rw [Nat.mul_add_div hd, Nat.mul_div_cancel_left _ hd]⟩

private theorem inv_len : ∀ j < 7, 0 < 2 <<< j ∧ 256 / (2 <<< j) ≤ 128 := by decide

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem irepI_gs {x y z t : VReg} (hxy : x ≠ y := by decide) (hx17 : x ≠ .v17 := by decide)
    (hy17 : y ≠ .v17 := by decide) (hzx : z ≠ x := by decide) (hz17 : z ≠ .v17 := by decide)
    (htx : t ≠ x := by decide) (hty : t ≠ y := by decide) (ht17 : t ≠ .v17 := by decide)
    (hqx : VReg.v31 ≠ x := by decide) (hqy : VReg.v31 ≠ y := by decide)
    {P : Poly} {j base K₀ Bx By : Nat} {ox oy kz : List Nat} (hok : okGs j ox oy kz = true)
    (hb : base % 32 = 0) (hb' : base + 32 ≤ 256)
    (hK : K₀ + 32 / (2 * (2 <<< j)) = 256 / (2 <<< j) - base / (2 * (2 <<< j)))
    (hx : IRepI P j base ox Bx (s.v x)) (hy : IRepI P j base oy By (s.v y))
    (hz : ZRep (s.v z) K₀ kz) (ht : TRep (s.v t) K₀ kz) (hq : Cst (s.v .v31) fun _ => 3329)
    (hB : Bx + By ≤ 32768)
    (k : ∀ s', VChg [.v17, x, y, .v17, y] s s' → IRepI P (j + 1) base ox (Bx + By) (s'.v x) →
      IRepI P (j + 1) base oy 3329 (s'.v y) → WP isa (.block rest) s' Q) :
    WP isa (.block (gs x y z t ++ rest)) s Q := by
  simp only [okGs, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, and_assoc] at hok
  obtain ⟨hj, h32, hl⟩ := hok
  obtain ⟨hlen, hA⟩ := inv_len j hj
  generalize hL : 2 <<< j = len at hl h32 hK hlen hA
  have hbd : base % (2 * len) = 0 := by
    obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h32
    obtain ⟨n, hn⟩ := Nat.dvd_of_mod_eq_zero hb
    rw [hn, hm, Nat.mul_assoc, Nat.mul_mod_right]
  have hidx : ∀ e < 8, K₀ + kz.getD e 0 + 1 + (base + ox.getD e 0) / (2 * len) = 256 / len ∧
      K₀ + kz.getD e 0 < 128 := fun e he => by
    obtain ⟨o1, -, -, -, o5⟩ := hl e he
    obtain ⟨-, d1⟩ := mod_div_base' (o := ox.getD e 0) (Nat.mul_pos (by decide) hlen) hbd
    have hD : ox.getD e 0 / (2 * len) < 32 / (2 * len) :=
      Nat.div_lt_div_of_lt_of_dvd (Nat.dvd_of_mod_eq_zero h32) o1
    rw [d1]
    generalize 256 / len = A at hK hA ⊢
    generalize base / (2 * len) = Bq at hK ⊢
    generalize 32 / (2 * len) = C at hK o5 hD
    generalize ox.getD e 0 / (2 * len) = D at o5 hD ⊢
    omega
  refine gs_ok hxy hx17 hy17 hzx hz17 htx hty ht17 hqx hqy hx hy hz ht hq (fun e _ => ?_) hB
    fun s' c' hx' hy' => k s' c' (?_ : Rep _ _ _) (?_ : Rep _ _ _)
  · simp only [Impl.MlKem.AArch64.Ntt16.zeta]
    by_cases h : K₀ + kz.getD e 0 < 128
    · exact zetaTable_lt _ h
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
        rw [zetaTable_eq, zetas_length]; omega)]; decide
  · refine hx'.congr fun e he => ?_
    obtain ⟨o1, o2, o3, o4, o5⟩ := hl e he
    obtain ⟨m1, d1⟩ := mod_div_base' (o := ox.getD e 0) (Nat.mul_pos (by decide) hlen) hbd
    rw [nttInvL_succ_get P hj (by omega), hL, ite_eq_left (by rw [m1]; exact o3), o4, Nat.add_assoc]
  · refine hy'.congr fun e he => ?_
    obtain ⟨o1, o2, o3, o4, o5⟩ := hl e he
    obtain ⟨m1, d1⟩ := mod_div_base' (o := ox.getD e 0) (Nat.mul_pos (by decide) hlen) hbd
    obtain ⟨m2, d2⟩ := mod_div_base' (o := oy.getD e 0) (Nat.mul_pos (by decide) hlen) hbd
    obtain ⟨hi1, hi2⟩ := hidx e he
    have hm : ¬ oy.getD e 0 % (2 * len) < len := by
      rw [o4]
      have : (ox.getD e 0 + len) % (2 * len) = ox.getD e 0 % (2 * len) + len := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show len < 2 * len by omega)]
        have := Nat.mod_lt (ox.getD e 0) (show 0 < 2 * len by omega)
        exact Nat.mod_eq_of_lt (by omega)
      omega
    have hq2 : oy.getD e 0 / (2 * len) = ox.getD e 0 / (2 * len) := by
      rw [o4]
      have h1 := Nat.div_add_mod (ox.getD e 0) (2 * len)
      refine Nat.div_eq_of_lt_le ?_ ?_
      · rw [Nat.mul_comm]; omega
      · rw [Nat.succ_mul, Nat.mul_comm]; omega
    rw [nttInvL_succ_get P hj (by omega), hL, ite_eq_right (by rw [m2]; exact hm), d2, hq2, ← d1,
      show 256 / len - 1 - (base + ox.getD e 0) / (2 * len) = K₀ + kz.getD e 0 by omega,
      ← ofNat_zeta hi2, o4, show base + (ox.getD e 0 + len) - len = base + ox.getD e 0 by omega]

end

end VG.Proof.MlKem.AArch64.Ntt16
