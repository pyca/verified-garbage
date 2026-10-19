module
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Blocks

import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dword
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane

/-!
# ML-KEM on AArch64: `ce10Math`

16 compressed coefficients of ten bits, paired into four groups of 40 bits in doublewords, whose
five low bytes TBL picks.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem

/-- The bytes `xs` (255 past its end). -/
def idxVec (xs : List Nat) : BitVec 128 := ofVBytes fun i => BitVec.ofNat 8 (xs.getD i 255)

theorem toNat_idxVec (xs : List Nat) (hxs : ∀ x ∈ xs, x < 256) {i : Nat} (hi : i < 16) :
    (vbyte (idxVec xs) i).toNat = xs.getD i 255 := by
  rw [idxVec, vbyte_ofVBytes _ hi, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  rw [List.getD_eq_getElem?_getD]
  cases h : xs[i]? with
  | none => decide
  | some x => exact hxs x (List.mem_of_getElem? h)

/-- TBL of two registers, from `n`, at the indices `idx`. -/
theorem vbyte_tbl2 {s : State} {n m d : VReg} {i : Nat} (hi : i < 16) {k : Nat} (hk : (vbyte (s.v m) i).toNat = k)
    (hk' : k < 32) :
    vbyte (ofVBytes fun i => if (vbyte (s.v m) i).toNat < 16 * 2 then tableByte s.v n (vbyte (s.v m) i).toNat
      else if false then vbyte (s.v d) i else 0) i =
      if k < 16 then vbyte (s.v n) k else vbyte (s.v n.succ) (k - 16) := by
  rw [vbyte_ofVBytes _ hi, hk, ite_eq_left hk', tableByte]
  by_cases h : k < 16
  · rw [ite_eq_left h, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]; rfl
  · rw [ite_eq_right h, show k / 16 = 1 by omega, show k % 16 = k - 16 by omega]; rfl

theorem ce10Idx_eq : ∀ j < 16, ce10Idx.getD j 255 = 8 * (j / 5) + j % 5 := by decide
theorem ce10IdxHi_eq : ∀ j < 4, ce10IdxHi.getD j 255 = 25 + j := by decide

/-- A group of 40 bits: four coefficients `Y (4 g) …` of ten bits. -/
abbrev grp10 (Y : Nat → Nat) (g : Nat) : Nat :=
  Y (4 * g) + Y (4 * g + 1) * 2 ^ 10 + (Y (4 * g + 2) + Y (4 * g + 3) * 2 ^ 10) * 2 ^ 20

theorem ce10Math_ok {s : State} (hc : CConsts 10 s) (h20 : s.v .v20 = idxVec ce10Idx)
    (h21 : s.v .v21 = idxVec ce10IdxHi) {X : Nat → Nat} (hX : ∀ i < 16, X i < 3329)
    (l0 : Lanes (s.v .v0) fun i => X i) (l1 : Lanes (s.v .v1) fun i => X (4 + i))
    (l2 : Lanes (s.v .v2) fun i => X (8 + i)) (l3 : Lanes (s.v .v3) fun i => X (12 + i)) :
    WP isa (.block ce10Math) s fun t => VChg [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v19] s t ∧
      (∀ j < 16, (vbyte (t.v .v6) j).toNat = grp10 (fun i => cf 10 (X i)) (j / 5) / 2 ^ (8 * (j % 5)) % 2 ^ 8) ∧
      (∀ j < 4, (vbyte (t.v .v7) j).toNat = grp10 (fun i => cf 10 (X i)) 3 / 2 ^ (8 * (1 + j)) % 2 ^ 8) := by
  have hd : (10 : Nat) ∈ compressWidths := by decide
  unfold ce10Math
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (cmp4_ok hd hc hX l0 l1 l2 l3) fun s1 ⟨c1, m0, m1, m2, m3⟩ => ?_
  let Y : Nat → Nat := fun i => cf 10 (X i)
  have hY : ∀ i, Y i < 2 ^ 10 := fun i => cf_lt 10 _
  let Z : Nat → Nat := fun i => Y (2 * i) + Y (2 * i + 1) * 2 ^ 10
  have hZ : ∀ i, Z i < 2 ^ 20 := fun i => by
    have := hY (2 * i); have := hY (2 * i + 1); simp only [Z]; omega
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 10) (f := Y) (by decide) (by decide) (by decide) (by decide) m0 m1
    fun i _ => hY i) fun s2 ⟨c2, p0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 10) (f := fun i => Y (8 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c2 (by decide) m2)
    ((Lanes.chg c2 (by decide) m3).congr fun i _ => by show Y (12 + i) = Y (8 + (4 + i)); congr 1; omega)
    fun i _ => hY _) fun s3 ⟨c3, p1⟩ => ?_
  have q0 : Lanes (s3.v .v4) fun i => Z i := Lanes.chg c3 (by decide) p0
  have q1 : Lanes (s3.v .v5) fun i => Z (4 + i) := p1.congr fun i _ => by
    show Y (8 + 2 * i) + Y (8 + (2 * i + 1)) * 2 ^ 10 = Y (2 * (4 + i)) + Y (2 * (4 + i) + 1) * 2 ^ 10
    rw [show 8 + 2 * i = 2 * (4 + i) by omega, show 8 + (2 * i + 1) = 2 * (4 + i) + 1 by omega]
  rw [WP.block_append_iff]
  refine WP.mono (dpairV_ok (b := 20) (by decide) (by decide) q0 fun i _ => hZ i) fun s4 ⟨c4, d0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dpairV_ok (b := 20) (by decide) (by decide) (Lanes.chg c4 (by decide) q1)
    fun i _ => hZ _) fun s5 ⟨c5, d1⟩ => ?_
  have e0 : DLanes (s5.v .v4) fun l => grp10 Y l := fun l hl => by
    rw [c5.get .v4 (by decide), d0 l hl]
    simp only [Z, grp10]
    rw [show 2 * (2 * l) + 1 = 4 * l + 1 by omega, show 2 * (2 * l) = 4 * l by omega,
      show 2 * (2 * l + 1) + 1 = 4 * l + 3 by omega, show 2 * (2 * l + 1) = 4 * l + 2 by omega]
  have e1 : DLanes (s5.v .v5) fun l => grp10 Y (2 + l) := fun l hl => by
    rw [d1 l hl]
    simp only [Z, grp10]
    rw [show 4 + 2 * l = 2 * (2 + l) by omega, show 4 + (2 * l + 1) = 2 * (2 + l) + 1 by omega,
      show 2 * (2 * (2 + l)) + 1 = 4 * (2 + l) + 1 by omega, show 2 * (2 * (2 + l)) = 4 * (2 + l) by omega,
      show 2 * (2 * (2 + l) + 1) + 1 = 4 * (2 + l) + 3 by omega,
      show 2 * (2 * (2 + l) + 1) = 4 * (2 + l) + 2 by omega]
  have g20 : s5.v .v20 = idxVec ce10Idx := by
    rw [c5.get .v20 (by decide), c4.get .v20 (by decide), c3.get .v20 (by decide), c2.get .v20 (by decide),
      c1.get .v20 (by decide), h20]
  have g21 : s5.v .v21 = idxVec ce10IdxHi := by
    rw [c5.get .v21 (by decide), c4.get .v21 (by decide), c3.get .v21 (by decide), c2.get .v21 (by decide),
      c1.get .v21 (by decide), h21]
  -- byte `8 l + b` of the table: byte `b` of group `l`
  have tb : ∀ l < 4, ∀ b < 8, (if 8 * l + b < 16 then vbyte (s5.v .v4) (8 * l + b)
      else vbyte (s5.v .v5) (8 * l + b - 16)).toNat = grp10 Y l / 2 ^ (8 * b) % 2 ^ 8 := by
    intro l hl b hb
    by_cases h : l < 2
    · rw [ite_eq_left (by omega), toNat_vbyte_dword _ hb, e0 l h]
    · rw [ite_eq_right (by omega),
        show 8 * l + b - 16 = 8 * (l - 2) + b by omega, toNat_vbyte_dword _ hb, e1 (l - 2) (by omega)]
      dsimp only
      rw [show 2 + (l - 2) = l by omega]
  refine wp_vop (by simp only [VOp.eval]; rfl) fun s6 h6 => wp_vop (by simp only [VOp.eval]; rfl)
    fun t h7 => wp_nil ⟨?_, ?_, ?_⟩
  · exact ((((c1.trans c2).trans c3).trans c4).trans (c5.trans (h6.chg.trans h7.chg))).mono
  · intro j hj
    rw [h7.get .v6 (by decide), h6.v]
    have hk : (vbyte (s5.v .v20) j).toNat = 8 * (j / 5) + j % 5 := by
      rw [g20, toNat_idxVec _ (by decide) hj, ce10Idx_eq j hj]
    rw [vbyte_tbl2 hj hk (by omega), show VReg.v4.succ = .v5 from rfl]
    exact tb (j / 5) (by omega) (j % 5) (by omega)
  · intro j hj
    rw [h7.v]
    have hk : (vbyte (s6.v .v21) j).toNat = 8 * 3 + (1 + j) := by
      rw [h6.get .v21 (by decide), g21, toNat_idxVec _ (by decide) (by omega), ce10IdxHi_eq j hj]; omega
    rw [vbyte_tbl2 (by omega) hk (by omega), show VReg.v4.succ = .v5 from rfl, h6.get .v4 (by decide),
      h6.get .v5 (by decide)]
    exact tb 3 (by decide) (1 + j) (by omega)

end VG.Proof.MlKem.AArch64.CodecV
