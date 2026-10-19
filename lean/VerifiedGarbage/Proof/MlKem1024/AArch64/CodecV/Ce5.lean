module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10
public import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Widths

/-!
# ML-KEM-1024 on AArch64: `ce5Math`

32 compressed coefficients of five bits, paired twice into values of 20 bits and those into four
groups of 40 bits in doublewords, whose five low bytes TBL picks, as for `d = 10` (`ce10Math_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Proof.MlKem1024.AArch64 VG.Spec.MlKem

/-- Pairs of values `Y` of five bits. -/
abbrev z5 (Y : Nat → Nat) (i : Nat) : Nat := Y (2 * i) + Y (2 * i + 1) * 2 ^ 5
/-- Pairs of pairs: values of 20 bits. -/
abbrev w5 (Y : Nat → Nat) (i : Nat) : Nat := z5 Y (2 * i) + z5 Y (2 * i + 1) * 2 ^ 10
/-- A group of 40 bits: eight values `Y (8 l) …` of five bits. -/
abbrev grp5 (Y : Nat → Nat) (l : Nat) : Nat := w5 Y (2 * l) + w5 Y (2 * l + 1) * 2 ^ 20

theorem ce5Math_ok {s : State} (hc : CConsts width5 s) (h20 : s.v .v20 = idxVec ce10Idx)
    (h21 : s.v .v21 = idxVec ce10IdxHi) {X : Nat → Nat} (hX : ∀ i < 32, X i < 3329)
    (l0 : Lanes (s.v .v0) fun i => X i) (l1 : Lanes (s.v .v1) fun i => X (4 + i))
    (l2 : Lanes (s.v .v2) fun i => X (8 + i)) (l3 : Lanes (s.v .v3) fun i => X (12 + i))
    (l4 : Lanes (s.v .v4) fun i => X (16 + i)) (l5 : Lanes (s.v .v5) fun i => X (20 + i))
    (l6 : Lanes (s.v .v6) fun i => X (24 + i)) (l7 : Lanes (s.v .v7) fun i => X (28 + i)) :
    WP isa (.block ce5Math) s fun t => VChg [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v19] s t ∧
      (∀ j < 16, (vbyte (t.v .v6) j).toNat = grp5 (fun i => cf width5 (X i)) (j / 5) / 2 ^ (8 * (j % 5)) % 2 ^ 8) ∧
      (∀ j < 4, (vbyte (t.v .v7) j).toNat = grp5 (fun i => cf width5 (X i)) 3 / 2 ^ (8 * (1 + j)) % 2 ^ 8) := by
  have hd : WOk width5 := width5_ok
  unfold ce5Math cmp8
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (cmp4_ok hd hc (fun i hi => hX i (by omega)) l0 l1 l2 l3) fun s1 ⟨c1, m0, m1, m2, m3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cmp4_ok hd (hc.chg c1) (X := fun i => X (16 + i)) (fun i hi => hX _ (by omega))
    (Lanes.chg c1 (by decide) l4) ((Lanes.chg c1 (by decide) l5).congr fun i _ => by congr 1; omega)
    ((Lanes.chg c1 (by decide) l6).congr fun i _ => by congr 1; omega)
    ((Lanes.chg c1 (by decide) l7).congr fun i _ => by congr 1; omega))
    fun s2 ⟨c2, m4, m5, m6, m7⟩ => ?_
  let Y : Nat → Nat := fun i => cf width5 (X i)
  have hY : ∀ i, Y i < 2 ^ 5 := fun i => cf_lt width5 _
  -- level 1: pairs of values of five bits
  let Z : Nat → Nat := fun i => Y (2 * i) + Y (2 * i + 1) * 2 ^ 5
  have hZ : ∀ i, Z i < 2 ^ 10 := fun i => by have := hY (2 * i); have := hY (2 * i + 1); simp only [Z]; omega
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 5) (f := Y) (by decide) (by decide) (by decide) (by decide)
    (Lanes.chg c2 (by decide) m0) (Lanes.chg c2 (by decide) m1) fun i _ => hY i)
    fun s3 ⟨c3, p0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 5) (f := fun i => Y (8 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c3 (by decide) (Lanes.chg c2 (by decide) m2))
    ((Lanes.chg c3 (by decide) (Lanes.chg c2 (by decide) m3)).congr fun i _ => by
      show Y (12 + i) = Y (8 + (4 + i)); congr 1; omega)
    fun i _ => hY _) fun s4 ⟨c4, p1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 5) (f := fun i => Y (16 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m4))
    (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m5))
    fun i _ => hY _) fun s5 ⟨c5, p2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 5) (f := fun i => Y (24 + i)) (by decide) (by decide) (by decide)
    (by decide) ((Lanes.chg c5 (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide)
      m6))).congr fun i _ => by show Y (16 + (8 + i)) = Y (24 + i); congr 1; omega)
    ((Lanes.chg c5 (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m7))).congr
      fun i _ => by show Y (16 + (12 + i)) = Y (24 + (4 + i)); congr 1; omega)
    fun i _ => hY _) fun s6 ⟨c6, p3⟩ => ?_
  have q0 : Lanes (s6.v .v0) fun i => Z i := Lanes.chg c6 (by decide) (Lanes.chg c5 (by decide)
    (Lanes.chg c4 (by decide) p0))
  have q1 : Lanes (s6.v .v1) fun i => Z (4 + i) := (Lanes.chg c6 (by decide) (Lanes.chg c5 (by decide)
    p1)).congr fun i _ => by
    show Y (8 + 2 * i) + Y (8 + (2 * i + 1)) * 2 ^ 5 = Y (2 * (4 + i)) + Y (2 * (4 + i) + 1) * 2 ^ 5
    rw [show 8 + 2 * i = 2 * (4 + i) by omega, show 8 + (2 * i + 1) = 2 * (4 + i) + 1 by omega]
  have q2 : Lanes (s6.v .v2) fun i => Z (8 + i) := (Lanes.chg c6 (by decide) p2).congr fun i _ => by
    show Y (16 + 2 * i) + Y (16 + (2 * i + 1)) * 2 ^ 5 = Y (2 * (8 + i)) + Y (2 * (8 + i) + 1) * 2 ^ 5
    rw [show 16 + 2 * i = 2 * (8 + i) by omega, show 16 + (2 * i + 1) = 2 * (8 + i) + 1 by omega]
  have q3 : Lanes (s6.v .v3) fun i => Z (12 + i) := p3.congr fun i _ => by
    show Y (24 + 2 * i) + Y (24 + (2 * i + 1)) * 2 ^ 5 = Y (2 * (12 + i)) + Y (2 * (12 + i) + 1) * 2 ^ 5
    rw [show 24 + 2 * i = 2 * (12 + i) by omega, show 24 + (2 * i + 1) = 2 * (12 + i) + 1 by omega]
  -- level 2: values of 20 bits
  let W : Nat → Nat := fun i => Z (2 * i) + Z (2 * i + 1) * 2 ^ 10
  have hW : ∀ i, W i < 2 ^ 20 := fun i => by have := hZ (2 * i); have := hZ (2 * i + 1); simp only [W]; omega
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 10) (f := Z) (by decide) (by decide) (by decide) (by decide)
    q0 q1 fun i _ => hZ i) fun s7 ⟨c7, r0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 10) (f := fun i => Z (8 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c7 (by decide) q2)
    ((Lanes.chg c7 (by decide) q3).congr fun i _ => by show Z (12 + i) = Z (8 + (4 + i)); congr 1; omega)
    fun i _ => hZ _) fun s8 ⟨c8, r1⟩ => ?_
  have u0 : Lanes (s8.v .v4) fun i => W i := Lanes.chg c8 (by decide) r0
  have u1 : Lanes (s8.v .v5) fun i => W (4 + i) := r1.congr fun i _ => by
    show Z (8 + 2 * i) + Z (8 + (2 * i + 1)) * 2 ^ 10 = Z (2 * (4 + i)) + Z (2 * (4 + i) + 1) * 2 ^ 10
    rw [show 8 + 2 * i = 2 * (4 + i) by omega, show 8 + (2 * i + 1) = 2 * (4 + i) + 1 by omega]
  -- level 3: groups of 40 bits in doublewords
  rw [WP.block_append_iff]
  refine WP.mono (dpairV_ok (b := 20) (by decide) (by decide) u0 fun i _ => hW i) fun s9 ⟨c9, d0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dpairV_ok (b := 20) (by decide) (by decide) (Lanes.chg c9 (by decide) u1)
    fun i _ => hW _) fun s10 ⟨c10, d1⟩ => ?_
  have e0 : DLanes (s10.v .v4) fun l => grp5 Y l := fun l hl => by
    rw [c10.get .v4 (by decide), d0 l hl]
  have e1 : DLanes (s10.v .v5) fun l => grp5 Y (2 + l) := fun l hl => by
    rw [d1 l hl]
    show W (4 + 2 * l) + W (4 + (2 * l + 1)) * 2 ^ 20 = W (2 * (2 + l)) + W (2 * (2 + l) + 1) * 2 ^ 20
    rw [show 4 + 2 * l = 2 * (2 + l) by omega, show 4 + (2 * l + 1) = 2 * (2 + l) + 1 by omega]
  have cA : VChg [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v19] s s10 :=
    (((((((((c1.trans c2).trans c3).trans c4).trans c5).trans c6).trans c7).trans c8).trans c9).trans
      c10).mono
  have g20 : s10.v .v20 = idxVec ce10Idx := by rw [cA.get .v20, h20]
  have g21 : s10.v .v21 = idxVec ce10IdxHi := by rw [cA.get .v21, h21]
  -- byte `8 l + b` of the table: byte `b` of group `l`
  have tb : ∀ l < 4, ∀ b < 8, (if 8 * l + b < 16 then vbyte (s10.v .v4) (8 * l + b)
      else vbyte (s10.v .v5) (8 * l + b - 16)).toNat = grp5 Y l / 2 ^ (8 * b) % 2 ^ 8 := by
    intro l hl b hb
    by_cases h : l < 2
    · rw [ite_eq_left (by omega), toNat_vbyte_dword _ hb, e0 l h]
    · rw [ite_eq_right (by omega),
        show 8 * l + b - 16 = 8 * (l - 2) + b by omega, toNat_vbyte_dword _ hb, e1 (l - 2) (by omega)]
      dsimp only
      rw [show 2 + (l - 2) = l by omega]
  refine wp_vop (by simp only [VOp.eval]; rfl) fun s11 h11 => wp_vop (by simp only [VOp.eval]; rfl)
    fun t h12 => wp_nil ⟨?_, ?_, ?_⟩
  · exact (cA.trans (h11.chg.trans h12.chg)).mono
  · intro j hj
    rw [h12.get .v6 (by decide), h11.v]
    have hk : (vbyte (s10.v .v20) j).toNat = 8 * (j / 5) + j % 5 := by
      rw [g20, toNat_idxVec _ (by decide) hj, ce10Idx_eq j hj]
    rw [vbyte_tbl2 hj hk (by omega), show VReg.v4.succ = .v5 from rfl]
    exact tb (j / 5) (by omega) (j % 5) (by omega)
  · intro j hj
    rw [h12.v]
    have hk : (vbyte (s11.v .v21) j).toNat = 8 * 3 + (1 + j) := by
      rw [h11.get .v21 (by decide), g21, toNat_idxVec _ (by decide) (by omega), ce10IdxHi_eq j hj]; omega
    rw [vbyte_tbl2 (by omega) hk (by omega), show VReg.v4.succ = .v5 from rfl, h11.get .v4 (by decide),
      h11.get .v5 (by decide)]
    exact tb 3 (by decide) (1 + j) (by omega)

end VG.Proof.MlKem1024.AArch64.CodecV
