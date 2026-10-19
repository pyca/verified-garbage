module

public import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Ce5
public import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Dword88

/-!
# ML-KEM-1024 on AArch64: `ce11Math`

32 compressed coefficients of 11 bits, paired into values of 22 bits, those into doublewords of 44
bits, and the two of each register into a group of 88 bits in its 11 low bytes (`merge88_ok`),
whose bytes TBL picks from the four registers.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Proof.MlKem1024.AArch64 VG.Spec.MlKem

/-- Pairs of values `Y` of 11 bits. -/
abbrev z11 (Y : Nat → Nat) (i : Nat) : Nat := Y (2 * i) + Y (2 * i + 1) * 2 ^ 11
/-- Pairs of pairs: values of 44 bits. -/
abbrev w11 (Y : Nat → Nat) (i : Nat) : Nat := z11 Y (2 * i) + z11 Y (2 * i + 1) * 2 ^ 22
/-- A group of 88 bits: eight values `Y (8 r) …` of 11 bits. -/
abbrev grp11 (Y : Nat → Nat) (r : Nat) : Nat := w11 Y (2 * r) + w11 Y (2 * r + 1) * 2 ^ 44

/-- TBL of `len` registers from `n`, at an index in the table. -/
theorem vbyte_tblN {s : State} {n m d : VReg} {len i k : Nat} (hi : i < 16)
    (hk : (vbyte (s.v m) i).toNat = k) (hk' : k < 16 * len) :
    vbyte (ofVBytes fun i => if (vbyte (s.v m) i).toNat < 16 * len then tableByte s.v n (vbyte (s.v m) i).toNat
      else if false then vbyte (s.v d) i else 0) i = tableByte s.v n k := by
  rw [vbyte_ofVBytes _ hi, hk, ite_eq_left hk']

/-- The index of byte `m` of the output: byte `m mod 11` of register `m / 11`. -/
abbrev idx11 (m : Nat) : Nat := 16 * (m / 11) + m % 11

theorem ce11Idx0_eq : ∀ j < 16, ce11Idx0.getD j 255 = idx11 j := by decide
theorem ce11Idx1_eq : ∀ j < 16, ce11Idx1.getD j 255 = idx11 (16 + j) := by decide
theorem ce11Idx2_eq : ∀ j < 12, ce11Idx2.getD j 255 = idx11 (32 + j) := by decide

theorem ce11Math_ok {s : State} (hc : CConsts width11 s) (h20 : s.v .v20 = idxVec ce11Idx0)
    (h21 : s.v .v21 = idxVec ce11Idx1) (h22 : s.v .v22 = idxVec ce11Idx2) {X : Nat → Nat}
    (hX : ∀ i < 32, X i < 3329)
    (l0 : Lanes (s.v .v0) fun i => X i) (l1 : Lanes (s.v .v1) fun i => X (4 + i))
    (l2 : Lanes (s.v .v2) fun i => X (8 + i)) (l3 : Lanes (s.v .v3) fun i => X (12 + i))
    (l4 : Lanes (s.v .v4) fun i => X (16 + i)) (l5 : Lanes (s.v .v5) fun i => X (20 + i))
    (l6 : Lanes (s.v .v6) fun i => X (24 + i)) (l7 : Lanes (s.v .v7) fun i => X (28 + i)) :
    WP isa (.block ce11Math) s fun t => VChg [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v19, .v23] s t ∧
      (∀ j < 16, (vbyte (t.v .v4) j).toNat =
        grp11 (fun i => cf width11 (X i)) (j / 11) / 2 ^ (8 * (j % 11)) % 2 ^ 8) ∧
      (∀ j < 16, (vbyte (t.v .v5) j).toNat =
        grp11 (fun i => cf width11 (X i)) ((16 + j) / 11) / 2 ^ (8 * ((16 + j) % 11)) % 2 ^ 8) ∧
      (∀ j < 12, (vbyte (t.v .v6) j).toNat =
        grp11 (fun i => cf width11 (X i)) ((32 + j) / 11) / 2 ^ (8 * ((32 + j) % 11)) % 2 ^ 8) := by
  have hd : WOk width11 := width11_ok
  unfold ce11Math cmp8
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (cmp4_ok hd hc (fun i hi => hX i (by omega)) l0 l1 l2 l3) fun s1 ⟨c1, m0, m1, m2, m3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cmp4_ok hd (hc.chg c1) (X := fun i => X (16 + i)) (fun i hi => hX _ (by omega))
    (Lanes.chg c1 (by decide) l4) ((Lanes.chg c1 (by decide) l5).congr fun i _ => by congr 1; omega)
    ((Lanes.chg c1 (by decide) l6).congr fun i _ => by congr 1; omega)
    ((Lanes.chg c1 (by decide) l7).congr fun i _ => by congr 1; omega))
    fun s2 ⟨c2, m4, m5, m6, m7⟩ => ?_
  let Y : Nat → Nat := fun i => cf width11 (X i)
  have hY : ∀ i, Y i < 2 ^ 11 := fun i => cf_lt width11 _
  -- level 1: pairs of values of 11 bits
  let Z : Nat → Nat := fun i => Y (2 * i) + Y (2 * i + 1) * 2 ^ 11
  have hZ : ∀ i, Z i < 2 ^ 22 := fun i => by have := hY (2 * i); have := hY (2 * i + 1); simp only [Z]; omega
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 11) (f := Y) (by decide) (by decide) (by decide) (by decide)
    (Lanes.chg c2 (by decide) m0) (Lanes.chg c2 (by decide) m1) fun i _ => hY i)
    fun s3 ⟨c3, p0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 11) (f := fun i => Y (8 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c3 (by decide) (Lanes.chg c2 (by decide) m2))
    ((Lanes.chg c3 (by decide) (Lanes.chg c2 (by decide) m3)).congr fun i _ => by
      show Y (12 + i) = Y (8 + (4 + i)); congr 1; omega)
    fun i _ => hY _) fun s4 ⟨c4, p1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 11) (f := fun i => Y (16 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m4))
    (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m5))
    fun i _ => hY _) fun s5 ⟨c5, p2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 11) (f := fun i => Y (24 + i)) (by decide) (by decide) (by decide)
    (by decide) ((Lanes.chg c5 (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide)
      m6))).congr fun i _ => by show Y (16 + (8 + i)) = Y (24 + i); congr 1; omega)
    ((Lanes.chg c5 (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m7))).congr
      fun i _ => by show Y (16 + (12 + i)) = Y (24 + (4 + i)); congr 1; omega)
    fun i _ => hY _) fun s6 ⟨c6, p3⟩ => ?_
  have q0 : Lanes (s6.v .v0) fun i => Z i := Lanes.chg c6 (by decide) (Lanes.chg c5 (by decide)
    (Lanes.chg c4 (by decide) p0))
  have q1 : Lanes (s6.v .v1) fun i => Z (4 + i) := (Lanes.chg c6 (by decide) (Lanes.chg c5 (by decide)
    p1)).congr fun i _ => by
    show Y (8 + 2 * i) + Y (8 + (2 * i + 1)) * 2 ^ 11 = Y (2 * (4 + i)) + Y (2 * (4 + i) + 1) * 2 ^ 11
    rw [show 8 + 2 * i = 2 * (4 + i) by omega, show 8 + (2 * i + 1) = 2 * (4 + i) + 1 by omega]
  have q2 : Lanes (s6.v .v2) fun i => Z (8 + i) := (Lanes.chg c6 (by decide) p2).congr fun i _ => by
    show Y (16 + 2 * i) + Y (16 + (2 * i + 1)) * 2 ^ 11 = Y (2 * (8 + i)) + Y (2 * (8 + i) + 1) * 2 ^ 11
    rw [show 16 + 2 * i = 2 * (8 + i) by omega, show 16 + (2 * i + 1) = 2 * (8 + i) + 1 by omega]
  have q3 : Lanes (s6.v .v3) fun i => Z (12 + i) := p3.congr fun i _ => by
    show Y (24 + 2 * i) + Y (24 + (2 * i + 1)) * 2 ^ 11 = Y (2 * (12 + i)) + Y (2 * (12 + i) + 1) * 2 ^ 11
    rw [show 24 + 2 * i = 2 * (12 + i) by omega, show 24 + (2 * i + 1) = 2 * (12 + i) + 1 by omega]
  -- level 2: doublewords of 44 bits
  let W : Nat → Nat := fun l => Z (2 * l) + Z (2 * l + 1) * 2 ^ 22
  have hW : ∀ l, W l < 2 ^ 44 := fun l => by have := hZ (2 * l); have := hZ (2 * l + 1); simp only [W]; omega
  rw [WP.block_append_iff]
  refine WP.mono (dpairV_ok (b := 22) (by decide) (by decide) q0 fun i _ => hZ i) fun s7 ⟨c7, d0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dpairV_ok (b := 22) (by decide) (by decide) (Lanes.chg c7 (by decide) q1)
    fun i _ => hZ _) fun s8 ⟨c8, d1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dpairV_ok (b := 22) (by decide) (by decide) (Lanes.chg c8 (by decide) (Lanes.chg c7 (by decide) q2))
    fun i _ => hZ _) fun s9 ⟨c9, d2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dpairV_ok (b := 22) (by decide) (by decide)
    (Lanes.chg c9 (by decide) (Lanes.chg c8 (by decide) (Lanes.chg c7 (by decide) q3)))
    fun i _ => hZ _) fun s10 ⟨c10, d3⟩ => ?_
  have e0 : DLanes (s10.v .v0) fun l => W (2 * 0 + l) := fun l hl => by
    rw [c10.get .v0 (by decide), c9.get .v0 (by decide), c8.get .v0 (by decide), d0 l hl]
    simp only [W]; rw [show 2 * (2 * 0 + l) = 2 * l by omega]
  have e1 : DLanes (s10.v .v1) fun l => W (2 * 1 + l) := fun l hl => by
    rw [c10.get .v1 (by decide), c9.get .v1 (by decide), d1 l hl]
    simp only [W]; rw [show 2 * (2 * 1 + l) = 4 + 2 * l by omega, show 4 + 2 * l + 1 = 4 + (2 * l + 1) by omega]
  have e2 : DLanes (s10.v .v2) fun l => W (2 * 2 + l) := fun l hl => by
    rw [c10.get .v2 (by decide), d2 l hl]
    simp only [W]; rw [show 2 * (2 * 2 + l) = 8 + 2 * l by omega, show 8 + 2 * l + 1 = 8 + (2 * l + 1) by omega]
  have e3 : DLanes (s10.v .v3) fun l => W (2 * 3 + l) := fun l hl => by
    rw [d3 l hl]
    simp only [W]; rw [show 2 * (2 * 3 + l) = 12 + 2 * l by omega, show 12 + 2 * l + 1 = 12 + (2 * l + 1) by omega]
  -- level 3: groups of 88 bits
  rw [WP.block_append_iff]
  refine WP.mono (merge88_ok (g := fun l => W (2 * 0 + l)) (by decide) (by decide) e0 (hW _)) fun s11 ⟨c11, b0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (merge88_ok (g := fun l => W (2 * 1 + l)) (by decide) (by decide)
    (fun l hl => by rw [c11.get .v1 (by decide)]; exact e1 l hl)
    (hW _)) fun s12 ⟨c12, b1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (merge88_ok (g := fun l => W (2 * 2 + l)) (by decide) (by decide)
    (fun l hl => by rw [c12.get .v2 (by decide), c11.get .v2 (by decide)]; exact e2 l hl) (hW _))
    fun s13 ⟨c13, b2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (merge88_ok (g := fun l => W (2 * 3 + l)) (by decide) (by decide)
    (fun l hl => by rw [c13.get .v3 (by decide), c12.get .v3 (by decide), c11.get .v3 (by decide)]; exact e3 l hl)
    (hW _)) fun s14 ⟨c14, b3⟩ => ?_
  -- the bytes of the four registers: byte `b` of register `r`, of group `r`
  have hg : ∀ r < 4, ∀ b < 11, (vbyte (s14.v (Nat.repeat VReg.succ r .v0)) b).toNat =
      grp11 Y r / 2 ^ (8 * b) % 2 ^ 8 := by
    intro r hr b hb
    have gr : ∀ r, grp11 Y r = W (2 * r + 0) + W (2 * r + 1) * 2 ^ 44 := fun r => rfl
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [show Nat.repeat VReg.succ 0 .v0 = .v0 from rfl, c14.get .v0 (by decide), c13.get .v0 (by decide),
        c12.get .v0 (by decide), b0 b hb, gr]
    · rw [show Nat.repeat VReg.succ 1 .v0 = .v1 from rfl, c14.get .v1 (by decide), c13.get .v1 (by decide),
        b1 b hb, gr]
    · rw [show Nat.repeat VReg.succ 2 .v0 = .v2 from rfl, c14.get .v2 (by decide), b2 b hb, gr]
    · rw [show Nat.repeat VReg.succ 3 .v0 = .v3 from rfl, b3 b hb, gr]
  have cA : VChg [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v19, .v23] s s14 :=
    (((((((((((((c1.trans c2).trans c3).trans c4).trans c5).trans c6).trans c7).trans c8).trans c9).trans
      c10).trans c11).trans c12).trans c13).trans c14).mono
  have tb : ∀ m < 44, (tableByte s14.v .v0 (idx11 m)).toNat = grp11 Y (m / 11) / 2 ^ (8 * (m % 11)) % 2 ^ 8 :=
    fun m hm => by
      unfold tableByte
      rw [show idx11 m / 16 = m / 11 by unfold idx11; omega, show idx11 m % 16 = m % 11 by unfold idx11; omega]
      exact hg (m / 11) (by omega) (m % 11) (by omega)
  have tf : ∀ (u u' : State) (d : VReg), (∀ r, r ≠ d → u'.v r = u.v r) → (d = .v4 ∨ d = .v5) →
      ∀ m < 44, tableByte u'.v .v0 (idx11 m) = tableByte u.v .v0 (idx11 m) := by
    intro u u' d hu hd m hm
    unfold tableByte
    rw [show idx11 m / 16 = m / 11 by unfold idx11; omega]
    apply congrArg (fun x => vbyte x _)
    apply hu
    rcases (show m / 11 = 0 ∨ m / 11 = 1 ∨ m / 11 = 2 ∨ m / 11 = 3 by omega) with h | h | h | h <;>
      rw [h] <;> rcases hd with rfl | rfl <;> decide
  refine wp_vop (by simp only [VOp.eval]; rfl) fun s15 h15 => wp_vop (by simp only [VOp.eval]; rfl)
    fun s16 h16 => wp_vop (by simp only [VOp.eval]; rfl) fun t h17 => wp_nil ⟨?_, ?_, ?_, ?_⟩
  · exact (cA.trans ((h15.chg.trans h16.chg).trans h17.chg)).mono
  · intro j hj
    rw [h17.get .v4 (by decide), h16.get .v4 (by decide), h15.v]
    have hk : (vbyte (s14.v .v20) j).toNat = idx11 j := by
      rw [cA.get .v20, h20, toNat_idxVec _ (by decide) hj, ce11Idx0_eq j hj]
    rw [vbyte_tblN hj hk (by unfold idx11; omega)]
    exact tb j (by omega)
  · intro j hj
    rw [h17.get .v5 (by decide), h16.v]
    have hk : (vbyte (s15.v .v21) j).toNat = idx11 (16 + j) := by
      rw [h15.get .v21 (by decide), cA.get .v21, h21, toNat_idxVec _ (by decide) hj, ce11Idx1_eq j hj]
    rw [vbyte_tblN hj hk (by unfold idx11; omega), tf s14 s15 .v4 h15.other (.inl rfl) (16 + j) (by omega)]
    exact tb (16 + j) (by omega)
  · intro j hj
    rw [h17.v]
    have hk : (vbyte (s16.v .v22) j).toNat = idx11 (32 + j) := by
      rw [h16.get .v22 (by decide), h15.get .v22 (by decide), cA.get .v22, h22,
        toNat_idxVec _ (by decide) (by omega), ce11Idx2_eq j hj]
    rw [vbyte_tblN (by omega) hk (by unfold idx11; omega), tf s15 s16 .v5 h16.other (.inr rfl) (32 + j) (by omega),
      tf s14 s15 .v4 h15.other (.inl rfl) (32 + j) (by omega)]
    exact tb (32 + j) (by omega)

end VG.Proof.MlKem1024.AArch64.CodecV
