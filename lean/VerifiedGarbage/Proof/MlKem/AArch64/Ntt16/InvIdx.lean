module

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Gs
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Last
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Rows
import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

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

/-- The offsets of `firstTwo`, from `op` and `oq`, with the zetas `kz7` (layer 1), `kz6`
(layer 2). -/
def okFirst (op oq kz7 kz6 : List Nat) : Bool :=
  let a := t1d op oq
  let b := t2d op oq
  let c := t1s a b
  let d := t2s a b
  okGs 0 c d kz7 && okGs 1 (t1s c d) (t2s c d) kz6 && t1d (t1s c d) (t2s c d) == op &&
    t2d (t1s c d) (t2s c d) == oq

private theorem idx_d1' : ∀ e < 8, (if decide (e < 4) then e else e - 4) < 8 := by decide
private theorem idx_d2' : ∀ e < 8, (if decide (e < 4) then e + 4 else e) < 8 := by decide
private theorem idx_s1' : ∀ e < 8, (if (e / 2 % 2 == 0) then e else e - 2) < 8 := by decide
private theorem idx_s2' : ∀ e < 8, (if (e / 2 % 2 == 0) then e + 2 else e) < 8 := by decide

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem firstTwo_ok {p q' z7 t7 z6 t6 : VReg}
    (hd : [p, q', z7, t7, z6, t6, VReg.v4, .v5, .v16, .v17, .v31].Nodup := by decide)
    {P : Poly} {base K7 K6 : Nat} {op oq kz7 kz6 : List Nat} (hok : okFirst op oq kz7 kz6 = true)
    (hb : base % 32 = 0) (hb' : base + 32 ≤ 256)
    (hK7 : K7 + 32 / (2 * (2 <<< 0)) = 256 / (2 <<< 0) - base / (2 * (2 <<< 0)))
    (hK6 : K6 + 32 / (2 * (2 <<< 1)) = 256 / (2 <<< 1) - base / (2 * (2 <<< 1)))
    (hp : IRepI P 0 base op 3329 (s.v p)) (hq' : IRepI P 0 base oq 3329 (s.v q'))
    (hz7 : ZRep (s.v z7) K7 kz7) (ht7 : TRep (s.v t7) K7 kz7)
    (hz6 : ZRep (s.v z6) K6 kz6) (ht6 : TRep (s.v t6) K6 kz6) (hq : Cst (s.v .v31) fun _ => 3329)
    (k : ∀ s', VChg (lastRegs p q') s s' → IRepI P 2 base op (4 * 3329) (s'.v p) →
      IRepI P 2 base oq (4 * 3329) (s'.v q') → WP isa (.block rest) s' Q) :
    WP isa (.block (firstTwo p q' z7 t7 z6 t6 ++ rest)) s Q := by
  simp only [okFirst, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨h1, h2⟩, e1⟩, e2⟩ := hok
  have n_pq : p ≠ q' := by rintro rfl; simp at hd
  have n_p4 : p ≠ .v4 := by rintro rfl; simp at hd
  have n_p5 : p ≠ .v5 := by rintro rfl; simp at hd
  have n_p17 : p ≠ .v17 := by rintro rfl; simp at hd
  have n_p31 : p ≠ .v31 := by rintro rfl; simp at hd
  have n_q4 : q' ≠ .v4 := by rintro rfl; simp at hd
  have n_q5 : q' ≠ .v5 := by rintro rfl; simp at hd
  have n_q17 : q' ≠ .v17 := by rintro rfl; simp at hd
  have n_q31 : q' ≠ .v31 := by rintro rfl; simp at hd
  have n_z7p : z7 ≠ p := by rintro rfl; simp at hd
  have n_z7q : z7 ≠ q' := by rintro rfl; simp at hd
  have n_z74 : z7 ≠ .v4 := by rintro rfl; simp at hd
  have n_z75 : z7 ≠ .v5 := by rintro rfl; simp at hd
  have n_z717 : z7 ≠ .v17 := by rintro rfl; simp at hd
  have n_t7p : t7 ≠ p := by rintro rfl; simp at hd
  have n_t7q : t7 ≠ q' := by rintro rfl; simp at hd
  have n_t74 : t7 ≠ .v4 := by rintro rfl; simp at hd
  have n_t75 : t7 ≠ .v5 := by rintro rfl; simp at hd
  have n_t717 : t7 ≠ .v17 := by rintro rfl; simp at hd
  have n_z6p : z6 ≠ p := by rintro rfl; simp at hd
  have n_z6q : z6 ≠ q' := by rintro rfl; simp at hd
  have n_z64 : z6 ≠ .v4 := by rintro rfl; simp at hd
  have n_z65 : z6 ≠ .v5 := by rintro rfl; simp at hd
  have n_z617 : z6 ≠ .v17 := by rintro rfl; simp at hd
  have n_t6p : t6 ≠ p := by rintro rfl; simp at hd
  have n_t6q : t6 ≠ q' := by rintro rfl; simp at hd
  have n_t64 : t6 ≠ .v4 := by rintro rfl; simp at hd
  have n_t65 : t6 ≠ .v5 := by rintro rfl; simp at hd
  have n_t617 : t6 ≠ .v17 := by rintro rfl; simp at hd
  clear hd
  simp only [firstTwo, List.cons_append, List.nil_append, List.append_assoc]
  -- v4, v5 ← trn1, trn2 (.2d) p q'; p, q' ← trn1, trn2 (.4s) v4 v5
  refine wp_vop rfl fun s₁ h₁ => wp_vop rfl fun s₂ h₂ => wp_vop rfl fun s₃ h₃ => wp_vop rfl fun s₄ h₄ => ?_
  have a₂ : IRepI P 0 base (t1d op oq) 3329 (s₂.v .v4) := by
    rw [h₂.get .v4, h₁.v]
    exact irepI_perm (src_trn1_d2 _ _) idx_d1' hp hq' (permO_apply _ _ _ _ _)
  have b₂ : IRepI P 0 base (t2d op oq) 3329 (s₂.v .v5) := by
    rw [h₂.v, h₁.get p n_p4, h₁.get q' n_q4]
    exact irepI_perm (src_trn2_d2 _ _) idx_d2' hp hq' (permO_apply _ _ _ _ _)
  have c₄ : IRepI P 0 base (t1s (t1d op oq) (t2d op oq)) 3329 (s₄.v p) := by
    rw [h₄.get p n_pq, h₃.v]
    exact irepI_perm (src_s4 .trn1 _ _) idx_s1' a₂ b₂ (permO_apply _ _ _ _ _)
  have d₄ : IRepI P 0 base (t2s (t1d op oq) (t2d op oq)) 3329 (s₄.v q') := by
    rw [h₄.v, h₃.get .v4 (Ne.symm n_p4), h₃.get .v5 (Ne.symm n_p5)]
    exact irepI_perm (src_s4 .trn2 _ _) idx_s2' a₂ b₂ (permO_apply _ _ _ _ _)
  have c₄' : VChg [.v4, .v5, p, q'] s s₄ :=
    (((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).mono fun r hr => by
      simp only [List.mem_append, List.mem_singleton] at hr; simp [hr.elim (fun h => h.elim
        (fun h => h.elim Or.inl (fun h => Or.inr (Or.inl h))) (fun h => Or.inr (Or.inr (Or.inl h))))
        (fun h => Or.inr (Or.inr (Or.inr h)))]
  refine irepI_gs n_pq n_p17 n_q17 n_z7p n_z717 n_t7p n_t7q n_t717 (Ne.symm n_p31) (Ne.symm n_q31)
    h1 hb hb' hK7 c₄ d₄ (by rw [c₄'.get z7 (by simp [n_z74, n_z75, n_z7p, n_z7q])]; exact hz7)
    (by rw [c₄'.get t7 (by simp [n_t74, n_t75, n_t7p, n_t7q])]; exact ht7)
    (by rw [c₄'.get .v31 (by simp [Ne.symm n_p31, Ne.symm n_q31])]; exact hq) (by decide)
    fun s₅ c₅ p₅ q₅ => ?_
  -- v4, v5 ← trn1, trn2 (.4s) p q'
  refine wp_vop rfl fun s₆ h₆ => wp_vop rfl fun s₇ h₇ => ?_
  have a₇ : IRepI P 1 base (t1s (t1s (t1d op oq) (t2d op oq)) (t2s (t1d op oq) (t2d op oq)))
      (2 * 3329) (s₇.v .v4) := by
    rw [h₇.get .v4, h₆.v]
    exact irepI_perm (src_s4 .trn1 _ _) idx_s1' p₅ (q₅.mono (by decide)) (permO_apply _ _ _ _ _)
  have b₇ : IRepI P 1 base (t2s (t1s (t1d op oq) (t2d op oq)) (t2s (t1d op oq) (t2d op oq)))
      (2 * 3329) (s₇.v .v5) := by
    rw [h₇.v, h₆.get p n_p4, h₆.get q' n_q4]
    exact irepI_perm (src_s4 .trn2 _ _) idx_s2' p₅ (q₅.mono (by decide)) (permO_apply _ _ _ _ _)
  have g : ∀ r, r ∉ [VReg.v4, .v5] → r ∉ [VReg.v17, p, q', .v17, q'] → r ∉ [VReg.v4, .v5, p, q'] →
      s₇.v r = s.v r := fun r g1 g2 g3 => by
    rw [(h₆.chg.trans h₇.chg).get r (by simpa using g1), c₅.get r g2, c₄'.get r g3]
  refine irepI_gs (by decide) (by decide) (by decide) n_z64 n_z617 n_t64 n_t65 n_t617 (by decide)
    (by decide) h2 hb hb' hK6 a₇ b₇
    (by rw [g z6 (by simp [n_z64, n_z65]) (by simp [n_z617, n_z6p, n_z6q])
          (by simp [n_z64, n_z65, n_z6p, n_z6q])]; exact hz6)
    (by rw [g t6 (by simp [n_t64, n_t65]) (by simp [n_t617, n_t6p, n_t6q])
          (by simp [n_t64, n_t65, n_t6p, n_t6q])]; exact ht6)
    (by rw [g .v31 (by decide) (by simp [Ne.symm n_p31, Ne.symm n_q31])
          (by simp [Ne.symm n_p31, Ne.symm n_q31])]; exact hq) (by decide)
    fun s₈ c₈ a₈ b₈ => ?_
  -- p, q' ← trn1, trn2 (.2d) v4 v5
  refine wp_vop rfl fun s₉ h₉ => wp_vop rfl fun s₁₀ h₁₀ => ?_
  refine k s₁₀ ((((c₄'.trans c₅).trans ((h₆.chg.trans h₇.chg))).trans c₈).trans
    (h₉.chg.trans h₁₀.chg) |>.mono (by simp)) ?_ ?_
  · rw [h₁₀.get p n_pq, h₉.v, ← e1]
    exact irepI_perm (src_trn1_d2 _ _) idx_d1' a₈ (b₈.mono (by decide)) (permO_apply _ _ _ _ _)
  · rw [h₁₀.v, h₉.get .v4 (Ne.symm n_p4), h₉.get .v5 (Ne.symm n_p5), ← e2]
    exact irepI_perm (src_trn2_d2 _ _) idx_d2' a₈ (b₈.mono (by decide)) (permO_apply _ _ _ _ _)

end

end VG.Proof.MlKem.AArch64.Ntt16
