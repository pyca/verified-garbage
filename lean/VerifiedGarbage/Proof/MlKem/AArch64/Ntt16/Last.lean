module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Idx

/-!
# ML-KEM's 16-bit NTT on AArch64: the last two layers of a block

`lastTwo p q' …` (`Impl/MlKem/AArch64/Ntt16.lean`) transposes the 16
coefficients of `p` and `q'` (`trn1`, `trn2` on doublewords, then on words)
so that the pairs of layers 6 and 7 are in the same lanes, and back
(`lastTwo_ok`). `okLast` checks the offsets of every register on the way.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

/-- The offsets after a permutation. -/
def applyPerm (c : Nat → Bool) (i₁ i₂ : Nat → Nat) (ox oy : List Nat) : List Nat :=
  (List.range 8).map fun e => if c e then ox.getD (i₁ e) 0 else oy.getD (i₂ e) 0

theorem permO_apply (c : Nat → Bool) (i₁ i₂ : Nat → Nat) (ox oy : List Nat) :
    permO ox oy c i₁ i₂ (applyPerm c i₁ i₂ ox oy) = true := by
  simp only [permO, applyPerm, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro e he
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range he]
  rfl

/-- `trn1`, `trn2` on doublewords and words, as offsets. -/
def t1d (ox oy : List Nat) : List Nat := applyPerm (fun e => decide (e < 4)) (fun e => e) (fun e => e - 4) ox oy
def t2d (ox oy : List Nat) : List Nat := applyPerm (fun e => decide (e < 4)) (fun e => e + 4) (fun e => e) ox oy
def t1s (ox oy : List Nat) : List Nat :=
  applyPerm (fun e => e / 2 % 2 == 0) (fun e => e) (fun e => e - 2) ox oy
def t2s (ox oy : List Nat) : List Nat :=
  applyPerm (fun e => e / 2 % 2 == 0) (fun e => e + 2) (fun e => e) ox oy

/-- The offsets of `lastTwo`, from `op` and `oq`, with the zetas `kz6`, `kz7`. -/
def okLast (op oq kz6 kz7 : List Nat) : Bool :=
  let a := t1d op oq
  let b := t2d op oq
  let c := t1s a b
  let d := t2s a b
  okBf 5 a b kz6 && okBf 6 c d kz7 && t1d (t1s c d) (t2s c d) == op && t2d (t1s c d) (t2s c d) == oq

private theorem idx_d1 : ∀ e < 8, (if decide (e < 4) then e else e - 4) < 8 := by decide
private theorem idx_d2 : ∀ e < 8, (if decide (e < 4) then e + 4 else e) < 8 := by decide
private theorem idx_s1 : ∀ e < 8, (if (e / 2 % 2 == 0) then e else e - 2) < 8 := by decide
private theorem idx_s2 : ∀ e < 8, (if (e / 2 % 2 == 0) then e + 2 else e) < 8 := by decide

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- The registers `lastTwo` changes. -/
abbrev lastRegs (p q' : VReg) : List VReg := [.v4, .v5, .v16, .v17, p, q']

theorem lastTwo_ok {p q' z6 t6 z7 t7 : VReg}
    (hd : [p, q', z6, t6, z7, t7, VReg.v4, .v5, .v16, .v17, .v31].Nodup := by decide)
    {P : Poly} {base K6 K7 : Nat} {op oq kz6 kz7 : List Nat} (hok : okLast op oq kz6 kz7 = true)
    (hb : base % 32 = 0) (hb' : base + 32 ≤ 256)
    (hK6 : K6 = 128 / (128 >>> 5) + base / (2 * (128 >>> 5)))
    (hK7 : K7 = 128 / (128 >>> 6) + base / (2 * (128 >>> 6)))
    (hp : IRep P 5 base op (s.v p)) (hq' : IRep P 5 base oq (s.v q'))
    (hz6 : ZRep (s.v z6) K6 kz6) (ht6 : TRep (s.v t6) K6 kz6)
    (hz7 : ZRep (s.v z7) K7 kz7) (ht7 : TRep (s.v t7) K7 kz7) (hq : Cst (s.v .v31) fun _ => 3329)
    (k : ∀ s', VChg (lastRegs p q') s s' → IRep P 7 base op (s'.v p) → IRep P 7 base oq (s'.v q') →
      WP isa (.block rest) s' Q) :
    WP isa (.block (lastTwo p q' z6 t6 z7 t7 ++ rest)) s Q := by
  simp only [okLast, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨h5, h6⟩, e1⟩, e2⟩ := hok
  have n_pq : p ≠ q' := by rintro rfl; simp at hd
  have n_p4 : p ≠ .v4 := by rintro rfl; simp at hd
  have n_p5 : p ≠ .v5 := by rintro rfl; simp at hd
  have n_p16 : p ≠ .v16 := by rintro rfl; simp at hd
  have n_p17 : p ≠ .v17 := by rintro rfl; simp at hd
  have n_p31 : p ≠ .v31 := by rintro rfl; simp at hd
  have n_q4 : q' ≠ .v4 := by rintro rfl; simp at hd
  have n_q5 : q' ≠ .v5 := by rintro rfl; simp at hd
  have n_q16 : q' ≠ .v16 := by rintro rfl; simp at hd
  have n_q31 : q' ≠ .v31 := by rintro rfl; simp at hd
  have n_z64 : z6 ≠ .v4 := by rintro rfl; simp at hd
  have n_z65 : z6 ≠ .v5 := by rintro rfl; simp at hd
  have n_t64 : t6 ≠ .v4 := by rintro rfl; simp at hd
  have n_t65 : t6 ≠ .v5 := by rintro rfl; simp at hd
  have n_t616 : t6 ≠ .v16 := by rintro rfl; simp at hd
  have n_z7p : z7 ≠ p := by rintro rfl; simp at hd
  have n_z7q : z7 ≠ q' := by rintro rfl; simp at hd
  have n_z74 : z7 ≠ .v4 := by rintro rfl; simp at hd
  have n_z75 : z7 ≠ .v5 := by rintro rfl; simp at hd
  have n_z716 : z7 ≠ .v16 := by rintro rfl; simp at hd
  have n_z717 : z7 ≠ .v17 := by rintro rfl; simp at hd
  have n_t7p : t7 ≠ p := by rintro rfl; simp at hd
  have n_t7q : t7 ≠ q' := by rintro rfl; simp at hd
  have n_t74 : t7 ≠ .v4 := by rintro rfl; simp at hd
  have n_t75 : t7 ≠ .v5 := by rintro rfl; simp at hd
  have n_t716 : t7 ≠ .v16 := by rintro rfl; simp at hd
  have n_t717 : t7 ≠ .v17 := by rintro rfl; simp at hd
  clear hd
  simp only [lastTwo, List.cons_append, List.nil_append, List.append_assoc]
  -- v4, v5 ← trn1, trn2 (.2d) p q'
  refine wp_vop rfl fun s₁ h₁ => wp_vop rfl fun s₂ h₂ => ?_
  have a₂ : IRep P 5 base (t1d op oq) (s₂.v .v4) := by
    rw [h₂.get .v4, h₁.v]
    exact irep_perm (src_trn1_d2 _ _) idx_d1 hp hq' (permO_apply _ _ _ _ _)
  have b₂ : IRep P 5 base (t2d op oq) (s₂.v .v5) := by
    rw [h₂.v, h₁.get p n_p4, h₁.get q' n_q4]
    exact irep_perm (src_trn2_d2 _ _) idx_d2 hp hq' (permO_apply _ _ _ _ _)
  have c₂ : VChg [.v4, .v5] s s₂ := h₁.chg.trans h₂.chg
  refine irep_bf (by decide) (by decide) (by decide) (by decide) n_t616 h5 hb hb' hK6 a₂ b₂
    (by rw [c₂.get z6 (by simp [n_z64, n_z65])]; exact hz6)
    (by rw [c₂.get t6 (by simp [n_t64, n_t65])]; exact ht6)
    (by rw [c₂.get .v31]; exact hq) fun s₃ c₃ a₃ b₃ => ?_
  -- p, q' ← trn1, trn2 (.4s) v4 v5
  refine wp_vop rfl fun s₄ h₄ => wp_vop rfl fun s₅ h₅ => ?_
  have pa : IRep P 6 base (t1s (t1d op oq) (t2d op oq)) (s₅.v p) := by
    rw [h₅.get p n_pq, h₄.v]
    exact irep_perm (src_s4 .trn1 _ _) idx_s1 a₃ b₃ (permO_apply _ _ _ _ _)
  have qa : IRep P 6 base (t2s (t1d op oq) (t2d op oq)) (s₅.v q') := by
    rw [h₅.v, h₄.get .v4 (Ne.symm n_p4), h₄.get .v5 (Ne.symm n_p5)]
    exact irep_perm (src_s4 .trn2 _ _) idx_s2 a₃ b₃ (permO_apply _ _ _ _ _)
  have c₅ : VChg [p, q'] s₃ s₅ := h₄.chg.trans h₅.chg
  have g : ∀ r, r ∉ [VReg.v4, .v5] → r ∉ [VReg.v16, .v17, .v16, .v5, .v4] → r ∉ [p, q'] →
      s₅.v r = s.v r := fun r g1 g2 g3 => by rw [c₅.get r g3, c₃.get r g2, c₂.get r g1]
  refine irep_bf n_pq n_p16 n_p17 n_q16 n_t716 h6 hb hb' hK7 pa qa
    (by rw [g z7 (by simp [n_z74, n_z75]) (by simp [n_z74, n_z75, n_z716, n_z717])
          (by simp [n_z7p, n_z7q])]
        exact hz7)
    (by rw [g t7 (by simp [n_t74, n_t75]) (by simp [n_t74, n_t75, n_t716, n_t717])
          (by simp [n_t7p, n_t7q])]
        exact ht7)
    (by rw [g .v31 (by decide) (by decide) (by simp [Ne.symm n_p31, Ne.symm n_q31])]; exact hq)
    fun s₆ c₆ p₆ q₆ => ?_
  -- v4, v5 ← trn1, trn2 (.4s) p q'; p, q' ← trn1, trn2 (.2d) v4 v5
  refine wp_vop rfl fun s₇ h₇ => wp_vop rfl fun s₈ h₈ => wp_vop rfl fun s₉ h₉ =>
    wp_vop rfl fun s₁₀ h₁₀ => ?_
  have a₈ : IRep P 7 base (t1s (t1s (t1d op oq) (t2d op oq)) (t2s (t1d op oq) (t2d op oq)))
      (s₈.v .v4) := by
    rw [h₈.get .v4, h₇.v]
    exact irep_perm (src_s4 .trn1 _ _) idx_s1 p₆ q₆ (permO_apply _ _ _ _ _)
  have b₈ : IRep P 7 base (t2s (t1s (t1d op oq) (t2d op oq)) (t2s (t1d op oq) (t2d op oq)))
      (s₈.v .v5) := by
    rw [h₈.v, h₇.get p n_p4, h₇.get q' n_q4]
    exact irep_perm (src_s4 .trn2 _ _) idx_s2 p₆ q₆ (permO_apply _ _ _ _ _)
  refine k s₁₀ (((((c₂.trans c₃).trans c₅).trans c₆).trans
    (((h₇.chg.trans h₈.chg).trans h₉.chg).trans h₁₀.chg)).mono (by simp)) ?_ ?_
  · rw [h₁₀.get p n_pq, h₉.v]
    have := irep_perm (src_trn1_d2 _ _) idx_d1 a₈ b₈ (permO_apply _ _ _ _ _)
    rw [← e1]; exact this
  · rw [h₁₀.v, h₉.get .v4 (Ne.symm n_p4), h₉.get .v5 (Ne.symm n_p5)]
    have := irep_perm (src_trn2_d2 _ _) idx_d2 a₈ b₈ (permO_apply _ _ _ _ _)
    rw [← e2]; exact this

end

end VG.Proof.MlKem.AArch64.Ntt16
