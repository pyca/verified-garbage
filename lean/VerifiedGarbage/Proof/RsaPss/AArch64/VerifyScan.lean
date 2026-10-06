import VerifiedGarbage.Proof.RsaPss.AArch64.SignTop
import VerifiedGarbage.Proof.RsaPss.VerifyCases

/-!
# RSASSA-PSS verification on AArch64: the first nonzero byte of `DB`

`posScan` visits every byte of `DB` and keeps, under masks, the index and
the value of the first nonzero one, and a mask of all ones while there is
none (`posScan_ok`), which is the number of leading zero octets `lz`
(`lz_of_nz`).
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_lsr wp_ldrb wp_and wp_orr
  wp_sub)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_mov wp_countdown)
open VG.Proof.RsaPss (lz)

/-- The first index below `j` at which `f` is not zero. -/
def nz (f : Nat → Byte) : Nat → Option Nat
  | 0 => none
  | j + 1 => match nz f j with
    | some i => some i
    | none => if f j = 0 then none else some j

theorem nz_none {f : Nat → Byte} : ∀ {j : Nat}, nz f j = none → ∀ i < j, f i = 0
  | 0, _, _, hi => absurd hi (by omega)
  | j + 1, h, i, hi => by
    simp only [nz] at h
    split at h
    · cases h
    · rename_i h'
      by_cases e : f j = 0
      · rcases (by omega : i < j ∨ i = j) with hl | rfl
        · exact nz_none h' i hl
        · exact e
      · rw [ite_eq_right e] at h; cases h

theorem nz_some {f : Nat → Byte} : ∀ {j i : Nat}, nz f j = some i → i < j ∧ f i ≠ 0 ∧ ∀ k < i, f k = 0
  | 0, _, h => by cases h
  | j + 1, i, h => by
    simp only [nz] at h
    split at h
    · rename_i i' h'
      cases h
      obtain ⟨a, b, c⟩ := nz_some h'
      exact ⟨by omega, b, c⟩
    · rename_i h'
      by_cases e : f j = 0
      · rw [ite_eq_left e] at h; cases h
      · rw [ite_eq_right e] at h
        cases h
        exact ⟨by omega, e, nz_none h'⟩

/-- `lz` from its characterization. -/
theorem lz_eq : ∀ {l : List Byte} {n : Nat}, (∀ j < n, l.getD j 0 = 0) →
    (n = l.length ∨ (n < l.length ∧ l.getD n 0 ≠ 0)) → lz l = n
  | [], n, _, h => by
    simp only [List.length_nil, Nat.not_lt_zero, false_and, or_false] at h
    subst h; rfl
  | b :: bs, 0, _, h => by
    simp at h
    simp only [lz]
    rw [ite_eq_right (by simpa using h)]
  | b :: bs, n + 1, hz, h => by
    have hb : b = 0 := by simpa using hz 0 (by omega)
    simp only [lz, ite_eq_left hb]
    congr 1
    refine lz_eq (fun j hj => by simpa using hz (j + 1) (by omega)) ?_
    simp only [List.length_cons] at h
    rcases h with h | ⟨h₁, h₂⟩
    · exact .inl (by omega)
    · exact .inr ⟨by omega, by simpa using h₂⟩

/-- The value of the first nonzero byte, or 0. -/
def nzV (f : Nat → Byte) (j : Nat) : Byte :=
  match nz f j with
  | some i => f i
  | none => 0

theorem zero_bit (b : Byte) : (BitVec.setWidth 64 b - BitVec.ofNat 64 1) >>> 63 = if b = 0 then 1#64 else 0#64 := by
  by_cases h : b = 0
  · subst h; rw [ite_eq_left rfl]; decide
  · rw [ite_eq_right h]
    have h' : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
    have := b.isLt
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega)]
    exact Nat.div_eq_of_lt (by omega)

theorem posScan_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) {e db : Nat}
    (he : e + db ≤ oRsa) (hdb : 0 < db) (h24 : t.gpr .x24 = off S e) (h25 : t.gpr .x25 = BitVec.ofNat 64 db) :
    WP isa posScan t fun t' => Only [.x10, .x11, .x12, .x13, .x14, .x15, .x9, .x8, .x16, .x17] t t' ∧
      t'.gpr .x13 = (if nz (fun i => V (e + i)) db = none then BitVec.allOnes 64 else 0) ∧
      t'.gpr .x14 = BitVec.ofNat 64 ((nz (fun i => V (e + i)) db).getD 0) ∧
      t'.gpr .x15 = (nzV (fun i => V (e + i)) db).setWidth 64 := by
  have c6 : oRsa = 8192 := rfl
  unfold posScan
  refine WP.seq (WP.mono (Q := fun (u : State) => Only [.x10, .x11, .x12, .x13, .x14, .x15] t u ∧
      u.gpr .x10 = off S e ∧ u.gpr .x11 = 0#64 ∧ u.gpr .x12 = BitVec.ofNat 64 db ∧ u.gpr .x13 = BitVec.allOnes 64 ∧
      u.gpr .x14 = 0#64 ∧ u.gpr .x15 = 0#64) ?_ fun u ⟨O, h10, h11, h12, h13, h14, h15⟩ => ?_)
  · refine wp_mov fun u₁ o₁ e₁ => wp_movz fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ => wp_movz fun u₄ o₄ e₄ =>
      wp_subImm (by decide) fun u₅ o₅ e₅ => wp_movz fun u₆ o₆ e₆ => wp_movz fun u₇ o₇ e₇ => wp_nil
        ⟨(o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [o₇.get .x10, o₆.get .x10, o₅.get .x10, o₄.get .x10, o₃.get .x10, o₂.get .x10, e₁, h24]
    · rw [o₇.get .x11, o₆.get .x11, o₅.get .x11, o₄.get .x11, o₃.get .x11, e₂]; rfl
    · rw [o₇.get .x12, o₆.get .x12, o₅.get .x12, o₄.get .x12, e₃, o₂.get .x25, o₁.get .x25, h25]
    · rw [o₇.get .x13, o₆.get .x13, e₅, e₄]; rfl
    · rw [o₇.get .x14, e₆]; rfl
    · rw [e₇]; rfl
  have Ru : Rep u.mem S V := O.mem ▸ R
  have Lu : Lay u F S := L.congr O.sp O.wr (O.get .x20)
  refine WP.mono (wp_countdown (cnt := .x12) (N := db) (by omega) hdb
    (fun j v => Only [.x9, .x8, .x16, .x17, .x10, .x11, .x12, .x13, .x14, .x15] u v ∧
      v.gpr .x10 = off S (e + j) ∧ v.gpr .x11 = BitVec.ofNat 64 j ∧
      v.gpr .x13 = (if nz (fun i => V (e + i)) j = none then BitVec.allOnes 64 else 0) ∧
      v.gpr .x14 = BitVec.ofNat 64 ((nz (fun i => V (e + i)) j).getD 0) ∧
      v.gpr .x15 = (nzV (fun i => V (e + i)) j).setWidth 64)
    (fun j hj v ⟨hO, h10', h11', h13', h14', h15'⟩ _ => ?_)
    ⟨Only.refl _ _, by rw [Nat.add_zero, h10], h11, by rw [h13]; rfl, by rw [h14]; rfl, by rw [h15]; rfl⟩ h12)
    fun v ⟨hO, _, _, h13', h14', h15'⟩ => ⟨(O.trans hO).mono, h13', h14', h15'⟩
  refine wp_ldrb (by decide) (by rw [h10', BitVec.add_zero]) (by rw [hO.rd, hO.wr]; exact Lu.ld (by omega))
    fun w₁ q₁ g₁ => ?_
  refine wp_subImm (by decide) fun w₂ q₂ g₂ => wp_lsr (by decide) fun w₃ q₃ g₃ => wp_subImm (by decide) fun w₄ q₄ g₄ =>
    wp_and fun w₅ q₅ g₅ => wp_and fun w₆ q₆ g₆ => wp_orr fun w₇ q₇ g₇ => wp_and fun w₈ q₈ g₈ =>
    wp_orr fun w₉ q₉ g₉ => wp_movz fun w₁₀ q₁₀ g₁₀ => wp_sub fun w₁₁ q₁₁ g₁₁ => wp_and fun w₁₂ q₁₂ g₁₂ =>
    wp_addImm (by decide) fun w₁₃ q₁₃ g₁₃ => wp_addImm (by decide) fun w₁₄ q₁₄ g₁₄ =>
    wp_subImm (by decide) fun w₁₅ q₁₅ g₁₅ => wp_nil ?_
  have Q : Only [.x9, .x8, .x16, .x17, .x14, .x15, .x13, .x10, .x11, .x12] v w₁₅ :=
    (q₁.trans (q₂.trans (q₃.trans (q₄.trans (q₅.trans (q₆.trans (q₇.trans (q₈.trans (q₉.trans (q₁₀.trans
      (q₁₁.trans (q₁₂.trans (q₁₃.trans (q₁₄.trans q₁₅)))))))))))))).mono
  generalize hb : V (e + j) = b
  have v9 : w₁.gpr .x9 = b.setWidth 64 := by rw [g₁, hO.mem, Ru _ (by omega), hb]
  have v8 : w₃.gpr .x8 = if b = 0 then 1#64 else 0#64 := by rw [g₃, g₂, v9, zero_bit]
  have v16 : w₅.gpr .x16 = (w₃.gpr .x8 - BitVec.ofNat 64 1) &&& v.gpr .x13 := by
    rw [g₅, g₄, q₄.get .x13, q₃.get .x13, q₂.get .x13, q₁.get .x13]
  have v14 : w₁₅.gpr .x14 = v.gpr .x14 ||| (BitVec.ofNat 64 j &&& w₅.gpr .x16) := by
    rw [q₁₅.get .x14, q₁₄.get .x14, q₁₃.get .x14, q₁₂.get .x14, q₁₁.get .x14, q₁₀.get .x14, q₉.get .x14,
      q₈.get .x14, g₇, g₆, q₆.get .x14, q₅.get .x14, q₄.get .x14, q₃.get .x14, q₂.get .x14, q₁.get .x14,
      q₅.get .x11, q₄.get .x11, q₃.get .x11, q₂.get .x11, q₁.get .x11, h11']
  have v15 : w₁₅.gpr .x15 = v.gpr .x15 ||| (b.setWidth 64 &&& w₅.gpr .x16) := by
    rw [q₁₅.get .x15, q₁₄.get .x15, q₁₃.get .x15, q₁₂.get .x15, q₁₁.get .x15, q₁₀.get .x15, g₉, g₈,
      q₈.get .x15, q₇.get .x15, q₆.get .x15, q₅.get .x15, q₄.get .x15, q₃.get .x15, q₂.get .x15, q₁.get .x15,
      q₇.get .x9, q₆.get .x9, q₅.get .x9, q₄.get .x9, q₃.get .x9, q₂.get .x9, v9, q₇.get .x16, q₆.get .x16]
  have v13 : w₁₅.gpr .x13 = v.gpr .x13 &&& (0#64 - w₃.gpr .x8) := by
    rw [q₁₅.get .x13, q₁₄.get .x13, q₁₃.get .x13, g₁₂, q₁₁.get .x13, q₁₀.get .x13, q₉.get .x13, q₈.get .x13,
      q₇.get .x13, q₆.get .x13, q₅.get .x13, q₄.get .x13, q₃.get .x13, q₂.get .x13, q₁.get .x13, g₁₁, g₁₀,
      q₁₀.get .x8, q₉.get .x8, q₈.get .x8, q₇.get .x8, q₆.get .x8, q₅.get .x8, q₄.get .x8]
    rfl
  have x10 : w₁₅.gpr .x10 = off S (e + (j + 1)) := by
    rw [q₁₅.get .x10, q₁₄.get .x10, g₁₃, q₁₂.get .x10, q₁₁.get .x10, q₁₀.get .x10, q₉.get .x10, q₈.get .x10,
      q₇.get .x10, q₆.get .x10, q₅.get .x10, q₄.get .x10, q₃.get .x10, q₂.get .x10, q₁.get .x10, h10', off_add,
      Nat.add_assoc]
  have x11 : w₁₅.gpr .x11 = BitVec.ofNat 64 (j + 1) := by
    rw [q₁₅.get .x11, g₁₄, q₁₃.get .x11, q₁₂.get .x11, q₁₁.get .x11, q₁₀.get .x11, q₉.get .x11, q₈.get .x11,
      q₇.get .x11, q₆.get .x11, q₅.get .x11, q₄.get .x11, q₃.get .x11, q₂.get .x11, q₁.get .x11, h11',
      BitVec.ofNat_add_ofNat]
  have x12 : w₁₅.gpr .x12 = v.gpr .x12 - BitVec.ofNat 64 1 := by
    rw [g₁₅, q₁₄.get .x12, q₁₃.get .x12, q₁₂.get .x12, q₁₁.get .x12, q₁₀.get .x12, q₉.get .x12, q₈.get .x12,
      q₇.get .x12, q₆.get .x12, q₅.get .x12, q₄.get .x12, q₃.get .x12, q₂.get .x12, q₁.get .x12]
  suffices key : w₁₅.gpr .x13 = (if nz (fun i => V (e + i)) (j + 1) = none then BitVec.allOnes 64 else 0) ∧
      w₁₅.gpr .x14 = BitVec.ofNat 64 ((nz (fun i => V (e + i)) (j + 1)).getD 0) ∧
      w₁₅.gpr .x15 = (nzV (fun i => V (e + i)) (j + 1)).setWidth 64 from
    ⟨⟨(hO.trans Q).mono, x10, x11, key.1, key.2.1, key.2.2⟩, x12⟩
  have hS : ∀ i, nz (fun i => V (e + i)) j = some i → nz (fun i => V (e + i)) (j + 1) = some i := fun i h => by
    simp only [nz, h]
  have hN0 : nz (fun i => V (e + i)) j = none → b = 0 → nz (fun i => V (e + i)) (j + 1) = none := fun h h0 => by
    simp only [nz, h, hb, h0, ite_true]
  have hN1 : nz (fun i => V (e + i)) j = none → b ≠ 0 → nz (fun i => V (e + i)) (j + 1) = some j := fun h h0 => by
    simp only [nz, h, hb, h0, ite_false]
  have az : ∀ x : BitVec 64, x &&& 0 = 0 := fun x => by ext i; simp
  have za : ∀ x : BitVec 64, 0 &&& x = 0 := fun x => by ext i; simp
  have oz : ∀ x : BitVec 64, x ||| 0 = x := fun x => by ext i; simp
  have zo : ∀ x : BitVec 64, 0 ||| x = x := fun x => by ext i; simp
  have aa : ∀ x : BitVec 64, x &&& BitVec.allOnes 64 = x := fun x => BitVec.and_allOnes
  have hb0 : (1#64 - BitVec.ofNat 64 1) = 0 := rfl
  have hb1 : (0#64 - BitVec.ofNat 64 1) = BitVec.allOnes 64 := rfl
  by_cases hN : nz (fun i => V (e + i)) j = none
  · rw [hN, ite_eq_left rfl] at h13'
    rw [hN] at h14'
    have h15'' : v.gpr .x15 = 0 := by rw [h15']; simp only [nzV, hN]; rfl
    by_cases b0 : b = 0
    · have e1 := hN0 hN b0
      rw [v8, ite_eq_left b0] at v16
      rw [v16, hb0, za] at v14 v15
      refine ⟨by rw [v13, h13', v8, ite_eq_left b0, e1, ite_eq_left rfl]; rfl, by rw [v14, h14', az, oz, e1],
        by rw [v15, h15'', az, oz]; simp only [nzV, e1]; rfl⟩
    · have e1 := hN1 hN b0
      rw [v8, ite_eq_right b0, hb1, h13', aa] at v16
      rw [v16] at v14 v15
      refine ⟨by rw [v13, h13', v8, ite_eq_right b0, e1]; rfl, by rw [v14, h14', aa]; simp [e1],
        by rw [v15, h15'', aa, zo]; simp only [nzV, e1, hb]⟩
  · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hN
    have e1 := hS i hi
    rw [hi] at h13' h14'
    rw [h13', ite_eq_right (by simp), az] at v16
    rw [v16, az, oz] at v14 v15
    refine ⟨by rw [v13, h13', ite_eq_right (by simp), za, e1]; rfl, by rw [v14, h14', e1],
      by rw [v15, h15']; simp only [nzV, hi, e1]⟩

end VG.Proof.RsaPss.AArch64
