module

public import VerifiedGarbage.Proof.X25519.AArch64.Hybrid.Convert
public import VerifiedGarbage.Proof.X25519.AArch64.Hybrid.Carry
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# X25519 on AArch64: the products of `Neon.prod2`

Untrusted: everything here is checked by Lean. Row `i` multiplies limb `i` of
the first operands (its row at `FBUF`) by every limb of the second ones (`v0`–`v18`)
into the coefficients `v19`–`v28`; after `r` rows, lane `e` of coefficient `k` is
`rowsUpTo r k`, the first `r` terms of `prodCoef` (`products_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Hybrid

open VG VG.AArch64
open VG.Impl.X25519.AArch64.Neon
open VG.Proof.Ed25519.AArch64 (Scr off word Outside ofs)

/-- Term `i` of coefficient `k`, in lane `e`. -/
def term (F G : Nat → Nat → Nat) (e i k : Nat) : Nat := coef i (colOf i k) * F e i * G e (colOf i k)

/-- The first `r` terms of coefficient `k`, in lane `e`. -/
def rowsUpTo (F G : Nat → Nat → Nat) (e : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | r + 1, k => rowsUpTo F G e r k + term F G e r k

theorem rowsUpTo_10 (F G : Nat → Nat → Nat) (e k : Nat) : rowsUpTo F G e 10 k = prodCoef (F e) (G e) k := by
  simp only [rowsUpTo, prodCoef, S10, term, Nat.zero_add]

theorem rowsUpTo_mono (F G : Nat → Nat → Nat) (e k r : Nat) : ∀ d, rowsUpTo F G e r k ≤ rowsUpTo F G e (r + d) k
  | 0 => Nat.le_refl _
  | d + 1 => Nat.le_trans (rowsUpTo_mono F G e k r d) (Nat.le_add_right _ _)

theorem rowsUpTo_le (F G : Nat → Nat → Nat) (e k : Nat) {r : Nat} (hr : r ≤ 10) :
    rowsUpTo F G e r k ≤ rowsUpTo F G e 10 k := by
  have := rowsUpTo_mono F G e k r (10 - r)
  rwa [Nat.add_sub_cancel' hr] at this

theorem prodB_lt : ∀ k < 10, prodB k < 2 ^ 61 := by decide +kernel

/-- The coefficients after `r` rows: all of them, but only those before `k'` for the first row. -/
def AccIn (s : State) (F G : Nat → Nat → Nat) (r k' : Nat) : Prop :=
  ∀ k < 10, (k < k' ∨ 0 < r) → ∀ e < 2,
    (vdword (s.v (V (19 + k))) e).toNat = rowsUpTo F G e (r + if k < k' then 1 else 0) k

theorem gReg_val {s : State} {G : Nat → Nat → Nat} {i k : Nat} (hi : i < 10) (hg : GRegs s G 9) {c : Nat} (hc : c < 4) :
    (vword (s.v (V (gReg i k))) c).toNat = (if 10 ≤ i + colOf i k then 19 else 1) * G (c % 2) (colOf i k) := by
  have hj := colOf_lt i k
  have hg' : gReg i k = if 10 ≤ i + colOf i k then 9 + colOf i k else colOf i k := by
    unfold gReg colOf; rfl
  rw [hg']
  split
  · rename_i hw
    have h := hg.2 (colOf i k - 1) (by omega) c hc
    rw [show 10 + (colOf i k - 1) = 9 + colOf i k by omega, show colOf i k - 1 + 1 = colOf i k by omega] at h
    exact h
  · rw [Nat.one_mul]; exact hg.1 _ hj c hc

theorem doubled_eq (i k : Nat) : doubled i k = decide (i % 2 = 1 ∧ colOf i k % 2 = 1) := by
  unfold doubled colOf
  rw [Bool.decide_and, Bool.beq_eq_decide_eq, Bool.beq_eq_decide_eq]

theorem mac_val {s : State} {F G : Nat → Nat → Nat} {i k : Nat} (hi : i < 10)
    (hrow : ∀ c < 4, (vword (s.v (V 29)) c).toNat = rowWord F i c) (hg : GRegs s G 9) {e : Nat} (he : e < 2) :
    (vword (s.v (V 29)) ((if doubled i k then 2 else 0) + e)).toNat *
      (vword (s.v (V (gReg i k))) ((if doubled i k then 2 else 0) + e)).toNat = term F G e i k := by
  have hc : (if doubled i k then 2 else 0) + e < 4 := by split <;> omega
  have he2 : ((if doubled i k then 2 else 0) + e) % 2 = e := by split <;> omega
  rw [hrow _ hc, gReg_val hi hg hc, he2, rowWord, he2, term, coef, doubled_eq]
  by_cases h : i % 2 = 1 ∧ colOf i k % 2 = 1
  · simp only [h, decide_true, ↓reduceIte, and_true, show 2 ≤ 2 + e by omega]
    simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  · have : ¬ (2 ≤ 0 + e ∧ i % 2 = 1) := by omega
    simp only [h, this, decide_false, Bool.false_eq_true, ↓reduceIte]
    simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem lane_ofVDwords (f : Nat → BitVec 64) {e : Nat} (he : e < 2) :
    vdword (ofVDwords (f 0) (f 1)) e = f e := by
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
  · exact vdword_ofVDwords_0 _ _
  · exact vdword_ofVDwords_1 _ _

theorem mac_ok {s : State} {F G : Nat → Nat → Nat} {i k : Nat} (hi : i < 10) (hk : k < 10)
    (hrow : ∀ c < 4, (vword (s.v (V 29)) c).toNat = rowWord F i c) (hg : GRegs s G 9)
    (hacc : AccIn s F G i k) (hb : ∀ e < 2, rowsUpTo F G e (i + 1) k < 2 ^ 64) :
    WP isa (.block [if i = 0 then vo (.umull false (V (19 + k)) (V 29) (V (gReg i k)))
      else vo (.umlal (doubled i k) (V (19 + k)) (V 29) (V (gReg i k)))]) s fun t =>
      AccIn t F G i (k + 1) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.flags = s.flags ∧ ∀ r, r ≠ V (19 + k) → t.v r = s.v r := by
  have old : ∀ k₀ < 10, k₀ ≠ k → (k₀ < k + 1 ∨ 0 < i) → ∀ e < 2, ∀ x : BitVec 128,
      (vdword ((s.setV (V (19 + k)) x).v (V (19 + k₀))) e).toNat =
        rowsUpTo F G e (i + if k₀ < k + 1 then 1 else 0) k₀ := by
    intro k₀ hk₀ hne hc e he x
    have hv : V (19 + k₀) ≠ V (19 + k) := V_ne _ (by omega) _ (by omega) (by omega)
    have hc' : k₀ < k ∨ 0 < i := by omega
    rw [RegUpd.v_setV_of_ne _ _ hv, hacc k₀ hk₀ hc' e he]
    congr 2
    split <;> split <;> omega
  split
  · rename_i h0
    subst h0
    have hd : doubled 0 k = false := by simp [doubled]
    refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
    refine WP.block_nil_iff.mpr ?_
    simp only [RegUpd.mem_setV, RegUpd.gpr_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.sp_setV, flags_setV,
      true_and]
    refine ⟨fun k₀ hk₀ hc e he => ?_, fun r h => RegUpd.v_setV_of_ne _ _ h⟩
    by_cases hkk : k₀ = k
    · subst hkk
      rw [RegUpd.v_setV_self, lane_ofVDwords (fun e => BitVec.setWidth 64 (vword (s.v (V 29)) ((if false = true then 2 else 0) + e)) *
                  BitVec.setWidth 64 (vword (s.v (V (gReg 0 k₀))) ((if false = true then 2 else 0) + e))) he,
        VG.Proof.Curve448.AArch64.Neon.umull_lane, ← hd, mac_val hi hrow hg he]
      simp only [Nat.lt_succ_self, ↓reduceIte, Nat.zero_add, rowsUpTo]
    · exact old k₀ hk₀ hkk hc e he _
  · rename_i h0
    refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
    refine WP.block_nil_iff.mpr ?_
    simp only [RegUpd.mem_setV, RegUpd.gpr_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.sp_setV, flags_setV,
      true_and]
    refine ⟨fun k₀ hk₀ hc e he => ?_, fun r h => RegUpd.v_setV_of_ne _ _ h⟩
    by_cases hkk : k₀ = k
    · subst hkk
      rw [RegUpd.v_setV_self, lane_ofVDwords (fun e => vdword (s.v (V (19 + k₀))) e +
          BitVec.setWidth 64 (vword (s.v (V 29)) ((if doubled i k₀ = true then 2 else 0) + e)) *
            BitVec.setWidth 64 (vword (s.v (V (gReg i k₀))) ((if doubled i k₀ = true then 2 else 0) + e))) he,
        VG.Proof.Curve448.AArch64.Neon.umlal_lane, mac_val hi hrow hg he,
        hacc k₀ hk₀ (Or.inr (Nat.pos_of_ne_zero h0)) e he]
      simp only [Nat.lt_irrefl, Nat.lt_succ_self, ↓reduceIte, Nat.add_zero]
      rw [rowsUpTo]
      exact Nat.mod_eq_of_lt (hb e he)
    · exact old k₀ hk₀ hkk hc e he _

theorem row_eq (i : Nat) : row i = ldq 29 (FBUF + 16 * i) :: (List.range 10).flatMap fun k =>
    [if i = 0 then vo (.umull false (V (19 + k)) (V 29) (V (gReg i k)))
     else vo (.umlal (doubled i k) (V (19 + k)) (V 29) (V (gReg i k)))] := rfl

theorem row_ok {s : State} {base : Addr} {F G : Nat → Nat → Nat} (hs : Scratch s base) {i : Nat} (hi : i < 10)
    (hf : FRows s.mem base F 10) (hg : GRegs s G 9) (hacc : AccIn s F G i 0)
    (hb : ∀ e < 2, ∀ k < 10, rowsUpTo F G e (i + 1) k < 2 ^ 64) :
    WP isa (.block (row i)) s fun t =>
      AccIn t F G (i + 1) 0 ∧ GRegs t G 9 ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.flags = s.flags := by
  have hd : (FBUF + 16 * i) % 16 = 0 := by simp only [FBUF]; omega
  have hd' : FBUF + 16 * i + 16 ≤ 4096 := by simp only [FBUF]; omega
  rw [row_eq]
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq hs 29 hd hd', ?_⟩
  have hrow : ∀ c < 4, (vword ((s.setV (V 29) (s.mem.read (off base (FBUF + 16 * i)) 16)).v (V 29)) c).toNat =
      rowWord F i c := fun c hc => by
    rw [RegUpd.v_setV_self, vword_ld _ _ _ hc]; exact hf i hi c hc
  have hg1 : GRegs (s.setV (V 29) (s.mem.read (off base (FBUF + 16 * i)) 16)) G 9 :=
    ⟨fun j hj c hc => by rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by decide) (by omega))]; exact hg.1 j hj c hc,
     fun j hj c hc => by rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by decide) (by omega))]; exact hg.2 j hj c hc⟩
  have ha1 : AccIn (s.setV (V 29) (s.mem.read (off base (FBUF + 16 * i)) 16)) F G i 0 := fun k hk hc e he => by
    rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by decide) (by omega))]; exact hacc k hk hc e he
  have m1 : (s.setV (V 29) (s.mem.read (off base (FBUF + 16 * i)) 16)).mem = s.mem := rfl
  have g1 : (s.setV (V 29) (s.mem.read (off base (FBUF + 16 * i)) 16)).gpr = s.gpr := rfl
  have r1 : (s.setV (V 29) (s.mem.read (off base (FBUF + 16 * i)) 16)).rd = s.rd := rfl
  have w1 : (s.setV (V 29) (s.mem.read (off base (FBUF + 16 * i)) 16)).wr = s.wr := rfl
  have sp1 : (s.setV (V 29) (s.mem.read (off base (FBUF + 16 * i)) 16)).sp = s.sp := rfl
  have f1 : (s.setV (V 29) (s.mem.read (off base (FBUF + 16 * i)) 16)).flags = s.flags := rfl
  generalize s.setV (V 29) (s.mem.read (off base (FBUF + 16 * i)) 16) = s₁ at hrow hg1 ha1 m1 g1 r1 w1 sp1 f1
  let inv := fun k (x : State) =>
    AccIn x F G i k ∧ (∀ c < 4, (vword (x.v (V 29)) c).toNat = rowWord F i c) ∧ GRegs x G 9 ∧
    x.mem = s.mem ∧ x.gpr = s.gpr ∧ x.rd = s.rd ∧ x.wr = s.wr ∧ x.sp = s.sp ∧ x.flags = s.flags
  refine WP.mono (wp_range_flatMap (M := isa) (N := 10) inv
    (fun k x hk ⟨xa, xr, xg, xm, xgg, xrd, xw, xsp, xf⟩ => ?_) 10 (by decide) s₁
    ⟨ha1, hrow, hg1, m1, g1, r1, w1, sp1, f1⟩) fun x ⟨xa, _, xg, xm, xgg, xrd, xw, xsp, xf⟩ =>
      ⟨fun k hk _ e he => by
        have := xa k hk (Or.inl hk) e he
        simp only [hk, ↓reduceIte] at this ⊢
        rw [this]; rfl, xg, xm, xgg, xrd, xw, xsp, xf⟩
  refine WP.mono (mac_ok hi hk xr xg xa (fun e he => hb e he k hk)) fun y ⟨ya, ym, yg, yr, yw, ysp, yf, yv⟩ =>
    ⟨ya, fun c hc => by rw [yv _ (V_ne _ (by decide) _ (by omega) (by omega))]; exact xr c hc,
     ⟨fun j hj c hc => by rw [yv _ (V_ne _ (by omega) _ (by omega) (by omega))]; exact xg.1 j hj c hc,
      fun j hj c hc => by rw [yv _ (V_ne _ (by omega) _ (by omega) (by omega))]; exact xg.2 j hj c hc⟩,
     ym.trans xm, yg.trans xgg, yr.trans xrd, yw.trans xw, ysp.trans xsp, yf.trans xf⟩


/-- All the rows: lane `e` of coefficient `k` is `prodCoef (F e) (G e) k`. -/
theorem products_ok {s : State} {base : Addr} {F G : Nat → Nat → Nat} (hs : Scratch s base)
    (hf : FRows s.mem base F 10) (hg : GRegs s G 9) (hF : ∀ e i, F e i ≤ maxLimb i) (hG : ∀ e i, G e i ≤ maxLimb i) :
    WP isa (.block products) s fun t =>
      (∀ k < 10, ∀ e < 2, (vdword (t.v (V (19 + k))) e).toNat = prodCoef (F e) (G e) k) ∧
      t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.flags = s.flags := by
  let inv := fun r (x : State) =>
    AccIn x F G r 0 ∧ GRegs x G 9 ∧ x.mem = s.mem ∧ x.gpr = s.gpr ∧ x.rd = s.rd ∧ x.wr = s.wr ∧ x.sp = s.sp ∧
    x.flags = s.flags
  refine WP.mono (wp_range_flatMap (M := isa) (N := 10) inv
    (fun i x hi ⟨xa, xg, xm, xgg, xrd, xw, xsp, xf⟩ => ?_) 10 (by decide) s
    ⟨fun _ _ h => absurd h (by omega), hg, rfl, rfl, rfl, rfl, rfl, rfl⟩)
    fun x ⟨xa, _, xm, xgg, xrd, xw, xsp, xf⟩ => ⟨fun k hk e he => ?_, xm, xgg, xrd, xw, xsp, xf⟩
  · have hx : Scratch x base := scratch_of hs xgg xw
    refine WP.mono (row_ok hx hi (by rw [xm]; exact hf) xg xa fun e he k hk => ?_) fun y hy => hy.elim
      fun ya ⟨yg, ym, yrest⟩ => ⟨ya, yg, ym.trans xm, ?_⟩
    · have h1 := rowsUpTo_le F G e k (r := i + 1) (by omega)
      rw [rowsUpTo_10] at h1
      have h2 := prodCoef_le (f := F e) (g := G e) (fun i _ => hF e i) (fun i _ => hG e i) k
      have h3 := prodB_lt k hk
      omega
    · obtain ⟨yg', yr, yw, ysp, yf⟩ := yrest
      exact ⟨yg'.trans xgg, yr.trans xrd, yw.trans xw, ysp.trans xsp, yf.trans xf⟩
  · have := xa k hk (Or.inr (by decide)) e he
    simp only [Nat.not_lt_zero, ↓reduceIte, Nat.add_zero, rowsUpTo_10] at this
    exact this

end VG.Proof.X25519.AArch64.Hybrid
