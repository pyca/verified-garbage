import VerifiedGarbage.Proof.X25519.X86_64.Divstep.ARow
import VerifiedGarbage.Proof.Divstep.Iter
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Divstep.Packed
import VerifiedGarbage.Proof.Ed25519.Group.Extended

/-!
# X25519 on x86-64, inversion by divsteps: the theory

`byAlg x = x^(p-2)` (`instance : DivstepInv`): a batch's rows are the exact
`(u f + v g) / 2⁵⁹` (`fRowV_eq`) and `u a + v b` modulo `p` (`aRowV_cong`),
given the bounds of 59 divsteps' matrix; so each batch keeps `f`, `g` those of
`Proof/Divstep/`'s `divsteps` and `2^(59 i) f ≡ x a`, `2^(59 i) g ≡ x b`
modulo `p` (`run_inv`); after 590 divsteps `g = 0` and `f = ±1`
(`divsteps_590`), so `a (±2⁻⁵⁹⁰) ≡ x⁻¹`, which is `x^(p-2)` as `p` is prime.

This module imports Mathlib's algebra: only the registration files import it.
-/

namespace VG.Proof.X25519.X86_64

open VG.Spec.X25519 VG.Proof.X25519

/-! ## The rows -/

/-- Four words as a number in two's complement. -/
def sv (X : Nat) : Int := if X < 2 ^ 255 then X else X - 2 ^ 256

theorem toInt_neg {m : BitVec 64} (h : m.msb = true) : m.toInt = -(absN m : Int) := by
  unfold absN
  have e := BitVec.toInt_eq_msb_cond m
  rw [h] at e
  simp only [↓reduceIte] at e
  have := m.isLt
  have := Int.natAbs_eq m.toInt
  omega

theorem toInt_pos {m : BitVec 64} (h : m.msb = false) : m.toInt = (absN m : Int) := by
  unfold absN
  have e := BitVec.toInt_eq_msb_cond m
  rw [h] at e
  simp only [Bool.false_eq_true, ↓reduceIte] at e
  have := Int.natAbs_eq m.toInt
  omega

/-- One product of a row of `f` and `g`. -/
theorem fterm (m : BitVec 64) {X : Nat} (hX : X < 2 ^ 256) :
    ((absN m * flipN m X + negN m : Nat) : Int) - 2 ^ 256 * (topN m X : Int) = m.toInt * sv X := by
  unfold topN
  unfold flipN negN sv
  cases hm : m.msb
  · rw [toInt_pos hm]
    by_cases hx : X < 2 ^ 255
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, hx, show ¬ 2 ^ 255 ≤ X by omega]
      push_cast; ring
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, hx, show 2 ^ 255 ≤ X by omega]
      push_cast; ring
  · rw [toInt_neg hm]
    have e : ((2 ^ 256 - 1 - X : Nat) : Int) = 2 ^ 256 - 1 - (X : Int) := by omega
    by_cases hx : X < 2 ^ 255
    · simp only [↓reduceIte, hx, show 2 ^ 255 ≤ 2 ^ 256 - 1 - X by omega]
      rw [Nat.cast_add, Nat.cast_mul, e]; push_cast; ring
    · simp only [↓reduceIte, hx, show ¬ 2 ^ 255 ≤ 2 ^ 256 - 1 - X by omega]
      rw [Nat.cast_add, Nat.cast_mul, e]; push_cast; ring

theorem shift_mod (Z k M D : Int) (hD : D ≠ 0) : (Z + k * M * D) / D % M = Z / D % M := by
  rw [Int.add_mul_ediv_right _ _ hD, Int.add_mul_emod_self_right]

theorem negN_le (m : BitVec 64) : negN m ≤ absN m := by unfold negN; split <;> omega

/-- A row of `f` and `g` is `(m₁ X + m₂ Y) / 2⁵⁹` modulo `2²⁵⁶`, if the corrections
`|m|` of the negative `m` do not overflow a word. -/
theorem fRowV_eq (m₁ m₂ : BitVec 64) {X Y : Nat} (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256)
    (hc : negN m₁ + negN m₂ < 2 ^ 64) :
    (fRowV m₁ m₂ X Y : Int) = (m₁.toInt * sv X + m₂.toInt * sv Y) / 2 ^ 59 % 2 ^ 256 := by
  unfold fRowV cN
  rw [Nat.mod_eq_of_lt hc]
  have t1 := topN_le m₁ X; have t2 := topN_le m₂ Y
  have e1 := fterm m₁ hX; have e2 := fterm m₂ hY
  have hN : ((absN m₁ * flipN m₁ X + absN m₂ * flipN m₂ Y + (negN m₁ + negN m₂) +
      (2 ^ 256 * 2 ^ 65 - 2 ^ 256 * (topN m₁ X + topN m₂ Y)) : Nat) : Int) =
      (m₁.toInt * sv X + m₂.toInt * sv Y) + (2 ^ 6 * 2 ^ 256) * 2 ^ 59 := by
    push_cast at e1 e2 ⊢
    rw [Nat.cast_sub (by omega)]
    push_cast
    linear_combination e1 + e2
  rw [Int.natCast_emod, Int.natCast_ediv, hN]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact shift_mod _ _ _ _ (by norm_num)

theorem P_val : (P : Int) = 2 ^ 255 - 19 := by simp [P]

/-- One product of a row of `a` and `b`, modulo `p`. -/
theorem aterm (m : BitVec 64) {A : Nat} (hA : A < 2 ^ 256) :
    ((absN m * flipN m A : Nat) : Int) - 37 * (negN m : Int) ≡ m.toInt * A [ZMOD P] := by
  unfold flipN negN
  cases hm : m.msb
  · rw [toInt_pos hm]; simp only [Bool.false_eq_true, ↓reduceIte]; push_cast; ring_nf; rfl
  · rw [toInt_neg hm]
    simp only [↓reduceIte]
    have e : ((2 ^ 256 - 1 - A : Nat) : Int) = 2 ^ 256 - 1 - (A : Int) := by omega
    rw [Nat.cast_mul, e, Int.modEq_iff_dvd, P_val]
    exact ⟨-(2 * (absN m : Int)), by ring⟩

/-- `foldV Q c` is `Q - 37 c` modulo `p`, below `2²⁵⁶`. -/
theorem foldV_cong {Q c : Nat} (hQ : Q < 2 ^ 256 * 2 ^ 64) (hc : c < 2 ^ 64) :
    (foldV Q c : Int) ≡ Q - 37 * c [ZMOD P] ∧ foldV Q c < 2 ^ 256 := by
  unfold foldV
  have hq := Nat.div_add_mod Q (2 ^ 256)
  have q4 : Q / 2 ^ 256 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [Nat.mul_comm]; exact hQ
  have lo := Nat.mod_lt Q (show 2 ^ 256 > 0 by positivity)
  generalize Q / 2 ^ 256 = h at hq q4
  generalize Q % 2 ^ 256 = l at hq lo
  subst hq
  dsimp only
  rw [Int.modEq_iff_dvd, P_val]
  split
  · refine ⟨⟨2 * ((h : Int) - 1), by omega⟩, by omega⟩
  · split
    · refine ⟨⟨2 * (h : Int), by omega⟩, by omega⟩
    · refine ⟨⟨2 * ((h : Int) + 1), by omega⟩, by omega⟩

/-- A row of `a` and `b` is `m₁ A + m₂ B` modulo `p`, below `2²⁵⁶`, if the
corrections do not overflow a word. -/
theorem aRowV_cong (m₁ m₂ : BitVec 64) {A B : Nat} (hA : A < 2 ^ 256) (hB : B < 2 ^ 256)
    (hc : negN m₁ + negN m₂ < 2 ^ 64) :
    (aRowV m₁ m₂ A B : Int) ≡ m₁.toInt * A + m₂.toInt * B [ZMOD P] ∧ aRowV m₁ m₂ A B < 2 ^ 256 := by
  unfold aRowV cN
  rw [Nat.mod_eq_of_lt hc]
  have p1 := prodN_le m₁ hA; have p2 := prodN_le m₂ hB
  obtain ⟨h1, h2⟩ := foldV_cong (Q := absN m₁ * flipN m₁ A + absN m₂ * flipN m₂ B) (by omega) hc
  refine ⟨h1.trans ?_, h2⟩
  have := (aterm m₁ hA).add (aterm m₂ hB)
  push_cast at this ⊢
  convert this using 1
  ring

/-! ## The batches -/

open VG.Proof.Divstep

/-- The divsteps' `(d, f, g)` after `i` batches from `x`. -/
def dsI (x : Nat) (i : Nat) : Int × Int × Int := divsteps (59 * i) (1, P, x)

/-- What `drun x i` holds: `d`, and `f`, `g` in two's complement, of `dsI`,
and `a`, `b` with `2^(59 i) f ≡ x a`, `2^(59 i) g ≡ x b` modulo `p` (and
`a ≡ 0` for `x = 0`). -/
structure RInv (x : Nat) (i : Nat) (t : DSt) : Prop where
  D : t.D = BitVec.ofInt 64 (dsI x i).1
  f : (t.f : Int) = (dsI x i).2.1 % 2 ^ 256
  g : (t.g : Int) = (dsI x i).2.2 % 2 ^ 256
  fl : t.f < 2 ^ 256
  gl : t.g < 2 ^ 256
  al : t.a < 2 ^ 256
  bl : t.b < 2 ^ 256
  ca : 2 ^ (59 * i) * (dsI x i).2.1 ≡ x * t.a [ZMOD P]
  cb : 2 ^ (59 * i) * (dsI x i).2.2 ≡ x * t.b [ZMOD P]
  z : x = 0 → (t.a : Int) ≡ 0 [ZMOD P]

theorem P_odd : (P : Int) % 2 = 1 := by rw [P_val]; norm_num

theorem dsI_odd (x i : Nat) : (dsI x i).1 % 2 = 1 ∧ (dsI x i).2.1 % 2 = 1 :=
  divsteps_odd (by decide) P_odd _

theorem dsI_le {x : Nat} (hx : x < P) (i : Nat) : |(dsI x i).2.1| ≤ P ∧ |(dsI x i).2.2| ≤ P :=
  divsteps_le (by decide) P_odd (by rw [abs_of_nonneg (by positivity)]) (by
    rw [abs_of_nonneg (by positivity)]; exact_mod_cast hx.le) _

theorem dsI_d (x i : Nat) : |(dsI x i).1| ≤ 1 + 2 * (59 * i) := by
  have := divsteps_d (1, (P : Int), (x : Int)) (59 * i)
  simp only [abs_one] at this
  exact_mod_cast this

theorem dsI_succ (x i : Nat) : dsI x (i + 1) = divsteps 59 (dsI x i) := by
  unfold dsI; rw [show 59 * (i + 1) = 59 * i + 59 by ring, divsteps_add]

theorem P_lt : (P : Int) < 2 ^ 255 := by rw [P_val]; norm_num

/-- Two's complement of a number at most `p`. -/
theorem sv_rep {f : Int} (hf : |f| ≤ P) {X : Nat} (hX : (X : Int) = f % 2 ^ 256) : sv X = f := by
  have := P_lt
  rw [abs_le] at hf
  unfold sv
  split <;> omega

theorem toInt_eq_of_abs {u : Int} (h : |u| ≤ 2 ^ 59) : (BitVec.ofInt 64 u).toInt = u := toInt_small h

theorem absN_ofInt {u : Int} (h : |u| ≤ 2 ^ 59) : (absN (BitVec.ofInt 64 u) : Int) = |u| := by
  unfold absN; rw [toInt_small h]; exact Int.natCast_natAbs u

theorem negN_ofInt_le {u : Int} (h : |u| ≤ 2 ^ 59) : (negN (BitVec.ofInt 64 u) : Int) ≤ |u| := by
  have := negN_le (BitVec.ofInt 64 u)
  rw [← absN_ofInt h]; exact_mod_cast this

theorem ofNat_rel64 {X : Nat} {f : Int} (hX : (X : Int) = f % 2 ^ 256) :
    ((BitVec.ofNat 64 X).toNat : Int) % 2 ^ 64 = f % 2 ^ 64 := by
  rw [BitVec.toNat_ofNat]
  push_cast
  rw [Int.emod_emod_of_dvd _ (by norm_num), hX, Int.emod_emod_of_dvd _ (by norm_num)]

/-! ## The packed divsteps

`pkBatchV`'s chunks are `msteps` (`pkChunkV_rel`, as `pchunk_ok` in
`Proof/Weierstrass/X86_64/InvPacked.lean` for the same code), so the batch's
words are those of 59 divsteps (`pkBatchV_rel`). -/

/-- A chunk's words for the batch's state `T` so far: `~d`, the low words of
`f` and `g` modulo `2^K`, and (but for the first chunk, whose `T` has the
identity) the matrix. -/
structure PkAt (K : Nat) (first : Bool) (T : MSt) (w : PkSt) : Prop where
  E : w.E = ~~~BitVec.ofInt 64 T.d
  F : (w.F.toNat : Int) % 2 ^ K = T.f % 2 ^ K
  G : (w.G.toNat : Int) % 2 ^ K = T.g % 2 ^ K
  id : first = true → T.u = 1 ∧ T.v = 0 ∧ T.q = 0 ∧ T.r = 1
  mat : first = false → w.U = BitVec.ofInt 64 T.u ∧ w.V = BitVec.ofInt 64 T.v ∧
    w.Q = BitVec.ofInt 64 T.q ∧ w.R = BitVec.ofInt 64 T.r

theorem pk_c31 : (2 ^ 31 : BitVec 64) = BitVec.ofInt 64 (2 ^ 31) := by decide
theorem pk_c47 : (2 ^ 47 : BitVec 64) = BitVec.ofInt 64 (2 ^ 47) := by decide

/-- A row's start as an integer: the low 15 bits, plus a constant. -/
theorem pk_set_int (w c : BitVec 64) {C : Int} (hc : c = BitVec.ofInt 64 C) :
    (w &&& 0x7fff) + c = BitVec.ofInt 64 (((w.toNat % 2 ^ 15 : Nat) : Int) + C) := by
  have h : (w &&& 0x7fff) = BitVec.ofNat 64 (w.toNat % 2 ^ 15) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (0x7fff : BitVec 64).toNat = 2 ^ 15 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by decide)) (by decide))]
  rw [h, hc, BitVec.ofInt_add, BitVec.ofInt_natCast]

/-- A row's start is congruent to the low word modulo `2^n`, `n ≤ 15`. -/
theorem pk_row_mod {w : BitVec 64} {F : Int} {K n k : Nat} (hn : n ≤ 15) (hK : n ≤ K) (hk : 15 ≤ k)
    (h : (w.toNat : Int) % 2 ^ K = F % 2 ^ K) :
    (((w.toNat % 2 ^ 15 : Nat) : Int) + 2 ^ k) % 2 ^ n = F % 2 ^ n := by
  have d1 : (2 : Int) ^ n ∣ 2 ^ 15 := pow_dvd_pow 2 hn
  have d2 : (2 : Int) ^ n ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
  have d3 : (2 : Int) ^ n ∣ 2 ^ K := pow_dvd_pow 2 hK
  rw [Int.natCast_mod, Nat.cast_pow, Nat.cast_ofNat, Int.add_emod, Int.emod_eq_zero_of_dvd d2, add_zero,
    Int.emod_emod_of_dvd _ d1, Int.emod_emod, ← Int.emod_emod_of_dvd _ d3, h, Int.emod_emod_of_dvd _ d3]

/-- A chunk of `n` steps from the batch's state `T` so far: `T`'s `n` steps. -/
theorem pkChunkV_rel {n K : Nat} {first last : Bool} (hn : 1 ≤ n ∧ n ≤ 15) (hK : n ≤ K ∧ K ≤ 64)
    {T : MSt} {w : PkSt} (hf : T.f % 2 = 1) (hd : |T.d| + 2 * n < 2 ^ 62) (hI : PkAt K first T w) :
    (pkChunkV n first last w).E = ~~~BitVec.ofInt 64 (msteps n T).d ∧
    (pkChunkV n first last w).U = BitVec.ofInt 64 (msteps n T).u ∧
    (pkChunkV n first last w).V = BitVec.ofInt 64 (msteps n T).v ∧
    (pkChunkV n first last w).Q = BitVec.ofInt 64 (msteps n T).q ∧
    (pkChunkV n first last w).R = BitVec.ofInt 64 (msteps n T).r ∧
    (last = false → (((pkChunkV n first last w).F.toNat : Int) % 2 ^ (K - n) = (msteps n T).f % 2 ^ (K - n) ∧
      ((pkChunkV n first last w).G.toNat : Int) % 2 ^ (K - n) = (msteps n T).g % 2 ^ (K - n))) := by
  have hmat := msteps_mat (d := T.d) (g := T.g) hf n
  have bnd := msteps_bnd T.d T.f T.g n
  have lo := msteps_lo T.d T.f T.g n
  have hrel := psteps_rel (d := T.d) (f := T.f) (g := T.g)
    (P := ((w.F.toNat % 2 ^ 15 : Nat) : Int) + 2 ^ 31)
    (Q := ((w.G.toNat % 2 ^ 15 : Nat) : Int) + 2 ^ 47) (n := n) (by omega) hf hd
    (pk_row_mod hn.2 hK.1 (by norm_num) hI.F) (pk_row_mod hn.2 hK.1 (by norm_num) hI.G) n le_rfl
  rw [msteps_gen n T]
  simp only
  set m := msteps n (MSt.init T.d T.f T.g) with hm
  have p15 : (2 : Int) ^ n ≤ 2 ^ 15 := pow_le_pow_right₀ (by norm_num) hn.2
  have ha : w.F.toNat % 2 ^ 15 < 2 ^ 15 := Nat.mod_lt _ (by norm_num)
  have hb : w.G.toNat % 2 ^ 15 < 2 ^ 15 := Nat.mod_lt _ (by norm_num)
  obtain ⟨eu, ev⟩ := pext_rel ha hb (u := m.u) (v := m.v) (by linarith [lo.1]) (by linarith [lo.2.1])
    (by linarith [bnd.1])
  obtain ⟨eq, er⟩ := pext_rel ha hb (u := m.q) (v := m.r) (by linarith [lo.2.2.1])
    (by linarith [lo.2.2.2.1]) (by linarith [bnd.2])
  have hps : Divstep.psteps n (w.E, (w.F &&& 0x7fff) + 2 ^ 31, (w.G &&& 0x7fff) + 2 ^ 47) =
      (~~~BitVec.ofInt 64 m.d,
        BitVec.ofInt 64 (m.u * (((w.F.toNat % 2 ^ 15 : Nat) : Int) + 2 ^ 31) +
          m.v * (((w.G.toNat % 2 ^ 15 : Nat) : Int) + 2 ^ 47)),
        BitVec.ofInt 64 (m.q * (((w.F.toNat % 2 ^ 15 : Nat) : Int) + 2 ^ 31) +
          m.r * (((w.G.toNat % 2 ^ 15 : Nat) : Int) + 2 ^ 47))) := by
    rw [pk_set_int _ _ pk_c31, pk_set_int _ _ pk_c47, hI.E]; exact hrel
  unfold pkChunkV
  rw [hps]
  simp only [eu, ev, eq, er]
  have lowF : last = false → (((if last = true then w.F else
      (w.G * BitVec.ofInt 64 m.v + w.F * BitVec.ofInt 64 m.u) >>> n).toNat : Int) % 2 ^ (K - n) =
        m.f % 2 ^ (K - n)) := fun h => by
    rw [h]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [add_comm]; exact low_upd hK.2 hK.1 hI.F hI.G hmat.1
  have lowG : last = false → (((if last = true then w.G else
      (w.G * BitVec.ofInt 64 m.r + w.F * BitVec.ofInt 64 m.q) >>> n).toNat : Int) % 2 ^ (K - n) =
        m.g % 2 ^ (K - n)) := fun h => by
    rw [h]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [add_comm]; exact low_upd hK.2 hK.1 hI.F hI.G hmat.2
  cases first
  · obtain ⟨m9, m10, m11, m12⟩ := hI.mat rfl
    simp only [Bool.false_eq_true, ↓reduceIte, m9, m10, m11, m12]
    refine ⟨trivial, ?_, ?_, ?_, ?_, fun h => ⟨lowF h, lowG h⟩⟩
    · rw [← BitVec.ofInt_mul, ← BitVec.ofInt_mul, ← BitVec.ofInt_add]
    · rw [← BitVec.ofInt_mul, ← BitVec.ofInt_mul, ← BitVec.ofInt_add]
    · rw [← BitVec.ofInt_mul, ← BitVec.ofInt_mul, ← BitVec.ofInt_add, add_comm]
    · rw [← BitVec.ofInt_mul, ← BitVec.ofInt_mul, ← BitVec.ofInt_add, add_comm]
  · obtain ⟨i1, i2, i3, i4⟩ := hI.id rfl
    simp only [↓reduceIte, i1, i2, i3, i4, mul_one, mul_zero, add_zero, zero_add]
    exact ⟨trivial, trivial, trivial, trivial, trivial, fun h => ⟨lowF h, lowG h⟩⟩

/-- A batch's packed divsteps are 59 divsteps, from `d` small, `f` odd and the
low words of `f` and `g`. -/
theorem pkBatchV_rel {d f g : Int} {D F G : BitVec 64} (hD : D = BitVec.ofInt 64 d)
    (hF : (F.toNat : Int) % 2 ^ 64 = f % 2 ^ 64) (hG : (G.toNat : Int) % 2 ^ 64 = g % 2 ^ 64)
    (hf : f % 2 = 1) (hd : |d| ≤ 2 ^ 30) :
    ~~~(pkBatchV D F G).E = BitVec.ofInt 64 (msteps 59 (MSt.init d f g)).d ∧
    (pkBatchV D F G).U = BitVec.ofInt 64 (msteps 59 (MSt.init d f g)).u ∧
    (pkBatchV D F G).V = BitVec.ofInt 64 (msteps 59 (MSt.init d f g)).v ∧
    (pkBatchV D F G).Q = BitVec.ofInt 64 (msteps 59 (MSt.init d f g)).q ∧
    (pkBatchV D F G).R = BitVec.ofInt 64 (msteps 59 (MSt.init d f g)).r := by
  set T0 := MSt.init d f g with hT0
  have f0 : T0.f % 2 = 1 := hf
  have odd : ∀ k, (msteps k T0).f % 2 = 1 := msteps_f_odd f0
  have dd : ∀ k, |(msteps k T0).d| ≤ 2 ^ 30 + 2 * k := fun k => by
    have := msteps_d T0 k
    rw [show T0.d = d from rfl] at this
    linarith
  unfold pkBatchV
  obtain ⟨d₂, u₂, v₂, q₂, r₂, w₂⟩ := pkChunkV_rel (n := 15) (K := 64) (first := true) (last := false)
    (T := T0) (w := ⟨~~~D, F, G, 0, 0, 0, 0⟩) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ f0
    (by rw [show T0.d = d from rfl]; push_cast; linarith)
    ⟨show ~~~D = ~~~BitVec.ofInt 64 d by rw [hD], hF, hG, fun _ => ⟨rfl, rfl, rfl, rfl⟩,
      fun h => absurd h (by decide)⟩
  obtain ⟨f₂, g₂⟩ := w₂ rfl
  obtain ⟨d₃, u₃, v₃, q₃, r₃, w₃⟩ := pkChunkV_rel (n := 15) (K := 49) (first := false) (last := false)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (odd 15) (by have := dd 15; norm_num at this ⊢; linarith)
    ⟨d₂, f₂, g₂, fun h => absurd h (by decide), fun _ => ⟨u₂, v₂, q₂, r₂⟩⟩
  obtain ⟨f₃, g₃⟩ := w₃ rfl
  rw [← msteps_add] at d₃ u₃ v₃ q₃ r₃ f₃ g₃
  obtain ⟨d₄, u₄, v₄, q₄, r₄, w₄⟩ := pkChunkV_rel (n := 15) (K := 34) (first := false) (last := false)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (odd 30) (by have := dd 30; norm_num at this ⊢; linarith)
    ⟨d₃, f₃, g₃, fun h => absurd h (by decide), fun _ => ⟨u₃, v₃, q₃, r₃⟩⟩
  obtain ⟨f₄, g₄⟩ := w₄ rfl
  rw [← msteps_add] at d₄ u₄ v₄ q₄ r₄ f₄ g₄
  obtain ⟨d₅, u₅, v₅, q₅, r₅, -⟩ := pkChunkV_rel (n := 14) (K := 19) (first := false) (last := true)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (odd 45) (by have := dd 45; norm_num at this ⊢; linarith)
    ⟨d₄, f₄, g₄, fun h => absurd h (by decide), fun _ => ⟨u₄, v₄, q₄, r₄⟩⟩
  rw [← msteps_add] at d₅ u₅ v₅ q₅ r₅
  exact ⟨by rw [d₅, BitVec.not_not], u₅, v₅, q₅, r₅⟩

/-- A batch keeps the invariant. -/
theorem run_step {x i : Nat} (hx : x < P) (hi : i < 10) {t : DSt} (h : RInv x i t) :
    RInv x (i + 1) (dbatchV t) := by
  obtain ⟨hD, hF, hG, hfl, hgl, hal, hbl, hca, hcb, hz⟩ := h
  obtain ⟨hod, hof⟩ := dsI_odd x i
  obtain ⟨hlf, hlg⟩ := dsI_le hx i
  have hd := dsI_d x i
  have hs1 := dsI_succ x i
  have hzero : x = 0 → (dsI x i).2.2 = 0 := fun hx0 => by
    unfold dsI; rw [hx0]; exact (divsteps_zero (t := (1, (P : Int), ((0 : Nat) : Int))) (by simp) _).1
  generalize dsI x i = st at hod hof hlf hlg hd hs1 hD hF hG hca hcb hzero
  obtain ⟨d, f, g⟩ := st
  simp only at hod hof hlf hlg hd hD hF hG hca hcb hzero
  -- The packed divsteps are those of the matrix.
  have hd30 : |d| ≤ 2 ^ 30 := by
    have : (59 * i : Int) ≤ 59 * 9 := by exact_mod_cast (by omega : 59 * i ≤ 59 * 9)
    linarith
  have hW := pkBatchV_rel (D := t.D) (F := BitVec.ofNat 64 t.f) (G := BitVec.ofNat 64 t.g) hD (ofNat_rel64 hF)
    (ofNat_rel64 hG) hof hd30
  have hm := msteps_mat (d := d) (g := g) hof 59
  have hb := msteps_bnd d f g 59
  have hdfg := msteps_dfg 59 (MSt.init d f g)
  have hg0 : g = 0 → (msteps 59 (MSt.init d f g)).v = 0 := fun hg => by
    subst hg; rw [MSt.init, msteps_g0]; simp
  generalize msteps 59 (MSt.init d f g) = tN at hW hm hb hdfg hg0
  simp only [MSt.init] at hdfg
  obtain ⟨wD, wU, wV, wQ, wR⟩ := hW
  obtain ⟨m1, m2⟩ := hm
  obtain ⟨b1, b2⟩ := hb
  unfold dbatchV
  generalize pkBatchV t.D (BitVec.ofNat 64 t.f) (BitVec.ofNat 64 t.g) = W at wD wU wV wQ wR
  dsimp only
  have hfX : sv t.f = f := sv_rep hlf hF
  have hgX : sv t.g = g := sv_rep hlg hG
  have nUV : negN W.U + negN W.V < 2 ^ 64 := by
    have := negN_ofInt_le (le_trans (le_add_of_nonneg_right (abs_nonneg tN.v)) b1)
    have := negN_ofInt_le (le_trans (le_add_of_nonneg_left (abs_nonneg tN.u)) b1)
    rw [wU, wV]; omega
  have nQR : negN W.Q + negN W.R < 2 ^ 64 := by
    have := negN_ofInt_le (le_trans (le_add_of_nonneg_right (abs_nonneg tN.r)) b2)
    have := negN_ofInt_le (le_trans (le_add_of_nonneg_left (abs_nonneg tN.q)) b2)
    rw [wQ, wR]; omega
  have tu := toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg tN.v)) b1)
  have tv := toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg tN.u)) b1)
  have tq := toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg tN.r)) b2)
  have tr := toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg tN.q)) b2)
  have fA := fRowV_eq W.U W.V hfl hgl nUV
  have fB := fRowV_eq W.Q W.R hfl hgl nQR
  obtain ⟨aA, aAl⟩ := aRowV_cong W.U W.V hal hbl nUV
  obtain ⟨aB, aBl⟩ := aRowV_cong W.Q W.R hal hbl nQR
  rw [wU, wV, tu, tv, hfX, hgX, ← m1] at fA
  rw [wQ, wR, tq, tr, hfX, hgX, ← m2] at fB
  rw [wU, wV, tu, tv] at aA
  rw [wQ, wR, tq, tr] at aB
  have p59 : (0 : Int) < 2 ^ 59 := by norm_num
  rw [Int.mul_ediv_cancel_left _ p59.ne'] at fA fB
  have hP : (2 : Int) ^ (59 * (i + 1)) = 2 ^ (59 * i) * 2 ^ 59 := by rw [← pow_add]; ring_nf
  have e : dsI x (i + 1) = (tN.d, tN.f, tN.g) := hs1.trans hdfg.symm
  rw [wU, wV] at aAl
  rw [wQ, wR] at aBl
  rw [wD, wU, wV, wQ, wR]
  refine ⟨by rw [e], by rw [e]; exact fA, by rw [e]; exact fB, by unfold fRowV; exact Nat.mod_lt _ (by positivity),
    by unfold fRowV; exact Nat.mod_lt _ (by positivity), aAl, aBl, ?_, ?_, fun hx0 => ?_⟩
  · rw [e]
    show 2 ^ (59 * (i + 1)) * tN.f ≡ x * aRowV _ _ t.a t.b [ZMOD P]
    rw [hP, mul_assoc, m1]
    calc 2 ^ (59 * i) * (tN.u * f + tN.v * g) = tN.u * (2 ^ (59 * i) * f) + tN.v * (2 ^ (59 * i) * g) := by ring
      _ ≡ tN.u * (x * t.a) + tN.v * (x * t.b) [ZMOD P] := (hca.mul_left _).add (hcb.mul_left _)
      _ = x * (tN.u * t.a + tN.v * t.b) := by ring
      _ ≡ x * aRowV _ _ t.a t.b [ZMOD P] := (aA.symm.mul_left _)
  · rw [e]
    show 2 ^ (59 * (i + 1)) * tN.g ≡ x * aRowV _ _ t.a t.b [ZMOD P]
    rw [hP, mul_assoc, m2]
    calc 2 ^ (59 * i) * (tN.q * f + tN.r * g) = tN.q * (2 ^ (59 * i) * f) + tN.r * (2 ^ (59 * i) * g) := by ring
      _ ≡ tN.q * (x * t.a) + tN.r * (x * t.b) [ZMOD P] := (hca.mul_left _).add (hcb.mul_left _)
      _ = x * (tN.q * t.a + tN.r * t.b) := by ring
      _ ≡ x * aRowV _ _ t.a t.b [ZMOD P] := (aB.symm.mul_left _)
  · have hv : tN.v = 0 := hg0 (hzero hx0)
    show (aRowV _ _ t.a t.b : Int) ≡ 0 [ZMOD P]
    refine aA.trans ?_
    rw [hv]
    have := (hz hx0).mul_left tN.u
    simpa using this

/-- The invariant through the batches. -/
theorem run_inv {x : Nat} (hx : x < P) : ∀ i, i ≤ 10 → RInv x i (drun x i)
  | 0, _ => by
    have hP := P_lt
    have e : dsI x 0 = (1, (P : Int), (x : Int)) := by simp only [dsI, divsteps]
    refine ⟨by rw [e]; rfl, by rw [e]; simp only [drun]; omega, by rw [e]; simp only [drun]; omega,
      by simp only [drun]; omega, by simp only [drun]; omega, by simp only [drun]; omega,
      by simp only [drun]; omega, ?_, ?_, fun _ => by simp [drun]⟩
    · rw [e]; simp only [drun, pow_zero, one_mul, Nat.cast_zero, mul_zero]
      exact (Int.emod_self).trans (by simp)
    · rw [e]; simp [drun]
  | i + 1, hi => run_step hx (by omega) (run_inv hx i (by omega))

theorem toZ_toFe (n : Nat) : VG.Proof.Ed25519.toZ (toFe n) = (n : ZMod P) := by
  apply ZMod.val_injective
  rw [ZMod.val_natCast]
  rfl

theorem kInv_spec : (2 ^ 590 * Impl.X25519.X86_64.kInv) % P = 1 := by decide +kernel

theorem kInvNeg_spec : Impl.X25519.X86_64.kInv + Impl.X25519.X86_64.kInvNeg = P := by decide +kernel

/-- The inversion by divsteps is `x^(p-2)`. -/
theorem byAlg_eq (x : Fe) : byAlg x = pow x (P - 2) := by
  have hx : x.val < P := x.isLt
  obtain ⟨hD, hF, hG, hfl, hgl, hal, hbl, hca, hcb, hz⟩ := run_inv hx 10 le_rfl
  rw [← VG.Proof.Ed25519.toZ_inj, VG.Proof.Ed25519.toZ_pow]
  unfold byAlg
  rw [VG.Proof.Ed25519.toZ_mul, toZ_toFe, toZ_toFe]
  have hxz : VG.Proof.Ed25519.toZ x = (x.val : ZMod P) := by
    have e : toFe x.val = x := Fin.ext (by
      show x.val % P = x.val
      exact Nat.mod_eq_of_lt hx)
    rw [← toZ_toFe, e]
  rw [hxz]
  by_cases h0 : x.val = 0
  · have ha := (ZMod.intCast_eq_intCast_iff _ _ _).2 (hz h0)
    push_cast at ha
    rw [ha, h0]
    simp only [Nat.cast_zero, zero_mul]
    rw [zero_pow (by simp [P])]
  · -- 590 divsteps end with `g = 0` and `f = ±1`.
    have hdone := divsteps_590 (f := (P : Int)) (g := (x.val : Int)) P_odd (by positivity)
      (by exact_mod_cast hx.le) (by rw [P_val]; norm_num) (n := 590) le_rfl
    have hcop : Int.gcd (P : Int) (x.val : Int) = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact Nat.coprime_of_lt_prime h0 hx VG.Proof.Ed25519.prime_field
    have hs : dsI x.val 10 = divsteps 590 (1, (P : Int), (x.val : Int)) := rfl
    rw [hs] at hF hca
    generalize (divsteps 590 (1, (P : Int), (x.val : Int))).2.1 = f at hdone hF hca
    rw [hcop] at hdone
    have hf : f = 1 ∨ f = -1 := by omega
    set A : ZMod P := ((drun x.val 10).a : ZMod P)
    set X : ZMod P := (x.val : ZMod P)
    have hc := (ZMod.intCast_eq_intCast_iff _ _ _).2 hca
    rw [Int.cast_mul, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast, Int.cast_natCast] at hc
    have k1 : ((2 : ZMod P) ^ (59 * 10)) * (Impl.X25519.X86_64.kInv : ZMod P) = 1 := by
      have := congrArg (fun n : Nat => (n : ZMod P)) kInv_spec
      rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at this
      exact this
    have k2 : (Impl.X25519.X86_64.kInvNeg : ZMod P) = -(Impl.X25519.X86_64.kInv : ZMod P) := by
      have := congrArg (fun n : Nat => (n : ZMod P)) kInvNeg_spec
      simp only [Nat.cast_add, ZMod.natCast_self] at this
      exact eq_neg_of_add_eq_zero_right this
    -- `x a k = 1`.
    have hxak : X * (A * (kSel (drun x.val 10).f : ZMod P)) = 1 := by
      unfold kSel
      rcases hf with rfl | rfl
      · have h1 : (drun x.val 10).f = 1 := by omega
        rw [h1]; simp only [show (1 : Nat) < 2 ^ 255 by norm_num, ↓reduceIte]
        rw [← mul_assoc, ← hc]
        simpa using k1
      · have h1 : (drun x.val 10).f = 2 ^ 256 - 1 := by omega
        rw [h1]; simp only [show ¬ (2 ^ 256 - 1 : Nat) < 2 ^ 255 by norm_num, ↓reduceIte]; rw [k2]
        rw [← mul_assoc, ← hc]
        have : (2 : ZMod P) ^ (59 * 10) * ((-1 : Int) : ZMod P) * -(Impl.X25519.X86_64.kInv : ZMod P) =
            (2 : ZMod P) ^ (59 * 10) * (Impl.X25519.X86_64.kInv : ZMod P) := by
          rw [Int.cast_neg, Int.cast_one, mul_neg_one, neg_mul_neg]
        exact this.trans k1
    have hX : X ≠ 0 := fun h => by rw [h, zero_mul] at hxak; exact zero_ne_one hxak
    calc A * (kSel (drun x.val 10).f : ZMod P)
        = A * (kSel (drun x.val 10).f : ZMod P) * X * X ^ (P - 2) := (VG.Proof.Ed25519.mul_pow_inv hX _).symm
      _ = X * (A * (kSel (drun x.val 10).f : ZMod P)) * X ^ (P - 2) := by ring
      _ = X ^ (P - 2) := by rw [hxak, one_mul]

instance divstepInv : DivstepInv := ⟨byAlg_eq⟩

end VG.Proof.X25519.X86_64
