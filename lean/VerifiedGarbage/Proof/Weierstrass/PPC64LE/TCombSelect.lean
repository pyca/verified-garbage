module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.LadderP
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Proof.Weierstrass.Comb
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontCall
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointFn
import VerifiedGarbage.Proof.Mont.PPC64LE.Const
import VerifiedGarbage.Proof.Mont.PPC64LE.Csub
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# The comb's selection of a table entry, on PPC64LE

As on 32-bit ARM (`Proof/Weierstrass/Arm/TCombSelect.lean` and the modules it
imports): the layout the comb needs, its read-only table, the mask of an
equality, and the scan of a row that keeps exactly its chosen entry in the
point functions' `Q` (or, for a magnitude of zero, `(0 : 1 : 0)`), whatever
the entry.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.TComb

open VG VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass.PPC64LE.Point
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Point VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Impl.Weierstrass.Point (elemBytes ownAt aAt b3At oAt pAt qAt)

/-! ## The layout -/

/-- `R`, zero and `-y` lie below the point functions' slots, at multiples of
4, apart from each other (but `R`'s coordinates, which are apart from each
other), on the ladder's layout. -/
structure Layout (K : TCombCfg) : Prop where
  point : LadPtLay K.L
  low : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.zero, K.neg], x + 8 * K.L.M.n ≤ oAt K.L.M.n
  al : K.zero % 4 = 0 ∧ K.neg % 4 = 0
  negApart : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.zero], K.neg + 8 * K.L.M.n ≤ x ∨ x + 8 * K.L.M.n ≤ K.neg
  zeroApart : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], K.zero + 8 * K.L.M.n ≤ x ∨ x + 8 * K.L.M.n ≤ K.zero

/-- What the comb writes: `R`, `-y`, and the point functions' slots and own
working space (with the field functions' own working space in it). -/
def writes (K : TCombCfg) : List (Nat × Nat) :=
  [(K.L.R.x, 8 * K.L.M.n), (K.L.R.y, 8 * K.L.M.n), (K.L.R.z, 8 * K.L.M.n), (K.neg, 8 * K.L.M.n),
    (oAt K.L.M.n, 4096 - oAt K.L.M.n)]

/-- What an iteration writes: also, the point functions' `O`, `P` and `Q`
and their own working space, but not their `a` and `3b`. -/
def loopWrites (K : TCombCfg) : List (Nat × Nat) :=
  [(K.L.R.x, 8 * K.L.M.n), (K.L.R.y, 8 * K.L.M.n), (K.L.R.z, 8 * K.L.M.n), (K.neg, 8 * K.L.M.n),
    (oAt K.L.M.n, 72 * K.L.M.n), (ownAt K.L.M.n, 4096 - ownAt K.L.M.n)]

theorem Layout.loop_cover {K : TCombCfg} (h : Layout K) :
    ∀ r ∈ loopWrites K, ∃ t ∈ writes K, t.1 ≤ r.1 ∧ r.1 + r.2 ≤ t.1 + t.2 := by
  obtain ⟨-, -, -, -, ha, hq, hp, ho, -, -⟩ := lay_nums h.point.k3 h.point.k6
  have := lay_nums h.point.k3 h.point.k6
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, by simp [writes], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, by simp [writes], Nat.le_refl _, Nat.le_refl _⟩
  all_goals exact ⟨(oAt K.L.M.n, 4096 - oAt K.L.M.n), by simp [writes], by dsimp only; omega_arith,
    by dsimp only; omega_arith⟩

theorem Layout.bounded {K : TCombCfg} (h : Layout K) : ∀ r ∈ writes K, r.1 + r.2 ≤ 4096 := by
  have := lay_nums h.point.k3 h.point.k6
  have low := h.low
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at low
  intro r hr
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> (dsimp only; omega_arith)

theorem Layout.loop_bounded {K : TCombCfg} (h : Layout K) : ∀ r ∈ loopWrites K, r.1 + r.2 ≤ 4096 :=
  fun r hr => by
    obtain ⟨t, ht, h1, h2⟩ := h.loop_cover r hr
    exact Nat.le_trans h2 (h.bounded t ht)

/-- The point functions' slots, by layout. -/
theorem Q_eq (K : TCombCfg) : K.Q = ⟨qAt K.L.M.n, qAt K.L.M.n + elemBytes K.L.M.n,
    qAt K.L.M.n + 2 * elemBytes K.L.M.n⟩ := rfl
theorem P_eq (K : TCombCfg) : K.P = ⟨pAt K.L.M.n, pAt K.L.M.n + elemBytes K.L.M.n,
    pAt K.L.M.n + 2 * elemBytes K.L.M.n⟩ := rfl
theorem O_eq (K : TCombCfg) : K.O = ⟨oAt K.L.M.n, oAt K.L.M.n + elemBytes K.L.M.n,
    oAt K.L.M.n + 2 * elemBytes K.L.M.n⟩ := rfl

/-! ## The table -/

/-- The table's words, readable at `T`. -/
structure TableMem (s : State) (T : Addr) (ws : List (BitVec 64)) : Prop where
  fit : T.toNat + 8 * ws.length ≤ 2 ^ 64
  readable : InRegions (s.rd ++ s.wr) T (8 * ws.length)
  words : ∀ i < ws.length, s.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = ws.getD i 0

/-- A word in a region apart from the working space survives a change in it. -/
theorem _root_.VG.Proof.Weierstrass.Unch.far_word {base X : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ 8192) {L d : Nat} (hd : Region.Disjoint ⟨X, L⟩ ⟨base, 8192⟩)
    (hdl : d + 8 ≤ L) (hfit : X.toNat + L ≤ 2 ^ 64) : word m' X d = word m X d := by
  refine (Mem.readW_congr fun i hi => (h.far fun w hw => ?_).symm).symm
  have hw' := hW w hw
  have hin : ((off X d + BitVec.ofNat 64 i) - X).toNat + 1 ≤ L := by
    rw [VG.Offset.add_add, VG.Offset.add_sub_cancel_left]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hn : ¬ ((off X d + BitVec.ofNat 64 i) - base).toNat + 1 ≤ 8192 := fun h' => hd _ hin h'
  simp only [ofs]
  omega

theorem TableMem.unch {s t : State} {T base : Addr} {ws : List (BitVec 64)} {W : List (Nat × Nat)}
    (h : TableMem s T ws) (hr : t.rd ++ t.wr = s.rd ++ s.wr) (hU : Unch base W s.mem t.mem)
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ 8192) (hd : Region.Disjoint ⟨T, 8 * ws.length⟩ ⟨base, 8192⟩) :
    TableMem t T ws :=
  ⟨h.fit, hr ▸ h.readable, fun i hi => by
    rw [← h.words i hi]
    exact hU.far_word hW (d := 8 * i) hd (by omega) h.fit⟩

theorem table_bytes {n R p H J : Nat} {tbl : List (List (Nat × Nat))}
    (hJ : tbl.length = J) (hH : ∀ j < J, (tbl.getD j []).length = H) :
    8 * (tcombWords n R p tbl).length = 16 * n * H * J := by
  rw [tcombWords_length hJ hH]
  calc
    8 * (J * (H * (2 * n))) = 8 * (2 * (n * (H * J))) := by ac_rfl
    _ = (8 * 2) * (n * (H * J)) := (Nat.mul_assoc _ _ _).symm
    _ = 16 * n * H * J := by
      rw [show (8 * 2 : Nat) = 16 by decide]
      simp only [Nat.mul_assoc]

/-! ## The mask of an equality -/

theorem zero_test_bit (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    (x - 1) >>> 63 = if x = 0#64 then 1 else 0 := by
  by_cases h : x = 0#64
  · subst h; decide
  · have h0 : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    simp only [h, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub,
      show (1 : BitVec 64).toNat = 1 from rfl]
    show _ = 0
    omega

theorem equality_mask {a b : BitVec 64} (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    0#64 - (((a ^^^ b) - 1) >>> 63) = if a = b then BitVec.allOnes 64 else 0 := by
  have hx : (a ^^^ b).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow ha hb
  rw [zero_test_bit _ hx]
  by_cases h : a = b
  · subst h; simp only [BitVec.xor_self, ↓reduceIte]; decide
  · have hn : a ^^^ b ≠ 0#64 := fun e => h (BitVec.xor_eq_zero_iff.mp e)
    simp only [hn, h, ↓reduceIte]; decide

theorem ofNat64_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro h
    have e := congrArg BitVec.toNat h
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using e
  · intro h; rw [h]

theorem sub_zero_iff (x y : BitVec 64) : x - y = 0#64 ↔ x = y := by
  constructor
  · intro h
    have e := congrArg (fun z : BitVec 64 => z + y) h
    simpa only [BitVec.sub_add_cancel, BitVec.zero_add] using e
  · intro h; rw [h, BitVec.sub_self]

theorem sub_ne_zero_dec {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 y != 0) = decide (x ≠ y) := by
  by_cases h : x = y
  · subst h; simp
  · have hne : BitVec.ofNat 64 x - BitVec.ofNat 64 y ≠ 0#64 := fun h0 =>
      h ((ofNat64_eq hx hy).mp ((sub_zero_iff _ _).mp h0))
    simp [hne, h]

/-- The mask of `r9 = idx` into `r10`. -/
theorem eqMask_ok {s : State} {idx : Reg} :
    WP isa (.block (TCombCfg.eqMask idx)) s fun t =>
      t.gpr .r10 = 0#64 - (((s.gpr .r9 ^^^ s.gpr idx) - 1) >>> 63) ∧ Kp [.r5, .r10] s t ∧ t.mem = s.mem := by
  unfold TCombCfg.eqMask
  refine wp_step exec_logic ?_
  refine wp_step (exec_subi (by decide) (by decide)) ?_
  refine wp_step (exec_lsr_d (by decide)) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub (WP.block_nil ?_)
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp only [write_gpr, reduceCtorEq, ite_false, ite_true]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2, ite_false]

/-- The mask of `a = m`, for numbers below `2^63`. -/
theorem eqMask_val {a m : Nat} (ha : a < 2 ^ 63) (hm : m < 2 ^ 63) :
    0#64 - (((BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 m) - 1) >>> 63) =
      if decide (a = m) then BitVec.allOnes 64 else 0 := by
  rw [equality_mask (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact ha)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hm)]
  simp only [ofNat64_eq (by omega : a < 2 ^ 64) (by omega : m < 2 ^ 64), decide_eq_true_eq]

/-! ## A word of the scan -/

/-- Word `i` of `Q` or'ed with the table's at `r8 = X` under the mask `r10`. -/
theorem selectWord_ok (K : TCombCfg) {s : State} {base X : Addr} {i : Nat}
    (hs : Ws s base 8192) (h3 : At s base .r3 0) (hX : s.gpr .r8 = X)
    (hq4 : K.Q.x % 4 = 0) (ho : K.Q.x + 8 * i + 8 ≤ 8192) (hi : 8 * i < 2 ^ 15)
    (hr : InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (8 * i)) 8)
    (b : Bool) (hc : s.gpr .r10 = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block (K.selectWord i)) s fun t =>
      word t.mem base (K.Q.x + 8 * i) =
        (if b then word s.mem X (8 * i) else word s.mem base (K.Q.x + 8 * i)) ∧
      Kp [.r4, .r5] s t ∧ Outside base (K.Q.x + 8 * i) 8 s.mem t.mem := by
  have hn := hs.nowrap
  unfold TCombCfg.selectWord
  refine wp_step (ld0_ok hs h3 (by decide) (by omega) ho) ?_
  refine wp_step (exec_load_d (by decide) ⟨hi, by omega⟩ (by
    simp only [write_gpr, reduceCtorEq, ite_false, hX]; exact hr)) ?_
  refine wp_step exec_logic ?_
  refine wp_step exec_logic ?_
  refine wp_step exec_logic ?_
  refine wp_step (std0_ok ((((hs.write _ _).write _ _).write _ _).write _ _ |>.write _ _)
    (((((h3.write _).write _).write _).write _).write _) (by decide) (by omega) ho) (WP.block_nil ?_)
  simp only [write_gpr, write_mem, reduceCtorEq, ite_false, ite_true, hX, hc]
  have hmk : (if b then BitVec.allOnes 64 else (0 : BitVec 64)) = 0 ∨
      (if b then BitVec.allOnes 64 else (0 : BitVec 64)) = BitVec.allOnes 64 := by
    cases b <;> simp
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, writeW_outside _ _ _ (by omega)⟩
  · rw [word_writeW_self, sel_mask _ _ hmk]
    cases b <;> simp [word, off]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2, ite_false]


/-- Numbers whose words agree are equal. -/
theorem wordsVal_congr_words {m m' : Mem} {a a' : Addr} {d d' : Nat} :
    ∀ {n : Nat}, (∀ i < n, word m a (d + 8 * i) = word m' a' (d' + 8 * i)) →
      wordsVal m a d n = wordsVal m' a' d' n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [wordsVal]
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    rw [h0, wordsVal_congr_words (n := n) (d := d + 8) (d' := d' + 8) fun i hi => by
      have := h (i + 1) (by omega)
      rw [show d + 8 + 8 * i = d + 8 * (i + 1) by omega, show d' + 8 + 8 * i = d' + 8 * (i + 1) by omega]
      exact this]

/-- A number whose words are zero is zero. -/
theorem wordsVal_zero_words {m : Mem} {a : Addr} {d : Nat} :
    ∀ {n : Nat}, (∀ i < n, word m a (d + 8 * i) = 0) → wordsVal m a d n = 0
  | 0, _ => rfl
  | n + 1, h => by
    simp only [wordsVal]
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    rw [h0, wordsVal_zero_words (n := n) (d := d + 8) fun i hi => by
      rw [show d + 8 + 8 * i = d + 8 * (i + 1) by omega]; exact h (i + 1) (by omega)]
    rfl

/-- The words of an entry `[X, X + 16 n)` selected into `Q` under the mask `r10`. -/
theorem selectWords_ok (K : TCombCfg) {s : State} {base X : Addr}
    (hs : Ws s base 8192) (h3 : At s base .r3 0) (hX : s.gpr .r8 = X)
    (hq4 : K.Q.x % 4 = 0) (ho : K.Q.x + 16 * K.L.M.n ≤ 8192) (hi : 16 * K.L.M.n < 2 ^ 15)
    (fit : X.toNat + 16 * K.L.M.n ≤ 2 ^ 64)
    (hr : InRegions (s.rd ++ s.wr) X (16 * K.L.M.n))
    (hd : Region.Disjoint ⟨X, 16 * K.L.M.n⟩ ⟨base, 8192⟩)
    (b : Bool) (hc : s.gpr .r10 = if b then BitVec.allOnes 64 else 0) :
    ∀ k, k ≤ 2 * K.L.M.n →
    WP isa (.block ((List.range k).flatMap K.selectWord)) s fun t =>
      (∀ i < k, word t.mem base (K.Q.x + 8 * i) =
        if b then word s.mem X (8 * i) else word s.mem base (K.Q.x + 8 * i)) ∧
      Kp [.r4, .r5] s t ∧ Outside base K.Q.x (8 * k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Kp.refl _ _, Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine wp_append (WP.mono (selectWords_ok K hs h3 hX hq4 ho hi fit hr hd b hc k (by omega))
      fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
    have hr₁ : InRegions (s₁.rd ++ s₁.wr) (X + BitVec.ofNat 64 (8 * k)) 8 := by
      rw [k₁.rd, k₁.wr]
      exact CallLay.inRegions_sub (off := 8 * k) (l := 8) hr (by omega) (by omega)
    refine WP.mono (selectWord_ok K (i := k) (k₁.ws hs) (k₁.at h3) (by rw [k₁.g]; exact hX) hq4
      (by omega) (by omega) hr₁ b (by rw [k₁.g]; exact hc)) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
    refine ⟨fun i hii => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    by_cases hik : i < k
    · rw [O₂.word (by omega) (by omega), e₁ i hik]
    · obtain rfl : i = k := by omega
      have xeq : word s₁.mem X (8 * i) = word s.mem X (8 * i) :=
        O₁.unch.far_word (fun w hw => by
          rw [List.mem_singleton] at hw; subst hw; dsimp only; omega) hd (by omega) fit
      have oeq : word s₁.mem base (K.Q.x + 8 * i) = word s.mem base (K.Q.x + 8 * i) :=
        O₁.word (by omega) (by omega)
      rw [v₂, xeq, oeq]

/-- Entry `m` (in `r7`, its words at `r8 = X`) of the row, for the magnitude
`a` in `r9`: its words or'ed into `Q` if `a = m`, then the next entry. -/
theorem selectBody_ok (K : TCombCfg) {s : State} {base X : Addr} {a m : Nat}
    (hs : Ws s base 8192) (h3 : At s base .r3 0) (hX : s.gpr .r8 = X)
    (hq4 : K.Q.x % 4 = 0) (ho : K.Q.x + 16 * K.L.M.n ≤ 8192) (hi : 16 * K.L.M.n < 2 ^ 15)
    (fit : X.toNat + 16 * K.L.M.n ≤ 2 ^ 64)
    (hr : InRegions (s.rd ++ s.wr) X (16 * K.L.M.n))
    (hd : Region.Disjoint ⟨X, 16 * K.L.M.n⟩ ⟨base, 8192⟩)
    (ha : a < 2 ^ 63) (hm : m < 2 ^ 63) (ga : s.gpr .r9 = BitVec.ofNat 64 a)
    (gm : s.gpr .r7 = BitVec.ofNat 64 m) (hH : K.H + 1 ≤ 2 ^ 15) :
    WP isa (.block K.selectBody) s fun t =>
      (∀ i < 2 * K.L.M.n, word t.mem base (K.Q.x + 8 * i) =
        if a = m then word s.mem X (8 * i) else word s.mem base (K.Q.x + 8 * i)) ∧
      Kp [.r4, .r5, .r6, .r7, .r8, .r10] s t ∧ Outside base K.Q.x (16 * K.L.M.n) s.mem t.mem ∧
      t.gpr .r8 = s.gpr .r8 + BitVec.ofNat 64 (16 * K.L.M.n) ∧
      t.gpr .r7 = BitVec.ofNat 64 (m + 1) ∧
      t.gpr .r6 = BitVec.ofNat 64 (m + 1) - BitVec.ofNat 64 (K.H + 1) := by
  unfold TCombCfg.selectBody
  rw [List.append_assoc]
  refine wp_append (WP.mono (eqMask_ok (s := s) (idx := .r7)) fun s₁ ⟨v₁, k₁, mem₁⟩ => ?_)
  have cm₁ : s₁.gpr .r10 = if decide (a = m) then BitVec.allOnes 64 else 0 := by
    rw [v₁, ga, gm, eqMask_val ha hm]
  have hr₁ : InRegions (s₁.rd ++ s₁.wr) X (16 * K.L.M.n) := by rw [k₁.rd, k₁.wr]; exact hr
  refine wp_append (WP.mono (selectWords_ok K (k₁.ws hs) (k₁.at h3) (by rw [k₁.g]; exact hX) hq4 ho hi fit
    hr₁ hd (decide (a = m)) cm₁ (2 * K.L.M.n) (Nat.le_refl _)) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_)
  have g₇ : s₂.gpr .r7 = BitVec.ofNat 64 m := by rw [k₂.g, k₁.g]; exact gm
  have g₈ : s₂.gpr .r8 = s.gpr .r8 := by rw [k₂.g, k₁.g]
  refine wp_step (exec_addi (by decide) (by omega)) ?_
  refine wp_step (exec_addi (by decide) (by decide)) ?_
  refine wp_step (exec_subi (by decide) hH) (WP.block_nil ?_)
  simp only [write_gpr, write_mem, reduceCtorEq, ite_false, ite_true]
  have g₇' : s₂.gpr .r7 + BitVec.ofNat 64 1 = BitVec.ofNat 64 (m + 1) := by
    rw [g₇]; exact (BitVec.ofNat_add _ _).symm
  refine ⟨fun i hii => ?_, ((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans
      ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, ?_, by rw [g₈], g₇', by rw [g₇']⟩
  · rw [v₂ i hii, mem₁]
    simp only [decide_eq_true_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, ite_false]
  · rw [mem₁] at O₂
    simpa only [show 8 * (2 * K.L.M.n) = 16 * K.L.M.n by omega] using O₂

/-- What the scan keeps after the entries before `m`: `Q` holds the entry
of magnitude `a` if it was among them, zeros if not. -/
structure ScanInv (K : TCombCfg) (base X : Addr) (s₀ : State) (a m : Nat) (s : State) : Prop where
  ptr : s.gpr .r8 = X + BitVec.ofNat 64 (16 * K.L.M.n * (m - 1))
  index : s.gpr .r7 = BitVec.ofNat 64 m
  keep : Kp [.r4, .r5, .r6, .r7, .r8, .r10] s₀ s
  unch : Outside base K.Q.x (16 * K.L.M.n) s₀.mem s.mem
  val : ∀ i < 2 * K.L.M.n, word s.mem base (K.Q.x + 8 * i) =
    if 1 ≤ a ∧ a < m then word s₀.mem X (16 * K.L.M.n * (a - 1) + 8 * i) else 0

theorem prefix_step {a m : Nat} (hm : 1 ≤ m) (f : Nat → BitVec 64) :
    (if a = m then f m else if 1 ≤ a ∧ a < m then f a else 0) =
      if 1 ≤ a ∧ a < m + 1 then f a else 0 := by
  by_cases h : a = m
  · subst a; simp only [↓reduceIte, hm, true_and, Nat.lt_succ_self]
  · have he : (1 ≤ a ∧ a < m) ↔ (1 ≤ a ∧ a < m + 1) := by omega
    simp only [h, ↓reduceIte, he]

/-- The row of `H` entries at `X`, in the table's region. -/
structure RowOk (K : TCombCfg) (s : State) (base X : Addr) : Prop where
  fit : X.toNat + 16 * K.L.M.n * K.H ≤ 2 ^ 64
  readable : InRegions (s.rd ++ s.wr) X (16 * K.L.M.n * K.H)
  apart : Region.Disjoint ⟨X, 16 * K.L.M.n * K.H⟩ ⟨base, 8192⟩

theorem scan_step (K : TCombCfg) {s₀ s : State} {base X : Addr} {a m : Nat}
    (hs₀ : Ws s₀ base 8192) (h3 : At s₀ base .r3 0) (hq4 : K.Q.x % 4 = 0)
    (ho : K.Q.x + 16 * K.L.M.n ≤ 8192) (hi : 16 * K.L.M.n < 2 ^ 15) (R : RowOk K s₀ base X)
    (hn1 : 1 ≤ K.L.M.n) (hH : K.H + 1 ≤ 2 ^ 15) (ha : a ≤ K.H) (ga : s₀.gpr .r9 = BitVec.ofNat 64 a)
    (hm : 1 ≤ m) (mh : m ≤ K.H) (I : ScanInv K base X s₀ a m s) :
    WP isa (.block K.selectBody) s fun t => ScanInv K base X s₀ a (m + 1) t ∧
      t.gpr .r6 = BitVec.ofNat 64 (m + 1) - BitVec.ofNat 64 (K.H + 1) := by
  have hn := hs₀.nowrap
  have hmul : 16 * K.L.M.n * (m - 1) + 16 * K.L.M.n ≤ 16 * K.L.M.n * K.H := by
    calc
      16 * K.L.M.n * (m - 1) + 16 * K.L.M.n = 16 * K.L.M.n * m := by
        rw [← Nat.mul_succ]; congr 1; omega
      _ ≤ 16 * K.L.M.n * K.H := Nat.mul_le_mul_left _ mh
  have fitR := R.fit
  have efit : (X + BitVec.ofNat 64 (16 * K.L.M.n * (m - 1))).toNat + 16 * K.L.M.n ≤ 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 16 * K.L.M.n * (m - 1) < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show X.toNat + 16 * K.L.M.n * (m - 1) < 2 ^ 64 by omega)]
    omega
  have er : InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (16 * K.L.M.n * (m - 1))) (16 * K.L.M.n) := by
    rw [I.keep.rd, I.keep.wr]
    have hb : 16 * K.L.M.n * K.H ≤ 16 * K.L.M.n * 2 ^ 15 := Nat.mul_le_mul_left _ (by omega)
    exact CallLay.inRegions_sub R.readable hmul (by omega)
  have ed : Region.Disjoint ⟨X + BitVec.ofNat 64 (16 * K.L.M.n * (m - 1)), 16 * K.L.M.n⟩ ⟨base, 8192⟩ :=
    R.apart.sub_left (Offset.sub_base X hmul)
  have hH63 : K.H < 2 ^ 63 := by omega
  refine WP.mono (selectBody_ok K (a := a) (m := m) (I.keep.ws hs₀) (I.keep.at h3) I.ptr hq4 ho hi efit er ed
    (by omega) (by omega) (by rw [I.keep.g]; exact ga) I.index hH)
    fun t ⟨v, k, O, p, index, z⟩ => ⟨?_, z⟩
  refine ⟨?_, index, I.keep.trans (k.mono (by decide)), I.unch.trans O, ?_⟩
  · have he : 16 * K.L.M.n * (m - 1) + 16 * K.L.M.n = 16 * K.L.M.n * m := by
      rw [← Nat.mul_succ]; congr 1; omega
    rw [p, I.ptr, VG.Offset.add_add, he, show m + 1 - 1 = m by omega]
  · intro i hii
    have hoff : 16 * K.L.M.n * (m - 1) + 8 * i + 8 ≤ 16 * K.L.M.n * K.H := by omega
    have src : word s.mem (X + BitVec.ofNat 64 (16 * K.L.M.n * (m - 1))) (8 * i) =
        word s₀.mem X (16 * K.L.M.n * (m - 1) + 8 * i) := by
      show s.mem.readW (X + BitVec.ofNat 64 (16 * K.L.M.n * (m - 1)) + BitVec.ofNat 64 (8 * i)) 64 = _
      rw [VG.Offset.add_add]
      exact I.unch.unch.far_word (fun w hw => by
        rw [List.mem_singleton] at hw; subst hw; dsimp only; omega) (d := 16 * K.L.M.n * (m - 1) + 8 * i)
        R.apart hoff R.fit
    rw [v i hii, src, I.val i hii]
    exact prefix_step hm (fun q => word s₀.mem X (16 * K.L.M.n * (q - 1) + 8 * i))

/-- Every entry of the row is visited, in order, whatever the magnitude. -/
theorem scan_loop_ok (K : TCombCfg) {s₀ : State} {base X : Addr} {a : Nat}
    (hs₀ : Ws s₀ base 8192) (h3 : At s₀ base .r3 0) (hq4 : K.Q.x % 4 = 0)
    (ho : K.Q.x + 16 * K.L.M.n ≤ 8192) (hi : 16 * K.L.M.n < 2 ^ 15) (R : RowOk K s₀ base X)
    (hX : s₀.gpr .r8 = X) (hn1 : 1 ≤ K.L.M.n) (hH : K.H + 1 ≤ 2 ^ 15) (ha : a ≤ K.H) (ga : s₀.gpr .r9 = BitVec.ofNat 64 a)
    (gm : s₀.gpr .r7 = 1) (hz : ∀ i < 2 * K.L.M.n, word s₀.mem base (K.Q.x + 8 * i) = 0) :
    WP isa (.loop (.block K.selectBody) (.nonzero .d .r6)) s₀ (ScanInv K base X s₀ a (K.H + 1)) := by
  have hHp : 1 ≤ K.H := Nat.two_pow_pos _
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ K.H ∧ ScanInv K base X s₀ a (K.H + 1 - j) s)
    (fun j s ⟨j1, jH, I⟩ => ?_) K.H s₀ ?_
  · refine WP.mono (scan_step K hs₀ h3 hq4 ho hi R hn1 hH ha ga (by omega) (by omega) I) fun t ⟨I', z⟩ => ?_
    have ev : isa.eval (.nonzero .d .r6) t = some (decide (K.H + 1 - j + 1 ≠ K.H + 1)) := by
      rw [eval_nonzero, z, sub_ne_zero_dec (by omega) (by omega)]
    by_cases je : j = 1
    · have me : K.H + 1 - j + 1 = K.H + 1 := by omega
      refine .inl ⟨by rw [ev, decide_eq_false (not_not.mpr me)], me ▸ I'⟩
    · have me : ¬K.H + 1 - j + 1 = K.H + 1 := by omega
      refine .inr ⟨by rw [ev, decide_eq_true me], j - 1, by omega, by omega, by omega, ?_⟩
      have e : K.H + 1 - (j - 1) = K.H + 1 - j + 1 := by omega
      rw [e]; exact I'
  · refine ⟨hHp, Nat.le_refl _, ?_⟩
    have e : K.H + 1 - K.H = 1 := by omega
    rw [e]
    refine ⟨?_, ?_, Kp.refl _ _, Outside.refl _ _ _ _, ?_⟩
    · rw [hX, show 16 * K.L.M.n * (1 - 1) = 0 by simp]
      exact (BitVec.add_zero X).symm
    · exact gm
    · intro i hi'
      rw [hz i hi']
      have h : ¬(1 ≤ a ∧ a < 1) := by omega
      simp only [h, ↓reduceIte]


/-- The words of a number that is zero are zero. -/
theorem words_zero_of_wordsVal {m : Mem} {a : Addr} {d : Nat} :
    ∀ {n : Nat}, wordsVal m a d n = 0 → ∀ i < n, word m a (d + 8 * i) = 0
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
    simp only [wordsVal] at h
    have h1 : (word m a d).toNat = 0 := by omega
    have h2 : wordsVal m a (d + 8) n = 0 := by
      have := Nat.two_pow_pos 64; rcases Nat.eq_zero_of_add_eq_zero h with ⟨-, h'⟩
      exact (Nat.mul_eq_zero.mp h').resolve_left (by omega)
    cases i with
    | zero => simpa using BitVec.eq_of_toNat_eq (h1.trans rfl)
    | succ i =>
      rw [show d + 8 * (i + 1) = d + 8 + 8 * i by omega]
      exact words_zero_of_wordsVal h2 i (by omega)

/-- `[r3 + o] = x`, `n` words, as a number. -/
theorem setConstW_ok {s : State} {base : Addr} (hw : WsReg s base) {n o x : Nat}
    (ho : o + 8 * n ≤ 8192) (hx : x < 2 ^ (64 * n)) :
    WP isa (.block (Impl.Mont.PPC64LE.setConst n o x)) s fun u =>
      Outside base o (8 * n) s.mem u.mem ∧ wordsVal u.mem base o n = x ∧ Kp [.r11] s u :=
  WP.mono (setConst_ok hw.ws hw.at3 ho hx) fun _ ⟨O, V, K⟩ => ⟨O, by rw [wordsVal_eq_val32]; exact V, K⟩

/-- The row's address (row `j`, in `r31`) in `r8`, `Q`'s `x` and `y` zero,
and `r7 = 1`. -/
theorem selectSetup_ok (K : TCombCfg) {s : State} {base : Addr} {j : Nat}
    (hw : WsReg s base) (hq : K.Q.x + 16 * K.L.M.n ≤ 8192)
    (gj : s.gpr .r31 = BitVec.ofNat 64 j) (hrow : 16 * K.L.M.n * K.H < 2 ^ 15) :
    WP isa (.block K.selectSetup) s fun t =>
      t.gpr .r8 = s.syms K.tsym + BitVec.ofNat 64 (16 * K.L.M.n * K.H * j) ∧
      t.gpr .r7 = 1 ∧ (∀ i < 2 * K.L.M.n, word t.mem base (K.Q.x + 8 * i) = 0) ∧
      Rk [.r4, .r7, .r8, .r11] s t ∧ Outside base K.Q.x (16 * K.L.M.n) s.mem t.mem := by
  have hy : K.Q.y = K.Q.x + 8 * K.L.M.n := rfl
  have hn := hw.nowrap
  unfold TCombCfg.selectSetup
  simp only [List.cons_append]
  refine wp_step (exec_adrSym (d := .r8) (by decide)) ?_
  generalize hs₁ : ({ s.write .r8 (s.syms K.tsym) with lr := s.unknowns 0, unknowns := fun i => s.unknowns (i + 1) } : State) = s₁
  have k₁ : Rk [.r8] s s₁ := by
    rw [← hs₁]; exact ⟨(Kp.write s (s.syms K.tsym) (by decide : Reg.r8 ∈ [.r8])).gpr, rfl, rfl, rfl⟩
  have m₁ : s₁.mem = s.mem := by rw [← hs₁]; rfl
  have g₁ : s₁.gpr .r8 = s.syms K.tsym := by rw [← hs₁]; simp only [write_gpr, ite_true]
  have w₁ := hw.of_rk k₁
  refine wp_step (exec_li hrow) ?_
  refine wp_step exec_mul ?_
  refine wp_step exec_add ?_
  generalize hs₄ : ((s₁.write .r4 (BitVec.ofNat 64 (16 * K.L.M.n * K.H))).write .r4
    ((s₁.write .r4 (BitVec.ofNat 64 (16 * K.L.M.n * K.H))).gpr .r4 *
      (s₁.write .r4 (BitVec.ofNat 64 (16 * K.L.M.n * K.H))).gpr .r31)).write .r8 _ = s₄
  have k₄ : Kp [.r4, .r8] s₁ s₄ := by
    rw [← hs₄]
    exact ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))
  have g₄ : s₄.gpr .r8 = s.syms K.tsym + BitVec.ofNat 64 (16 * K.L.M.n * K.H * j) := by
    rw [← hs₄]
    simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    rw [g₁, k₁.g, gj, ← BitVec.ofNat_mul]
  have m₄ : s₄.mem = s.mem := by rw [← hs₄]; exact m₁
  have w₄ := w₁.of_kp k₄
  rw [List.append_assoc]
  refine wp_append (WP.mono (setConstW_ok w₄ (o := K.Q.x) (x := 0) (n := K.L.M.n) (by omega)
    (Nat.two_pow_pos _)) fun s₅ ⟨Ox, vx, k₅⟩ => ?_)
  refine wp_append (WP.mono (setConstW_ok (w₄.of_kp k₅) (o := K.Q.y) (x := 0) (n := K.L.M.n)
    (by rw [hy]; omega) (Nat.two_pow_pos _)) fun s₆ ⟨Oy, vy, k₆⟩ => ?_)
  refine wp_step (exec_li (by decide)) (WP.block_nil ?_)
  simp only [write_gpr, write_mem, reduceCtorEq, ite_false, ite_true]
  have k₄₆ : Kp [.r11] s₄ s₆ := k₅.trans k₆
  refine ⟨by rw [k₄₆.g, g₄], rfl, fun i hi => ?_, ?_, ?_⟩
  · by_cases hx : i < K.L.M.n
    · rw [Oy.word (by rw [hy]; omega) (by omega)]
      exact words_zero_of_wordsVal vx i hx
    · have e := words_zero_of_wordsVal vy (i - K.L.M.n) (by omega)
      rwa [hy, show K.Q.x + 8 * K.L.M.n + 8 * (i - K.L.M.n) = K.Q.x + 8 * i by omega] at e
  · exact (k₁.mono (by decide)).trans ((k₄.rk (rs' := [.r4, .r7, .r8, .r11])).trans
      ((k₄₆.rk (rs' := [.r4, .r7, .r8, .r11])).trans ((Kp.write s₆ 1 (rs := [.r7]) (by decide)).rk)))
  · rw [← m₄]
    exact (Ox.mono (Nat.le_refl _) (by omega)).trans (Oy.mono (by rw [hy]; omega) (by rw [hy]; omega))

/-- `Z = 1`, and `(0 : 1 : 0)` for a magnitude of zero. -/
theorem selectTail_ok (K : TCombCfg) {s : State} {base : Addr} {a : Nat}
    (hw : WsReg s base) (hq4 : K.Q.x % 4 = 0) (hz4 : K.zero % 4 = 0) (hq : K.Q.x + 24 * K.L.M.n ≤ 8192)
    (hzle : K.zero + 8 * K.L.M.n ≤ 8192)
    (hza : K.zero + 8 * K.L.M.n ≤ K.Q.x ∨ K.Q.x + 24 * K.L.M.n ≤ K.zero)
    (hone : K.one < 2 ^ (64 * K.L.M.n)) (ha : a < 2 ^ 63) (ga : s.gpr .r9 = BitVec.ofNat 64 a)
    (hz : wordsVal s.mem base K.zero K.L.M.n = 0) :
    WP isa (.block K.selectTail) s fun t =>
      wordsVal t.mem base K.Q.x K.L.M.n = wordsVal s.mem base K.Q.x K.L.M.n ∧
      wordsVal t.mem base K.Q.y K.L.M.n = (if a = 0 then K.one else wordsVal s.mem base K.Q.y K.L.M.n) ∧
      wordsVal t.mem base K.Q.z K.L.M.n = (if a = 0 then 0 else K.one) ∧
      Kp [.r4, .r5, .r7, .r10, .r11] s t ∧ Outside base K.Q.x (24 * K.L.M.n) s.mem t.mem := by
  have hy : K.Q.y = K.Q.x + 8 * K.L.M.n := rfl
  have hzz : K.Q.z = K.Q.x + 16 * K.L.M.n := by
    simp only [TCombCfg.Q, ptAt, elemBytes]; omega
  have hn := hw.nowrap
  unfold TCombCfg.selectTail
  rw [List.append_assoc, List.append_assoc, List.append_assoc, List.singleton_append]
  refine wp_append (WP.mono (setConstW_ok hw (o := K.Q.z) (n := K.L.M.n) (by rw [hzz]; omega) hone)
    fun s₁ ⟨O₁, one₁, k₁⟩ => ?_)
  refine wp_step (exec_li (by decide)) ?_
  refine wp_append (WP.mono (eqMask_ok (idx := .r7)) fun s₂ ⟨mask₂, k₂, mem₂⟩ => ?_)
  simp only [write_gpr, ite_true, reduceCtorEq, ite_false] at mask₂
  simp only [write_mem] at mem₂
  have k₁₂ : Kp [.r4, .r5, .r7, .r10, .r11] s s₂ :=
    ((k₁.mono (by decide)).trans (Kp.write _ _ (by decide))).trans (k₂.mono (by decide))
  have w₂ := hw.of_kp k₁₂
  have cm₂ : s₂.gpr .r10 = if decide (a = 0) then BitVec.allOnes 64 else 0 := by
    rw [mask₂, k₁.g, ga]
    exact eqMask_val (m := 0) ha (by decide)
  have zm₁ : wordsVal s₁.mem base K.zero K.L.M.n = 0 := by
    rw [O₁.wordsVal (by rw [hzz]; omega) (by omega), hz]
  refine wp_append (WP.mono (sel_ok (decide (a = 0)) K.L.M.n (o := K.Q.y) (a := K.Q.y) (b := K.Q.z) w₂.ws w₂.at3
    cm₂ (by rw [hy]; omega) (by rw [hy]; omega) (by rw [hzz]; omega) (by rw [hy]; omega) (by rw [hy]; omega)
    (by rw [hzz]; omega) (.inl (Nat.le_refl _)) (.inl (by rw [hy, hzz]; omega))) fun s₃ ⟨y₃, k₃, O₃⟩ => ?_)
  have w₃ := w₂.of_kp k₃
  refine WP.mono (sel_ok (decide (a = 0)) K.L.M.n (o := K.Q.z) (a := K.Q.z) (b := K.zero) w₃.ws w₃.at3
    (by rw [k₃.g, cm₂]) (by rw [hzz]; omega) (by rw [hzz]; omega) hz4 (by rw [hzz]; omega) (by rw [hzz]; omega)
    hzle (.inl (Nat.le_refl _)) (by rw [hzz]; omega)) fun s₄ ⟨z₄, k₄, O₄⟩ => ?_
  have oldx : wordsVal s₄.mem base K.Q.x K.L.M.n = wordsVal s.mem base K.Q.x K.L.M.n := by
    rw [O₄.wordsVal (by rw [hzz]; omega) (by omega), O₃.wordsVal (by rw [hy]; omega) (by omega),
      mem₂, O₁.wordsVal (by rw [hzz]; omega) (by omega)]
  have oldy : wordsVal s₁.mem base K.Q.y K.L.M.n = wordsVal s.mem base K.Q.y K.L.M.n := by
    rw [O₁.wordsVal (by rw [hy, hzz]; omega) (by omega)]
  have oz : wordsVal s₃.mem base K.Q.z K.L.M.n = K.one := by
    rw [O₃.wordsVal (by rw [hy, hzz]; omega) (by omega), mem₂, one₁]
  have zero₃ : wordsVal s₃.mem base K.zero K.L.M.n = 0 := by
    rw [O₃.wordsVal (by rw [hy]; omega) (by omega), mem₂, zm₁]
  refine ⟨oldx, ?_, ?_, k₁₂.trans ((k₃.mono (by decide)).trans (k₄.mono (by decide))), ?_⟩
  · rw [O₄.wordsVal (by rw [hy, hzz]; omega) (by omega), y₃, mem₂, one₁, oldy]
    simp only [decide_eq_true_eq]
  · rw [z₄, oz, zero₃]
    simp only [decide_eq_true_eq]
  · have O₂ : Outside base K.Q.x (24 * K.L.M.n) s₁.mem s₂.mem := by
      rw [mem₂]; exact Outside.refl _ _ _ _
    exact ((O₁.mono (by rw [hzz]; omega) (by rw [hzz]; omega)).trans O₂).trans
      ((O₃.mono (by rw [hy]; omega) (by rw [hy]; omega)).trans (O₄.mono (by rw [hzz]; omega) (by rw [hzz]; omega)))


/-- The whole selection: entry `a - 1` of the row at `X`, affine, or
`(0 : 1 : 0)` for `a = 0`. -/
theorem selectRow_ok (K : TCombCfg) {s : State} {base X : Addr} {a j : Nat}
    (hw : WsReg s base) (hq4 : K.Q.x % 4 = 0) (hz4 : K.zero % 4 = 0)
    (hq : K.Q.x + 24 * K.L.M.n ≤ 8192) (hzle : K.zero + 8 * K.L.M.n ≤ 8192)
    (hza : K.zero + 8 * K.L.M.n ≤ K.Q.x ∨ K.Q.x + 24 * K.L.M.n ≤ K.zero)
    (hone : K.one < 2 ^ (64 * K.L.M.n)) (hz : wordsVal s.mem base K.zero K.L.M.n = 0)
    (hn1 : 1 ≤ K.L.M.n) (hH : K.H + 1 ≤ 2 ^ 15) (hrow : 16 * K.L.M.n * K.H < 2 ^ 15) (ha : a ≤ K.H)
    (ga : s.gpr .r9 = BitVec.ofNat 64 a) (gj : s.gpr .r31 = BitVec.ofNat 64 j)
    (hX : s.syms K.tsym + BitVec.ofNat 64 (16 * K.L.M.n * K.H * j) = X) (R : RowOk K s base X) :
    WP isa K.select s fun t =>
      wordsVal t.mem base K.Q.x K.L.M.n =
        (if a = 0 then 0 else wordsVal s.mem X (16 * K.L.M.n * (a - 1)) K.L.M.n) ∧
      wordsVal t.mem base K.Q.y K.L.M.n =
        (if a = 0 then K.one else wordsVal s.mem X (16 * K.L.M.n * (a - 1) + 8 * K.L.M.n) K.L.M.n) ∧
      wordsVal t.mem base K.Q.z K.L.M.n = (if a = 0 then 0 else K.one) ∧
      Rk [.r4, .r5, .r6, .r7, .r8, .r10, .r11] s t ∧ Outside base K.Q.x (24 * K.L.M.n) s.mem t.mem := by
  have hy : K.Q.y = K.Q.x + 8 * K.L.M.n := rfl
  have hn := hw.nowrap
  have hHp : 1 ≤ K.H := Nat.two_pow_pos _
  have hrowle : 16 * K.L.M.n ≤ 16 * K.L.M.n * K.H := Nat.le_mul_of_pos_right _ hHp
  have span : 16 * K.L.M.n * (a - 1) + 16 * K.L.M.n ≤ 16 * K.L.M.n * K.H := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ (by omega)
  unfold TCombCfg.select
  rw [WP.seq_iff]
  refine WP.mono (selectSetup_ok K hw (by omega) gj hrow) fun s₁ ⟨p₁, g₁, z₁, k₁, O₁⟩ => ?_
  have w₁ := hw.of_rk k₁
  have R₁ : RowOk K s₁ base X := ⟨R.fit, by rw [k₁.rd, k₁.wr]; exact R.readable, R.apart⟩
  rw [WP.seq_iff]
  refine WP.mono (scan_loop_ok K (a := a) w₁.ws w₁.at3 hq4 (by omega) (by omega) R₁ (by rw [p₁]; exact hX) hn1 hH ha
    (by rw [k₁.g]; exact ga) g₁ z₁) fun s₂ I => ?_
  have keep₂ : Rk [.r4, .r5, .r6, .r7, .r8, .r10, .r11] s s₂ := (k₁.mono (by decide)).trans (I.keep.rk (by decide))
  have w₂ := hw.of_rk keep₂
  have source : ∀ i < 2 * K.L.M.n,
      word s₁.mem X (16 * K.L.M.n * (a - 1) + 8 * i) = word s.mem X (16 * K.L.M.n * (a - 1) + 8 * i) :=
    fun i hi => O₁.unch.far_word (fun w hw => by
      rw [List.mem_singleton] at hw; subst hw; dsimp only; omega) R.apart (by omega) R.fit
  have raw : ∀ i < 2 * K.L.M.n, word s₂.mem base (K.Q.x + 8 * i) =
      if a = 0 then 0 else word s.mem X (16 * K.L.M.n * (a - 1) + 8 * i) := by
    intro i hi
    rw [I.val i hi, source i hi]
    by_cases zero : a = 0
    · have no : ¬(1 ≤ a ∧ a < K.H + 1) := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false no), ite_eq_left_of_eq_true _ _ (eq_true zero)]
    · have yes : 1 ≤ a ∧ a < K.H + 1 := by omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true yes), ite_eq_right_of_eq_false _ _ (eq_false zero)]
  have x₂ : wordsVal s₂.mem base K.Q.x K.L.M.n =
      if a = 0 then 0 else wordsVal s.mem X (16 * K.L.M.n * (a - 1)) K.L.M.n := by
    by_cases zero : a = 0
    · simp only [zero, ↓reduceIte]
      exact wordsVal_zero_words fun i hi => by rw [raw i (by omega)]; simp only [zero, ↓reduceIte]
    · simp only [zero, ↓reduceIte]
      exact wordsVal_congr_words fun i hi => by rw [raw i (by omega)]; simp only [zero, ↓reduceIte]
  have y₂ : wordsVal s₂.mem base K.Q.y K.L.M.n =
      if a = 0 then 0 else wordsVal s.mem X (16 * K.L.M.n * (a - 1) + 8 * K.L.M.n) K.L.M.n := by
    have word' : ∀ i < K.L.M.n, word s₂.mem base (K.Q.y + 8 * i) =
        if a = 0 then 0 else word s.mem X (16 * K.L.M.n * (a - 1) + 8 * K.L.M.n + 8 * i) := by
      intro i hi
      have e := raw (K.L.M.n + i) (by omega)
      rw [show K.Q.x + 8 * (K.L.M.n + i) = K.Q.y + 8 * i by rw [hy]; omega,
        show 16 * K.L.M.n * (a - 1) + 8 * (K.L.M.n + i) = 16 * K.L.M.n * (a - 1) + 8 * K.L.M.n + 8 * i by
          omega] at e
      exact e
    by_cases zero : a = 0
    · simp only [zero, ↓reduceIte]
      exact wordsVal_zero_words fun i hi => by rw [word' i hi]; simp only [zero, ↓reduceIte]
    · simp only [zero, ↓reduceIte]
      exact wordsVal_congr_words fun i hi => by rw [word' i hi]; simp only [zero, ↓reduceIte]
  have zero₂ : wordsVal s₂.mem base K.zero K.L.M.n = 0 := by
    rw [I.unch.wordsVal (by omega) (by omega), O₁.wordsVal (by omega) (by omega), hz]
  refine WP.mono (selectTail_ok K (a := a) w₂ hq4 hz4 hq hzle hza hone (by omega)
    (by rw [keep₂.g]; exact ga) zero₂) fun s₃ ⟨x₃, y₃, z₃, k₃, O₃⟩ => ?_
  refine ⟨by rw [x₃, x₂], ?_, z₃, keep₂.trans (k₃.rk (by decide)), ?_⟩
  · rw [y₃, y₂]
    by_cases zero : a = 0 <;> simp only [zero, ↓reduceIte]
  · exact ((O₁.mono (Nat.le_refl _) (by omega)).trans (I.unch.mono (Nat.le_refl _) (by omega))).trans O₃

/-- The selection from the table's row `j`: its entry `a - 1`, affine, or
`(0 : 1 : 0)` for `a = 0`. -/
theorem selectTable_ok (K : TCombCfg) {s : State} {base T : Addr} {a j R p : Nat}
    {tbl : List (List (Nat × Nat))}
    (hw : WsReg s base) (hq4 : K.Q.x % 4 = 0) (hz4 : K.zero % 4 = 0)
    (hq : K.Q.x + 24 * K.L.M.n ≤ 8192) (hzle : K.zero + 8 * K.L.M.n ≤ 8192)
    (hza : K.zero + 8 * K.L.M.n ≤ K.Q.x ∨ K.Q.x + 24 * K.L.M.n ≤ K.zero)
    (hone : K.one < 2 ^ (64 * K.L.M.n)) (hz : wordsVal s.mem base K.zero K.L.M.n = 0)
    (hn1 : 1 ≤ K.L.M.n) (hH : K.H + 1 ≤ 2 ^ 15) (hrow : 16 * K.L.M.n * K.H < 2 ^ 15) (ha : a ≤ K.H)
    (ga : s.gpr .r9 = BitVec.ofNat 64 a) (gj : s.gpr .r31 = BitVec.ofNat 64 j)
    (hT : TableMem s T (tcombWords K.L.M.n R p tbl)) (sym : s.syms K.tsym = T)
    (hJ : tbl.length = K.J) (hRows : ∀ j < K.J, (tbl.getD j []).length = K.H) (hj : j < K.J)
    (hJ32 : K.J < 2 ^ 32) (hp : 0 < p) (hpfit : p ≤ 2 ^ (64 * K.L.M.n))
    (hd : Region.Disjoint ⟨T, 8 * (tcombWords K.L.M.n R p tbl).length⟩ ⟨base, 8192⟩) :
    WP isa K.select s fun t =>
      wordsVal t.mem base K.Q.x K.L.M.n = (if a = 0 then 0 else (combAt tbl j (a - 1)).1 * R % p) ∧
      wordsVal t.mem base K.Q.y K.L.M.n = (if a = 0 then K.one else (combAt tbl j (a - 1)).2 * R % p) ∧
      wordsVal t.mem base K.Q.z K.L.M.n = (if a = 0 then 0 else K.one) ∧
      Rk [.r4, .r5, .r6, .r7, .r8, .r10, .r11] s t ∧ Outside base K.Q.x (24 * K.L.M.n) s.mem t.mem := by
  have total := table_bytes (n := K.L.M.n) (R := R) (p := p) hJ hRows
  have hHp : 1 ≤ K.H := Nat.two_pow_pos _
  have span : 16 * K.L.M.n * K.H * j + 16 * K.L.M.n * K.H ≤ 8 * (tcombWords K.L.M.n R p tbl).length := by
    rw [total, ← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hj
  have fit := hT.fit
  have hpos : 16 ≤ 16 * K.L.M.n * K.H := Nat.le_trans (by omega) (Nat.le_mul_of_pos_right _ hHp)
  have hb : 16 * K.L.M.n * K.H * K.J ≤ 2 ^ 15 * 2 ^ 32 := Nat.mul_le_mul (Nat.le_of_lt hrow) (Nat.le_of_lt hJ32)
  rw [total] at span fit
  let X := T + BitVec.ofNat 64 (16 * K.L.M.n * K.H * j)
  have row : RowOk K s base X := by
    have rd := hT.readable
    rw [total] at rd hd
    refine ⟨?_, CallLay.inRegions_sub rd span (by omega), hd.sub_left (Offset.sub_base T span)⟩
    dsimp only [X]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 16 * K.L.M.n * K.H * j < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : T.toNat + 16 * K.L.M.n * K.H * j < 2 ^ 64)]
    omega
  have entry := tcombWords_entry hT.words hJ hRows hj (show a - 1 < K.H by omega)
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) hpfit) (Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) hpfit)
  rw [Nat.mul_comm j (16 * K.L.M.n * K.H)] at entry
  refine WP.mono (selectRow_ok K hw hq4 hz4 hq hzle hza hone hz hn1 hH hrow ha ga gj
    (by rw [sym]) row) fun t ⟨x, y, z, keep, unch⟩ => ?_
  exact ⟨by rw [x, entry.1], by rw [y, entry.2], z, keep, unch⟩

end VG.Proof.Weierstrass.PPC64LE.TComb
