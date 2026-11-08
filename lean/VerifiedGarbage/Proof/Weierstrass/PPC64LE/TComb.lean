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
public import VerifiedGarbage.Proof.Weierstrass.CombDigitW
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Weierstrass.CombDigitTopW
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Bits
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontFn
import VerifiedGarbage.Proof.Weierstrass.CombPointW
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.LadderPCall
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Loop
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow

/-!
# The comb's `[k]G`, on PPC64LE

As on 32-bit ARM (`Proof/Weierstrass/Arm/TCombCorrect.lean` and the modules
it imports): the side conditions of a comb (`Config`), what every iteration
keeps (`Inputs`), the signed entry, the addition, an iteration, and
`comb_ok`: `R = [k]G`, reduced, with only the registers of `powClob` and the
memory of `writes` changed. The selection of an entry (`selectTable_ok`)
and the digits (`digit_ok`, `signMask_ok`) are 32-bit ARM's
(`Proof/Weierstrass/Arm/TCombSelect.lean`, `TCombDigit.lean`, `TCombSign.lean`).
-/

-- separate module: the comb of every curve on PPC64LE, which each curve's configuration imports

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.TComb

open VG VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass.PPC64LE.Point
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Point VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Impl.Weierstrass.Point (elemBytes ownAt aAt b3At oAt pAt qAt)
open VG.Impl.Weierstrass.PPC64LE.Mont (own)
open Spec.Weierstrass

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
  /-- The entry is selected to the point functions' `Q`. -/
  qAt : K.qBase = qAt K.L.M.n

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
theorem Q_eq {K : TCombCfg} (h : Layout K) : K.Q = ⟨qAt K.L.M.n, qAt K.L.M.n + elemBytes K.L.M.n,
    qAt K.L.M.n + 2 * elemBytes K.L.M.n⟩ := by
  simp only [TCombCfg.Q, ptAt, h.qAt]
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

/-- `r9 = Σ_{i<k} 2^i v (d + i)` from the bytes `v (d + i)` at `bits + d + i`
from `r4`. -/
theorem hornerAt_ok (K : TCombCfg) {v : Nat → Nat} (hv : ∀ i, v i ≤ 1) {base : Addr} {W : Nat} :
    ∀ k d (s : State), Ws s base 8192 → At s base .r4 W → k < 63 → K.L.bits + d + k < 2 ^ 15 →
    W + K.L.bits + d + k ≤ 8192 →
    (∀ i < k, s.mem (off base (W + K.L.bits + d + i)) = BitVec.ofNat 8 (v (d + i))) →
    WP isa (.block (K.hornerAt d k)) s fun t =>
      t.gpr .r9 = BitVec.ofNat 64 (hornerVal v d k) ∧ Kp [.r5, .r9] s t ∧ t.mem = s.mem
  | 0, d, s, _, _, _, _, _, _ => by
    unfold TCombCfg.hornerAt
    refine wp_step (exec_li (by decide)) (WP.block_nil ⟨?_, Kp.write _ _ (by decide), rfl⟩)
    simp only [write_gpr, ite_true]; rfl
  | k + 1, d, s, hs, h4, hk, ho, hw, hb => by
    rw [TCombCfg.hornerAt]
    refine wp_append (WP.mono (hornerAt_ok K hv k (d + 1) s hs h4 (by omega) (by omega) (by omega)
      fun i hi => by
        rw [show W + K.L.bits + (d + 1) + i = W + K.L.bits + d + (i + 1) by omega,
          show d + 1 + i = d + (i + 1) by omega]
        exact hb (i + 1) (by omega)) fun s₁ ⟨v₁, k₁, m₁⟩ => ?_)
    have h0 := hb 0 (by omega)
    simp only [Nat.add_zero] at h0
    refine wp_step exec_add ?_
    refine wp_step (lbz_ok ((k₁.ws hs).write _ _) ((k₁.at h4).write (d := .r9) _) (by decide)
      (d := K.L.bits + d) (by omega)) ?_
    refine wp_step exec_add (WP.block_nil ?_)
    simp only [write_gpr, write_mem, ite_true, reduceCtorEq, ite_false]
    refine ⟨?_, k₁.trans ((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide)))), m₁⟩
    rw [v₁, m₁, show W + (K.L.bits + d) = W + K.L.bits + d by omega, h0]
    have hn := hornerVal_lt hv (d + 1) k
    have hvd := hv d
    have hp : 2 ^ k < 2 ^ 62 := Nat.pow_lt_pow_right (by decide) (by omega)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, hornerVal]
    rw [Nat.mod_eq_of_lt (by omega : hornerVal v (d + 1) k < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : v d < 2 ^ 8), Nat.mod_eq_of_lt (by omega : v d < 2 ^ 64)]
    omega

/-- `r4 = r3 + w j`, for `j` in `r31`. -/
theorem windowIndex_ok (K : TCombCfg) {s : State} {base : Addr} {j : Nat}
    (h3 : At s base .r3 0) (hw : K.w < 2 ^ 15) (gj : s.gpr .r31 = BitVec.ofNat 64 j) :
    WP isa (.block K.windowIndex) s fun t =>
      At t base .r4 (K.w * j) ∧ Kp [.r4] s t ∧ t.mem = s.mem := by
  unfold TCombCfg.windowIndex
  refine wp_step (exec_li hw) ?_
  refine wp_step exec_mul ?_
  refine wp_step exec_add (WP.block_nil ?_)
  refine ⟨?_, ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide)), rfl⟩
  simp only [At, write_gpr, ite_true, reduceCtorEq, ite_false]
  rw [h3, gj, ← BitVec.ofNat_mul, off, off, BitVec.add_zero]

/-- `r6 = r31 - (J - 1)`, zero exactly for the last window. -/
theorem lastTest_ok (K : TCombCfg) {s : State} {j : Nat} (hj : j < 2 ^ 64) (hJ : K.J - 1 ≤ 2 ^ 15)
    (gj : s.gpr .r31 = BitVec.ofNat 64 j) :
    WP isa (.block K.lastTest) s fun t =>
      isa.eval TCombCfg.isLast t = some (decide (j = K.J - 1)) ∧ Kp [.r6] s t ∧ t.mem = s.mem := by
  unfold TCombCfg.lastTest
  refine wp_step (exec_subi (by decide) hJ) (WP.block_nil ⟨?_, Kp.write _ _ (by decide), rfl⟩)
  rw [eval_zero]
  simp only [write_gpr, ite_true, gj]
  congr 1
  by_cases e : j = K.J - 1
  · rw [e, BitVec.sub_self]; simp
  · have hne : BitVec.ofNat 64 j - BitVec.ofNat 64 (K.J - 1) ≠ 0#64 := fun h0 => by
      have e' := congrArg (fun z : BitVec 64 => z + BitVec.ofNat 64 (K.J - 1)) h0
      simp only [BitVec.sub_add_cancel, BitVec.zero_add] at e'
      have := congrArg BitVec.toNat e'
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (by omega)] at this
      exact e this
    simp [hne, e]

/-- The 64-bit signed-digit magnitude. -/
theorem magH_fact64 : ∀ w < 9, ∀ v < 2 ^ w,
    (BitVec.ofNat 64 v - BitVec.ofNat 64 (2 ^ (w - 1)) ^^^
        (BitVec.ofNat 64 0 - (BitVec.ofNat 64 v - BitVec.ofNat 64 (2 ^ (w - 1))) >>> 63)) -
      (BitVec.ofNat 64 0 - (BitVec.ofNat 64 v - BitVec.ofNat 64 (2 ^ (w - 1))) >>> 63) =
      BitVec.ofNat 64 (magH (2 ^ (w - 1)) v) := by
  decide +kernel

/-- `r9 = |v - H|` from the window `v` in `r9`. -/
theorem magnitude_ok (K : TCombCfg) {s : State} {v : Nat} (hw : K.w < 9) (hv : v < 2 ^ K.w)
    (gv : s.gpr .r9 = BitVec.ofNat 64 v) :
    WP isa (.block K.magnitude) s fun t =>
      t.gpr .r9 = BitVec.ofNat 64 (magH K.H v) ∧ Kp [.r4, .r5, .r9] s t ∧ t.mem = s.mem := by
  have hH : K.H ≤ 2 ^ 15 := Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 15 by omega))
    (by decide)
  unfold TCombCfg.magnitude
  refine wp_step (exec_subi (by decide) hH) ?_
  refine wp_step (exec_lsr_d (by decide)) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub ?_
  refine wp_step exec_logic ?_
  refine wp_step exec_sub (WP.block_nil ?_)
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp only [write_gpr, ite_true, reduceCtorEq, ite_false, gv]
    exact magH_fact64 K.w hw v hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2.1, hr.2.2, ite_false]

/-- The window's `count` bits by Horner's rule. -/
theorem hornerWindow_ok (K : TCombCfg) {s : State} {base : Addr} {j count : Nat}
    (hs : Ws s base 8192) (h4 : At s base .r4 (K.w * j)) (hc : count ≤ K.w) (hw : K.w < 9)
    (ho : K.L.bits + K.w < 2 ^ 15) (hl : K.w * j + K.L.bits + count ≤ 8192)
    {v : Nat → Nat} (hv : ∀ i, v i ≤ 1)
    (hb : ∀ i < count, s.mem (off base (K.L.bits + K.w * j + i)) = BitVec.ofNat 8 (v i)) :
    WP isa (.block (K.horner count)) s fun t =>
      t.gpr .r9 = BitVec.ofNat 64 (hornerVal v 0 count) ∧ Kp [.r5, .r9] s t ∧ t.mem = s.mem := by
  unfold TCombCfg.horner
  exact hornerAt_ok K hv count 0 s hs h4 (by omega) (by omega) (by omega) fun i hi => by
    rw [show K.w * j + K.L.bits + 0 + i = K.L.bits + K.w * j + i by omega, Nat.zero_add]
    exact hb i hi

/-- The digit's magnitude `|k_j - H|` into `r9`, from the window's bits
(only its real ones, for the last window). -/
theorem digit_ok (K : TCombCfg) {s : State} {base : Addr} {j k : Nat}
    (hs : Ws s base 8192) (h3 : At s base .r3 0) (hw : K.w < 9) (hj : j < K.J) (hJ : K.J ≤ 2 ^ 15)
    (start : K.w * (K.J - 1) ≤ K.L.nbits) (cover : K.L.nbits ≤ K.w * K.J)
    (ho : K.L.bits + K.w < 2 ^ 15) (hl : K.L.bits + K.L.nbits ≤ 8192) (hk : k < 2 ^ K.L.nbits)
    (gj : s.gpr .r31 = BitVec.ofNat 64 j)
    (hb : ∀ i < K.L.nbits, s.mem (off base (K.L.bits + i)) = if k.testBit i then 1 else 0) :
    WP isa K.digit s fun t =>
      t.gpr .r9 = BitVec.ofNat 64 (magH K.H (combWin K.w k j)) ∧ Kp [.r4, .r5, .r6, .r9] s t ∧
        t.mem = s.mem := by
  let count := if j = K.J - 1 then K.topBits else K.w
  have bounds := windowBits_bounds hj start cover
  change count ≤ K.w ∧ K.w * j + count ≤ K.L.nbits ∧ (count = K.w ∨ K.w * j + count = K.L.nbits) at bounds
  let v := fun i => (k.testBit (K.w * j + i)).toNat
  have hv : ∀ i, v i ≤ 1 := fun i => by dsimp only [v]; cases k.testBit (K.w * j + i) <;> decide
  have bytes : ∀ i < count, s.mem (off base (K.L.bits + K.w * j + i)) = BitVec.ofNat 8 (v i) := by
    intro i hi
    rw [show K.L.bits + K.w * j + i = K.L.bits + (K.w * j + i) by omega, hb _ (by omega)]
    dsimp only [v]
    cases k.testBit (K.w * j + i) <;> rfl
  unfold TCombCfg.digit
  rw [WP.seq_iff]
  refine WP.mono (windowIndex_ok K h3 (by omega) gj) fun s₁ ⟨p₁, k₁, m₁⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (lastTest_ok K (j := j) (by omega) (by omega) (by rw [k₁.g]; exact gj))
    fun s₂ ⟨z₂, k₂, m₂⟩ => ?_
  have k₁₂ : Kp [.r4, .r6] s s₂ := (k₁.mono (by decide)).trans (k₂.mono (by decide))
  have hh := hornerWindow_ok K (s := s₂) (j := j) (count := count) (k₁₂.ws hs)
    (by rw [At, k₂.g]; exact p₁) bounds.1 hw ho (by omega) hv
    (by intro i hi; rw [m₂, m₁]; exact bytes i hi)
  have decode : WP isa (.ite TCombCfg.isLast (.block (K.horner K.topBits)) (.block (K.horner K.w))) s₂
      fun t => t.gpr .r9 = BitVec.ofNat 64 (hornerVal v 0 count) ∧ Kp [.r5, .r9] s₂ t ∧ t.mem = s₂.mem := by
    by_cases h : j = K.J - 1
    · refine WP.ite true (by rw [z₂]; simp [h]) (fun _ => ?_) (fun hf => by cases hf)
      simpa only [count, h, ↓reduceIte] using hh
    · refine WP.ite false (by rw [z₂]; simp [h]) (fun ht => by cases ht) (fun _ => ?_)
      simpa only [count, h, ↓reduceIte] using hh
  rw [WP.seq_iff]
  refine WP.mono decode fun s₃ ⟨v₃, k₃, m₃⟩ => ?_
  have hvlt : hornerVal v 0 count < 2 ^ K.w :=
    Nat.lt_of_lt_of_le (hornerVal_lt hv 0 count) (Nat.pow_le_pow_right (by decide) bounds.1)
  refine WP.mono (magnitude_ok K hw hvlt v₃) fun s₄ ⟨v₄, k₄, m₄⟩ => ⟨?_, ?_, by rw [m₄, m₃, m₂, m₁]⟩
  · rw [v₄]
    change BitVec.ofNat 64 (magH K.H (hornerVal v 0 count)) = _
    rw [window_without_padding bounds.1 bounds.2.2 hk]
  · exact ((k₁₂.mono (by decide)).trans (k₃.mono (by decide))).trans (k₄.mono (by decide))

/-- The mask `r10` of the window's top bit being clear. -/
theorem signRead_ok (K : TCombCfg) {s : State} {base : Addr} {j : Nat} {b : Bool}
    (hs : Ws s base 8192) (h3 : At s base .r3 0) (hw : 1 ≤ K.w ∧ K.w < 9)
    (ho : K.L.bits + K.w < 2 ^ 15) (hl : K.L.bits + K.w * j + K.w ≤ 8192)
    (gj : s.gpr .r31 = BitVec.ofNat 64 j)
    (hb : s.mem (off base (K.L.bits + K.w * j + K.w - 1)) = if b then 1 else 0) :
    WP isa (.block K.signRead) s fun t =>
      t.gpr .r10 = (if b then 0 else BitVec.allOnes 64) ∧ Kp [.r4, .r10] s t ∧ t.mem = s.mem := by
  unfold TCombCfg.signRead
  refine wp_append (WP.mono (windowIndex_ok K h3 (by omega) gj) fun s₁ ⟨p₁, k₁, m₁⟩ => ?_)
  refine wp_step (lbz_ok (k₁.ws hs) p₁ (by decide) (d := K.L.bits + K.w - 1) (by omega)) ?_
  refine wp_step (exec_subi (by decide) (by decide)) (WP.block_nil ?_)
  simp only [write_gpr, write_mem, ite_true, reduceCtorEq, ite_false]
  refine ⟨?_, (k₁.mono (by decide)).trans ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))), m₁⟩
  rw [m₁, show K.w * j + (K.L.bits + K.w - 1) = K.L.bits + K.w * j + K.w - 1 by omega, hb]
  cases b <;> rfl

/-- The mask `r10` of the digit `k_j - H` being negative. -/
theorem signMask_ok (K : TCombCfg) {s : State} {base : Addr} {j k : Nat}
    (hs : Ws s base 8192) (h3 : At s base .r3 0) (hw : 1 ≤ K.w ∧ K.w < 9) (hj : j < K.J)
    (hJ : K.J ≤ 2 ^ 15) (start : K.w * (K.J - 1) ≤ K.L.nbits) (cover : K.L.nbits ≤ K.w * K.J)
    (ho : K.L.bits + K.w < 2 ^ 15) (hl : K.L.bits + K.L.nbits ≤ 8192) (hk : k < 2 ^ K.L.nbits)
    (gj : s.gpr .r31 = BitVec.ofNat 64 j)
    (hb : ∀ i < K.L.nbits, s.mem (off base (K.L.bits + i)) = if k.testBit i then 1 else 0) :
    WP isa K.signMask s fun t =>
      t.gpr .r10 = (if K.H ≤ combWin K.w k j then 0 else BitVec.allOnes 64) ∧
        Kp [.r4, .r6, .r10] s t ∧ t.mem = s.mem := by
  have bounds := windowBits_bounds hj start cover
  change (if j = K.J - 1 then K.topBits else K.w) ≤ K.w ∧
    K.w * j + (if j = K.J - 1 then K.topBits else K.w) ≤ K.L.nbits ∧
    ((if j = K.J - 1 then K.topBits else K.w) = K.w ∨
      K.w * j + (if j = K.J - 1 then K.topBits else K.w) = K.L.nbits) at bounds
  have top : k.testBit (K.w * j + (K.w - 1)) = decide (K.H ≤ combWin K.w k j) := testBit_top k K.w j hw.1
  have read : ∀ u : State, Kp [.r6] s u → u.mem = s.mem → K.w * j + K.w ≤ K.L.nbits →
      WP isa (.block K.signRead) u fun t =>
        t.gpr .r10 = (if K.H ≤ combWin K.w k j then 0 else BitVec.allOnes 64) ∧
          Kp [.r4, .r6, .r10] s t ∧ t.mem = s.mem := by
    intro u ku mu hr
    refine WP.mono (signRead_ok K (j := j) (b := k.testBit (K.w * j + (K.w - 1))) (ku.ws hs) (ku.at h3) hw ho
      (by omega) (by rw [ku.g]; exact gj) ?_) fun t ⟨val, kt, mt⟩ => ⟨?_, (ku.mono (by decide)).trans
        (kt.mono (by decide)), mt.trans mu⟩
    · rw [mu, show K.L.bits + K.w * j + K.w - 1 = K.L.bits + (K.w * j + (K.w - 1)) by omega]
      exact hb _ (by omega)
    · rw [val, top]
      by_cases h : K.H ≤ combWin K.w k j <;> simp [h]
  unfold TCombCfg.signMask
  by_cases shortTop : K.topBits < K.w
  · simp only [shortTop, ↓reduceIte]
    rw [WP.seq_iff]
    refine WP.mono (lastTest_ok K (j := j) (by omega) (by omega) gj) fun u ⟨zero, ku, mu⟩ => ?_
    by_cases last : j = K.J - 1
    · refine WP.ite true (by rw [zero]; simp [last]) (fun _ => ?_) (fun hf => by cases hf)
      have e : K.w * j + K.topBits = K.L.nbits := by
        rw [last]; exact Nat.add_sub_of_le start
      have hfalse : k.testBit (K.w * j + (K.w - 1)) = false := by
        rw [Nat.testBit_eq_decide_div_mod_eq,
          Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) (by omega)))]
        decide
      have high : ¬ K.H ≤ combWin K.w k j := fun h => by
        rw [top, decide_eq_true h] at hfalse; cases hfalse
      refine wp_step (exec_li (by decide)) ?_
      refine wp_step (exec_subi (by decide) (by decide)) (WP.block_nil ?_)
      simp only [write_gpr, write_mem, ite_true]
      rw [ite_eq_right_of_eq_false _ _ (eq_false high)]
      exact ⟨by decide, (ku.mono (by decide)).trans ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))),
        mu⟩
    · refine WP.ite false (by rw [zero]; simp [last]) (fun ht => by cases ht) (fun _ => ?_)
      exact read u ku mu (by simpa only [last, ↓reduceIte] using bounds.2.1)
  · simp only [shortTop, ↓reduceIte]
    apply read s (Kp.refl _ _) rfl
    have cw : K.w ≤ (if j = K.J - 1 then K.topBits else K.w) := by split <;> omega
    omega

/-- The side conditions of a comb, which do not depend on the scalar. -/
structure Config (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) (start : Nat × Nat) : Prop where
  layout : Layout K
  fieldK : K.F.k = K.L.M.n
  fieldM : K.F.m = C.p
  modulus : ModOk K.L.M.n C.p
  odd : C.p % 2 = 1
  unit : UnitMod C.p (2 ^ (64 * K.L.M.n))
  tables : CombOkW C K.w K.J tbl start
  one_lt : K.one < C.p
  one : toM C.p (2 ^ (64 * K.L.M.n)) K.one = 1
  startX : K.start.1 = start.1 * 2 ^ (64 * K.L.M.n) % C.p
  startY : K.start.2 = start.2 * 2 ^ (64 * K.L.M.n) % C.p
  w1 : 1 ≤ K.w
  w9 : K.w < 9
  J1 : 1 ≤ K.J
  J15 : K.J < 2 ^ 15
  startBits : K.w * (K.J - 1) ≤ K.L.nbits
  coverBits : K.L.nbits ≤ K.w * K.J
  bitsOff : K.L.bits + K.w < 2 ^ 15
  row : 16 * K.L.M.n * K.H < 2 ^ 15

theorem Config.magnitude {K : TCombCfg} {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : Config K C tbl start) (k j : Nat) : magH K.H (combWin K.w k j) ≤ K.H := by
  apply magH_le
  have pow : 2 ^ K.w = 2 * K.H := by
    change 2 ^ K.w = 2 * 2 ^ (K.w - 1)
    calc
      2 ^ K.w = 2 ^ ((K.w - 1) + 1) := congrArg (fun n => 2 ^ n) (by have := h.w1; omega)
      _ = 2 * 2 ^ (K.w - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [← pow]
  exact combWin_lt _ _ _

/-- The table's words, for curve `C`. -/
def tableWords (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) : List (BitVec 64) :=
  tcombWords K.L.M.n (2 ^ (64 * K.L.M.n)) C.p tbl

/-- What every iteration keeps: the working space, the table, zero, the
scalar's bits, and the point functions' `a` and `3b`. -/
structure Inputs (K : TCombCfg) (base T : Addr) (ws : List (BitVec 64)) (k a b : Nat) (s : State) : Prop where
  wsr : WsReg s base
  table : TableMem s T ws
  symbol : s.syms K.tsym = T
  zero : wordsVal s.mem base K.zero K.L.M.n = 0
  bits : ∀ i < K.L.nbits, s.mem (off base (K.L.bits + i)) = if k.testBit i then 1 else 0
  coeffA : wordsVal s.mem base (aAt K.L.M.n) K.L.M.n = a
  coeffB : wordsVal s.mem base (b3At K.L.M.n) K.L.M.n = b

/-- `Inputs` for the curve `C`: `a` and `3b` in Montgomery's form. -/
abbrev CurveInputs (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) (base T : Addr) (k : Nat)
    (s : State) : Prop :=
  Inputs K base T (tableWords K C tbl) k (C.a * 2 ^ (64 * K.L.M.n) % C.p)
    ((3 * C.b) * 2 ^ (64 * K.L.M.n) % C.p) s

theorem Layout.zero_apart {K : TCombCfg} (h : Layout K) :
    ∀ r ∈ loopWrites K, K.zero + 8 * K.L.M.n ≤ r.1 ∨ r.1 + r.2 ≤ K.zero := by
  have := lay_nums h.point.k3 h.point.k6
  have low := h.low K.zero (by simp)
  have neg := h.negApart K.zero (by simp)
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.zeroApart _ (by simp)
  · exact h.zeroApart _ (by simp)
  · exact h.zeroApart _ (by simp)
  · exact neg.symm
  · exact .inl low
  · exact .inl (by dsimp only; omega_arith)

theorem Layout.params_apart {K : TCombCfg} (h : Layout K) :
    ∀ x ∈ [aAt K.L.M.n, b3At K.L.M.n], ∀ r ∈ loopWrites K, x + 8 * K.L.M.n ≤ r.1 ∨ r.1 + r.2 ≤ x := by
  have := lay_nums h.point.k3 h.point.k6
  have low := h.low
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at low
  intro x hx r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hx with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; omega_arith)

theorem Inputs.keep {K : TCombCfg} {base T : Addr} {ws : List (BitVec 64)} {k a b : Nat}
    {s t : State} {rs : List Reg} (i : Inputs K base T ws k a b s) (h : Layout K)
    (hd : Region.Disjoint ⟨T, 8 * ws.length⟩ ⟨base, 8192⟩)
    (keep : Rk rs s t) (r3 : Reg.r3 ∉ rs) (mem : Unch base (loopWrites K) s.mem t.mem)
    (syms : t.syms = s.syms) : Inputs K base T ws k a b t := by
  have := lay_nums h.point.k3 h.point.k6
  have bounded := h.loop_bounded
  have nowrap := i.wsr.nowrap
  have hb := h.point.bits
  have hbe := h.point.bitsE
  have params : ∀ x ∈ [aAt K.L.M.n, b3At K.L.M.n],
      wordsVal t.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n := by
    intro x hx
    apply mem.wordsVal (h.params_apart x hx)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> omega_arith
  refine ⟨i.wsr.of_rk keep r3, i.table.unch (by rw [keep.rd, keep.wr]) mem bounded' hd,
    by rw [syms]; exact i.symbol, ?_, ?_, ?_, ?_⟩
  · rw [mem.wordsVal h.zero_apart (by have := h.low K.zero (by simp); omega_arith), i.zero]
  · intro j hj
    rw [mem.byte (fun w hw => .inr (by have := bounded w hw; omega_arith)) (by omega_arith), i.bits j hj]
  · rw [params _ (by simp), i.coeffA]
  · rw [params _ (by simp), i.coeffB]
where
  bounded' : ∀ w ∈ loopWrites K, w.1 + w.2 ≤ 8192 := fun w hw => by
    have := h.loop_bounded w hw; omega

/-! ## The start -/

/-- `a` and `3b` to the point functions' slots, `R = S`, and `r31 = J`. -/
theorem start_ok (K : TCombCfg) {s : State} {base : Addr} (h : Layout K) (hw : WsReg s base)
    (hx : K.start.1 < 2 ^ (64 * K.L.M.n)) (hy : K.start.2 < 2 ^ (64 * K.L.M.n))
    (hz : K.one < 2 ^ (64 * K.L.M.n)) (hJ : K.J < 2 ^ 15) :
    WP isa (.block (ladderSetup K.L ++ Impl.Mont.PPC64LE.setConst K.L.M.n K.L.R.x K.start.1 ++
      Impl.Mont.PPC64LE.setConst K.L.M.n K.L.R.y K.start.2 ++
      Impl.Mont.PPC64LE.setConst K.L.M.n K.L.R.z K.one ++ ([.li .r31 K.J] : List Instr))) s fun t =>
      Kp [.r4, .r11, .r31] s t ∧ Unch base (writes K) s.mem t.mem ∧ CpOk K.L base t.mem s.mem ∧
      t.gpr .r31 = BitVec.ofNat 64 K.J ∧
      wordsVal t.mem base K.L.R.x K.L.M.n = K.start.1 ∧ wordsVal t.mem base K.L.R.y K.L.M.n = K.start.2 ∧
      wordsVal t.mem base K.L.R.z K.L.M.n = K.one := by
  have := lay_nums h.point.k3 h.point.k6
  have low := h.low
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at low
  obtain ⟨rx, ry, rz, -, -⟩ := low
  obtain ⟨rxy, rxz, ryz⟩ := h.point.rne
  have nowrap := hw.nowrap
  rw [List.append_assoc, List.append_assoc, List.append_assoc]
  refine wp_append (WP.mono (ladderSetup_ok hw h.point) fun u ⟨ku, ou, cp⟩ => ?_)
  have wu := hw.of_kp ku
  refine wp_append (WP.mono (setConstW_ok wu (o := K.L.R.x) (by omega_arith) hx) fun v ⟨ov, xv, kv⟩ => ?_)
  have wv := wu.of_kp kv
  refine wp_append (WP.mono (setConstW_ok wv (o := K.L.R.y) (by omega_arith) hy) fun a ⟨oa, ya, ka⟩ => ?_)
  have wa := wv.of_kp ka
  refine wp_append (WP.mono (setConstW_ok wa (o := K.L.R.z) (by omega_arith) hz) fun b ⟨ob, zb, kb⟩ => ?_)
  refine wp_step (exec_li hJ) (WP.block_nil ?_)
  simp only [write_gpr, write_mem, ite_true]
  have ub : Unch base [(K.L.R.x, 8 * K.L.M.n), (K.L.R.y, 8 * K.L.M.n), (K.L.R.z, 8 * K.L.M.n)] u.mem b.mem :=
    ov.unch.trans (oa.unch.trans ob.unch)
  refine ⟨((ku.mono (by decide)).trans ((kv.mono (by decide)).trans ((ka.mono (by decide)).trans
      (kb.mono (by decide))))).trans (Kp.write _ _ (by decide)), ?_, ?_, trivial, ?_, ?_, zb⟩
  · apply (ou.trans ub).mono
    intro w hw'
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | (rfl | rfl | rfl) <;> simp [writes]
  · apply cp.keep h.point.k3 h.point.k6 ub
    intro w hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl <;> (left; dsimp only; omega_arith)
  · rw [ob.wordsVal (by omega_arith) (by omega_arith), oa.wordsVal (by omega_arith) (by omega_arith), xv]
  · rw [ob.wordsVal (by omega_arith) (by omega_arith), ya]


/-! ## The signed entry -/

theorem q_lay {K : TCombCfg} (h : Layout K) :
    oAt K.L.M.n + 48 * K.L.M.n = K.Q.x ∧ K.Q.y = K.Q.x + 8 * K.L.M.n ∧ K.Q.z = K.Q.x + 16 * K.L.M.n ∧
      K.Q.x + 24 * K.L.M.n = aAt K.L.M.n ∧ aAt K.L.M.n + 16 * K.L.M.n + 64 + 48 * K.L.M.n = own K.L.M.n ∧
      own K.L.M.n + 64 * K.L.M.n = 4096 ∧ b3At K.L.M.n = aAt K.L.M.n + 8 * K.L.M.n ∧
      ownAt K.L.M.n = aAt K.L.M.n + 16 * K.L.M.n ∧ K.Q.x % 4 = 0 := by
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, ho, -, h8⟩ := lay_nums h.point.k3 h.point.k6
  simp only [TCombCfg.Q, ptAt, h.qAt]
  omega

/-- `y = -y` if the digit is negative: `-y` by the field's subtraction from
zero, then the selection by the sign's mask. -/
theorem negate_ok (K : TCombCfg) {s : State} {base : Addr} {m : Nat} (positive : Prop) [Decidable positive]
    (h : Layout K) (hw : WsReg s base) (hm : K.F.m = m) (hn : K.F.k = K.L.M.n) (hM : ModOk K.L.M.n m)
    (hz : wordsVal s.mem base K.zero K.L.M.n = 0) (hy : wordsVal s.mem base K.Q.y K.L.M.n < m)
    (hmask : ∀ u, Rk fnClob s u → Unch base [(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] s.mem u.mem →
      WP isa K.signMask u fun v =>
        v.gpr .r10 = (if positive then 0 else BitVec.allOnes 64) ∧ Kp [.r4, .r6, .r10] u v ∧ v.mem = u.mem) :
    WP isa (.seq (subCall K.F K.neg K.zero K.Q.y) (.seq K.signMask (.block (sel K.L.M.n K.Q.y K.Q.y K.neg)))) s
      fun t =>
      Rk fnClob s t ∧ Unch base (loopWrites K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal t.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n) ∧
      wordsVal t.mem base K.Q.x K.L.M.n = wordsVal s.mem base K.Q.x K.L.M.n ∧
      wordsVal t.mem base K.Q.y K.L.M.n =
        (if positive then wordsVal s.mem base K.Q.y K.L.M.n else (m - wordsVal s.mem base K.Q.y K.L.M.n) % m) ∧
      wordsVal t.mem base K.Q.z K.L.M.n = wordsVal s.mem base K.Q.z K.L.M.n := by
  obtain ⟨hqx, hqy, hqz, hqa, hown, hown', -, -, hq4⟩ := q_lay h
  have := lay_nums h.point.k3 h.point.k6
  have low := h.low
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at low
  obtain ⟨rx, ry, rz, hzero, hneg⟩ := low
  have nowrap := hw.nowrap
  have fm : ModOk K.F.k K.F.m := by rw [hn, hm]; exact hM
  refine WP.seq (WP.mono (subCall_ok fm hw (by rw [hn]; omega) (by rw [hn]; omega) (by rw [hn]; omega)
    (by rw [hn, hm, hz]; exact hM.m0) (by rw [hn, hm]; exact hy)) fun u ⟨ku, yu⟩ => ?_)
  rw [hn, hm, hz, Nat.zero_add] at yu
  have ou : Unch base [(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] s.mem u.mem := by
    have := ku.mem; rw [hn] at this; exact this
  have wu := hw.of_rk (ku.rk (rs := fnClob))
  refine WP.seq (WP.mono (hmask u (ku.rk) ou) fun v ⟨mask, kv, mv⟩ => ?_)
  have wv := wu.of_kp kv
  have msk : v.gpr .r10 = if decide (¬positive) then BitVec.allOnes 64 else 0 := by
    rw [mask]; by_cases hp : positive <;> simp [hp]
  refine WP.mono (sel_ok (decide (¬positive)) K.L.M.n (o := K.Q.y) (a := K.Q.y) (b := K.neg) wv.ws wv.at3 msk
    (by omega) (by omega) h.al.2 (by omega) (by omega) (by omega) (.inl (Nat.le_refl _))
    (.inr (by omega))) fun t ⟨yt, kt, ot⟩ => ?_
  have qold : ∀ x ∈ [K.Q.x, K.Q.y, K.Q.z], wordsVal v.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n := by
    intro x hx
    rw [mv]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    apply ou.wordsVal _ (by rcases hx with rfl | rfl | rfl <;> omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rcases hx with rfl | rfl | rfl <;> exact ⟨.inr (by omega), .inl (by omega)⟩
  refine ⟨(ku.rk).trans ((kv.rk (by decide)).trans (kt.rk (by decide))), ?_, ?_, ?_, ?_, ?_⟩
  · have ov : Unch base [(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] s.mem v.mem := by rw [mv]; exact ou
    apply (ov.trans ot.unch).cover
    intro w hw'
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with (rfl | rfl) | rfl
    · exact ⟨_, by simp [loopWrites], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(ownAt K.L.M.n, 4096 - ownAt K.L.M.n), by simp [loopWrites], by dsimp only; omega,
        by dsimp only; omega⟩
    · exact ⟨(oAt K.L.M.n, 72 * K.L.M.n), by simp [loopWrites], by dsimp only; omega, by dsimp only; omega⟩
  · intro x hx
    have lowx : x + 8 * K.L.M.n ≤ oAt K.L.M.n := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> with_reducible assumption
    have negx := h.negApart x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp)
    rw [ot.wordsVal (.inl (by omega)) (by omega), mv]
    apply ou.wordsVal _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨negx.symm, .inl (by omega)⟩
  · rw [ot.wordsVal (by omega) (by omega), qold _ (by simp)]
  · rw [yt, mv, yu]
    have qo := qold K.Q.y (by simp)
    rw [mv] at qo
    rw [qo]
    by_cases hp : positive <;> simp [hp]
  · rw [ot.wordsVal (by omega) (by omega), qold _ (by simp)]

/-- The entry of digit `j`, signed, in the point functions' `Q`. -/
theorem entry_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : Config K C tbl start) (hC : Law C) {s : State} {base T : Addr} {k j : Nat}
    (i : CurveInputs K C tbl base T k s) (hj : j < K.J) (hk : k < 2 ^ K.L.nbits)
    (gj : s.gpr .r31 = BitVec.ofNat 64 j)
    (hd : Region.Disjoint ⟨T, 8 * (tableWords K C tbl).length⟩ ⟨base, 8192⟩) :
    WP isa K.entry s fun t =>
      Rk fnClob s t ∧ Unch base (loopWrites K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal t.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n) ∧
      (∀ x ∈ [K.Q.x, K.Q.y, K.Q.z], wordsVal t.mem base x K.L.M.n < C.p) ∧
      Rep C (tmv C K.L.M.n base t K.Q.x) (tmv C K.L.M.n base t K.Q.y) (tmv C K.L.M.n base t K.Q.z)
        (signedPtW C K.w k j) := by
  unfold TCombCfg.entry
  have hp : 0 < C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  have hfit : C.p ≤ 2 ^ (64 * K.L.M.n) := Nat.le_of_lt h.modulus.m_lt
  have hl := lay_nums h.layout.point.k3 h.layout.point.k6
  obtain ⟨hqx, hqy, hqz, hqa, hown, hown', -, -, hq4⟩ := q_lay h.layout
  have lo := h.layout.low
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at lo
  obtain ⟨rx, ry, rz, zlo, nlo⟩ := lo
  have hbits := h.layout.point.bitsE
  have hb4 := h.layout.point.bits
  have nowrap := i.wsr.nowrap
  have hH15 : K.H + 1 ≤ 2 ^ 15 := by
    have := h.row
    have := Nat.le_mul_of_pos_left K.H (show 0 < 16 * K.L.M.n by have := h.layout.point.k3; omega)
    omega
  refine WP.seq (WP.mono_syms (digit_ok K i.wsr.ws i.wsr.at3 h.w9 hj (Nat.le_of_lt h.J15) h.startBits h.coverBits h.bitsOff
    hbits hk gj i.bits) fun u ⟨gu, ku, mu⟩ syu => ?_)
  have iu : CurveInputs K C tbl base T k u :=
    i.keep h.layout hd (ku.rk (rs' := fnClob)) (by decide) (by rw [mu]; exact Unch.refl _ _ _) syu
  refine WP.seq (WP.mono_syms (selectTable_ok K (a := magH K.H (combWin K.w k j)) iu.wsr hq4 h.layout.al.1
    (by omega) (by omega) (.inl (by omega)) (Nat.lt_of_lt_of_le h.one_lt hfit) iu.zero
    (by have := h.layout.point.k3; omega) hH15 h.row (h.magnitude k j) gu
    (by rw [ku.g]; exact gj) iu.table iu.symbol h.tables.len h.tables.lenH hj (by have := h.J15; omega) hp hfit hd)
    fun v ⟨xv, yv, zv, kv, ov⟩ syv => ?_)
  have ouv : Unch base (loopWrites K) u.mem v.mem :=
    ov.unch.cover fun w hw' => by
      rw [List.mem_singleton] at hw'; subst hw'
      exact ⟨(oAt K.L.M.n, 72 * K.L.M.n), by simp [loopWrites], by dsimp only; omega, by dsimp only; omega⟩
  have iv : CurveInputs K C tbl base T k v := iu.keep h.layout hd kv (by decide) ouv syv
  have ylt : wordsVal v.mem base K.Q.y K.L.M.n < C.p := by
    rw [yv]; split
    · exact h.one_lt
    · exact Nat.mod_lt _ hp
  have oldR : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z],
      wordsVal v.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n := by
    intro x hx
    have lowx : x + 8 * K.L.M.n ≤ oAt K.L.M.n := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> with_reducible assumption
    rw [ov.wordsVal (.inl (by omega)) (by omega), mu]
  have mask : ∀ a, Rk fnClob v a → Unch base [(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] v.mem a.mem →
      WP isa K.signMask a fun b =>
        b.gpr .r10 = (if K.H ≤ combWin K.w k j then 0 else BitVec.allOnes 64) ∧ Kp [.r4, .r6, .r10] a b ∧
          b.mem = a.mem := by
    intro a ka ma
    have wa := iv.wsr.of_rk ka
    refine WP.mono (signMask_ok K wa.ws wa.at3 ⟨h.w1, h.w9⟩ hj (Nat.le_of_lt h.J15) h.startBits h.coverBits h.bitsOff hbits hk
      (by rw [ka.g, kv.g, ku.g]; exact gj) fun b hb => ?_) fun t ⟨v', k', m'⟩ => ⟨v', k', m'⟩
    rw [ma.byte (fun w hw' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
        rcases hw' with rfl | rfl <;> (right; dsimp only; omega)) (by omega), iv.bits b hb]
  refine WP.mono (negate_ok K (K.H ≤ combWin K.w k j) h.layout iv.wsr h.fieldM h.fieldK h.modulus iv.zero ylt mask)
    fun t ⟨kt, ot, rt, xt, yt, zt⟩ => ?_
  refine ⟨((ku.rk (rs' := fnClob)).trans ((kv.mono (by decide)).trans kt)), ?_,
    fun x hx => (rt x hx).trans (oldR x hx), ?_, ?_⟩
  · have ou : Unch base (loopWrites K) s.mem u.mem := by rw [mu]; exact Unch.refl _ _ _
    exact (ou.trans (ouv.trans ot)).cover fun w hw' => ⟨w, by
      simpa only [List.mem_append, or_self] using hw', Nat.le_refl _, Nat.le_refl _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [xt, yt, zt, xv, zv]
    refine ⟨?_, ?_, ?_⟩
    · split
      · exact hp
      · exact Nat.mod_lt _ hp
    · split
      · exact ylt
      · exact Nat.mod_lt _ hp
    · split
      · exact hp
      · exact h.one_lt
  · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [xt, yt, zt]
    exact combSigned_rep hC h.tables h.unit h.one hj h.w1 xv yv zv ylt

/-! ## The addition -/

/-- `ptCall_ok`, for the functions of `S` of `n`-word coordinates modulo `m`. -/
theorem ptCallAt_ok {S : Impl.Weierstrass.Mont.Modulus} {n m : Nat} [NeZero m] (hk : S.k = n) (hm : S.m = m)
    (hM : ModOk n m) (hodd : m % 2 = 1) (hk3 : 3 ≤ n) (hk6 : n ≤ 6) (dbl : Bool) {a0 : Bool} {s : State}
    {base : Addr} (hw : WsReg s base) (hlt : ∀ x ∈ rIds, wordsVal s.mem base (enc n dbl x) n < m) :
    WP isa (ptCall S dbl a0) s fun s' => Rk fnClob s s' ∧
      Outs base [(oAt n, 3 * elemBytes n), (ownAt n, 4096 - ownAt n)] s.mem s'.mem ∧
      (∀ j < 3, wordsVal s'.mem base (enc n dbl j) n < m) ∧
      (Eb n m dbl s'.mem base 0, Eb n m dbl s'.mem base 1, Eb n m dbl s'.mem base 2) =
        ptVal a0 dbl (Eb n m dbl s.mem base) := by
  obtain ⟨c, w, m', k', d⟩ := S
  dsimp only at hk hm
  subst hk hm
  exact ptCall_ok hM hodd hk3 hk6 dbl hw hlt

/-- `R = R + Q` by a call of the complete addition. -/
theorem add_ok (K : TCombCfg) {s : State} {base : Addr} {m : Nat} [NeZero m]
    (h : Layout K) (hw : WsReg s base) (hm : K.F.m = m) (hn : K.F.k = K.L.M.n) (hM : ModOk K.L.M.n m)
    (hodd : m % 2 = 1)
    (hlt : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.Q.x, K.Q.y, K.Q.z, aAt K.L.M.n, b3At K.L.M.n],
      wordsVal s.mem base x K.L.M.n < m) :
    WP isa K.add s fun t =>
      Rk fnClob s t ∧ Unch base (loopWrites K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal t.mem base x K.L.M.n < m) ∧
      (toM m (2 ^ (64 * K.L.M.n)) (wordsVal t.mem base K.L.R.x K.L.M.n),
       toM m (2 ^ (64 * K.L.M.n)) (wordsVal t.mem base K.L.R.y K.L.M.n),
       toM m (2 ^ (64 * K.L.M.n)) (wordsVal t.mem base K.L.R.z K.L.M.n)) =
        rcbAdd (toM m (2 ^ (64 * K.L.M.n)) (wordsVal s.mem base (aAt K.L.M.n) K.L.M.n))
          (toM m (2 ^ (64 * K.L.M.n)) (wordsVal s.mem base (b3At K.L.M.n) K.L.M.n))
          (toM m (2 ^ (64 * K.L.M.n)) (wordsVal s.mem base K.L.R.x K.L.M.n))
          (toM m (2 ^ (64 * K.L.M.n)) (wordsVal s.mem base K.L.R.y K.L.M.n))
          (toM m (2 ^ (64 * K.L.M.n)) (wordsVal s.mem base K.L.R.z K.L.M.n))
          (toM m (2 ^ (64 * K.L.M.n)) (wordsVal s.mem base K.Q.x K.L.M.n))
          (toM m (2 ^ (64 * K.L.M.n)) (wordsVal s.mem base K.Q.y K.L.M.n))
          (toM m (2 ^ (64 * K.L.M.n)) (wordsVal s.mem base K.Q.z K.L.M.n)) := by
  unfold TCombCfg.add
  have hk3 := h.point.k3
  have hk6 := h.point.k6
  obtain ⟨h1, h2, he, hb3', ha', hq', hp', ho', -, -⟩ := lay_nums hk3 hk6
  obtain ⟨hqx, hqy, hqz, hqa, hown, hown', hb3, hoA, hq4⟩ := q_lay h
  have low := h.low
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at low hlt
  obtain ⟨rx, ry, rz, -, -⟩ := low
  obtain ⟨lx, ly, lz, lqx, lqy, lqz, la, lb⟩ := hlt
  obtain ⟨-, -, -, -, -, rxl, ryl, rzl⟩ := h.point.al
  have nowrap := hw.nowrap
  have cp := copyPt_conds (a := K.L.R) hk3 hk6 (.inl rfl) (by omega) (by omega) (by omega) ⟨rxl, ryl, rzl⟩
  refine WP.seq (WP.mono (copyPt_ok hw.ws hw.at3 (n := K.L.M.n) (o := K.P) (a := K.L.R)
    cp.1 cp.2.1 cp.2.2.1 cp.2.2.2) fun u ⟨px, py, pz, ku, outs⟩ => ?_)
  simp only [P_eq] at px py pz outs
  have wu := hw.of_kp ku
  have other : ∀ x ∈ [K.Q.x, K.Q.y, K.Q.z, aAt K.L.M.n, b3At K.L.M.n],
      wordsVal u.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n := by
    intro x hx
    have U : Unch base [(pAt K.L.M.n, 8 * K.L.M.n), (pAt K.L.M.n + elemBytes K.L.M.n, 8 * K.L.M.n),
      (pAt K.L.M.n + 2 * elemBytes K.L.M.n, 8 * K.L.M.n)] s.mem u.mem := outs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    apply U.wordsVal _ (by rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> (refine ⟨.inr ?_, .inr ?_, .inr ?_⟩ <;> omega)
  have hltu : ∀ x ∈ rIds, wordsVal u.mem base (enc K.L.M.n false x) K.L.M.n < m := by
    apply rIds_lt_of false
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    refine ⟨by rw [px]; exact lx, by rw [py]; exact ly, by rw [pz]; exact lz, ?_, ?_, ?_, ?_, ?_⟩
    · have e := other K.Q.x (by simp); rw [Q_eq h] at e; rw [e, ← congrArg Pt.x (Q_eq h)]; exact lqx
    · have e := other K.Q.y (by simp); rw [Q_eq h] at e; rw [e, ← congrArg Pt.y (Q_eq h)]; exact lqy
    · have e := other K.Q.z (by simp); rw [Q_eq h] at e; rw [e, ← congrArg Pt.z (Q_eq h)]; exact lqz
    · rw [other _ (by simp)]; exact la
    · rw [other _ (by simp)]; exact lb
  refine WP.seq (WP.mono (ptCallAt_ok (S := K.F) (a0 := false) hn hm hM hodd hk3 hk6 false wu hltu)
    fun v ⟨kv, ov, lv, eqv⟩ => ?_)
  have wv := wu.of_rk kv
  have cO := copyPt_conds (a := K.L.R) hk3 hk6 (.inl rfl) (by omega) (by omega) (by omega) ⟨rxl, ryl, rzl⟩
  have backIn : ∀ d ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.O.x, K.O.y, K.O.z], d + 8 * K.L.M.n ≤ 8192 := by
    simp only [O_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    omega
  have back4 : ∀ d ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.O.x, K.O.y, K.O.z], d % 4 = 0 := by
    simp only [O_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, elemBytes]
    omega
  have backApart : ∀ d ∈ [K.L.R.x, K.L.R.y, K.L.R.z], ∀ e ∈ [K.O.x, K.O.y, K.O.z],
      d + 8 * K.L.M.n ≤ e ∨ e + 8 * K.L.M.n ≤ d := by
    simp only [O_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    omega
  refine WP.mono (copyPt_ok wv.ws wv.at3 (n := K.L.M.n) (o := K.L.R) (a := K.O) back4 backIn h.point.rne
    backApart) fun t ⟨tx, ty, tz, kt, ot⟩ => ?_
  refine ⟨((ku.rk (by decide)).trans (kv.trans (kt.rk (by decide)))), ?_, ?_, ?_⟩
  · have U₁ : Unch base [(pAt K.L.M.n, 8 * K.L.M.n), (pAt K.L.M.n + elemBytes K.L.M.n, 8 * K.L.M.n),
      (pAt K.L.M.n + 2 * elemBytes K.L.M.n, 8 * K.L.M.n)] s.mem u.mem := outs
    have U₂ : Unch base [(oAt K.L.M.n, 3 * elemBytes K.L.M.n), (ownAt K.L.M.n, 4096 - ownAt K.L.M.n)]
      u.mem v.mem := ov
    have U₃ : Unch base [(K.L.R.x, 8 * K.L.M.n), (K.L.R.y, 8 * K.L.M.n), (K.L.R.z, 8 * K.L.M.n)]
      v.mem t.mem := ot
    apply (U₁.trans (U₂.trans U₃)).cover
    intro w hw'
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw'
    have mO : (oAt K.L.M.n, 72 * K.L.M.n) ∈ loopWrites K := by simp [loopWrites]
    have mW : (ownAt K.L.M.n, 4096 - ownAt K.L.M.n) ∈ loopWrites K := by simp [loopWrites]
    rcases hw' with (rfl | rfl | rfl) | (rfl | rfl) | (rfl | rfl | rfl)
    · exact ⟨_, mO, by dsimp only; omega, by dsimp only; omega⟩
    · exact ⟨_, mO, by dsimp only; omega, by dsimp only; omega⟩
    · exact ⟨_, mO, by dsimp only; omega, by dsimp only; omega⟩
    · exact ⟨_, mO, by dsimp only; omega, by dsimp only; omega⟩
    · exact ⟨_, mW, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [loopWrites], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [loopWrites], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [loopWrites], Nat.le_refl _, Nat.le_refl _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    have l0 := lv 0 (by decide)
    have l1 := lv 1 (by decide)
    have l2 := lv 2 (by decide)
    rw [enc_0] at l0
    rw [enc_1] at l1
    rw [enc_2] at l2
    rw [tx, ty, tz, O_eq]
    exact ⟨l0, l1, l2⟩
  · rw [tx, ty, tz]
    simp only [Eb, enc_0, enc_1, enc_2] at eqv
    simp only [O_eq]
    rw [eqv]
    simp only [ptVal, Eb, enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, enc_9, enc_10, Bool.false_eq_true, ↓reduceIte]
    rw [px, py, pz]
    have oa := other (aAt K.L.M.n) (by simp)
    have ob := other (b3At K.L.M.n) (by simp)
    have ox := other K.Q.x (by simp)
    have oy := other K.Q.y (by simp)
    have oz := other K.Q.z (by simp)
    rw [Q_eq h] at ox oy oz
    dsimp only at ox oy oz
    rw [Q_eq h]
    dsimp only
    rw [oa, ob, ox, oy, oz]


/-! ## An iteration, and the comb -/

/-- The accumulator after the digits above `j`. -/
structure Acc (K : TCombCfg) (C : Curve) (base : Addr) (k j : Nat) (s : State) : Prop where
  lt : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal s.mem base x K.L.M.n < C.p
  rep : Rep C (tmv C K.L.M.n base s K.L.R.x) (tmv C K.L.M.n base s K.L.R.y) (tmv C K.L.M.n base s K.L.R.z)
    (mul (combEW K.w k K.J j) (G C))

/-- An iteration: digit `j - 1` added to the accumulator. -/
theorem step_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : Config K C tbl start) (hC : Law C) (hG : onCurve C (G C) = true)
    {s : State} {base T : Addr} {k j : Nat}
    (i : CurveInputs K C tbl base T k s) (acc : Acc K C base k j s)
    (hj : 1 ≤ j) (hJ : j ≤ K.J) (hk : k < 2 ^ K.L.nbits) (gj : s.gpr .r31 = BitVec.ofNat 64 j)
    (hd : Region.Disjoint ⟨T, 8 * (tableWords K C tbl).length⟩ ⟨base, 8192⟩) :
    WP isa K.step s fun t =>
      Rk powClob s t ∧ Unch base (loopWrites K) s.mem t.mem ∧
      CurveInputs K C tbl base T k t ∧ Acc K C base k (j - 1) t ∧ t.gpr .r31 = BitVec.ofNat 64 (j - 1) := by
  apply WP.of_syms
  unfold TCombCfg.step
  have hp : 0 < C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  refine WP.seq (wp_decCounter hj gj (WP.block_nil ?_))
  generalize hu : s.write .r31 (BitVec.ofNat 64 (j - 1)) = u
  have ku : Kp [.r31] s u := by rw [← hu]; exact Kp.write _ _ (by decide)
  have gu : u.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [← hu]; simp only [write_gpr, ite_true]
  have mu : u.mem = s.mem := by rw [← hu]; rfl
  have syu : u.syms = s.syms := by rw [← hu]; rfl
  have iu : CurveInputs K C tbl base T k u :=
    i.keep h.layout hd (ku.rk (rs' := [.r31])) (by decide) (by rw [mu]; exact Unch.refl _ _ _) syu
  refine WP.seq (WP.mono_syms (entry_ok K h hC iu (by omega) hk gu hd) fun v ⟨kv, ov, rv, lv, pv⟩ syv => ?_)
  have iv : CurveInputs K C tbl base T k v := iu.keep h.layout hd kv (by decide) ov syv
  have rlt : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal v.mem base x K.L.M.n < C.p := by
    intro x hx
    rw [rv x hx, mu]
    exact acc.lt x hx
  have rrep : Rep C (tmv C K.L.M.n base v K.L.R.x) (tmv C K.L.M.n base v K.L.R.y)
      (tmv C K.L.M.n base v K.L.R.z) (mul (combEW K.w k K.J j) (G C)) := by
    show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [rv _ (by simp), rv _ (by simp), rv _ (by simp), mu]
    exact acc.rep
  have hlt : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.Q.x, K.Q.y, K.Q.z, aAt K.L.M.n, b3At K.L.M.n],
      wordsVal v.mem base x K.L.M.n < C.p := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨rlt _ (by simp), rlt _ (by simp), rlt _ (by simp), lv _ (by simp), lv _ (by simp), lv _ (by simp),
      iv.coeffA ▸ Nat.mod_lt _ hp, iv.coeffB ▸ Nat.mod_lt _ hp⟩
  refine WP.mono_syms (add_ok K h.layout iv.wsr h.fieldM h.fieldK h.modulus h.odd hlt)
    fun t ⟨kt, ot, lt, et⟩ syt => fun syt' => ?_
  have keep : Rk powClob s t :=
    (ku.rk (by decide)).trans ((kv.mono (by decide)).trans (kt.mono (by decide)))
  have unch : Unch base (loopWrites K) s.mem t.mem := by
    have ou : Unch base (loopWrites K) s.mem u.mem := by rw [mu]; exact Unch.refl _ _ _
    exact (ou.trans (ov.trans ot)).cover fun w hw' => ⟨w, by
      simpa only [List.mem_append, or_self] using hw', Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨keep, unch, i.keep h.layout hd keep (by decide) unch syt', ⟨lt, ?_⟩,
    by rw [kt.g, kv.g]; exact gu⟩
  have pa : Rep C (tmv C K.L.M.n base t K.L.R.x) (tmv C K.L.M.n base t K.L.R.y)
      (tmv C K.L.M.n base t K.L.R.z)
      (Spec.Weierstrass.add (mul (combEW K.w k K.J j) (G C)) (signedPtW C K.w k (j - 1))) := by
    apply hC.add (hC.onCurve_mul hG _) (by
      unfold signedPtW combPtW
      split
      · exact hC.onCurve_mul hG _
      · exact onCurve_negPt (hC.onCurve_mul hG _)) rrep pv
    show rcbAddC C _ _ _ _ _ _ = (toM _ _ _, toM _ _ _, toM _ _ _)
    rw [et, iv.coeffA, iv.coeffB, toM_mont h.unit, toM_mont h.unit]
  have eqj : j - 1 + 1 = j := by omega
  have sum := combW_add hC hG (w := K.w) (k := k) (j := j - 1) (J := K.J) (by omega)
  change Spec.Weierstrass.add _ (signedPtW C K.w k (j - 1)) = _ at sum
  rw [eqj] at sum
  rw [sum] at pa
  exact pa

/-- The comb: `R = [k]G`, for the scalar `k` of `nbits` bits whose table of
bits is at `bits`, reduced, with only the registers of `powClob` and the
memory of `writes` changed. -/
theorem comb_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : Config K C tbl start) (hC : Law C) (hG : onCurve C (G C) = true)
    {s : State} {base T : Addr} {k : Nat} (hw : WsReg s base)
    (ht : TableMem s T (tableWords K C tbl)) (sym : s.syms K.tsym = T)
    (hd : Region.Disjoint ⟨T, 8 * (tableWords K C tbl).length⟩ ⟨base, 8192⟩)
    (hk : k < 2 ^ K.L.nbits) (zero : wordsVal s.mem base K.zero K.L.M.n = 0)
    (bits : ∀ i < K.L.nbits, s.mem (off base (K.L.bits + i)) = if k.testBit i then 1 else 0)
    (coeffA : wordsVal s.mem base K.L.S.a K.L.M.n = C.a * 2 ^ (64 * K.L.M.n) % C.p)
    (coeffB : wordsVal s.mem base K.L.S.b3 K.L.M.n = (3 * C.b) * 2 ^ (64 * K.L.M.n) % C.p) :
    WP isa K.comb s fun t =>
      Rk powClob s t ∧ Unch base (writes K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal t.mem base x K.L.M.n < C.p) ∧
      Rep C (tmv C K.L.M.n base t K.L.R.x) (tmv C K.L.M.n base t K.L.R.y) (tmv C K.L.M.n base t K.L.R.z)
        (mul k (G C)) := by
  have hp : 0 < C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  have fit := h.modulus.m_lt
  have sx : K.start.1 < C.p := by rw [h.startX]; exact Nat.mod_lt _ hp
  have sy : K.start.2 < C.p := by rw [h.startY]; exact Nat.mod_lt _ hp
  have := lay_nums h.layout.point.k3 h.layout.point.k6
  have hbits := h.layout.point.bits
  have hbe := h.layout.point.bitsE
  have nowrap := hw.nowrap
  unfold TCombCfg.comb
  refine WP.seq (WP.mono_syms (start_ok K h.layout hw (Nat.lt_trans sx fit) (Nat.lt_trans sy fit)
    (Nat.lt_trans h.one_lt fit) h.J15) fun u ⟨ku, ou, cp, gu, xu, yu, zu⟩ syu => ?_)
  have low := h.layout.low K.zero (by simp)
  have iu : CurveInputs K C tbl base T k u := by
    refine ⟨hw.of_kp ku, ht.unch (by rw [ku.rd, ku.wr]) ou (fun w hw' => by
        have := h.layout.bounded w hw'; omega) hd, by rw [syu]; exact sym, ?_, ?_, ?_, ?_⟩
    · rw [ou.wordsVal (by
        intro r hr
        simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact h.layout.zeroApart _ (by simp)
        · exact h.layout.zeroApart _ (by simp)
        · exact h.layout.zeroApart _ (by simp)
        · exact (h.layout.negApart K.zero (by simp)).symm
        · exact .inl low) (by omega), zero]
    · intro j hj
      rw [ou.byte (fun w hw' => .inr (by have := h.layout.bounded w hw'; omega)) (by omega), bits j hj]
    · exact cp.2.2.2.1.trans coeffA
    · exact cp.2.2.2.2.trans coeffB
  have au : Acc K C base k K.J u := by
    refine ⟨?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      rw [xu, yu, zu]
      exact ⟨sx, sy, h.one_lt⟩
    · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [xu, yu, zu, h.startX, h.startY, toM_mont h.unit, toM_mont h.unit, h.one, combEW_top, h.tables.start]
      exact rep_affine' hC _ _
  let Inv := fun j t => CurveInputs K C tbl base T k t ∧ Acc K C base k j t ∧
    t.gpr .r31 = BitVec.ofNat 64 j ∧ Rk powClob s t ∧ Unch base (writes K) s.mem t.mem
  refine countLoop_ok (Inv := Inv) (fun j t hi => hi.2.2.1) (fun j t hj hJ hi => ?_) (fun t hi => ?_) h.J1
    (by have := h.J15; omega) ⟨iu, au, gu, ku.rk (by decide), ou⟩
  · obtain ⟨it, accT, gt, kt, ot⟩ := hi
    refine WP.mono (step_ok K h hC hG it accT hj hJ hk gt hd) fun v ⟨kv, ov, iv, av, gv⟩ => ?_
    refine ⟨iv, av, gv, kt.trans kv, ?_⟩
    exact (ot.trans (ov.cover h.layout.loop_cover)).cover fun w hw' => ⟨w, by
      simpa only [List.mem_append, or_self] using hw', Nat.le_refl _, Nat.le_refl _⟩
  · obtain ⟨_, accT, _, kt, ot⟩ := hi
    refine ⟨kt, ot, accT.lt, ?_⟩
    have hk' : k < 2 ^ (K.w * K.J) := Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) h.coverBits)
    simpa only [combEW_zero hk'] using accT.rep

end VG.Proof.Weierstrass.PPC64LE.TComb
