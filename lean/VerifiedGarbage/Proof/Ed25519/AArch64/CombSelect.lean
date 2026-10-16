module

public import VerifiedGarbage.Proof.Ed25519.AArch64.CombDigit
public import VerifiedGarbage.Proof.Ed25519.AArch64.Field
import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep
public import VerifiedGarbage.Proof.Ed25519.AArch64.CombTbl
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The comb's constant-time selection

With `magReg k` all ones exactly for `k` the digit's magnitude, copied into
both lanes of `maskV k`, and `x22` the bit of a zero magnitude, `selectHalf`
loads every candidate's half (two words) into a vector register and inserts it
into `v2` where its mask is set (BIT), so only the digit's candidate survives,
and stores it. The
candidates are loaded from the tables at `T` (`TblAt`): readable, beyond the
working space, word `i` the static's `combWord i`. Nothing here unfolds a
table: each lemma holds for any words.
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 VG.Proof.X25519
open Word64

private theorem mag_regs : ∀ k < 9, magReg k ∉ [Reg.x9, .x2, .x4] := by decide

private theorem ne_of_not_mem {r : Reg} {rs : List Reg} (h : r ∉ rs) {r' : Reg} (hr : r' ∈ rs) :
    r ≠ r' := fun e => h (e ▸ hr)

/-! ## The tables -/

/-- The comb's tables at `T`: readable, beyond the working space at `base`, word `i` the
static's (`combWord i`). -/
structure TblAt (s : State) (base T : Addr) : Prop where
  rd : InRegions (s.rd ++ s.wr) T (8 * (32 * 96))
  far : ∀ i < 8 * (32 * 96), 8192 ≤ ofs base (T + BitVec.ofNat 64 i)
  val : ∀ i < 32 * 96, s.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = combWord i

theorem tbl_add (T : Addr) (a b : Nat) :
    T + BitVec.ofNat 64 a + BitVec.ofNat 64 b = T + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The tables survive what keeps the regions and the memory beyond the working space. -/
theorem TblAt.of_far {s t : State} {base T : Addr} (h : TblAt s base T)
    (hrw : t.rd ++ t.wr = s.rd ++ s.wr) (hm : ∀ x, 8192 ≤ ofs base x → t.mem x = s.mem x) :
    TblAt t base T :=
  ⟨hrw ▸ h.rd, h.far, fun i hi => by
    rw [← h.val i hi]
    refine Mem.readW_congr fun b hb => hm _ ?_
    rw [tbl_add T _ _]
    exact h.far _ (by omega)⟩

/-- The tables, from a contract's facts: readable, and apart from the working space at `base`,
one of the regions `wr`. -/
theorem CombHeld.tblAt {s : State} {wr : List Region} {base : Addr} (h : CombHeld s wr)
    (hrd : (⟨s.syms combSym, 8 * combWords.length⟩ : Region) ∈ s.rd ++ s.wr)
    (hsc : (⟨base, 8192⟩ : Region) ∈ wr) : TblAt s base (s.syms combSym) := by
  obtain ⟨held, fit, dj⟩ := h
  rw [combWords_length] at held fit dj hrd
  have hc : Region.Contains ⟨s.syms combSym, 8 * (32 * 96)⟩ (s.syms combSym) (8 * (32 * 96)) := by
    have := Offset.contains_base (s.syms combSym) (d := 0) (n := 8 * (32 * 96)) (k := 8 * (32 * 96))
      (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  refine ⟨⟨_, hrd, hc⟩, fun i hi => ?_, fun i hi => ?_⟩
  · refine Nat.le_of_not_lt fun hlt => dj _ hsc _
      (Offset.contains_base _ (d := i) (n := 1) (k := 8 * (32 * 96)) (by omega) (by omega)) ?_
    simp only [Region.Contains]; simp only [ofs] at hlt; omega
  · rw [← combWords_getD hi, ← held i hi]

/-- The digit's masks, for the magnitude `a`. -/
def Masks (a : Nat) (s : State) : Prop :=
  (∀ k, 1 ≤ k → k ≤ 8 → s.gpr (magReg k) = mask (decide (a = k))) ∧ s.gpr .x22 = zeroBit a

/-- What a selection leaves of the registers. -/
def RegsKept (s t : State) : Prop :=
  (∀ r, r ∉ [Reg.x9, .x2, .x4] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp

theorem RegsKept.trans {s t u : State} (h : RegsKept s t) (k : RegsKept t u) : RegsKept s u :=
  ⟨fun r hr => (k.1 r hr).trans (h.1 r hr), k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1,
    k.2.2.2.trans h.2.2.2⟩

theorem RegsKept.of_keeps {s t : State} (k : Keeps [.x9, .x2, .x4] s t) : RegsKept s t :=
  ⟨k.gpr, k.rd, k.wr, k.sp⟩

theorem Masks.of_kept {a : Nat} {s t : State} (h : Masks a s) (k : RegsKept s t) : Masks a t :=
  ⟨fun j h1 h8 => by rw [k.1 _ (mag_regs j (by omega))]; exact h.1 j h1 h8,
    by rw [k.1 _ (by decide)]; exact h.2⟩

theorem feWord_val (v : Spec.X25519.Fe) :
    val4 (feWord v 0) (feWord v 1) (feWord v 2) (feWord v 3) = v.val := by
  simp only [feWord, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul]
  exact limbs_nat _ (by have := v.isLt; simp only [Spec.X25519.P] at this; omega)

/-! ## The masks, in vector registers -/

private theorem exec_ldrq {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp only [exec, addr, show 4096 * 16 = 65536 from rfl, ho, and_self, ite_true, State.load, h,
    Option.bind_some, Option.map_some]

private theorem exec_strq {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, show off < 4096 * 16 by omega, ho, and_self, ite_true, Option.bind_some,
    State.store, h]

/-- The digit's masks, each in both lanes of its vector register. -/
def VMasks (a : Nat) (s : State) : Prop :=
  ∀ k, 1 ≤ k → k ≤ 8 → s.v (maskV k) = ofVDwords (mask (decide (a = k))) (mask (decide (a = k)))

/-- What the vector selection keeps: everything but the vector registers and the memory. -/
structure VKept (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem VKept.refl (s : State) : VKept s s := ⟨rfl, rfl, rfl, rfl⟩

theorem VKept.trans {s t u : State} (h : VKept s t) (k : VKept t u) : VKept s u :=
  ⟨k.gpr.trans h.gpr, k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp⟩

theorem VKept.regs {s t : State} (h : VKept s t) : RegsKept s t :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp⟩

private theorem maskV_ne : ∀ j < 8, ∀ k, 1 ≤ k → k ≤ j → maskV k ≠ maskV (j + 1) := by decide

private theorem maskV_ne_cand : ∀ m < 8, ∀ k, 1 ≤ k → k ≤ 8 → maskV k ≠ candV m := by decide

private theorem candV_ne_v2 : ∀ m < 8, candV m ≠ .v2 := by decide

private theorem maskV_ne_v2 : ∀ k, 1 ≤ k → k ≤ 8 → maskV k ≠ .v2 := by decide

theorem selectMasksPrefix_ok (s : State) {a : Nat} (hm : Masks a s) (n : Nat) (hn : n ≤ 8) :
    WP isa (.block ((List.range n).map fun k => .vop (.dup .d2 (maskV (k + 1)) (magReg (k + 1))))) s
      fun t => (∀ k, 1 ≤ k → k ≤ n →
        t.v (maskV k) = ofVDwords (mask (decide (a = k))) (mask (decide (a = k)))) ∧
        VKept s t ∧ t.mem = s.mem := by
  induction n with
  | zero => exact WP.block_nil ⟨fun k h1 h0 => absurd h0 (by omega), VKept.refl s, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨tv, kt, tm⟩ => ?_
    refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil ⟨fun k h1 hk => ?_, kt.trans ⟨rfl, rfl, rfl, rfl⟩,
      tm⟩⟩
    show (t.setV (maskV (n + 1)) (ofVDwords (t.gpr (magReg (n + 1))) (t.gpr (magReg (n + 1))))).v
      (maskV k) = _
    by_cases hk' : k = n + 1
    · subst hk'
      rw [RegUpd.v_setV_self, kt.gpr, hm.1 (n + 1) (by omega) (by omega)]
    · rw [RegUpd.v_setV_of_ne _ _ (maskV_ne n (by omega) k h1 (by omega))]
      exact tv k h1 (by omega)

theorem selectMasks_ok (s : State) {a : Nat} (hm : Masks a s) :
    WP isa (.block selectMasks) s fun t => VMasks a t ∧ VKept s t ∧ t.mem = s.mem :=
  WP.mono (selectMasksPrefix_ok s hm 8 (le_refl _)) fun _ ⟨tv, kt, tm⟩ => ⟨tv, kt, tm⟩

theorem VMasks.of_v {a : Nat} {s t : State} (h : VMasks a s)
    (hv : ∀ k, 1 ≤ k → k ≤ 8 → t.v (maskV k) = s.v (maskV k)) : VMasks a t :=
  fun k h1 h8 => (hv k h1 h8).trans (h k h1 h8)

/-! ## One candidate's half -/

theorem bit_dwords (a b c d k : BitVec 64) :
    VSelOp.eval .bit (ofVDwords a b) (ofVDwords c d) (ofVDwords k k) =
      ofVDwords (a ^^^ ((a ^^^ c) &&& k)) (b ^^^ ((b ^^^ d) &&& k)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [VSelOp.eval, ofVDwords, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_append]
  split <;> rfl

/-- The words of `vs[a]` after the candidates `k ≤ n`, zero if `a > n`. -/
def selWord (vs : List Spec.X25519.Fe) (a n w : Nat) : BitVec 64 :=
  if a ≤ n then feWord (vs.getD a 0) w else 0

theorem sel_bit (vs : List Spec.X25519.Fe) (a n w : Nat) :
    selWord vs a n w ^^^ ((selWord vs a n w ^^^ feWord (vs.getD (n + 1) 0) w) &&&
      mask (decide (a = n + 1))) = selWord vs a (n + 1) w := by
  unfold selWord
  by_cases h : a ≤ n
  · simp [h, show a ≤ n + 1 by omega, show ¬ a = n + 1 by omega, mask]
  · by_cases he : a = n + 1
    · subst he
      simp only [h, ↓reduceIte, Nat.le_refl, decide_true, mask, BitVec.and_allOnes]
      simp
    · simp [h, he, show ¬ a ≤ n + 1 by omega, mask]

/-- The candidates' halves `h` of coordinate `c` of the table at `x9`: entry `m + 1`'s at
`256 c + 32 m + 16 h`, words `2h` and `2h + 1`. -/
def CandsH (s : State) (vs : List Spec.X25519.Fe) (c h : Nat) : Prop :=
  ∀ m < 8, InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 (256 * c + 32 * m + 16 * h)) 16 ∧
    s.mem.read (s.gpr .x9 + BitVec.ofNat 64 (256 * c + 32 * m + 16 * h)) 16 =
      ofVDwords (feWord (vs.getD (m + 1) 0) (2 * h)) (feWord (vs.getD (m + 1) 0) (2 * h + 1))

/-- The half in `v2` after the candidates `k ≤ n`. -/
def selHalf (vs : List Spec.X25519.Fe) (a n h : Nat) : BitVec 128 :=
  ofVDwords (selWord vs a n (2 * h)) (selWord vs a n (2 * h + 1))

theorem selectHalfCands_ok (s : State) {a : Nat} (hm : VMasks a s)
    (vs : List Spec.X25519.Fe) {c h : Nat} (hc : c < 3) (hh : h < 2) (ht : CandsH s vs c h) (n : Nat)
    (hn : n ≤ 8) (h0 : s.v .v2 = selHalf vs a 0 h) :
    WP isa (.block ((List.range n).flatMap (selectHalfCand c h))) s
      fun t => t.v .v2 = selHalf vs a n h ∧ VMasks a t ∧ VKept s t ∧ t.mem = s.mem := by
  induction n with
  | zero => exact WP.block_nil ⟨h0, hm, VKept.refl s, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨t2, tm, kt, tmem⟩ => ?_
    obtain ⟨hr, hv⟩ := ht n (by omega)
    have hr' : InRegions (t.rd ++ t.wr) (t.gpr .x9 + BitVec.ofNat 64 (256 * c + 32 * n + 16 * h)) 16 := by
      rw [kt.gpr, kt.rd, kt.wr]; exact hr
    have hld := exec_ldrq (t := candV n) (n := .x9) (off := 256 * c + 32 * n + 16 * h)
      ⟨by omega, by omega⟩ hr'
    rw [kt.gpr, tmem, hv] at hld
    refine WP.block_cons_iff.mpr ⟨_, hld, WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil ?_⟩⟩
    have hmk := tm (n + 1) (by omega) (by omega)
    refine ⟨?_, fun k h1 h8 => ?_, kt.trans ⟨rfl, rfl, rfl, rfl⟩, tmem⟩
    · show (VSelOp.eval .bit ((t.setV (candV n) _).v .v2) ((t.setV (candV n) _).v (candV n))
          ((t.setV (candV n) _).v (maskV (n + 1)))) = _
      rw [RegUpd.v_setV_self, RegUpd.v_setV_of_ne _ _ (candV_ne_v2 n (by omega)).symm,
        RegUpd.v_setV_of_ne _ _ (maskV_ne_cand n (by omega) (n + 1) (by omega) (by omega)), t2, hmk,
        selHalf, selHalf, bit_dwords, sel_bit, sel_bit]
    · show (t.setV (candV n) _ |>.setV .v2 _).v (maskV k) = _
      rw [RegUpd.v_setV_of_ne _ _ (maskV_ne_v2 k h1 h8),
        RegUpd.v_setV_of_ne _ _ (maskV_ne_cand n (by omega) k h1 h8)]
      exact tm k h1 h8

theorem setLane_pair_lo (a b c : BitVec 64) :
    setLane (ofVDwords a b) 64 0 c = ofVDwords c b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [setLane, ofVDwords, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_append,
    hj, decide_true, Bool.true_and, Nat.reduceMul, Nat.sub_zero]
  by_cases h : j < 64 <;> simp (disch := omega) [h]

theorem selectHalfStart_ok (s : State) {a : Nat} (hm : Masks a s) (hv : VMasks a s) (one : Bool)
    (vs : List Spec.X25519.Fe) (h0 : vs.getD 0 0 = if one then 1 else 0) (h : Nat) (hh : h < 2) :
    WP isa (.block (selectHalfStart one h)) s fun t =>
      t.v .v2 = selHalf vs a 0 h ∧ VMasks a t ∧ VKept s t ∧ t.mem = s.mem := by
  -- The identity's words: `1` in word 0 of `Y - X` and `Y + X` (`one`), zero elsewhere.
  have hz : ∀ w, w < 4 → selWord vs a 0 w = if (one && w == 0) = true then zeroBit a else 0 := by
    intro w hw
    unfold selWord zeroBit
    by_cases ha : a = 0
    · subst ha
      have : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by omega
      simp only [Nat.le_refl, ↓reduceIte, h0]
      cases one <;> rcases this with rfl | rfl | rfl | rfl <;> decide
    · simp [ha, show ¬ a ≤ 0 by omega]
  have hm2 : ∀ k, 1 ≤ k → k ≤ 8 → ∀ x : BitVec 128, (s.setV .v2 x).v (maskV k) = s.v (maskV k) :=
    fun k h1 h8 x => RegUpd.v_setV_of_ne _ _ (maskV_ne_v2 k h1 h8)
  have h0' : (0 : BitVec 128) = ofVDwords 0 0 := by decide
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
  · cases one
    · rw [show selectHalfStart false 0 = [.vop (.movi0 .v2)] from rfl]
      refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil ?_⟩
      refine ⟨?_, fun k h1 h8 => ?_, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
      · show (s.setV .v2 0).v .v2 = _
        rw [RegUpd.v_setV_self, selHalf, hz 0 (by decide), hz 1 (by decide), h0']
        rfl
      · rw [hm2 k h1 h8]; exact hv k h1 h8
    · rw [show selectHalfStart true 0 = [.vop (.movi0 .v2), .vop (.ins .d2 .v2 0 .x22)] from rfl]
      refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil ?_⟩⟩
      refine ⟨?_, fun k h1 h8 => ?_, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
      · show setLane ((s.setV .v2 0).v .v2) 64 0 ((s.setV .v2 0).gpr .x22) = _
        rw [RegUpd.v_setV_self, RegUpd.gpr_setV, hm.2, h0', setLane_pair_lo, selHalf,
          hz 0 (by decide), hz 1 (by decide)]
        rfl
      · show ((s.setV .v2 0).setV .v2 _).v (maskV k) = _
        rw [RegUpd.v_setV_of_ne _ _ (maskV_ne_v2 k h1 h8), hm2 k h1 h8]
        exact hv k h1 h8
  · rw [show selectHalfStart one 1 = [.vop (.movi0 .v2)] by cases one <;> rfl]
    refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil ?_⟩
    refine ⟨?_, fun k h1 h8 => ?_, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    · show (s.setV .v2 0).v .v2 = _
      rw [RegUpd.v_setV_self, selHalf, hz 2 (by decide), hz 3 (by decide), h0']
      cases one <;> rfl
    · rw [hm2 k h1 h8]; exact hv k h1 h8

/-- `off base d + 8 = off base (d + 8)`. -/
private theorem off_add8 (base : Addr) (d : Nat) :
    off base d + BitVec.ofNat 64 8 = off base (d + 8) := tbl_add base d 8

theorem selectHalf_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (hm : Masks a s)
    (hv : VMasks a s) (one : Bool) (vs : List Spec.X25519.Fe) (h0 : vs.getD 0 0 = if one then 1 else 0)
    {c o : Nat} (hc : c < 3) (ho : o % 16 = 0) (hb : o + 32 ≤ 8192) (h : Nat) (hh : h < 2)
    (ht : CandsH s vs c h) :
    WP isa (.block (selectHalf one c o h)) s fun t =>
      t.mem = (s.mem.writeW (off base (o + 16 * h)) (selWord vs a 8 (2 * h))).writeW
        (off base (o + 16 * h + 8)) (selWord vs a 8 (2 * h + 1)) ∧ VMasks a t ∧ VKept s t := by
  rw [selectHalf, List.append_assoc, WP.block_append_iff]
  refine WP.mono (selectHalfStart_ok s hm hv one vs h0 h hh) fun a' ⟨a2, am, ka, amem⟩ => ?_
  rw [WP.block_append_iff]
  have hta : CandsH a' vs c h := fun m hm' => by
    rw [ka.gpr, ka.rd, ka.wr, amem]; exact ht m hm'
  refine WP.mono (selectHalfCands_ok a' am vs hc hh hta 8 (le_refl _) a2) fun b ⟨b2, bm, kb, bmem⟩ => ?_
  have hx0 : b.gpr .x0 = base := by rw [kb.gpr, ka.gpr]; exact hs.x0
  have hwr : InRegions b.wr (b.gpr .x0 + BitVec.ofNat 64 (o + 16 * h)) 16 := by
    rw [hx0, kb.wr, ka.wr]
    exact ⟨_, hs.wr, contains_sc (by omega)⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_strq ⟨by omega, by omega⟩ hwr,
    WP.block_nil ⟨?_, bm, ka.trans (kb.trans ⟨rfl, rfl, rfl, rfl⟩)⟩⟩
  show b.mem.write (b.gpr .x0 + BitVec.ofNat 64 (o + 16 * h)) 16 (b.v .v2) = _
  rw [hx0, b2, selHalf, bmem, amem, show base + BitVec.ofNat 64 (o + 16 * h) = off base (o + 16 * h)
    from rfl, write16_dwords, off_add8]

/-- The candidates of every half, beyond the working space at `base`. -/
def CandsFar (s : State) (base : Addr) (vs : List Spec.X25519.Fe) (c : Nat) : Prop :=
  ∀ h < 2, CandsH s vs c h ∧ ∀ m < 8, ∀ b < 16,
    8192 ≤ ofs base (s.gpr .x9 + BitVec.ofNat 64 (256 * c + 32 * m + 16 * h) + BitVec.ofNat 64 b)

private theorem read16_congr {m m' : Mem} {p : Addr} (h : ∀ b < 16, m' (p + BitVec.ofNat 64 b) = m (p + BitVec.ofNat 64 b)) :
    m'.read p 16 = m.read p 16 := by
  rw [read16_dwords, read16_dwords]
  refine congrArg₂ ofVDwords (Mem.readW_congr fun b hb => h b (by omega))
    (Mem.readW_congr fun b hb => ?_)
  rw [tbl_add p 8 b]
  exact h (8 + b) (by omega)

/-- The candidates survive the registers' and the working space's changes. -/
theorem CandsFar.of_outside {s t : State} {base : Addr} {vs : List Spec.X25519.Fe} {c : Nat}
    (h : CandsFar s base vs c) (k : VKept s t) {o : Nat}
    (hb : o + 32 ≤ 8192) (hm : Outside base o 32 s.mem t.mem) :
    CandsFar t base vs c := fun hh hh' => by
  obtain ⟨hc, hf⟩ := h hh hh'
  refine ⟨fun m hm' => ?_, by rw [k.gpr]; exact hf⟩
  obtain ⟨hr, hv⟩ := hc m hm'
  rw [k.gpr, k.rd, k.wr]
  refine ⟨hr, ?_⟩
  rw [← hv]
  exact read16_congr fun b hb' => hm _ (by have := hf m hm' b hb'; omega)

theorem selectField_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : a < 9)
    (hm : Masks a s) (hv : VMasks a s) (one : Bool) (vs : List Spec.X25519.Fe)
    (h0 : vs.getD 0 0 = if one then 1 else 0)
    {c o : Nat} (hc : c < 3) (ho : o % 16 = 0) (hb : o + 32 ≤ 8192) (hcf : CandsFar s base vs c) :
    WP isa (.block (selectField one c o)) s fun t =>
      F t.mem base o = vs.getD a 0 ∧ Outside base o 32 s.mem t.mem ∧ VMasks a t ∧ VKept s t := by
  rw [selectField, show List.range 2 = [0, 1] from rfl, List.flatMap_cons, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, WP.block_append_iff]
  refine WP.mono (selectHalf_ok hs hm hv one vs h0 hc ho hb 0 (by decide) (hcf 0 (by decide)).1)
    fun t ⟨tmem, tv, kt⟩ => ?_
  have ht : Scr t base := ⟨kt.gpr ▸ hs.x0, kt.wr ▸ hs.wr, hs.nowrap⟩
  have tf : Outside base o 32 s.mem t.mem := by
    rw [tmem]
    exact ((Outside.refl base o 32 s.mem).writeW (by omega) (by omega) (by omega) _).writeW
      (by omega) (by omega) (by omega) _
  have hmt : Masks a t := hm.of_kept kt.regs
  refine WP.mono (selectHalf_ok ht hmt tv one vs h0 hc ho hb 1 (by decide)
    ((hcf.of_outside kt hb tf) 1 (by decide)).1) fun u ⟨umem, uv, ku⟩ => ⟨?_, ?_, uv, kt.trans ku⟩
  · simp only [F, fe]
    rw [umem, tmem]
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, show o + 16 + 8 = o + 24 by omega]
    simp (disch := omega) only [word_writeW_self, word_writeW_sep]
    simp only [selWord, show a ≤ 8 by omega, ↓reduceIte]
    rw [feWord_val, toFe_self]
  · rw [umem]
    exact (tf.writeW (by omega) (by omega) (by omega) _).writeW (by omega) (by omega) (by omega) _

/-- The cached point in slots `a`, `b`, `c`, with `2Z = 2`. -/
def cachedAt (e : Env) (a b c : Slot) : Spec.Ed25519.Point := ⟨e a, e b, e c, 2⟩

/-- Coordinate `c` of a cached point in the tables: `Y - X`, `Y + X`, `2dT`. -/
def coord : Nat → Spec.Ed25519.Point → Spec.X25519.Fe
  | 0, p => p.X
  | 1, p => p.Y
  | _, p => p.Z

private theorem entries_getD (j a : Nat) (ha : a < 9) (f : Spec.Ed25519.Point → Spec.X25519.Fe) :
    (((List.range 9).map (combCached j)).map f).getD a 0 = f (combCached j a) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha, Option.map_some,
    Option.getD_some]

theorem combCached_T (j a : Nat) : (combCached j a).T = 2 := by
  unfold combCached
  split
  · rfl
  · split; rfl

theorem cachedAt_eq {e : Env} {a b c : Slot} {q : Spec.Ed25519.Point} (hq : q.T = 2)
    (ha : e a = q.X) (hb : e b = q.Y) (hc : e c = q.Z) : cachedAt e a b c = q := by
  cases q
  simp only [cachedAt, ha, hb, hc] at hq ⊢
  rw [hq]

/-! ## The tables' words -/

/-- Word `96 j + 32 c + 4 m + w` of the tables is word `w` of coordinate `c` of entry `m + 1` of
table `j`. -/
theorem combWord_eq {j c m w : Nat} (hc : c < 3) (hm : m < 8) (hw : w < 4) :
    combWord (96 * j + 32 * c + 4 * m + w) = feWord (coord c (combCached j (m + 1))) w := by
  have e1 : (96 * j + 32 * c + 4 * m + w) / 96 = j := by omega
  have e2 : (96 * j + 32 * c + 4 * m + w) % 32 / 4 + 1 = m + 1 := by omega
  have e3 : (96 * j + 32 * c + 4 * m + w) % 4 = w := by omega
  have e4 : (96 * j + 32 * c + 4 * m + w) % 96 = 32 * c + 4 * m + w := by omega
  unfold combWord
  simp only [e1, e2, e3, e4]
  refine congrArg (feWord · w) ?_
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
  · simp only [show 32 * 0 + 4 * m + w < 32 from by omega, ite_true]; rfl
  · simp only [show ¬ 32 * 1 + 4 * m + w < 32 from by omega, show 32 * 1 + 4 * m + w < 64 from by omega,
      ite_true, ite_false]; rfl
  · simp only [show ¬ 32 * 2 + 4 * m + w < 32 from by omega, show ¬ 32 * 2 + 4 * m + w < 64 from by omega,
      ite_false]; rfl

/-- `x9` = table `j`'s address, from the static's and `x19 = j`. -/
theorem tblAddr_ok (s : State) {T : Addr} (hT : s.syms combSym = T) {j : Nat} (hj : j < 32)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block tblAddr) s fun t =>
      t.gpr .x9 = T + BitVec.ofNat 64 (768 * j) ∧ Keeps [.x9, .x2] s t := by
  have hsh : BitVec.ofNat 64 j <<< 8 = BitVec.ofNat 64 (256 * j) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 256 * j < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show j * 2 ^ 8 < 2 ^ 64 by omega)]
    omega
  have h3 : T + BitVec.ofNat 64 (256 * j) + BitVec.ofNat 64 (256 * j) + BitVec.ofNat 64 (256 * j) =
      T + BitVec.ofNat 64 (768 * j) := by
    rw [tbl_add T _ _, tbl_add T _ _, show 256 * j + 256 * j + 256 * j = 768 * j by omega]
  apply WP.of_runBlock
  simp only [tblAddr, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 8 < 64 from by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, ite_false,
    reduceCtorEq, hc, hT, hsh, h3, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- Table `j`'s candidates for coordinate `c`, from the tables at `T`. -/
theorem candsFar_of_tbl {s : State} {base T : Addr} (h : TblAt s base T) {j : Nat} (hj : j < 32)
    (hx9 : s.gpr .x9 = T + BitVec.ofNat 64 (768 * j)) {c : Nat} (hc : c < 3) :
    CandsFar s base (((List.range 9).map (combCached j)).map (coord c)) c := fun hh hh2 => by
  -- Half `hh` of entry `m + 1` is words `96 j + 32 c + 4 m + 2 hh` and the next of the tables.
  have addr : ∀ m < 8, ∀ b < 16, s.gpr .x9 + BitVec.ofNat 64 (256 * c + 32 * m + 16 * hh) +
      BitVec.ofNat 64 b = T + BitVec.ofNat 64 (8 * (96 * j + 32 * c + 4 * m + 2 * hh) + b) :=
    fun m hm b hb => by
      rw [hx9, tbl_add T _ _, tbl_add T _ _, show 768 * j + (256 * c + 32 * m + 16 * hh) + b =
        8 * (96 * j + 32 * c + 4 * m + 2 * hh) + b by omega]
  refine ⟨fun m hm => ?_, fun m hm b hb => ?_⟩
  · have a0 := addr m hm 0 (by decide)
    rw [BitVec.add_zero, Nat.add_zero] at a0
    rw [a0]
    refine ⟨VG.CallLay.inRegions_sub h.rd (by omega) (by decide), ?_⟩
    rw [read16_dwords, tbl_add T _ 8,
      show 8 * (96 * j + 32 * c + 4 * m + 2 * hh) + 8 = 8 * (96 * j + 32 * c + 4 * m + (2 * hh + 1))
        by omega,
      h.val _ (by omega), h.val _ (by omega), combWord_eq hc hm (by omega : 2 * hh < 4),
      combWord_eq hc hm (by omega : 2 * hh + 1 < 4), entries_getD j (m + 1) (by omega)]
  · rw [addr m hm b hb]
    exact h.far _ (by omega)

/-- **Table `j`'s entry** for the digit, `|d| = a`, from the tables at `T`. -/
theorem combSelect_ok {s : State} {base T : Addr} (hs : Scr s base) (htb : TblAt s base T)
    (hT : s.syms combSym = T) {j : Nat} (hj : j < 32) (hc : s.gpr .x19 = BitVec.ofNat 64 j)
    {a : Nat} (ha : a < 9) (hm : Masks a s) :
    WP isa (.block combSelect) s fun t =>
      cachedAt (env t.mem base) 4 5 6 = combCached j a ∧
      Outside base (offset 4) 96 s.mem t.mem ∧ RegsKept s t := by
  rw [combSelect]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (tblAddr_ok s hT hj hc) fun a' ⟨a9, ka⟩ => ?_
  have hsa : Scr a' base := hs.of_keeps ka (by decide)
  have kra : RegsKept s a' := RegsKept.of_keeps (ka.mono (by simp))
  have hma : Masks a a' := hm.of_kept kra
  rw [WP.block_append_iff]
  refine WP.mono (selectMasks_ok a' hma) fun a2 ⟨av, ka2, amem⟩ => ?_
  have hsa2 : Scr a2 base := ⟨ka2.gpr ▸ hsa.x0, ka2.wr ▸ hsa.wr, hsa.nowrap⟩
  have hta : TblAt a2 base T := htb.of_far (by rw [ka2.rd, ka2.wr, ka.rd, ka.wr])
    (fun x _ => by rw [amem, ka.mem])
  have hma2 : Masks a a2 := hma.of_kept ka2.regs
  have a9' : a2.gpr .x9 = T + BitVec.ofNat 64 (768 * j) := by rw [ka2.gpr]; exact a9
  rw [WP.block_append_iff]
  refine WP.mono (selectField_ok hsa2 ha hma2 av true _ (by rw [entries_getD j 0 (by decide)]; rfl)
    (c := 0) (o := offset 4) (by decide) (by decide) (by decide)
    (candsFar_of_tbl hta hj a9' (by decide)))
    fun b ⟨b4, bf, bv, kb⟩ => ?_
  have hsb : Scr b base := ⟨kb.gpr ▸ hsa2.x0, kb.wr ▸ hsa2.wr, hs.nowrap⟩
  have htb' : TblAt b base T := hta.of_far (by rw [kb.rd, kb.wr])
    (fun x hx => bf x (Or.inr (by simp only [offset]; omega)))
  rw [WP.block_append_iff]
  refine WP.mono (selectField_ok hsb ha (hma2.of_kept kb.regs) bv true _
    (by rw [entries_getD j 0 (by decide)]; rfl)
    (c := 1) (o := offset 5) (by decide) (by decide) (by decide)
    (candsFar_of_tbl htb' hj (by rw [kb.gpr]; exact a9') (by decide)))
    fun c ⟨c5, cf, cv, kc⟩ => ?_
  have hsc : Scr c base := ⟨kc.gpr ▸ hsb.x0, kc.wr ▸ hsb.wr, hs.nowrap⟩
  have htc : TblAt c base T := htb'.of_far (by rw [kc.rd, kc.wr])
    (fun x hx => cf x (Or.inr (by simp only [offset]; omega)))
  refine WP.mono (selectField_ok hsc ha ((hma2.of_kept kb.regs).of_kept kc.regs) cv false _
    (by rw [entries_getD j 0 (by decide)]; rfl)
    (c := 2) (o := offset 6) (by decide) (by decide) (by decide)
    (candsFar_of_tbl htc hj (by rw [kc.gpr, kb.gpr]; exact a9') (by decide)))
    fun t ⟨t6, tf, _, kt⟩ => ⟨?_, ?_, (((kra.trans ka2.regs).trans kb.regs).trans kc.regs).trans kt.regs⟩
  · rw [entries_getD j a ha] at b4 c5 t6
    refine cachedAt_eq (combCached_T j a) ?_ ?_ t6
    · change F t.mem base (offset 4) = _
      unfold F
      rw [tf.fe (by decide) (by decide), cf.fe (by decide) (by decide)]
      exact b4
    · change F t.mem base (offset 5) = _
      unfold F
      rw [tf.fe (by decide) (by decide)]
      exact c5
  · have ka' : Outside base (offset 4) 96 s.mem a2.mem := fun x _ => by rw [amem, ka.mem]
    exact ((ka'.trans (bf.mono (by decide) (by decide))).trans (cf.mono (by decide) (by decide))).trans
      (tf.mono (by decide) (by decide))

end VG.Proof.Ed25519.AArch64
