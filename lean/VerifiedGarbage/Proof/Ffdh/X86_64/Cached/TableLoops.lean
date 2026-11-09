module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.Table
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring

/-! # FFDH's context on x86-64: the table's loops -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64 (ModCtx)

theorem ofNat_succ_sub_one (k : Nat) :
    BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem ofNat_beq_zero {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this; exact this
  · rintro rfl; rfl

/-- `[i] := [i] - 1`, and whether it is now zero. -/
theorem dec_ok {T : TabP} {s : State} (he : Env T s) {i k : Nat} (hi' : i < 32)
    (hv : word s.mem (off T.B T.o) (8 * i) = BitVec.ofNat 64 (k + 1)) (hk : k + 1 < 2 ^ 64) :
    WP isa (.block [.mov .rax (.mem (hdr i)), .alu .sub .rax (.imm 1), .store (hdr i) .rax]) s fun t =>
      t.zf = some (decide (k = 0)) ∧ t.mem = s.mem.writeW (off (off T.B T.o) (8 * i)) (BitVec.ofNat 64 k) ∧
      Keep [.rax] s t := by
  have hg := he.mc.sub.good
  have hl := hdr_lt_slot T.w 8 hi'
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (k = 0)) ∧
      t.mem = s.mem.writeW (off (off T.B T.o) (8 * i)) (BitVec.ofNat 64 k)) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * i) (by omega), hg.scr.st (d := 8 * i) (by omega), hv,
      ofNat_succ_sub_one k, ofNat_beq_zero (show k < 2 ^ 64 by omega)])  rfl) fun t ⟨h, k'⟩ => ⟨h.1, h.2, k'⟩

/-- What a stage keeps: the arrays not in `as`, the inner slots not in `hs`,
and what `Kept` keeps. -/
structure Same (T : TabP) (as hs : List Nat) (s t : State) : Prop where
  arr : ∀ b < 8, b ∉ as → wv t.mem (off T.B T.o) (slot T.w b) T.w = wv s.mem (off T.B T.o) (slot T.w b) T.w
  hdr : ∀ i, 17 ≤ i → i < 32 → i ∉ hs → word t.mem (off T.B T.o) (8 * i) = word s.mem (off T.B T.o) (8 * i)
  kept : Kept T s t

theorem Kept.of_eq {T : TabP} {s t : State} (h : t.mem = s.mem) : Kept T s t :=
  ⟨fun x _ _ => by rw [h], fun i _ => by rw [h], fun i _ => by rw [h]⟩

theorem Same.refl (T : TabP) (as hs : List Nat) (s : State) : Same T as hs s s :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, Kept.refl _ _⟩

theorem Same.trans {T : TabP} {as hs : List Nat} {s t u : State} (h₁ : Same T as hs s t) (h₂ : Same T as hs t u) :
    Same T as hs s u :=
  ⟨fun b hb hn => (h₂.arr b hb hn).trans (h₁.arr b hb hn), fun i h1 h2 hn => (h₂.hdr i h1 h2 hn).trans (h₁.hdr i h1 h2 hn),
    h₁.kept.trans h₂.kept⟩

theorem Same.mono {T : TabP} {as hs as' hs' : List Nat} {s t : State} (h : Same T as hs s t)
    (ha : ∀ b ∈ as, b ∈ as') (hh : ∀ i ∈ hs, i ∈ hs') : Same T as' hs' s t :=
  ⟨fun b hb hn => h.arr b hb (fun hm => hn (ha b hm)), fun i h1 h2 hn => h.hdr i h1 h2 (fun hm => hn (hh i hm)), h.kept⟩

theorem Same.of_eq {T : TabP} {as hs : List Nat} {s t : State} (h : t.mem = s.mem) : Same T as hs s t :=
  ⟨fun _ _ _ => by rw [h], fun _ _ _ _ => by rw [h], Kept.of_eq h⟩

theorem Same.of_outScr {T : TabP} {as hs : List Nat} {s t : State} (he : Env T s)
    (h : OutScr T.B T.Z s.mem t.mem) (hk : Kept T s t) : Same T as hs s t := by
  have hn := he.mc.sub.scr.nowrap
  refine ⟨fun b hb _ => OutScr.wvAt h (by have := slot_le (w := T.w) hb; have := he.mc.sub.hi; omega) hn,
    fun i _ h2 _ => OutScr.wordAt h (by
      have := hdr_lt_slot T.w 8 h2; have := he.mc.sub.lo; have := he.mc.sub.hi; omega) hn, hk⟩

theorem Same.of_slot {T : TabP} {as hs : List Nat} {s t : State} {i : Nat} (hi : i ∈ hs)
    (hh : ∀ i', i' < 32 → i' ≠ i → word t.mem (off T.B T.o) (8 * i') = word s.mem (off T.B T.o) (8 * i'))
    (ha : ∀ b < 8, wv t.mem (off T.B T.o) (slot T.w b) T.w = wv s.mem (off T.B T.o) (slot T.w b) T.w)
    (hk : Kept T s t) : Same T as hs s t :=
  ⟨fun b hb _ => ha b hb, fun i' _ h2 hn => hh i' h2 (fun e => hn (e ▸ hi)), hk⟩

/-- After `j` of the squares from `s`. -/
def SqInv (T : TabP) (s : State) (E j : Nat) (t : State) : Prop := Env T t ∧
  word t.mem (off T.B T.o) (8 * iI) = BitVec.ofNat 64 (T.rows - j) ∧
  wv t.mem (off T.B T.o) (slot T.w aY) T.w = T.M (E * 2 ^ j) ∧
  (∀ j', RowFits T j' → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧
  Same T [aAcc, aTmp, aY] [iI] s t ∧ Keep mmRegs s t

/-- The squares' loop body. -/
abbrev sqBody (Mo : Mont) : Prog isa := .seq (Mo.mm aY aY aY)
  (.block [.mov .rax (.mem (hdr iI)), .alu .sub .rax (.imm 1), .store (hdr iI) .rax])

theorem squares_step (Mo : Mont) {T : TabP} {s : State} (he : Env T s) {E j : Nat} (hj : j < T.rows)
    (hr' : T.rows < 2 ^ 63) {t : State} (hI : SqInv T s E j t) :
    WP isa (sqBody Mo) t fun u => u.zf = some (decide (j + 1 = T.rows)) ∧ SqInv T s E (j + 1) u := by
  obtain ⟨het, hIt, hxt, hrt, st, kt⟩ := hI
  have hP : 0 < T.P := by have := he.mc.x1; omega
  refine WP.seq (WP.mono (mm_env Mo het (Or.inr (Or.inr rfl)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hxt]; exact T.M_lt hP _)) fun u ⟨heu, hlu, hvu, hau, hru, hhu, kpu, ku⟩ => ?_)
  rw [hxt] at hvu
  have hxu := T.M_mul he.mc.odd hlu hvu
  have hIu : word u.mem (off T.B T.o) (8 * iI) = BitVec.ofNat 64 (T.rows - (j + 1) + 1) := by
    rw [hhu _ (by decide) (by decide), hIt]; congr 1; omega
  refine WP.mono (dec_ok heu (by decide) hIu (by omega)) fun v ⟨hz, hmv, kv⟩ => ?_
  obtain ⟨hev, hIv, hhv, hav, hrv, kpv⟩ := slot_env heu (i := iI) (by decide) (by decide) hmv kv.2.1 kv.2.2
    (kv.gpr (by decide))
  refine ⟨by rw [hz]; congr 1; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_iff]; omega,
    hev, hIv, by rw [hav _ (by decide), hxu]; congr 1; rw [Nat.pow_succ]; ring, fun j' hj' => (hrv j' hj').trans
      ((hru j' hj').trans (hrt j' hj')), st.trans ⟨fun b hb hn => (hav b hb).trans (hau.wv_of_not_mem hb hn
        he.mc.sub.good.scr.nowrap), fun i h1 h2 hn => (hhv i h2 (fun e => hn (by simp [e]))).trans (hhu i h1 h2),
        kpu.trans kpv⟩, (kt.trans (ku.trans kv)).mono (by decide)⟩

/-- The squares' setup: `iI := rows`. -/
theorem squares_start {T : TabP} {s : State} (he : Env T s) {E : Nat}
    (hx : wv s.mem (off T.B T.o) (slot T.w aY) T.w = T.M E) :
    WP isa (.block [.mov .rax (.mem (hdr iRows)), .store (hdr iI) .rax]) s (SqInv T s E 0) := by
  have hg := he.mc.sub.good
  have hl := hdr_lt_slot T.w 8 (show iI < 32 by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = s.mem.writeW (off (off T.B T.o) (8 * iI)) (BitVec.ofNat 64 T.rows)) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * iRows) (by have := hdr_lt_slot T.w 8 (show iRows < 32 by decide); omega),
      hg.scr.st (d := 8 * iI) (by omega), he.rows]) rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_
  obtain ⟨he₁, hI₁, hh₁, ha₁, hr₁, kp₁⟩ := slot_env he (i := iI) (by decide) (by decide) hm₁ k₁.2.1 k₁.2.2
    (k₁.gpr (by decide))
  exact ⟨he₁, by rw [hI₁]; simp, by rw [ha₁ _ (by decide), hx, Nat.pow_zero, Nat.mul_one],
      fun j' hj' => hr₁ j' hj',
      ⟨fun b hb _ => ha₁ b hb, fun i _ h2 hn => hh₁ i h2 (fun e => hn (by simp [e])), kp₁⟩, k₁.mono (by decide)⟩

/-- `aY := aY^(2^rows)`: the next tooth's entry from the last. -/
theorem squares_ok (Mo : Mont) {T : TabP} {s : State} (he : Env T s) {E : Nat}
    (hx : wv s.mem (off T.B T.o) (slot T.w aY) T.w = T.M E) (hr : 1 ≤ T.rows) (hr' : T.rows < 2 ^ 63) :
    WP isa (Precompute.squares Mo.mm) s fun t => Env T t ∧
      wv t.mem (off T.B T.o) (slot T.w aY) T.w = T.M (E * 2 ^ T.rows) ∧
      (∀ j', RowFits T j' → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧
      Same T [aAcc, aTmp, aY] [iI] s t ∧ Keep mmRegs s t := by
  unfold Precompute.squares
  refine WP.seq (WP.mono (squares_start he hx) fun s₁ h₁ =>
    wp_upto (a := 0) (N := T.rows) (by omega) (SqInv T s E) (fun j _ hj t hI => squares_step Mo he hj hr' hI)
      (fun t h => ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩) h₁)

/-- The entries `a < n` are in their rows. -/
def Entries (T : TabP) (n : Nat) (m : Mem) : Prop :=
  ∀ a < n, row m T.cp T.w (2 + a) = Spec.Rsa.toWords (T.entry a) T.w

theorem Env.P_lt {T : TabP} {s : State} (he : Env T s) : T.P < 2 ^ (64 * T.w) := by
  rw [← he.mc.xv.n]; exact wv_lt _ _ _ _

theorem rowFits_of {T : TabP} {j : Nat} (hj : j < 34) : RowFits T j := by
  unfold RowFits TabP.n; have := Nat.mul_le_mul_left T.w (show j + 1 ≤ 34 by omega); omega

/-- Entry `d + J := ` entry `J` times entry `d`, for `0 < J < d = 2^jt`. -/
theorem product_ok (Mo : Mont) {T : TabP} {s : State} (he : Env T s) {jt J : Nat} (hjt : jt < 5) (hJ : 0 < J)
    (hJd : J < 2 ^ jt) (hjtp : 0 < jt)
    (hJs : word s.mem (off T.B T.o) (8 * iJ) = BitVec.ofNat 64 J)
    (hDs : word s.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ jt))
    (hx : wv s.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ jt))
    (hE : Entries T (2 ^ jt + J) s.mem) :
    WP isa (Precompute.product Mo.mm) s fun t => Env T t ∧
      t.zf = some (decide (J + 1 = 2 ^ jt)) ∧
      word t.mem (off T.B T.o) (8 * iJ) = BitVec.ofNat 64 (J + 1) ∧
      word t.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ jt) ∧
      wv t.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ jt) ∧
      Entries T (2 ^ jt + (J + 1)) t.mem ∧
      (∀ j', j' < 2 → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧
      Same T [aAcc, aTmp, aX, aY] [iJ] s t ∧ Keep mmRegs s t := by
  have hg := he.mc.sub.good
  have hP : 0 < T.P := by have := he.mc.x1; omega
  have hlJ := hdr_lt_slot T.w 8 (show iJ < 32 by decide)
  have hlD := hdr_lt_slot T.w 8 (show iD < 32 by decide)
  have h32 : 2 ^ jt ≤ 16 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show jt ≤ 4 by omega); simpa using this
  unfold Precompute.product
  simp only [seqs]
  -- `rax := J + 2`.
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (J + 2) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * iJ) (by omega), hJs]
    apply BitVec.eq_of_toNat_eq; simp) rfl)
    fun s₁ ⟨⟨hax₁, hm₁⟩, k₁⟩ => ?_)
  have he₁ : Env T s₁ := he.of_outScr (by intro x _; rw [hm₁]) k₁.2.1 k₁.2.2 (k₁.gpr (by decide))
  have hrJ : row s₁.mem T.cp T.w (J + 2) = Spec.Rsa.toWords (T.entry J) T.w := by
    rw [hm₁, show J + 2 = 2 + J by omega]; exact hE J (by omega)
  refine WP.seq (WP.mono (load_env he₁ hax₁ (Or.inl rfl) (by omega) hrJ
    (T.M_lt_R hP (Nat.le_of_lt he.P_lt) _))
    fun s₂ ⟨he₂, hL₂, ha₂, hr₂, hh₂, kp₂, k₂⟩ => ?_)
  have hX₂ : wv s₂.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ jt) := by
    rw [ha₂ _ (by decide) (by decide), hm₁, hx]
  refine WP.seq (WP.mono (mm_env Mo he₂ (Or.inl rfl) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hX₂]; exact T.M_lt hP _))
    fun s₃ ⟨he₃, hl₃, hv₃, ha₃, hr₃, hh₃, kp₃, k₃⟩ => ?_)
  rw [hL₂, hX₂] at hv₃
  have hv₃' : wv s₃.mem (off T.B T.o) (slot T.w aX) T.w = T.entry (2 ^ jt + J) := by
    rw [T.entry_add hjt hJd]; exact T.M_mul he.mc.odd hl₃ hv₃
  have hJ₃ : word s₃.mem (off T.B T.o) (8 * iJ) = BitVec.ofNat 64 J := by
    rw [hh₃ _ (by decide) (by decide), hh₂ _ (by decide), hm₁, hJs]
  have hD₃ : word s₃.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ jt) := by
    rw [hh₃ _ (by decide) (by decide), hh₂ _ (by decide), hm₁, hDs]
  have hg₃ := he₃.mc.sub.good
  -- `rax := J + d + 2`.
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (2 + (2 ^ jt + J)) ∧
      t.mem = s₃.mem) (by
    xrun [State.ea, hdr, hg₃.rdi, hdrOff, hg₃.scr.ld (d := 8 * iJ) (by omega), hg₃.scr.ld (d := 8 * iD) (by omega),
      hJ₃, hD₃]
    apply BitVec.eq_of_toNat_eq; simp; omega) rfl)
    fun s₄ ⟨⟨hax₄, hm₄⟩, k₄⟩ => ?_)
  have he₄ : Env T s₄ := he₃.of_outScr (by intro x _; rw [hm₄]) k₄.2.1 k₄.2.2 (k₄.gpr (by decide))
  refine WP.seq (WP.mono (store_env he₄ hax₄ (by decide) (by omega))
    fun s₅ ⟨he₅, hrow₅, hr₅, hos₅, kp₅, k₅⟩ => ?_)
  rw [hm₄, hv₃'] at hrow₅
  have hg₅ := he₅.mc.sub.good
  have hJ₅ : word s₅.mem (off T.B T.o) (8 * iJ) = BitVec.ofNat 64 J := by
    rw [OutScr.wordAt hos₅ (by have := he.mc.sub.hi; have := he.mc.sub.lo; omega) he.mc.sub.scr.nowrap, hm₄, hJ₃]
  have hD₅ : word s₅.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ jt) := by
    rw [OutScr.wordAt hos₅ (by have := he.mc.sub.hi; have := he.mc.sub.lo; omega) he.mc.sub.scr.nowrap, hm₄, hD₃]
  have hD₅' : (s₅.mem.writeW (off (off T.B T.o) (8 * iJ)) (BitVec.ofNat 64 (J + 1))).readW
      (off (off T.B T.o) (8 * iD)) 64 = BitVec.ofNat 64 (2 ^ jt) := by
    change Bignum.word _ (off T.B T.o) (8 * iD) = _
    rw [(writeW_outside s₅.mem (off T.B T.o) (d := 8 * iJ) _ (by decide)).word (d := 8 * iD) (by decide)
      (by decide)]; exact hD₅
  -- `J := J + 1`, and whether it reached `d`.
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (J + 1 = 2 ^ jt)) ∧
      t.mem = s₅.mem.writeW (off (off T.B T.o) (8 * iJ)) (BitVec.ofNat 64 (J + 1))) (by
    xrun [State.ea, hdr, hg₅.rdi, hdrOff, hg₅.scr.ld (d := 8 * iJ) (by omega), hg₅.scr.st (d := 8 * iJ) (by omega),
      hg₅.scr.ld (d := 8 * iD) (by omega), hJ₅, ofNat_add_one, hD₅', ofNat_sub_beq (show J + 1 < 2 ^ 64 by omega)
      (show 2 ^ jt < 2 ^ 64 by omega)]) rfl)
    fun t ⟨⟨hz, hmt⟩, kt⟩ => ?_
  obtain ⟨het, hJt, hht, hat, hrt, kpt⟩ := slot_env he₅ (i := iJ) (by decide) (by decide) hmt kt.2.1 kt.2.2
    (kt.gpr (by decide))
  have hn := he.mc.sub.scr.nowrap
  have hio : ∀ i < 32, T.o + 8 * i + 8 ≤ T.Z := fun i hi => by
    have := hdr_lt_slot T.w 8 hi; have := he.mc.sub.lo; have := he.mc.sub.hi; omega
  have hwo : ∀ b < 8, T.o + slot T.w b + 8 * T.w ≤ T.Z := fun b hb => by
    have := slot_le (w := T.w) hb; have := he.mc.sub.hi; omega
  refine ⟨het, by rw [hz], hJt, ?_, ?_, fun a ha => ?_, fun j' hj' => ?_, ⟨fun b hb hnb => ?_,
    fun i h1 h2 hni => ?_, ((((Kept.of_eq hm₁).trans kp₂).trans kp₃).trans
      ((Kept.of_eq hm₄).trans kp₅)).trans kpt⟩, ((((k₁.trans k₂).trans k₃).trans k₄).trans (k₅.trans kt)).mono
      (by decide)⟩
  · rw [hht _ (by decide) (by decide)]; exact hD₅
  · rw [hat _ (by decide), OutScr.wvAt hos₅ (hwo _ (by decide)) hn, hm₄,
      ha₃.wv_of_not_mem (by decide) (by decide) he.mc.sub.good.scr.nowrap, hX₂]
  · rw [hrt _ (rowFits_of (by omega))]
    by_cases hlast : a = 2 ^ jt + J
    · rw [hlast]; exact hrow₅
    · rw [hr₅ _ (by omega) (rowFits_of (by omega)), hm₄, hr₃ _ (rowFits_of (by omega)), hr₂ _ (rowFits_of (by omega)),
        hm₁]
      exact hE a (by omega)
  · rw [hrt _ (rowFits_of (by omega)), hr₅ _ (by omega) (rowFits_of (by omega)), hm₄, hr₃ _ (rowFits_of (by omega)),
      hr₂ _ (rowFits_of (by omega)), hm₁]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnb
    rw [hat _ hb, OutScr.wvAt hos₅ (hwo _ hb) hn, hm₄,
      ha₃.wv_of_not_mem hb (by simp [hnb.1, hnb.2.1, hnb.2.2.1]) he.mc.sub.good.scr.nowrap,
      ha₂ _ hb hnb.2.2.1, hm₁]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hni
    rw [hht _ h2 hni, OutScr.wordAt hos₅ (hio _ h2) hn, hm₄, hh₃ _ h1 h2, hh₂ _ h2, hm₁]

/-- The tooth `d = 2^(c+1)`: its entry and the entries `d + J` for `0 < J < d`. -/
theorem column_ok (Mo : Mont) {T : TabP} {s : State} (he : Env T s) {c : Nat} (hc : c < 4)
    (hDs : word s.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (c + 1)))
    (hx : wv s.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ c))
    (hE : Entries T (2 ^ (c + 1)) s.mem) (hr : 1 ≤ T.rows) (hr' : T.rows < 2 ^ 63) :
    WP isa (Precompute.column Mo.mm) s fun t => Env T t ∧
      t.zf = some (decide (c + 1 = 4)) ∧
      word t.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (c + 2)) ∧
      wv t.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ (c + 1)) ∧
      Entries T (2 ^ (c + 2)) t.mem ∧
      (∀ j', j' < 2 → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧
      Same T [aAcc, aTmp, aX, aXm, aY] [iI, iJ, iD] s t ∧ Keep mmRegs s t := by
  have hn := he.mc.sub.scr.nowrap
  have hio : ∀ i < 32, T.o + 8 * i + 8 ≤ T.Z := fun i hi => by
    have := hdr_lt_slot T.w 8 hi; have := he.mc.sub.lo; have := he.mc.sub.hi; omega
  have hwo : ∀ b < 8, T.o + slot T.w b + 8 * T.w ≤ T.Z := fun b hb => by
    have := slot_le (w := T.w) hb; have := he.mc.sub.hi; omega
  have hlD := hdr_lt_slot T.w 8 (show iD < 32 by decide)
  have hlJ := hdr_lt_slot T.w 8 (show iJ < 32 by decide)
  have hd16 : 2 ^ (c + 1) ≤ 16 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show c + 1 ≤ 4 by omega); simpa using this
  have hd2 : 2 ≤ 2 ^ (c + 1) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ c + 1 by omega); simpa using this
  unfold Precompute.column
  simp only [seqs]
  refine WP.seq (WP.mono (squares_ok Mo he hx hr hr') fun s₁ ⟨he₁, hx₁, hr₁, st₁, k₁⟩ => ?_)
  rw [← T.entry_tooth hc] at hx₁
  have hD₁ : word s₁.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (c + 1)) := by
    rw [st₁.hdr _ (by decide) (by decide) (by decide)]; exact hDs
  have hg₁ := he₁.mc.sub.good
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (2 + 2 ^ (c + 1)) ∧
      t.mem = s₁.mem) (by
    xrun [State.ea, hdr, hg₁.rdi, hdrOff, hg₁.scr.ld (d := 8 * iD) (by omega), hD₁]
    apply BitVec.eq_of_toNat_eq; simp; omega) rfl)
    fun s₂ ⟨⟨hax₂, hm₂⟩, k₂⟩ => ?_)
  have he₂ : Env T s₂ := he₁.of_outScr (by intro x _; rw [hm₂]) k₂.2.1 k₂.2.2 (k₂.gpr (by decide))
  refine WP.seq (WP.mono (store_env he₂ hax₂ (by decide) (by omega))
    fun s₃ ⟨he₃, hrow₃, hr₃, hos₃, kp₃, k₃⟩ => ?_)
  rw [hm₂, hx₁] at hrow₃
  have hg₃ := he₃.mc.sub.good
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = s₃.mem.writeW (off (off T.B T.o) (8 * iJ)) (BitVec.ofNat 64 1)) (by
    xrun [State.ea, hdr, hg₃.rdi, hdrOff, hg₃.scr.st (d := 8 * iJ) (by omega),
      show BitVec.setWidth 64 (1 : BitVec 32) = BitVec.ofNat 64 1 from rfl]) rfl)
    fun s₄ ⟨hm₄, k₄⟩ => ?_)
  obtain ⟨he₄, hJ₄, hh₄, ha₄, hr₄, kp₄⟩ := slot_env he₃ (i := iJ) (by decide) (by decide) hm₄ k₄.2.1 k₄.2.2
    (k₄.gpr (by decide))
  have hD₄ : word s₄.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (c + 1)) := by
    rw [hh₄ _ (by decide) (by decide), OutScr.wordAt hos₃ (hio _ (by decide)) hn, hm₂, hD₁]
  have hx₄ : wv s₄.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ (c + 1)) := by
    rw [ha₄ _ (by decide), OutScr.wvAt hos₃ (hwo _ (by decide)) hn, hm₂, hx₁]
  have hE₄ : Entries T (2 ^ (c + 1) + 1) s₄.mem := fun a ha => by
    rw [hr₄ _ (rowFits_of (by omega))]
    by_cases hlast : a = 2 ^ (c + 1)
    · rw [hlast]; exact hrow₃
    · rw [hr₃ _ (by omega) (rowFits_of (by omega)), hm₂, hr₁ _ (rowFits_of (by omega))]
      exact hE a (by omega)
  let Inv : Nat → State → Prop := fun J t => Env T t ∧
    word t.mem (off T.B T.o) (8 * iJ) = BitVec.ofNat 64 J ∧
    word t.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (c + 1)) ∧
    wv t.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ (c + 1)) ∧
    Entries T (2 ^ (c + 1) + J) t.mem ∧
    (∀ j', j' < 2 → row t.mem T.cp T.w j' = row s₄.mem T.cp T.w j') ∧
    Same T [aAcc, aTmp, aX, aY] [iJ] s₄ t ∧ Keep mmRegs s₄ t
  refine WP.seq (WP.mono (wp_upto (a := 1) (N := 2 ^ (c + 1)) (by omega) Inv
    (fun J hJ1 hJN t ⟨het, hJt, hDt, hxt, hEt, hpt, stt, kt⟩ => WP.mono
      (product_ok Mo het (jt := c + 1) (by omega) (by omega) hJN (by omega) hJt hDt hxt hEt)
      fun u ⟨heu, hz, hJu, hDu, hxu, hEu, hpu, stu, ku⟩ =>
        ⟨hz, heu, hJu, hDu, hxu, hEu, fun j' hj' => (hpu j' hj').trans (hpt j' hj'), stt.trans stu,
          (kt.trans ku).mono (by decide)⟩)
    (fun t h => h) ⟨he₄, hJ₄, hD₄, hx₄, hE₄, fun _ _ => rfl, Same.refl _ _ _ _, Keep.refl _ _⟩)
    fun s₅ ⟨he₅, _, hD₅, hx₅, hE₅, hp₅, st₅, k₅⟩ => ?_)
  have hg₅ := he₅.mc.sub.good
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (c + 1 = 4)) ∧
      t.mem = s₅.mem.writeW (off (off T.B T.o) (8 * iD)) (BitVec.ofNat 64 (2 ^ (c + 2)))) (by
    have e : BitVec.ofNat 64 (2 ^ (c + 1)) + BitVec.ofNat 64 (2 ^ (c + 1)) = BitVec.ofNat 64 (2 ^ (c + 2)) := by
      rw [BitVec.ofNat_add_ofNat, Nat.pow_succ 2 (c + 1)]; congr 1; omega
    have hb : (BitVec.ofNat 64 (2 ^ (c + 2)) - 32 == 0) = decide (c + 1 = 4) := by
      have hc4 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases hc4 with rfl | rfl | rfl | rfl <;> decide
    xrun [State.ea, hdr, hg₅.rdi, hdrOff, hg₅.scr.ld (d := 8 * iD) (by omega), hg₅.scr.st (d := 8 * iD) (by omega),
      hD₅, e, hb]) rfl)
    fun t ⟨⟨hz, hmt⟩, kt⟩ => ?_
  obtain ⟨het, hDt, hht, hat, hrt, kpt⟩ := slot_env he₅ (i := iD) (by decide) (by decide) hmt kt.2.1 kt.2.2
    (kt.gpr (by decide))
  refine ⟨het, hz, hDt, by rw [hat _ (by decide)]; exact hx₅,
    fun a ha => by rw [hrt _ (rowFits_of (by rw [Nat.pow_succ 2 (c + 1)] at ha; omega))]
                   exact hE₅ a (by rw [Nat.pow_succ 2 (c + 1)] at ha; omega),
    fun j' hj' => by
      rw [hrt _ (rowFits_of (by omega)), hp₅ j' hj', hr₄ _ (rowFits_of (by omega)), hr₃ _ (by omega)
        (rowFits_of (by omega)), hm₂, hr₁ _ (rowFits_of (by omega))],
    ?_, ?_⟩
  · exact ((((((st₁.mono (by decide) (by decide)).trans (Same.of_eq hm₂)).trans (Same.of_outScr he₂ hos₃ kp₃)).trans
      (Same.of_slot (i := iJ) (by decide) hh₄ ha₄ kp₄)).trans (st₅.mono (by decide) (by decide))).trans
      (Same.of_slot (i := iD) (by decide) hht hat kpt))
  · exact ((k₁.trans k₂).trans ((k₃.trans k₄).trans (k₅.trans kt))).mono (by decide)

/-- Bytes outside the working space and the context keep their values. -/
theorem Src.of_only {T : TabP} {s t : State} {p : Addr} {bs : List Byte} (h : Src s T.B T.Z p bs)
    (hm : Only T s.mem t.mem) (hsep : ∀ i < bs.length, 8 * T.n ≤ ofs T.cp (p + BitVec.ofNat 64 i))
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Src t T.B T.Z p bs :=
  ⟨fun i hi => by rw [hrd, hwr]; exact h.rd i hi,
    fun i hi => by rw [hm _ (h.out i hi) (hsep i hi)]; exact h.val i hi, h.out⟩

/-- Entries 0 and 1, and the first tooth `d := 2`. -/
theorem initial_ok (Mo : Mont) {T : TabP} {s : State} (he : Env T s)
    {gp : Addr} {gb : List Byte} (hG : Spec.Rsa.os2ip gb = T.G)
    (hsG : word s.mem T.B (8 * VG.Impl.Ffdh.X86_64.Domain.sG) = gp)
    (hsK : word s.mem T.B (8 * sK) = BitVec.ofNat 64 gb.length)
    (hsrc : Src s T.B T.Z gp gb) (hgsep : ∀ i < gb.length, 8 * T.n ≤ ofs T.cp (gp + BitVec.ofNat 64 i))
    (hgl : 1 ≤ gb.length) (hgw : (gb.length + 7) / 8 ≤ T.w) :
    WP isa (seqs (Precompute.initial Mo.mm ++ ([.block [.mov32 .rax (.imm 2), .store (hdr iD) .rax]] : List (Prog isa)))) s fun t =>
      Env T t ∧ word t.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (0 + 1)) ∧
      wv t.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ 0) ∧ Entries T (2 ^ (0 + 1)) t.mem ∧
      (∀ j', j' < 2 → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧ Kept T s t ∧ Keep mmRegs s t := by
  have hn := he.mc.sub.scr.nowrap
  have hP : 0 < T.P := by have := he.mc.x1; omega
  have hR : Nat.Coprime T.R T.P := VG.Proof.Bignum.coprime_pow2 he.mc.odd _
  have hio : ∀ i < 32, T.o + 8 * i + 8 ≤ T.Z := fun i hi => by
    have := hdr_lt_slot T.w 8 hi; have := he.mc.sub.lo; have := he.mc.sub.hi; omega
  unfold Precompute.initial
  simp only [List.cons_append, List.append_assoc]
  -- Entry 0.
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (mm_env Mo he (Or.inr (Or.inr rfl)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [he.mc.xv.one]; exact he.mc.x1))
    fun s₁ ⟨he₁, hl₁, hv₁, ha₁, hr₁, hh₁, kp₁, k₁⟩ => ?_)
  have hY₁ : wv s₁.mem (off T.B T.o) (slot T.w aY) T.w = T.entry 0 := by
    rw [T.entry_zero he.mc.x1]
    have := mont_cancel hR (o := wv s₁.mem (off T.B T.o) (slot T.w aY) T.w) (c := T.R) (by
      rw [hv₁, he.mc.xv.one, Nat.mul_one, ← he.mc.r2])
    rw [Nat.mod_eq_of_lt hl₁] at this
    exact this
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 2 ∧
      t.mem = s₁.mem) (by xrun [show BitVec.setWidth 64 (2 : BitVec 32) = BitVec.ofNat 64 2 from rfl]) rfl)
    fun s₂ ⟨⟨hax₂, hm₂⟩, k₂⟩ => ?_)
  have he₂ : Env T s₂ := he₁.of_outScr (by intro x _; rw [hm₂]) k₂.2.1 k₂.2.2 (k₂.gpr (by decide))
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp [Crt.loadArr]) (WP.mono (store_env he₂ hax₂ (by decide) (by decide))
    fun s₃ ⟨he₃, hrow₃, hr₃, hos₃, kp₃, k₃⟩ => ?_)
  rw [hm₂, hY₁] at hrow₃
  -- `aX := g`.
  have kp₃' : Kept T s s₃ := (kp₁.trans (Kept.of_eq hm₂)).trans kp₃
  have hsrc₃ : Src s₃ T.B T.Z gp gb := Src.of_only hsrc kp₃'.only hgsep
    (by rw [k₃.2.1, k₂.2.1, k₁.2.1]) (by rw [k₃.2.2, k₂.2.2, k₁.2.2])
  refine wp_seqs_append (a := Crt.loadArr aX VG.Impl.Ffdh.X86_64.Domain.sG sK) (by simp [Crt.loadArr]) (by simp) (WP.mono (primeLoad_ok he₃.mc.sub he.mc.w2 (Nat.le_refl _)
    (by have := he.mc.w28; omega) (show aX < 8 by decide) (show VG.Impl.Ffdh.X86_64.Domain.sG < 32 by decide)
    (show sK < 32 by decide) (by rw [kp₃'.outer _ (by decide)]; exact hsG)
    (by rw [kp₃'.outer _ (by decide)]; exact hsK) hsrc₃ hgl (by have := he.mc.w28; omega) hgw)
    fun s₄ ⟨_, hX₄, ho₄, k₄⟩ => ?_)
  have hf₄ : Frm (off T.B T.o) [(slot T.w aX, 8 * (T.w + 2))] s₃.mem s₄.mem := Frm.of_outside ho₄ (by simp)
  obtain ⟨hin₄, hout₄⟩ := inScr_of_inner he₃ hf₄ (fun r hr => by rw [List.mem_singleton.mp hr]; exact slot_le (by decide))
  have hd₄ : ∀ i, i < 32 → word s₄.mem (off T.B T.o) (8 * i) = word s₃.mem (off T.B T.o) (8 * i) :=
    fun i hi => hf₄.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (hdr_lt_slot T.w aX hi))
      (by have := hdr_lt_slot T.w 8 hi; omega)
  have he₄ : Env T s₄ := he₃.of_inner (Frm.cover hf₄ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨(slot T.w aX, 3 * (8 * (T.w + 2))), by simp [innerR], by simp only; omega, by simp only; omega⟩))
    k₄.2.1 k₄.2.2 (k₄.gpr (by decide)) (hd₄ _ (by decide)) (hd₄ _ (by decide))
  have kp₄ : Kept T s₃ s₄ := ⟨Only.of_inScr hin₄, hout₄, fun i hi => ctxWord_of_inScr he₃ hin₄ (by unfold TabP.n; omega)⟩
  have hR2₄ : wv s₄.mem (off T.B T.o) (slot T.w aR2) T.w = wv s.mem (off T.B T.o) (slot T.w aR2) T.w := by
    rw [hf₄.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [slot, aX, aR2]; omega)
      (by have := slot_le (w := T.w) (show aR2 < 8 by decide); have := he.mc.w28; unfold slot hdrBytes at *; omega),
      OutScr.wvAt hos₃ (by have := slot_le (w := T.w) (show aR2 < 8 by decide); have := he.mc.sub.hi; omega) hn,
      hm₂, ha₁.wv_of_not_mem (by decide) (by decide) he.mc.sub.good.scr.nowrap]
  -- Entry 1.
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (mm_env Mo he₄ (Or.inr (Or.inl rfl)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [hR2₄]; exact he.mc.r2l))
    fun s₅ ⟨he₅, hl₅, hv₅, ha₅, hr₅, hh₅, kp₅, k₅⟩ => ?_)
  have hXm₅ : wv s₅.mem (off T.B T.o) (slot T.w aXm) T.w = T.entry 1 := by
    rw [T.entry_one]
    have := mont_cancel hR (o := wv s₅.mem (off T.B T.o) (slot T.w aXm) T.w) (c := T.G * T.R) (by
      rw [hv₅, hX₄, hG, hR2₄, Nat.mul_mod, he.mc.r2, ← Nat.mul_mod, Nat.mul_assoc])
    rw [Nat.mod_eq_of_lt hl₅] at this
    exact this
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 3 ∧
      t.mem = s₅.mem) (by xrun [show BitVec.setWidth 64 (3 : BitVec 32) = BitVec.ofNat 64 3 from rfl]) rfl)
    fun s₆ ⟨⟨hax₆, hm₆⟩, k₆⟩ => ?_)
  have he₆ : Env T s₆ := he₅.of_outScr (by intro x _; rw [hm₆]) k₆.2.1 k₆.2.2 (k₆.gpr (by decide))
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (store_env he₆ hax₆ (by decide) (by decide))
    fun s₇ ⟨he₇, hrow₇, hr₇, hos₇, kp₇, k₇⟩ => ?_)
  rw [hm₆, hXm₅] at hrow₇
  -- `aY :=` entry 1.
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 3 ∧
      t.mem = s₇.mem) (by xrun [show BitVec.setWidth 64 (3 : BitVec 32) = BitVec.ofNat 64 3 from rfl]) rfl)
    fun s₉ ⟨⟨hax₉, hm₉⟩, k₉⟩ => ?_)
  have he₉ : Env T s₉ := he₇.of_outScr (by intro x _; rw [hm₉]) k₉.2.1 k₉.2.2 (k₉.gpr (by decide))
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (load_env he₉ hax₉ (V := T.entry 1) (Or.inr (Or.inr rfl)) (by decide)
    (by rw [hm₉]; exact hrow₇) (T.M_lt_R hP (Nat.le_of_lt he.P_lt) _))
    fun s₁₀ ⟨he₁₀, hY₁₀, _, hr₁₀, _, kp₁₀, k₁₀⟩ => ?_)
  have hg₇ := he₁₀.mc.sub.good
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = s₁₀.mem.writeW (off (off T.B T.o) (8 * iD)) (BitVec.ofNat 64 2)) (by
    xrun [State.ea, hdr, hg₇.rdi, hdrOff, hg₇.scr.st (d := 8 * iD) (by have := hdr_lt_slot T.w 8 (show iD < 32 by decide); omega),
      show BitVec.setWidth 64 (2 : BitVec 32) = BitVec.ofNat 64 2 from rfl]) rfl)
    fun s₈ ⟨hm₈, k₈⟩ => ?_
  obtain ⟨he₈, hD₈, _, ha₈, hr₈, kp₈⟩ := slot_env he₁₀ (i := iD) (by decide) (by decide) hm₈ k₈.2.1 k₈.2.2
    (k₈.gpr (by decide))
  have hXm₈ : wv s₈.mem (off T.B T.o) (slot T.w aY) T.w = T.entry 1 := by
    rw [ha₈ _ (by decide)]; exact hY₁₀
  have hE₈ : Entries T 2 s₈.mem := fun a ha => by
    rw [hr₈ _ (rowFits_of (by omega)), hr₁₀ _ (rowFits_of (by omega)), hm₉]
    rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl
    · rw [hr₇ _ (by decide) (rowFits_of (by decide)), hm₆, hr₅ _ (rowFits_of (by decide)),
        row_of_inScr he₃ hin₄ (rowFits_of (by decide))]
      exact hrow₃
    · exact hrow₇
  have hp₈ : ∀ j', j' < 2 → row s₈.mem T.cp T.w j' = row s.mem T.cp T.w j' := fun j' hj' => by
    rw [hr₈ _ (rowFits_of (by omega)), hr₁₀ _ (rowFits_of (by omega)), hm₉,
      hr₇ _ (by omega) (rowFits_of (by omega)), hm₆, hr₅ _ (rowFits_of (by omega)),
      row_of_inScr he₃ hin₄ (rowFits_of (by omega)), hr₃ _ (by omega) (rowFits_of (by omega)), hm₂,
      hr₁ _ (rowFits_of (by omega))]
  have kp₈' : Kept T s s₈ := (((((kp₃'.trans kp₄).trans kp₅).trans (Kept.of_eq hm₆)).trans kp₇).trans
    ((Kept.of_eq hm₉).trans kp₁₀)).trans kp₈
  have k₈' : Keep mmRegs s s₈ := ((((k₁.trans k₂).trans (k₃.trans k₄)).trans (k₅.trans k₆)).trans
    ((k₇.trans (k₉.trans k₁₀)).trans k₈)).mono (by decide)
  exact ⟨he₈, hD₈, hXm₈, hE₈, hp₈, kp₈', k₈'⟩

/-- The table: entries 0 and 1, then the four teeth's columns. -/
theorem table_ok (Mo : Mont) {T : TabP} {s : State} (he : Env T s) (hr : 1 ≤ T.rows) (hr' : T.rows < 2 ^ 63)
    {gp : Addr} {gb : List Byte} (hG : Spec.Rsa.os2ip gb = T.G)
    (hsG : word s.mem T.B (8 * VG.Impl.Ffdh.X86_64.Domain.sG) = gp)
    (hsK : word s.mem T.B (8 * sK) = BitVec.ofNat 64 gb.length)
    (hsrc : Src s T.B T.Z gp gb) (hgsep : ∀ i < gb.length, 8 * T.n ≤ ofs T.cp (gp + BitVec.ofNat 64 i))
    (hgl : 1 ≤ gb.length) (hgw : (gb.length + 7) / 8 ≤ T.w) :
    WP isa (seqs (Precompute.table Mo.mm)) s fun t => Env T t ∧ Entries T 32 t.mem ∧
      (∀ j', j' < 2 → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧ Kept T s t ∧ Keep mmRegs s t := by
  unfold Precompute.table
  rw [show Precompute.initial Mo.mm ++ [.block [.mov32 .rax (.imm 2), .store (hdr iD) .rax],
      .loop (Precompute.column Mo.mm) .ne] = (Precompute.initial Mo.mm ++
      [.block [.mov32 .rax (.imm 2), .store (hdr iD) .rax]]) ++ [.loop (Precompute.column Mo.mm) .ne] by simp]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (initial_ok Mo he hG hsG hsK hsrc hgsep hgl hgw)
    fun s₈ ⟨he₈, hD₈, hXm₈, hE₈, hp₈, kp₈', k₈'⟩ => ?_)
  -- The four teeth.
  let Inv : Nat → State → Prop := fun c t => Env T t ∧
    word t.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (c + 1)) ∧
    wv t.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ c) ∧ Entries T (2 ^ (c + 1)) t.mem ∧
    (∀ j', j' < 2 → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧ Kept T s t ∧ Keep mmRegs s t
  exact wp_upto (a := 0) (N := 4) (by decide) Inv
    (fun c _ hc t ⟨het, hDt, hxt, hEt, hpt, kpt, kt⟩ => WP.mono (column_ok Mo het hc hDt hxt hEt hr hr')
      fun u ⟨heu, hz, hDu, hxu, hEu, hpu, stu, ku⟩ =>
        ⟨hz, heu, hDu, by rw [hxu], hEu, fun j' hj' => (hpu j' hj').trans (hpt j' hj'), kpt.trans stu.kept,
          (kt.trans ku).mono (by decide)⟩)
    (fun t ⟨het, _, _, hEt, hpt, kpt, kt⟩ => ⟨het, hEt, hpt, kpt, kt⟩)
    ⟨he₈, hD₈, hXm₈, hE₈, hp₈, kp₈', k₈'⟩

end VG.Proof.Ffdh.X86_64.Cached
