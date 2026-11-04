module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.Table
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
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

theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 := by decide
theorem sx2 : BitVec.signExtend 64 (2 : BitVec 32) = BitVec.ofNat 64 2 := by decide

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

/-- `aXm := aXm^(2^rows)`: the next tooth's entry from the last. -/
theorem squares_ok (Mo : Mont) {T : TabP} {s : State} (he : Env T s) {E : Nat}
    (hx : wv s.mem (off T.B T.o) (slot T.w aXm) T.w = T.M E) (hr : 1 ≤ T.rows) (hr' : T.rows < 2 ^ 63) :
    WP isa (Precompute.squares Mo.mm) s fun t => Env T t ∧
      wv t.mem (off T.B T.o) (slot T.w aXm) T.w = T.M (E * 2 ^ T.rows) ∧
      (∀ j', RowFits T j' → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧
      Same T [aAcc, aTmp, aXm] [iI] s t ∧ Keep mmRegs s t := by
  have hg := he.mc.sub.good
  have hl := hdr_lt_slot T.w 8 (show iI < 32 by decide)
  have hP : 0 < T.P := by have := he.mc.x1; omega
  unfold Precompute.squares
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = s.mem.writeW (off (off T.B T.o) (8 * iI)) (BitVec.ofNat 64 T.rows)) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * iRows) (by have := hdr_lt_slot T.w 8 (show iRows < 32 by decide); omega),
      hg.scr.st (d := 8 * iI) (by omega), he.rows]) rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_)
  obtain ⟨he₁, hI₁, hh₁, ha₁, hr₁, kp₁⟩ := slot_env he (i := iI) (by decide) (by decide) hm₁ k₁.2.1 k₁.2.2
    (k₁.gpr (by decide))
  let Inv : Nat → State → Prop := fun j t => Env T t ∧
    word t.mem (off T.B T.o) (8 * iI) = BitVec.ofNat 64 (T.rows - j) ∧
    wv t.mem (off T.B T.o) (slot T.w aXm) T.w = T.M (E * 2 ^ j) ∧
    (∀ j', RowFits T j' → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧
    Same T [aAcc, aTmp, aXm] [iI] s t ∧ Keep mmRegs s t
  refine wp_upto (a := 0) (N := T.rows) (by omega) Inv (fun j _ hj t ⟨het, hIt, hxt, hrt, st, kt⟩ => ?_)
    (fun t h => ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩)
    ⟨he₁, by rw [hI₁]; simp, by rw [ha₁ _ (by decide), hx, Nat.pow_zero, Nat.mul_one],
      fun j' hj' => hr₁ j' hj',
      ⟨fun b hb _ => ha₁ b hb, fun i _ h2 hn => hh₁ i h2 (fun e => hn (by simp [e])), kp₁⟩, k₁.mono (by decide)⟩
  refine WP.seq (WP.mono (mm_env Mo het (Or.inr (Or.inl rfl)) (by decide) (by decide) (by decide) (by decide)
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
    (hx : wv s.mem (off T.B T.o) (slot T.w aXm) T.w = T.entry (2 ^ jt))
    (hE : Entries T (2 ^ jt + J) s.mem) :
    WP isa (Precompute.product Mo.mm) s fun t => Env T t ∧
      t.zf = some (decide (J + 1 = 2 ^ jt)) ∧
      word t.mem (off T.B T.o) (8 * iJ) = BitVec.ofNat 64 (J + 1) ∧
      word t.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ jt) ∧
      wv t.mem (off T.B T.o) (slot T.w aXm) T.w = T.entry (2 ^ jt) ∧
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
  refine WP.seq (WP.mono (load_env he₁ hax₁ (Or.inr (Or.inr rfl)) (by omega) hrJ
    (T.M_lt_R hP (Nat.le_of_lt he.P_lt) _))
    fun s₂ ⟨he₂, hY₂, ha₂, hr₂, hh₂, kp₂, k₂⟩ => ?_)
  have hX₂ : wv s₂.mem (off T.B T.o) (slot T.w aXm) T.w = T.entry (2 ^ jt) := by
    rw [ha₂ _ (by decide) (by decide), hm₁, hx]
  refine WP.seq (WP.mono (mm_env Mo he₂ (Or.inl rfl) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hX₂]; exact T.M_lt hP _))
    fun s₃ ⟨he₃, hl₃, hv₃, ha₃, hr₃, hh₃, kp₃, k₃⟩ => ?_)
  rw [hY₂, hX₂] at hv₃
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
      ha₂ _ hb hnb.2.2.2, hm₁]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hni
    rw [hht _ h2 hni, OutScr.wordAt hos₅ (hio _ h2) hn, hm₄, hh₃ _ h1 h2, hh₂ _ h2, hm₁]

end VG.Proof.Ffdh.X86_64.Cached
