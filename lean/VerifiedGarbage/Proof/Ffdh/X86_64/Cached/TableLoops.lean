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

end VG.Proof.Ffdh.X86_64.Cached
