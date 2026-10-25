module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.SqrRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish64
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontSqr
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound

/-!
# Montgomery squaring on PPC64LE: the square

`dbl_ok`: `b := 2 a`. `sqrRounds_ok`: round 0 and the rounds `1` to `w - 1`,
with the invariant that after `i` rounds `2^(64 i) T = L² + 2 L H 2^(64 i) + U m`
for `L` the low `i` words of `a`, `H` the others and some `U < 2^(64 i)`, and
`b`'s words from `i` hold `2 H`: after `w` rounds `2^(64 w) T = a² + U m`.
`sqrN_ok`: `sqrTail`, stated as `tailN_ok` with `a = b`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Sqr

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.MontSqr VG.Proof.Bignum.PPC64LE

/-- A word of the doubling: `2 x + c` is the low word of `(x << 1) + c` and
`2⁶⁴` times `x`'s top bit. -/
theorem sqr_dbl_arith (x c : BitVec 64) (hc : c.toNat ≤ 1) :
    (x <<< 1 + c).toNat + 2 ^ 64 * (x >>> 63).toNat = 2 * x.toNat + c.toNat ∧ (x >>> 63).toNat ≤ 1 := by
  have hx := x.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  omega

/-- `dbl`, `a` (`w` words) at `da` (`r6`) and `b` at `dB` (`r9`): `b`'s `w + 1`
words are `2 a`. -/
theorem dbl_ok {s : State} {B : Addr} {Z da dB w : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .r6 = off B da) (h9 : s.gpr .r9 = off B dB) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hB : dB + 8 * (w + 1) ≤ Z) (ha : da + 8 * w ≤ Z)
    (sab : da + 8 * w ≤ dB ∨ dB + 8 * (w + 1) ≤ da) :
    WP isa dbl s fun s' =>
      wordsVal s'.mem B dB (w + 1) = 2 * wordsVal s.mem B da w ∧
      Mont.Outside B dB (8 * (w + 1)) s.mem s'.mem ∧ Keep [.r14, .r15, .r16, .r19, .r20, .r22] s s' := by
  have hnw := hs.nowrap
  unfold dbl
  have hpre : WP isa (.block [.addi .r14 .r6 0, .addi .r15 .r9 0, .li .r20 0, .lsr .d .r16 .r11 1]) s
      fun s₁ => (s₁.gpr .r14 = off B da ∧ s₁.gpr .r15 = off B dB ∧ s₁.gpr .r20 = 0 ∧
        s₁.gpr .r16 = BitVec.ofNat 64 w ∧ s₁.mem = s.mem) ∧ Keep [.r14, .r15, .r16, .r20] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h6, h9, h11, BitVec.add_zero, mont_ofNat_shr1 (show w < 2 ^ 63 by omega)]
    rfl
  refine WP.seq (WP.mono hpre fun s₁ ⟨⟨i14, i15, i20, i16, im⟩, k₁⟩ => ?_)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (da + 8 * i) ∧ t.gpr .r15 = off B (dB + 8 * i) ∧ (t.gpr .r20).toNat ≤ 1 ∧
      Mont.Outside B dB (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dB i + 2 ^ (64 * i) * (t.gpr .r20).toNat = 2 * wordsVal s.mem B da i ∧
      Keep [.r14, .r15, .r16, .r19, .r20, .r22] s₁ t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .d .r19 .r14 0, .lsl .r22 .r19 1, .add .r22 .r22 .r20,
      .lsr .d .r20 .r19 63, .store .d .r22 .r15 0, .addi .r14 .r14 8, .addi .r15 .r15 8] ++
      ([.subi .r16 .r16 1] : List Instr))) (cnt := .r16) (N := w) (by omega) (by omega) Inv
    (fun i hi t ⟨j14, j15, j20, jout, jv, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, by rw [i15]; rfl, by rw [i20]; decide, by rw [← im]; exact Mont.Outside.refl _ _ _ _,
      by simp [wordsVal, i20], Keep.refl _ _⟩ i16)
    fun t ⟨_, t15, _, tout, tv, tk⟩ => ?_)
  · have hst : WP isa (.block [.load .d .r19 .r14 0, .lsl .r22 .r19 1, .add .r22 .r22 .r20, .lsr .d .r20 .r19 63,
        .store .d .r22 .r15 0, .addi .r14 .r14 8, .addi .r15 .r15 8, .subi .r16 .r16 1]) t
        fun t' => (t'.gpr .r14 = off B (da + 8 * i + 8) ∧ t'.gpr .r15 = off B (dB + 8 * i + 8) ∧
          t'.gpr .r20 = word t.mem B (da + 8 * i) >>> 63 ∧
          t'.mem = t.mem.writeW (off B (dB + 8 * i)) (word t.mem B (da + 8 * i) <<< 1 + t.gpr .r20) ∧
          t'.gpr .r16 = t.gpr .r16 - BitVec.ofNat 64 1) ∧ Keep [.r14, .r15, .r16, .r19, .r20, .r22] t t' := by
      refine WP.keep _ ?_ (by decide)
      prun [j14, j15, (hs.congr (k₁.trans jk).wr).ld (show da + 8 * i + 8 ≤ Z by omega),
        (hs.congr (k₁.trans jk).wr).st (show dB + 8 * i + 8 ≤ Z by omega)]
    refine WP.mono hst fun t' ⟨⟨u14, u15, u20, um, u16⟩, uk⟩ => ⟨⟨u14.trans (by rw [Nat.mul_succ, Nat.add_assoc]),
      u15.trans (by rw [Nat.mul_succ, Nat.add_assoc]), ?_, ?_, ?_, (jk.trans uk).mono⟩, u16⟩
    · rw [u20]; exact (sqr_dbl_arith (word t.mem B (da + 8 * i)) (t.gpr .r20) j20).2
    · rw [um]
      exact (jout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside t.mem B (d := dB + 8 * i) _ (by omega)).mono (by omega) (by omega))
    · have e := (sqr_dbl_arith (word t.mem B (da + 8 * i)) (t.gpr .r20) j20).1
      have wx : word t.mem B (da + 8 * i) = word s.mem B (da + 8 * i) := jout.word (by omega) (by omega)
      rw [um, fios_wordsVal_write_top _ _ _ _ _ (by omega), u20, Nat.mul_succ, Nat.pow_add,
        wordsVal_succ_top s.mem B da i]
      rw [wx] at e ⊢
      grind
  · have hst : WP isa (.block [.store .d .r20 .r15 0]) t fun t' =>
        t' = { t with mem := t.mem.writeW (off B (dB + 8 * w)) (t.gpr .r20) } := by
      prun [t15, (hs.congr (k₁.trans tk).wr).st (show dB + 8 * w + 8 ≤ Z by omega)]
    refine WP.mono hst fun t' e => ?_
    subst e
    refine ⟨?_, ?_, ((k₁.trans tk).trans (Keep.mem _ _)).mono⟩
    · show wordsVal (t.mem.writeW (off B (dB + 8 * w)) (t.gpr .r20)) B dB (w + 1) = _
      rw [fios_wordsVal_write_top _ _ _ _ _ (by omega), ← tv]
    · exact (tout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside t.mem B (d := dB + 8 * w) _ (by omega)).mono (by omega) (by omega))

/-- A round's step of the invariant: from `P T = L² + 2 L H P + U M` (`P =
2^(64 i)`, `H = x + 2⁶⁴ H'`) and `2⁶⁴ T' = T + P x (x + 2⁶⁴ · 2 H') + u M`, the
same for `i + 1`: `L + P x`, `H'` and `U + P u`. -/
theorem sq_step {P T L H U M x H' u T' : Nat} (hI : P * T = L * L + 2 * L * H * P + U * M)
    (hH : H = x + 2 ^ 64 * H') (hT : 2 ^ 64 * T' = T + P * (x * (x + 2 ^ 64 * (2 * H'))) + u * M) :
    2 ^ 64 * P * T' = (L + P * x) * (L + P * x) + 2 * (L + P * x) * H' * (2 ^ 64 * P) + (U + P * u) * M := by
  have : 2 ^ 64 * P * T' = P * (2 ^ 64 * T') := by grind
  rw [this, hT, Nat.mul_add, Nat.mul_add, hI, hH]
  grind

theorem outs_wordsVal {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') :
    ∀ {d k : Nat}, (∀ r ∈ rs, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) → d + 8 * k ≤ 2 ^ 64 →
      wordsVal m' B d k = wordsVal m B d k
  | _, 0, _, _ => rfl
  | d, k + 1, ap, fit => by
    rw [wordsVal, wordsVal, h.word (fun r hr => by have := ap r hr; omega) (by omega),
      outs_wordsVal h (d := d + 8) (k := k) (fun r hr => by have := ap r hr; omega) (by omega)]

/-- What holds after `i` rounds from `s₀`: `a` (`w` words at `da`) read up to
word `i`, `b`'s words from `i` holding `2 H` and `2^(64 i) T = L² + 2 L H 2^(64 i)
+ U m`, for `L` and `H` the words of `a` below and from `i`. -/
structure RI (s₀ : State) (B : Addr) (da dA dB dM w i : Nat) (s : State) : Prop where
  r6 : s.gpr .r6 = off B (da + 8 * i)
  r4 : s.gpr .r4 = BitVec.ofNat 64 (w - i)
  out : Outs B [(dA, 8 * (w + 1)), (dB, 8 * (w + 1))] s₀.mem s.mem
  buf : wordsVal s.mem B (dB + 8 * i) (w - i + 1) = 2 * wordsVal s₀.mem B (da + 8 * i) (w - i)
  t : ∃ U < 2 ^ (64 * i), 2 ^ (64 * i) * wordsVal s.mem B dA (w + 1) =
    wordsVal s₀.mem B da i * wordsVal s₀.mem B da i +
      2 * wordsVal s₀.mem B da i * wordsVal s₀.mem B (da + 8 * i) (w - i) * 2 ^ (64 * i) +
      U * wordsVal s₀.mem B dM w
  keep : Keep sqRoundRegs s₀ s

/-- The rounds `i` to `w - 1` (`.loop roundI`), counted by `r4`, from `RI` at
`i = 1`: `RI` at `w`. -/
theorem roundsI_ok {s₀ s : State} {B : Addr} {Z da dA dB dM w : Nat} (hs : Scr s B Z)
    (h8 : s₀.gpr .r8 = off B dA) (h9 : s₀.gpr .r9 = off B dB)
    (h10 : s₀.gpr .r10 = off B dM) (h11 : s₀.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hinv : ((word s₀.mem B dM).toNat % 2 ^ 32 * (s₀.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (ha : da + 8 * w ≤ Z) (hA : dA + 8 * (w + 1) ≤ Z) (hB : dB + 8 * (w + 1) ≤ Z) (hM : dM + 8 * w ≤ Z)
    (sAB : dA + 8 * (w + 1) ≤ dB ∨ dB + 8 * (w + 1) ≤ dA)
    (sAM : dM + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dM)
    (sBM : dM + 8 * w ≤ dB ∨ dB + 8 * (w + 1) ≤ dM)
    (saA : da + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ da)
    (saB : da + 8 * w ≤ dB ∨ dB + 8 * (w + 1) ≤ da)
    (h1 : RI s₀ B da dA dB dM w 1 s) :
    WP isa (.loop roundI (.nonzero .d .r4)) s (RI s₀ B da dA dB dM w w) := by
  have hnw := hs.nowrap
  refine (wp_countdown (cnt := .r4) (N := w - 1) (by omega) (by omega) (fun j t => RI s₀ B da dA dB dM w (j + 1) t)
    (fun j hj t I hc => ?_) h1 (by rw [h1.r4])).mono fun t h => by rwa [Nat.sub_add_cancel (by omega)] at h
  have g : ∀ r ∈ [Reg.r8, .r9, .r10, .r11, .r12], t.gpr r = s₀.gpr r := fun r hr =>
    I.keep.gpr r (by revert r hr; decide)
  have ap : ∀ {d k}, d + 8 * k ≤ Z → (d + 8 * k ≤ dA ∨ dA + 8 * (w + 1) ≤ d) →
      (d + 8 * k ≤ dB ∨ dB + 8 * (w + 1) ≤ d) → wordsVal t.mem B d k = wordsVal s₀.mem B d k :=
    fun h1 h2 h3 => outs_wordsVal I.out (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  have wM : Mont.word t.mem B dM = Mont.word s₀.mem B dM := I.out.word (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  have wa : Mont.word t.mem B (da + 8 * (j + 1)) = Mont.word s₀.mem B (da + 8 * (j + 1)) := I.out.word (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  refine WP.mono (roundI_ok (i := j + 1) (hs.congr (I.keep.wr.trans h1.keep.wr.symm)) I.r6
    ((g .r8 (by decide)).trans h8) ((g .r9 (by decide)).trans h9) ((g .r10 (by decide)).trans h10)
    ((g .r11 (by decide)).trans h11) I.r4 (by rw [wM, g .r12 (by decide)]; exact hinv) (by omega) (by omega) hw'
    ha hA hB hM sAB sAM sBM (by rw [I.buf, ap (by omega) (by omega) (by omega)]))
    fun t' ⟨⟨u6, u4, uo, ub, u, hu, ue⟩, uk⟩ => ⟨⟨?_, ?_, I.out.trans uo, ?_, ?_, I.keep.trans uk |>.mono⟩, ?_⟩
  · rw [u6, Nat.add_assoc, ← Nat.mul_succ]
  · rw [u4, show w - (j + 1) - 1 = w - (j + 1 + 1) by omega]
  · rw [show dB + 8 * (j + 1 + 1) = dB + 8 * (j + 1) + 8 by omega, show w - (j + 1 + 1) + 1 = w - (j + 1) by omega,
      ub, ap (by omega) (by omega) (by omega), show da + 8 * (j + 1) + 8 = da + 8 * (j + 1 + 1) by omega,
      show w - (j + 1) - 1 = w - (j + 1 + 1) by omega]
  · obtain ⟨U, hU, hI⟩ := I.t
    rw [wa, ap (d := da + 8 * (j + 1) + 8) (k := w - (j + 1) - 1) (by omega) (by omega) (by omega),
      ap (d := dM) (k := w) (by omega) (by omega) (by omega),
      show da + 8 * (j + 1) + 8 = da + 8 * (j + 1 + 1) by omega, show w - (j + 1) - 1 = w - (j + 1 + 1) by omega] at ue
    have hH := fios_wordsVal_pred s₀.mem B (da + 8 * (j + 1)) (show 1 ≤ w - (j + 1) by omega)
    rw [show da + 8 * (j + 1) + 8 = da + 8 * (j + 1 + 1) by omega,
      show w - (j + 1) - 1 = w - (j + 1 + 1) by omega] at hH
    have e := sq_step hI hH ue
    refine ⟨U + 2 ^ (64 * (j + 1)) * u, ?_, ?_⟩
    · have : 2 ^ (64 * (j + 1)) * u ≤ 2 ^ (64 * (j + 1)) * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
      rw [show 64 * (j + 1 + 1) = 64 * (j + 1) + 64 by omega, Nat.pow_add]
      have : 2 ^ (64 * (j + 1)) * (2 ^ 64 - 1) + 2 ^ (64 * (j + 1)) = 2 ^ (64 * (j + 1)) * 2 ^ 64 := by
        rw [Nat.mul_sub, Nat.mul_one]; have := Nat.one_le_two_pow (n := 64 * (j + 1)); omega
      omega
    · rw [wordsVal_succ_top s₀.mem B da (j + 1), show 64 * (j + 1 + 1) = 64 + 64 * (j + 1) by omega, Nat.pow_add]
      exact e
  · rw [u4, I.r4, ofNat_sub_one (by omega) (by omega), show w - (j + 1) - 1 = w - (j + 1 + 1) by omega]

/-- `T < 2 m` and `T R ≡ a²` from `R T = a² + U m`, for `a < m < R` and `U < R`. -/
theorem sq_final {R T A U M : Nat} (h : R * T = A * A + U * M) (hA : A < M) (hM : M < R) (hU : U < R) :
    T < 2 * M ∧ R * T % M = A * A % M := by
  refine ⟨?_, by rw [h, Nat.add_mul_mod_self_right]⟩
  have h1 : A * A < R * M := Nat.mul_lt_mul_of_lt_of_le (by omega) (Nat.le_of_lt hA) (by omega)
  have h2 : U * M ≤ R * M := Nat.mul_le_mul_right _ (Nat.le_of_lt hU)
  have : R * T < R * (2 * M) := by rw [h]; grind
  exact Nat.lt_of_mul_lt_mul_left this

/-- Everything `mul` does after loading the bases, for `a = b`, by `sqrTail`
(`tailN_ok` with `a = b`; `a` may not be array 3, which `sqrTail` uses for
`2 a`): `[o] < m` and `[o] 2^(64 w) ≡ [a]² (mod m)`, with only arrays 2, 3
and `o` changed. -/
theorem sqrN_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {n o a : Nat} (hn : 4 ≤ n) (ho : o < n) (ha : a < n) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2)
    (ha3 : a ≠ 3) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w n ≤ Z)
    (i5 : s.gpr .r5 = off B (slot w o)) (i6 : s.gpr .r6 = off B (slot w a))
    (i8 : s.gpr .r8 = off B (slot w 2))
    (i9 : s.gpr .r9 = off B (slot w 3)) (i10 : s.gpr .r10 = off B (slot w 0))
    (i11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (_i4 : s.gpr .r4 = BitVec.ofNat 64 (2 * w))
    (_i12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hA : val32 s.mem B (slot w a) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa sqrTail s fun t =>
      (val32 t.mem B (slot w o) (2 * w) < val32 s.mem B (slot w 0) (2 * w) ∧
        val32 t.mem B (slot w o) (2 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          val32 s.mem B (slot w a) (2 * w) * val32 s.mem B (slot w a) (2 * w) %
            val32 s.mem B (slot w 0) (2 * w) ∧
        Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))] s.mem t.mem) ∧
      Keep tailRegs s t := by
  have hnw := hs.nowrap
  have sl : ∀ j < n, slot w j + 8 * (w + 2) ≤ Z := fun j hj => by
    have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ n by omega_using [hj])
    rw [Nat.add_mul, Nat.one_mul] at this
    unfold slot at hZ ⊢; omega_using [this, hZ]
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  have s0 := sl 0 (by omega)
  have s2 := sl 2 (by omega)
  have s3 := sl 3 (by omega)
  have sa := sl a ha
  have so := sl o ho
  have p20 := sp (show (2 : Nat) ≠ 0 by decide)
  have p23 := sp (show (2 : Nat) ≠ 3 by decide)
  have p30 := sp (show (3 : Nat) ≠ 0 by decide)
  have p2a := sp (Ne.symm ha2)
  have p3a := sp (Ne.symm ha3)
  have p2o := sp (Ne.symm ho2)
  have p3o := sp (Ne.symm ho3)
  have wv : ∀ (m : Mem) (j : Nat), wordsVal m B (slot w j) w = val32 m B (slot w j) (2 * w) :=
    fun m j => wordsVal_eq_val32 m B _ w
  unfold sqrTail
  -- The accumulator := 0, and the rounds' count.
  refine WP.seq (WP.mono (zeroAcc_ok (w := w) hs i8 i11 hw' (by omega_arith)) fun s₁ ⟨hz, out₁, j4, k₁⟩ => ?_)
  have g₁ : ∀ r ∈ [Reg.r5, .r6, .r8, .r9, .r10, .r11, .r12], s₁.gpr r = s.gpr r := fun r hr =>
    k₁.gpr r (by revert r hr; decide)
  -- `b := 2 a`.
  refine WP.seq (WP.mono (dbl_ok (da := slot w a) (dB := slot w 3) (hs.congr k₁.wr)
    ((g₁ .r6 (by decide)).trans i6) ((g₁ .r9 (by decide)).trans i9) ((g₁ .r11 (by decide)).trans i11)
    (by omega) hw' (by omega_arith) (by omega_arith) (by omega_arith)) fun s₂ ⟨hd, out₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have g₂ : ∀ r ∈ [Reg.r4, .r5, .r6, .r8, .r9, .r10, .r11, .r12], s₂.gpr r = s₁.gpr r := fun r hr =>
    k₂.gpr r (by revert r hr; decide)
  -- What changed so far: the accumulator and `b`.
  have v₂ : ∀ {j}, j < n → j ≠ 2 → j ≠ 3 → wordsVal s₂.mem B (slot w j) w = wordsVal s.mem B (slot w j) w :=
    fun hj h2 h3 => (out₂.wordsVal (by have := sp h3; omega_arith) (by have := sl _ hj; omega_arith)).trans
      (out₁.wordsVal (by have := sp h2; omega_arith) (by have := sl _ hj; omega_arith))
  have m0₂ : Mont.word s₂.mem B (slot w 0) = Mont.word s.mem B (slot w 0) :=
    (out₂.word (by omega_arith) (by omega_arith)).trans (out₁.word (by omega_arith) (by omega_arith))
  have z₂ : wordsVal s₂.mem B (slot w 2) (w + 1) = 0 := by
    rw [out₂.wordsVal (by omega_arith) (by omega_arith)]; exact hz
  have hinv' : ((Mont.word s₂.mem B (slot w 0)).toNat % 2 ^ 32 * (s₂.gpr .r12).toNat + 1) % 2 ^ 32 = 0 := by
    rw [m0₂, g₂ .r12 (by decide), g₁ .r12 (by decide)]; rw [w32_eq_mod] at hinv; exact hinv
  have hs₂ := hs.congr k12.wr
  -- Round 0.
  refine WP.seq (WP.mono (round0_ok (da := slot w a) (dA := slot w 2) (dB := slot w 3) (dM := slot w 0) hs₂
    ((g₂ .r6 (by decide)).trans ((g₁ .r6 (by decide)).trans i6))
    ((g₂ .r8 (by decide)).trans ((g₁ .r8 (by decide)).trans i8))
    ((g₂ .r9 (by decide)).trans ((g₁ .r9 (by decide)).trans i9))
    ((g₂ .r10 (by decide)).trans ((g₁ .r10 (by decide)).trans i10))
    ((g₂ .r11 (by decide)).trans ((g₁ .r11 (by decide)).trans i11)) ((g₂ .r4 (by decide)).trans j4) hinv'
    hw2 hw' (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by rw [hd, out₂.wordsVal (by omega_arith) (by omega_arith)]))
    fun s₃ ⟨⟨r6, r4, ro, rb, u, hu, re⟩, k₃⟩ => ?_)
  rw [z₂, Nat.zero_add] at re
  -- The rounds `1` to `w - 1`.
  have I1 : RI s₂ B (slot w a) (slot w 2) (slot w 3) (slot w 0) w 1 s₃ := by
    refine ⟨by rw [r6, Nat.mul_one], r4, ro, by rw [Nat.mul_one, Nat.sub_add_cancel (by omega)]; exact rb,
      ⟨u, by rw [Nat.mul_one]; exact hu, ?_⟩, k₃⟩
    rw [Nat.mul_one, re, Nat.mul_one, show wordsVal s₂.mem B (slot w a) 1 = (Mont.word s₂.mem B (slot w a)).toNat by
      simp [wordsVal]]
    grind
  refine WP.seq (WP.mono (roundsI_ok (s₀ := s₂) (hs₂.congr k₃.wr)
    ((g₂ .r8 (by decide)).trans ((g₁ .r8 (by decide)).trans i8))
    ((g₂ .r9 (by decide)).trans ((g₁ .r9 (by decide)).trans i9))
    ((g₂ .r10 (by decide)).trans ((g₁ .r10 (by decide)).trans i10))
    ((g₂ .r11 (by decide)).trans ((g₁ .r11 (by decide)).trans i11)) hinv' hw2 hw'
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) I1) fun s₄ I => ?_)
  obtain ⟨_, _, out₄, _, ⟨U, hU, hT⟩, k₄⟩ := I
  rw [Nat.sub_self] at hT
  rw [show wordsVal s₂.mem B (slot w a + 8 * w) 0 = 0 from rfl, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hT
  rw [v₂ ha ha2 ha3, v₂ (by omega) (by decide) (by decide)] at hT
  have hM := wordsVal_lt s.mem B (slot w 0) w
  have hA' : wordsVal s.mem B (slot w a) w < wordsVal s.mem B (slot w 0) w := by rw [wv, wv]; exact hA
  obtain ⟨tlt, teq⟩ := sq_final hT hA' hM hU
  rw [wordsVal_succ_top] at tlt teq
  have hs₄ := hs₂.congr k₄.wr
  have k14 := k12.trans k₄
  have g₄ : ∀ r ∈ [Reg.r5, .r8, .r9, .r10, .r11], s₄.gpr r = s.gpr r := fun r hr =>
    k14.gpr r (by revert r hr; decide)
  have v₄ : ∀ {j}, j < n → j ≠ 2 → j ≠ 3 → wordsVal s₄.mem B (slot w j) w = wordsVal s.mem B (slot w j) w :=
    fun hj h2 h3 => (outs_wordsVal out₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have := sp h2; simp only; omega_arith
      · have := sp h3; simp only; omega_arith) (by have := sl _ hj; omega_arith)).trans (v₂ hj h2 h3)
  -- `T - m`.
  refine WP.seq (WP.mono (subMod64_ok (w := w) (dA := slot w 2) (dT := slot w 3) (dM := slot w 0) hs₄
    (by rw [g₄ .r8 (by decide), i8]) (by rw [g₄ .r9 (by decide), i9]) (by rw [g₄ .r10 (by decide), i10])
    (by rw [g₄ .r11 (by decide), i11]) (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith))
    fun s₅ ⟨⟨c, hc, hD, h20⟩, out₅, k₅⟩ => ?_)
  rw [v₄ (by omega) (by decide) (by decide)] at hD
  have hs₅ := hs₄.congr k₅.wr
  have g₅ : ∀ r ∈ [Reg.r5, .r8, .r9, .r11], s₅.gpr r = s.gpr r := fun r hr => by
    rw [k₅.gpr r (by revert r hr; decide), g₄ r (by revert r hr; decide)]
  have accA : wordsVal s₅.mem B (slot w 2) w = wordsVal s₄.mem B (slot w 2) w :=
    out₅.wordsVal (by omega_arith) (by omega_arith)
  -- The selection.
  refine WP.mono (selectAcc64_ok (w := w) (dA := slot w 2) (dT := slot w 3) (dO := slot w o)
    (b := decide ((Mont.word s₄.mem B (slot w 2 + 8 * w)).toNat < c)) hs₅
    (by rw [g₅ .r8 (by decide), i8]) (by rw [g₅ .r9 (by decide), i9]) (by rw [g₅ .r5 (by decide), i5])
    (by rw [g₅ .r11 (by decide), i11]) (by rw [h20]; simp only [decide_eq_true_eq]) (by omega_arith) hw'
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨hv, out₆, k₆⟩ => ?_
  rw [accA] at hv
  have hM0 : 0 < wordsVal s.mem B (slot w 0) w := by omega_arith
  have hres : wordsVal t.mem B (slot w o) w =
      (wordsVal s₄.mem B (slot w 2) w + 2 ^ (64 * w) * ((Mont.word s₄.mem B (slot w 2 + 8 * w)).toNat +
        2 ^ 64 * 0)) % wordsVal s.mem B (slot w 0) w := by
    rw [hv, ← VG.Proof.Bignum.csub_result hM (wordsVal_lt _ _ _ _) hc (wordsVal_lt _ _ _ _)
      (by rw [Nat.mul_zero, Nat.add_zero]; exact tlt) hD]
    by_cases h : (Mont.word s₄.mem B (slot w 2 + 8 * w)).toNat < c <;> simp [h]
  rw [Nat.mul_zero, Nat.add_zero] at hres
  rw [← wv, ← wv, ← wv]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hres]; exact Nat.mod_lt _ hM0
  · rw [hres, Nat.mod_mul_mod, Nat.mul_comm, teq]
  · refine Outs.trans (Outs.of_outside (o := slot w 2) (n := 8 * (w + 2))
      (out₁.mono (Nat.le_refl _) (by omega_arith)) (by simp)) ?_
    refine Outs.trans (Outs.of_outside (o := slot w 3) (n := 8 * (w + 2))
      (out₂.mono (Nat.le_refl _) (by omega_arith)) (by simp)) ?_
    refine Outs.trans (Outs.cover out₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Nat.le_refl _, by simp only; omega_arith⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Nat.le_refl _, by simp only; omega_arith⟩)) ?_
    refine Outs.trans (Outs.of_outside (o := slot w 3) (n := 8 * (w + 2))
      (out₅.mono (Nat.le_refl _) (by omega_arith)) (by simp)) ?_
    exact Outs.of_outside (o := slot w o) (n := 8 * (w + 2)) (out₆.mono (Nat.le_refl _) (by omega_arith)) (by simp)
  · exact ((k14.trans k₅).trans k₆).mono

end VG.Proof.Bignum.PPC64LE.Sqr
