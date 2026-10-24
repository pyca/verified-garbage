module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Dsa.DomainShape
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# DSA on PPC64LE: the sizes and the oddness of p and q

* `sigLen_ok`, `bytesBits_ok`: the scan of a number's octets
  (`Proof/Dsa/DomainShape.lean`'s `significant`): its significant octets in
  `r16`, and `r0 = 0` exactly when the first has its top bit set;
* `pairs_ok`: `r0 = 0` exactly when the significant octets of p and q are a
  supported pair;
* `odd_ok`: `r0 = 0` exactly when the number is odd;
* `sizes_ok`, `odds_ok`: `sizes` and `odds` run `rest` exactly when the
  sizes are supported, and p and q are odd.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE
open VG.Proof.Dsa (significant)
open VG.Proof.Bignum (slot)

/-! ## The scan of a number's octets -/

/-- One step of `sigLen`'s scan: whether a nonzero octet was seen, and the
octets counted from the first nonzero one. -/
def scanStep (a : Bool × Nat) (b : Byte) : Bool × Nat :=
  (a.1 || b != 0, if (a.1 || b != 0) = true then a.2 + 1 else a.2)

theorem scan_foldl (bs : List Byte) (a : Bool × Nat) :
    (bs.foldl scanStep a).2 = if a.1 = true then a.2 + bs.length else a.2 + (significant bs).1 := by
  induction bs generalizing a with
  | nil => cases a.1 <;> rfl
  | cons b bs ih =>
    rw [List.foldl_cons, ih]
    rcases a with ⟨_ | _, c⟩
    · by_cases hb : b = 0#8
      · subst hb; simp [scanStep, significant]
      · simp [scanStep, significant, hb]; omega
    · simp [scanStep]; omega

theorem bytesAt_take_succ (m : Mem) (N : Addr) {k i : Nat} (hi : i < k) :
    (Spec.Rsa.bytesAt m N k).take (i + 1) = (Spec.Rsa.bytesAt m N k).take i ++ [m (off N i)] := by
  simp [Spec.Rsa.bytesAt, List.take_add_one, hi]

theorem bytesAt_length (m : Mem) (N : Addr) (k : Nat) : (Spec.Rsa.bytesAt m N k).length = k := by
  simp [Spec.Rsa.bytesAt]

/-- The scan of the first `i` octets. -/
def scanAcc (bs : List Byte) (i : Nat) : Bool × Nat := (bs.take i).foldl scanStep (false, 0)

theorem scanAcc_succ (m : Mem) (N : Addr) {k i : Nat} (hi : i < k) :
    scanAcc (Spec.Rsa.bytesAt m N k) (i + 1) = scanStep (scanAcc (Spec.Rsa.bytesAt m N k) i) (m (off N i)) := by
  rw [scanAcc, bytesAt_take_succ m N hi, List.foldl_append]; rfl

theorem scanAcc_all (m : Mem) (N : Addr) (k : Nat) :
    (scanAcc (Spec.Rsa.bytesAt m N k) k).2 = (significant (Spec.Rsa.bytesAt m N k)).1 := by
  rw [scanAcc, List.take_of_length_le (by rw [bytesAt_length]), scan_foldl]
  simp

theorem scanAcc_le (bs : List Byte) (i : Nat) : (scanAcc bs i).2 ≤ i := by
  rw [scanAcc, scan_foldl]
  have := significant_fits (bs.take i)
  simp only [Bool.false_eq_true, ite_false, Nat.zero_add, List.length_take] at this ⊢
  omega

theorem scanStep_or {c : Bool × Nat} {x : Nat} (b : Byte) (hx : x = 0 ↔ c.1 = false) :
    (x ||| b.toNat = 0 ↔ (scanStep c b).1 = false) ∧
      (scanStep c b).2 = c.2 + if x ||| b.toNat = 0 then 0 else 1 := by
  have hb : b.toNat = 0 ↔ b = 0 := ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => h ▸ rfl⟩
  have e : x ||| b.toNat = 0 ↔ (c.1 || b != 0) = false := by
    rw [Nat.or_eq_zero_iff, hx, hb, Bool.or_eq_false_iff, bne_eq_false_iff_eq]
  refine ⟨e, ?_⟩
  simp only [scanStep]
  by_cases h : x ||| b.toNat = 0
  · rw [e.mp h]; simp [h]
  · have hc : (c.1 || b != 0) = true := by
      cases hc : (c.1 || b != 0)
      · exact absurd (e.mpr hc) h
      · rfl
    rw [hc]; simp [h]

/-- The first significant octet. -/
theorem significant_get (bs : List Byte) (h : (significant bs).1 ≠ 0) :
    bs[bs.length - (significant bs).1]? = some (significant bs).2 := by
  induction bs with
  | nil => exact absurd rfl h
  | cons b bs ih =>
    by_cases hb : b = 0
    · rw [significant, ite_eq_left hb] at h ⊢
      have := significant_fits bs
      rw [List.length_cons, show bs.length + 1 - (significant bs).1 = (bs.length - (significant bs).1) + 1 by
        omega, List.getElem?_cons_succ]
      exact ih h
    · rw [significant, ite_eq_right hb]
      simp

theorem bytesAt_get (m : Mem) (N : Addr) {k j : Nat} (hj : j < k) :
    (Spec.Rsa.bytesAt m N k)[j]? = some (m (off N j)) := by
  simp [Spec.Rsa.bytesAt, hj]

theorem bytesAt_last (m : Mem) (N : Addr) {k : Nat} (hk : 1 ≤ k) :
    Spec.Rsa.bytesAt m N k = Spec.Rsa.bytesAt m N (k - 1) ++ [m (off N (k - 1))] := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp [Spec.Rsa.bytesAt, List.range_succ]

theorem or_ofNat {x y : Nat} (hx : x < 256) (hy : y < 256) :
    BitVec.ofNat 64 x ||| BitVec.ofNat 64 y = BitVec.ofNat 64 (x ||| y) := by
  have : x ||| y < 2 ^ 8 := Nat.or_lt_two_pow (by omega) (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem neg_shr63 {y : Nat} (hy : y < 256) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 y) >>> 63 = BitVec.ofNat 64 (if y = 0 then 0 else 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  split <;> simp only [Nat.reducePow, Nat.zero_mod, Nat.add_zero] <;> omega

/-- The registers `sigLen` and `bytesBits` write. -/
def sigRegs : List Reg := [.r0, .r3, .r14, .r15, .r16, .r17]

/-- `sigLen`: the significant octets of the `k` octets at `N` (`r12`, `k` in
`r6`), into `r16`. -/
theorem sigLen_ok {s : State} {N : Addr} {k : Nat} (h12 : s.gpr .r12 = N) (h6 : s.gpr .r6 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hk' : k ≤ 1024) (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1) :
    WP isa sigLen s fun t =>
      (t.gpr .r16 = BitVec.ofNat 64 (significant (Spec.Rsa.bytesAt s.mem N k)).1 ∧ t.mem = s.mem) ∧
        Keep sigRegs s t := by
  refine WP.keep sigRegs ?_ (by decide)
  unfold sigLen Precompute.countLoop
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .r14 .r12 0, .addi .r17 .r6 0, .li .r15 0, .li .r16 0]) s fun s₁ =>
      s₁.gpr .r14 = off N 0 ∧ s₁.gpr .r17 = BitVec.ofNat 64 k ∧ s₁.gpr .r15 = BitVec.ofNat 64 0 ∧
        s₁.gpr .r16 = BitVec.ofNat 64 0 ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    prun [h12, h6, BitVec.add_zero]
  refine WP.mono hpre fun s₁ ⟨i14, i17, i15, i16, im, ird, iwr⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off N i ∧ (∃ x, x < 256 ∧ t.gpr .r15 = BitVec.ofNat 64 x ∧
      (x = 0 ↔ (scanAcc (Spec.Rsa.bytesAt s.mem N k) i).1 = false)) ∧
      t.gpr .r16 = BitVec.ofNat 64 (scanAcc (Spec.Rsa.bytesAt s.mem N k) i).2 ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine WP.mono (wp_countdown (body := .block ([.lbz .r0 .r14 0, .logic .or .r15 .r15 .r0, .li .r3 0,
      .sub .r3 .r3 .r15, .lsr .d .r3 .r3 63, .add .r16 .r16 .r3, .addi .r14 .r14 1] ++
      ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := k) (by omega) (by omega) Inv
    (fun i hi t ⟨t14, ⟨x, hx, t15, hx0⟩, t16, tm, trd, twr⟩ _ => ?_)
    ⟨i14, ⟨0, by decide, i15, by simp [scanAcc]⟩, by rw [i16]; rfl, im, ird, iwr⟩ i17)
    fun t ⟨_, _, t16, tm, _⟩ => ⟨by rw [t16, scanAcc_all], tm⟩
  have hb := (s.mem (off N i)).isLt
  have hy : x ||| (s.mem (off N i)).toNat < 256 := Nat.or_lt_two_pow (n := 8) hx hb
  have hs := scanStep_or (s.mem (off N i)) hx0
  prun [t14, t15, t16, tm, exec_lbz' (show Reg.r14 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
    (by rw [trd, twr]; exact hrd i hi : InRegions (t.rd ++ t.wr) (off N i) 1), read_byte64,
    or_ofNat hx hb, neg_shr63 hy, ← BitVec.ofNat_add]
  rw [← scanAcc_succ s.mem N hi] at hs
  exact ⟨by gsimp, ⟨_, hy, by gsimp, hs.1⟩, by gsimp; rw [hs.2], by gsimp; exact tm, by gsimp; exact trd,
    by gsimp; exact twr⟩

/-- `bytesBits`: the significant octets into `r16`, and `r0 = 0` exactly
when the first has its top bit set. -/
theorem bytesBits_ok {s : State} {N : Addr} {k : Nat} (h12 : s.gpr .r12 = N)
    (h6 : s.gpr .r6 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k ≤ 1024)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1) :
    WP isa bytesBits s fun t =>
      (t.gpr .r16 = BitVec.ofNat 64 (significant (Spec.Rsa.bytesAt s.mem N k)).1 ∧
        (t.gpr .r0 = 0 ↔ 128 ≤ (significant (Spec.Rsa.bytesAt s.mem N k)).2.toNat) ∧ t.mem = s.mem) ∧
        Keep sigRegs s t := by
  refine WP.keep sigRegs ?_ (by decide)
  unfold bytesBits
  refine WP.seq (WP.mono (sigLen_ok h12 h6 hk hk' hrd) fun t ⟨⟨t16, tm⟩, kt⟩ => ?_)
  have hc := significant_fits (Spec.Rsa.bytesAt s.mem N k)
  rw [bytesAt_length] at hc
  refine WP.ite _ (eval_zero_ofNat _ _ (by omega) t16) (fun hz => ?_) (fun hz => ?_)
  · have hz : (significant (Spec.Rsa.bytesAt s.mem N k)).1 = 0 := by simpa using hz
    have h2 := (significant_nonzero _).mp hz
    prun [t16, tm]
    rw [h2]
    decide
  · have hz : (significant (Spec.Rsa.bytesAt s.mem N k)).1 ≠ 0 := by simpa using hz
    have hg := significant_get _ hz
    rw [bytesAt_length, bytesAt_get _ _ (by omega), Option.some.injEq] at hg
    have hr : InRegions (t.rd ++ t.wr) (off N (k - (significant (Spec.Rsa.bytesAt s.mem N k)).1)) 1 := by
      rw [kt.rd, kt.wr]; exact hrd _ (by omega)
    unfold topBit
    prun [kt.gpr .r12 (by decide), kt.gpr .r6 (by decide), h12, h6, t16,
      Offset.add_ofNat_sub N (show (significant (Spec.Rsa.bytesAt s.mem N k)).1 ≤ k by omega),
      exec_lbz' (show Reg.r14 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hr, read_byte64, tm, hg]
    exact top_xor (significant (Spec.Rsa.bytesAt s.mem N k)).2.isLt

theorem ofNat_sub_eq_zero {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 y = 0 ↔ x = y := by
  have := Offset.ofNat_sub_ofNat_beq hx hy
  rwa [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff] at this

/-- `pairOk P Q`: `r0 := 0` if `(a, b) = (P, Q)`. -/
theorem pairOk_ok {s : State} {a b P Q : Nat} {R : Prop} (h27 : s.gpr .r27 = BitVec.ofNat 64 a)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 b) (ha : a ≤ 1024) (hb : b ≤ 1024) (hP : P ≤ 2 ^ 15)
    (hQ : Q ≤ 2 ^ 15) (h0 : s.gpr .r0 = 0 ↔ R) :
    WP isa (pairOk P Q) s fun t =>
      ((t.gpr .r0 = 0 ↔ R ∨ (a = P ∧ b = Q)) ∧ t.gpr .r27 = BitVec.ofNat 64 a ∧
        t.gpr .r28 = BitVec.ofNat 64 b ∧ t.mem = s.mem) ∧ Keep [.r0, .r3, .r4] s t := by
  refine WP.keep _ ?_ rfl
  unfold pairOk
  refine WP.seq (WP.mono (WP.keep [.r3, .r4] (Q := fun t => t.gpr .r3 =
      (BitVec.ofNat 64 a - BitVec.ofNat 64 P ||| BitVec.ofNat 64 b - BitVec.ofNat 64 Q) ∧ t.mem = s.mem)
    (by prun [h27, h28, hP, hQ]) rfl) fun t ⟨⟨t3, tm⟩, kt⟩ => ?_)
  have e : (t.gpr .r3 == 0) = decide (a = P ∧ b = Q) := by
    rw [t3, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff,
      show ∀ x y : BitVec 64, (x ||| y = 0 ↔ x = 0 ∧ y = 0) from fun _ _ => BitVec.or_eq_zero_iff,
      ofNat_sub_eq_zero (by omega) (by omega), ofNat_sub_eq_zero (by omega) (by omega)]
  have t27 : t.gpr .r27 = BitVec.ofNat 64 a := (kt.gpr _ (by decide)).trans h27
  have t28 : t.gpr .r28 = BitVec.ofNat 64 b := (kt.gpr _ (by decide)).trans h28
  refine WP.ite _ (by rw [eval_zero, e]) (fun hz => ?_) (fun hz => ?_)
  · have hz := of_decide_eq_true hz
    prun [t27, t28, tm]
    exact ⟨fun _ => .inr hz, fun _ => rfl⟩
  · have hz := of_decide_eq_false hz
    refine wp_nil ⟨?_, t27, t28, tm⟩
    rw [kt.gpr _ (by decide), h0]
    exact ⟨.inl, fun h => h.resolve_right hz⟩

/-- `pairs`: `r0 = 0` exactly when `(8 a, 8 b)` are supported sizes. -/
theorem pairs_ok {s : State} {a b : Nat} (h27 : s.gpr .r27 = BitVec.ofNat 64 a)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 b) (ha : a ≤ 1024) (hb : b ≤ 1024) :
    WP isa pairs s fun t =>
      ((t.gpr .r0 = 0 ↔ Spec.Dsa.supportedSizes (8 * a) (8 * b)) ∧ t.mem = s.mem) ∧
        Keep [.r0, .r3, .r4] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold pairs
  refine WP.seq (WP.mono (WP.keep [.r0] (Q := fun t => t.gpr .r0 = 1#64 ∧ t.mem = s.mem) (by prun)
    (by decide)) fun t₀ ⟨⟨a0, m0⟩, k0⟩ => ?_)
  have h0 : t₀.gpr .r0 = 0 ↔ False := ⟨fun h => absurd (a0.symm.trans h) (by decide), False.elim⟩
  refine WP.seq (WP.mono (pairOk_ok (P := 128) (Q := 20) ((k0.gpr _ (by decide)).trans h27)
    ((k0.gpr _ (by decide)).trans h28) ha hb (by decide) (by decide) h0)
    fun t₁ ⟨⟨a1, b1, c1, m1⟩, _⟩ => ?_)
  refine WP.seq (WP.mono (pairOk_ok (P := 256) (Q := 20) b1 c1 ha hb (by decide) (by decide) a1)
    fun t₂ ⟨⟨a2, b2, c2, m2⟩, _⟩ => ?_)
  refine WP.seq (WP.mono (pairOk_ok (P := 256) (Q := 28) b2 c2 ha hb (by decide) (by decide) a2)
    fun t₃ ⟨⟨a3, b3, c3, m3⟩, _⟩ => ?_)
  refine WP.seq (WP.mono (pairOk_ok (P := 256) (Q := 32) b3 c3 ha hb (by decide) (by decide) a3)
    fun t₄ ⟨⟨a4, b4, c4, m4⟩, _⟩ => ?_)
  refine WP.mono (pairOk_ok (P := 384) (Q := 32) b4 c4 ha hb (by decide) (by decide) a4)
    fun t ⟨⟨a5, _, _, m5⟩, _⟩ => ⟨?_, by rw [m5, m4, m3, m2, m1, m0]⟩
  rw [a5, false_or]
  constructor
  · rintro ((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) <;> decide
  · unfold Spec.Dsa.supportedSizes
    rintro (⟨h1, h2⟩ | ⟨h1, h2 | h2 | h2⟩ | ⟨h1, h2⟩)
    · exact .inl (.inl (.inl (.inl ⟨by omega, by omega⟩)))
    · exact .inl (.inl (.inl (.inr ⟨by omega, by omega⟩)))
    · exact .inl (.inl (.inr ⟨by omega, by omega⟩))
    · exact .inl (.inr ⟨by omega, by omega⟩)
    · exact .inr ⟨by omega, by omega⟩

/-- `odd`: `r0 = 0` exactly when the number of the `k` octets at `N` is odd. -/
theorem odd_ok {s : State} {N : Addr} {k : Nat} (h12 : s.gpr .r12 = N) (h6 : s.gpr .r6 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hk' : k ≤ 1024) (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1) :
    WP isa (.block odd) s fun t =>
      ((t.gpr .r0 = 0 ↔ Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem N k) % 2 = 1) ∧ t.mem = s.mem) ∧
        Keep [.r0, .r3, .r14] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold odd
  have hr : InRegions (s.rd ++ s.wr) (off N (k - 1)) 1 := hrd _ (by omega)
  prun [h12, h6, Offset.add_ofNat_sub N hk, exec_lbz' (show Reg.r14 ≠ .r0 by decide)
    (show 0 < 2 ^ 15 by decide), hr, read_byte64]
  rw [odd_xor, bytesAt_last s.mem N hk, Proof.Dsa.decodeBE_last_mod_two]

/-- The registers `sizes` and `odds` write before `rest` or `fail`. -/
def sizesRegs : List Reg := [.r0, .r3, .r4, .r6, .r12, .r14, .r15, .r16, .r17, .r27, .r28]

/-- The sizes are supported. -/
abbrev SizesOk (m : Mem) (L : Lay) (key : Addr) : Prop :=
  Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (pOf m L key)) (Spec.Dsa.bitLength (qOf m L key))

/-- `sizes rest fail`: `rest` with q's significant octets (`bitLength q / 8`)
in the header's word `hQb`, if the sizes are supported; else `fail`, with at
most that word changed. -/
theorem sizes_ok {s : State} {L : Lay} {key sig dig : Addr} {Q : State → Prop} {rest fail : Prog isa}
    (hL : L.Ok) (hs : ScrL s L) (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S)
    (hk : Src s L key (3 * L.pl + L.ql))
    (hrest : ∀ t, SizesOk s.mem L key →
      t.mem = s.mem.writeW (off L.S hQb) (BitVec.ofNat 64 (Spec.Dsa.bitLength (qOf s.mem L key) / 8)) →
      Keep sizesRegs s t → WP isa rest t Q)
    (hfail : ∀ t, ¬ SizesOk s.mem L key → Outside L.S hQb 8 s.mem t.mem → Keep sizesRegs s t →
      WP isa fail t Q) :
    WP isa (sizes rest fail) s Q := by
  have hpl : 128 ≤ L.pl ∧ L.pl ≤ 384 := by rcases hL.pl with e | e | e <;> omega
  have hql := hL.ql
  have hZ : 128 * L.pl ≤ L.Z := hL.room
  have hnw := hL.nowrap
  have fp := significant_fits (Spec.Rsa.bytesAt s.mem key L.pl)
  have fq := significant_fits (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)
  rw [bytesAt_length] at fp fq
  have hSz : SizesOk s.mem L key ↔
      128 ≤ (significant (Spec.Rsa.bytesAt s.mem key L.pl)).2.toNat ∧
        128 ≤ (significant (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)).2.toNat ∧
        Spec.Dsa.supportedSizes (8 * (significant (Spec.Rsa.bytesAt s.mem key L.pl)).1)
          (8 * (significant (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)).1) :=
    Proof.Dsa.supported_scans _ _
  unfold sizes andThen
  -- p's octets
  refine WP.seq (WP.seq (WP.mono (ptrP_ok hL hs hh h21) fun t₁ ⟨⟨a12, a6, am⟩, k1⟩ =>
    WP.mono (bytesBits_ok a12 a6 (by omega) (by omega) fun i hi => by
      rw [k1.rd, k1.wr]; exact hk.rd i (by omega)) fun t₂ ⟨⟨b16, b0, bm⟩, k2⟩ => ?_))
  rw [am] at b16 b0
  have m2 : t₂.mem = s.mem := by rw [bm, am]
  refine WP.ite _ (eval_zero _ _) (fun hz => ?ok) (fun hz => ?bad)
  case bad =>
    refine hfail t₂ (fun h => ?_) (by rw [m2]; exact Outside.refl _ _ _ _) (k1.trans k2).mono
    rw [b0.mpr (hSz.mp h).1] at hz
    exact absurd hz (by decide)
  have hp := b0.mp (beq_iff_eq.mp hz)
  refine WP.seq (WP.mono (WP.keep [.r27] (Q := fun t =>
    t.gpr .r27 = BitVec.ofNat 64 (significant (Spec.Rsa.bytesAt s.mem key L.pl)).1 ∧ t.mem = t₂.mem)
    (by prun [b16, BitVec.add_zero]) (by decide)) fun t₃ ⟨⟨c27, cm⟩, k3⟩ => ?_)
  have kA := (k1.trans k2).trans k3
  have hs₃ : ScrL t₃ L := hs.congr kA.wr
  have hh₃ : Hdr t₃.mem L key sig dig := by rw [cm, m2]; exact hh
  have h21₃ : t₃.gpr .r21 = L.S := (kA.gpr _ (by decide)).trans h21
  -- q's octets
  refine WP.seq (WP.seq (WP.mono (ptrQ_ok hL hs₃ hh₃ h21₃) fun t₄ ⟨⟨d12, d6, dm⟩, k4⟩ =>
    WP.mono (bytesBits_ok d12 d6 (by omega) (by omega) fun i hi => by
      rw [k4.rd, k4.wr, kA.rd, kA.wr]; exact (hk.sub (o := L.pl) (k := L.ql) (by omega)).rd i hi)
      fun t₅ ⟨⟨e16, e0, em⟩, k5⟩ => ?_))
  rw [dm, cm, m2] at e16 e0
  have m5 : t₅.mem = s.mem := by rw [em, dm, cm, m2]
  have kB := (kA.trans k4).trans k5
  refine WP.ite _ (eval_zero _ _) (fun hz' => ?ok2) (fun hz' => ?bad2)
  case bad2 =>
    refine hfail t₅ (fun h => ?_) (by rw [m5]; exact Outside.refl _ _ _ _) kB.mono
    rw [e0.mpr (hSz.mp h).2.1] at hz'
    exact absurd hz' (by decide)
  have hq := e0.mp (beq_iff_eq.mp hz')
  have hst : InRegions t₅.wr (off L.S 72) 8 := (hs.congr kB.wr).st (by omega)
  have h21₅ : t₅.gpr .r21 = L.S := (kB.gpr _ (by decide)).trans h21
  refine WP.seq (WP.mono (WP.keep [.r28] (Q := fun t =>
    t.gpr .r28 = BitVec.ofNat 64 (significant (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)).1 ∧
      t.mem = s.mem.writeW (off L.S hQb)
        (BitVec.ofNat 64 (significant (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)).1))
    (by prun [e16, h21₅, hst, hQb, m5, BitVec.add_zero]) (by decide)) fun t₆ ⟨⟨f28, fm⟩, k6⟩ => ?_)
  -- the pair
  have g27 : t₆.gpr .r27 = BitVec.ofNat 64 (significant (Spec.Rsa.bytesAt s.mem key L.pl)).1 :=
    (((k4.trans k5).trans k6).gpr _ (by decide)).trans c27
  refine WP.seq (WP.mono (pairs_ok g27 f28 (by omega) (by omega)) fun t₇ ⟨⟨g0, gm⟩, k7⟩ => ?_)
  have kC := (kB.trans k6).trans k7
  have m7 := gm.trans fm
  refine WP.ite _ (eval_zero _ _) (fun hz'' => ?_) (fun hz'' => ?_)
  · have hok : SizesOk s.mem L key := hSz.mpr ⟨hp, hq, g0.mp (beq_iff_eq.mp hz'')⟩
    have hb : Spec.Dsa.bitLength (qOf s.mem L key) / 8 =
        (significant (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)).1 := by
      rw [show qOf s.mem L key = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql) from rfl,
        Proof.Dsa.subgroup_scan_width (p := Spec.Rsa.bytesAt s.mem key L.pl) hok]
      omega
    exact hrest t₇ hok (by rw [m7, hb]) kC.mono
  · refine hfail t₇ (fun h => ?_) (by rw [m7]; exact writeW_outside s.mem L.S _ (by decide)) kC.mono
    rw [g0.mpr (hSz.mp h).2.2] at hz''
    exact absurd hz'' (by decide)

/-- `odds rest fail`: `rest` if p and q are odd, else `fail`. -/
theorem odds_ok {s : State} {L : Lay} {key sig dig : Addr} {Q : State → Prop} {rest fail : Prog isa}
    (hL : L.Ok) (hs : ScrL s L) (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S)
    (hk : Src s L key (3 * L.pl + L.ql))
    (hrest : ∀ t, pOf s.mem L key % 2 = 1 → qOf s.mem L key % 2 = 1 → t.mem = s.mem → Keep sizesRegs s t →
      WP isa rest t Q)
    (hfail : ∀ t, ¬ (pOf s.mem L key % 2 = 1 ∧ qOf s.mem L key % 2 = 1) → t.mem = s.mem →
      Keep sizesRegs s t → WP isa fail t Q) :
    WP isa (odds rest fail) s Q := by
  have hpl : 128 ≤ L.pl ∧ L.pl ≤ 384 := by rcases hL.pl with e | e | e <;> omega
  have hql := hL.ql
  unfold odds andThen
  refine WP.seq (WP.block_append (WP.mono (ptrP_ok hL hs hh h21) fun t₁ ⟨⟨a12, a6, am⟩, k1⟩ =>
    WP.mono (odd_ok a12 a6 (by omega) (by omega) fun i hi => by
      rw [k1.rd, k1.wr]; exact hk.rd i (by omega)) fun t₂ ⟨⟨b0, bm⟩, k2⟩ => ?_))
  rw [am] at b0
  have kA := k1.trans k2
  have hs₂ : ScrL t₂ L := hs.congr kA.wr
  have hh₂ : Hdr t₂.mem L key sig dig := by rw [bm, am]; exact hh
  have h21₂ : t₂.gpr .r21 = L.S := (kA.gpr _ (by decide)).trans h21
  refine WP.ite _ (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  · have hp : pOf s.mem L key % 2 = 1 := b0.mp (beq_iff_eq.mp hz)
    refine WP.seq (WP.block_append (WP.mono (ptrQ_ok hL hs₂ hh₂ h21₂) fun t₃ ⟨⟨c12, c6, cm⟩, k3⟩ =>
      WP.mono (odd_ok c12 c6 (by omega) (by omega) fun i hi => by
        rw [k3.rd, k3.wr, kA.rd, kA.wr]; exact (hk.sub (o := L.pl) (k := L.ql) (by omega)).rd i hi)
        fun t₄ ⟨⟨d0, dm⟩, k4⟩ => ?_))
    rw [cm, bm, am] at d0
    have kB := (kA.trans k3).trans k4
    have m4 : t₄.mem = s.mem := by rw [dm, cm, bm, am]
    refine WP.ite _ (eval_zero _ _) (fun hz' => ?_) (fun hz' => ?_)
    · exact hrest t₄ hp (d0.mp (beq_iff_eq.mp hz')) m4 kB.mono
    · refine hfail t₄ (fun h => ?_) m4 kB.mono
      rw [d0.mpr h.2] at hz'
      exact absurd hz' (by decide)
  · refine hfail t₂ (fun h => ?_) (by rw [bm, am]) kA.mono
    rw [b0.mpr h.1] at hz
    exact absurd hz (by decide)

end VG.Proof.Dsa.PPC64LE
