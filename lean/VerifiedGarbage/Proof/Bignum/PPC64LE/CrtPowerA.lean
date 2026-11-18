module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtReduce
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2Prime
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
public import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Bignum.PPC64LE.CrtR2`, which this module and modules that import it used -/

section

/-!
# The RSA private-key operation on PPC64LE: the cached `R² mod p`

`r2Copy_ok`: `vg_rsa_private_crt_precomputed`'s `R² mod p` into array 1 of
a prime's working space, from `w` words of a read-only buffer apart from it,
under the mask `r26` of `b`: the buffer's number if `b`, else 1.
`r2Step_ok`: `R² mod p` into array 1 as `Pre.r2Prime_ok` gives it, either
computed or, with `pc`, copied from the cached values (`R2C`): with the
mask clear, the prime is 3, and `R² mod 3 = 1`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE
open VG.Proof.Mont (val32 w32)

/-- `n` words, the lowest 1 and the others 0, are 1. -/
theorem wv_one_low {m : Mem} {p : Addr} {d : Nat} :
    ∀ {n : Nat}, 1 ≤ n → word m p d = 1#64 → (∀ i < n, 1 ≤ i → word m p (d + 8 * i) = 0#64) → wv m p d n = 1
  | 1, _, h0, _ => by simp [wv, h0]
  | n + 2, _, h0, h => by
    rw [wv, wv_one_low (n := n + 1) (by omega_arith) h0 fun i hi hi1 => h i (by omega_arith) hi1,
      h (n + 1) (by omega_arith) (by omega_arith)]
    simp

/-- The word `r2Copy` writes at index `k`, from the buffer's word `x`, under
the mask `m`. -/
abbrev r2Word (m x : BitVec 64) (k : Nat) : BitVec 64 :=
  (x &&& m) ||| (if k = 0 then (BitVec.ofNat 64 0 - BitVec.ofNat 64 1 ^^^ m) &&& 1#64 else 0#64)

/-- What `r2Copy`'s words are, as a number. -/
theorem r2_words {mt ms : Mem} {B P : Addr} {w : Nat} {b : Bool} {m : BitVec 64} (hw : 1 ≤ w)
    (h26 : m = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))
    (tc : ∀ k < w, word mt B (slot w 1 + 8 * k) = r2Word m (word ms P (8 * k)) k) :
    wv mt B (slot w 1) w = (if b then wv ms P 0 w else 1) := by
  subst h26
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at tc ⊢
    have c1 : (BitVec.ofNat 64 0 - BitVec.ofNat 64 1 ^^^ BitVec.ofNat 64 0) &&& 1#64 = 1#64 := by decide
    have t0 := tc 0 (by omega_arith)
    rw [Nat.mul_zero, Nat.add_zero] at t0
    refine wv_one_low (m := mt) (p := B) (d := slot w 1) hw (by
      rw [t0]; simp only [r2Word, BitVec.sub_self, BitVec.and_zero, BitVec.zero_or, ↓reduceIte, c1]) fun i hi hi1 => ?_
    rw [tc i hi]
    simp only [r2Word, BitVec.sub_self, BitVec.and_zero, BitVec.zero_or, show i ≠ 0 by omega_arith, ↓reduceIte]
  · simp only [↓reduceIte] at tc ⊢
    refine wv_congr2 fun i hi => ?_
    rw [Nat.zero_add, tc i hi]
    have h1 : BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 := by decide
    simp only [r2Word, h1, BitVec.and_allOnes, BitVec.xor_self, BitVec.zero_and, ite_self, BitVec.or_zero]

/-- `r2Copy`, in a working space at `B` of `w` words (array 0 in `r10`, an
array's size in `r29`, `2 w` in `r11`), from the `w` words at `P` (`r15`),
readable and apart from it, under the mask of `b` (`r26`): array 1 holds
the buffer's number if `b`, else 1. -/
theorem r2Copy_ok {s : State} {B P : Addr} {Z w : Nat} {b : Bool} (hs : Scr s B Z)
    (hP : P.toNat + 8 * w ≤ 2 ^ 64) (hrd : ∀ i < w, InRegions (s.rd ++ s.wr) (off P (8 * i)) 8)
    (hsep : ∀ x, ofs P x < 8 * w → Z ≤ ofs B x)
    (h30 : s.gpr .r30 = off P 0) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h26 : s.gpr .r26 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 2 ≤ Z) :
    WP isa r2Copy s fun t =>
      (wv t.mem B (slot w 1) w = (if b then wv s.mem P 0 w else 1) ∧
        Outside B (slot w 1) (8 * w) s.mem t.mem) ∧ Keep [.r0, .r3, .r4, .r14, .r30, .r17] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e1 := e 1; have e2 := e 2
  have hh : hdrBytes = 256 := rfl
  unfold r2Copy
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 1) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  have hpre : WP isa (.block [.li .r3 0, .subi .r3 .r3 1, .logic .xor .r3 .r3 .r26, .li .r4 1,
      .logic .and .r3 .r3 .r4, .lsr .d .r17 .r11 1]) s₁ fun s₂ =>
      (s₂.gpr .r17 = BitVec.ofNat 64 w ∧
        s₂.gpr .r3 = (BitVec.ofNat 64 0 - BitVec.ofNat 64 1 ^^^ s.gpr .r26) &&& 1#64 ∧ s₂.mem = s₁.mem) ∧
        Keep [.r3, .r4, .r17] s₁ s₂ := by
    refine WP.keep _ ?_ (by decide)
    prun [(k1.gpr .r26 (by decide)), (k1.gpr .r11 (by decide)).trans h11]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_arith
  refine WP.mono hpre fun s₂ ⟨⟨i17, i3, im⟩, k₂⟩ => ?_
  have k12 := k1.trans k₂
  have g26 : ∀ {t : State}, Keep [.r0, .r3, .r4, .r14, .r30, .r17] s t → t.gpr .r26 = s.gpr .r26 :=
    fun k => k.gpr _ (by decide)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (slot w 1 + 8 * i) ∧ t.gpr .r30 = off P (8 * i) ∧
      t.gpr .r3 = (if i = 0 then (BitVec.ofNat 64 0 - BitVec.ofNat 64 1 ^^^ s.gpr .r26) &&& 1#64 else 0#64) ∧
      Outside B (slot w 1) (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem B (slot w 1 + 8 * k) = r2Word (s.gpr .r26) (word s.mem P (8 * k)) k) ∧
      Keep [.r0, .r3, .r4, .r14, .r30, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .r0 .r30 0, .logic .and .r0 .r0 .r26,
      .logic .or .r0 .r0 .r3, .store .d .r0 .r14 0, .li .r3 0, .addi .r14 .r14 8, .addi .r30 .r30 8] ++
      ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := w) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j14, j30, j3, jout, jc, jk⟩ hc => ?_)
    ⟨by rw [k₂.gpr .r14 (by decide), a14]; rfl, by rw [k12.gpr .r30 (by decide), h30],
      by rw [i3]; rfl, by rw [im, m1]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k12.mono⟩ i17) fun t ⟨_, _, _, tout, tc, tk⟩ => ⟨⟨r2_words hw h26 tc, tout⟩, tk⟩
  have hsrc : word t.mem P (8 * i) = word s.mem P (8 * i) :=
    Pub.Outside.word_apart jout hsep (by omega_arith) (by omega_arith) hP
  have hst : WP isa (.block [.load .d .r0 .r30 0, .logic .and .r0 .r0 .r26, .logic .or .r0 .r0 .r3,
      .store .d .r0 .r14 0, .li .r3 0, .addi .r14 .r14 8, .addi .r30 .r30 8, .subi .r17 .r17 1]) t
      fun t' => t' = (((({ (((t.write .r0 (word t.mem P (8 * i))).write .r0 (word t.mem P (8 * i) &&& t.gpr .r26)).write
          .r0 ((word t.mem P (8 * i) &&& t.gpr .r26) ||| t.gpr .r3)) with
        mem := t.mem.writeW (off B (slot w 1 + 8 * i)) ((word t.mem P (8 * i) &&& t.gpr .r26) ||| t.gpr .r3) } :
        State).write .r3 (BitVec.ofNat 64 0)).write .r14 (off B (slot w 1 + 8 * i + 8))).write .r30
          (off P (8 * i + 8))).write .r17 (t.gpr .r17 - BitVec.ofNat 64 1) := by
    prun [j14, j30, (by rw [jk.rd, jk.wr]; exact hrd i hi : InRegions (t.rd ++ t.wr) (off P (8 * i)) 8),
      (hs.congr jk.wr).st (show slot w 1 + 8 * i + 8 ≤ Z by omega_arith)]
  refine WP.mono hst fun t' ee => ?_
  subst ee
  have hw := writeW_outside t.mem B (d := slot w 1 + 8 * i) ((word t.mem P (8 * i) &&& t.gpr .r26) ||| t.gpr .r3)
    (by omega_arith)
  refine ⟨⟨by gsimp; rw [show slot w 1 + 8 * i + 8 = slot w 1 + 8 * (i + 1) by omega_arith],
    by gsimp; rw [show 8 * i + 8 = 8 * (i + 1) by omega_arith], by gsimp, ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega_arith) (by omega_arith)]; exact jc k hk
    · rw [word_writeW_self, hsrc, j3, g26 jk]
  · exact jk.trans' ((((((((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans
      (Keep.mem _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans
      (Keep.write _ _ _)).mono

/-- `R² mod 3 = 1`. -/
theorem pow128_mod3 (w : Nat) : 2 ^ (128 * w) % 3 = 1 := by
  rw [Nat.pow_mul, Nat.pow_mod, show 2 ^ 128 % 3 = 1 by decide, Nat.one_pow]

/-- With `pc`, where `r2Step pc` copies from, in a state whose header is
at `BX` (of `Zs` bytes of working space): the cached `R² mod p`, `w` words
at `S`, readable and apart from the working space, at the header's `oR2`
(with `q`, after `p`'s `wsWords pL` words, `pL` at `oPLen`); and the mask of
`b` in `r26`. -/
structure R2S (q : Bool) (s : State) (BX S : Addr) (Zs w pL : Nat) (b : Bool) : Prop where
  src : S = word s.mem BX oR2 + BitVec.ofNat 64 (if q then 8 * wsWords pL else 0)
  pl : q = true → word s.mem BX oPLen = BitVec.ofNat 64 pL
  pl1 : 1 ≤ pL
  pl2 : pL < 2 ^ 60
  hS : S.toNat + 8 * w ≤ 2 ^ 64
  rd : ∀ i < w, InRegions (s.rd ++ s.wr) (off S (8 * i)) 8
  sep : ∀ x, ofs S x < 8 * w → Zs ≤ ofs BX x
  r26 : s.gpr .r26 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)

/-- `R2S`, with the prime `Pv` whose `R² mod p` the buffer holds if `b`,
else 3. -/
structure R2C (q : Bool) (s : State) (BX S : Addr) (Zs w Pv pL : Nat) (b : Bool) : Prop
    extends R2S q s BX S Zs w pL b where
  val : b = true → wv s.mem S 0 w = 2 ^ (128 * w) % Pv
  three : b = false → Pv = 3

/-- `R2C` after steps that write only the working space past its header,
keeping `r26` and the regions. -/
theorem R2C.mono {q : Bool} {s t : State} {BX S : Addr} {Zs w Pv pL oA n : Nat} {b : Bool}
    (C : R2C q s BX S Zs w Pv pL b) (ho : Outside BX oA n s.mem t.mem) (h1 : 96 ≤ oA) (h2 : oA + n ≤ Zs)
    (hrw : t.rd ++ t.wr = s.rd ++ s.wr) (h26 : t.gpr .r26 = s.gpr .r26) : R2C q t BX S Zs w Pv pL b where
  src := by rw [ho.word (Or.inl (by unfold oR2; omega_arith)) (by unfold oR2; omega_arith)]; exact C.src
  pl hq := by rw [ho.word (Or.inl (by unfold oPLen; omega_arith)) (by unfold oPLen; omega_arith)]; exact C.pl hq
  pl1 := C.pl1
  pl2 := C.pl2
  hS := C.hS
  rd i hi := by rw [hrw]; exact C.rd i hi
  sep := C.sep
  r26 := h26.trans C.r26
  val hb := by
    rw [← C.val hb]
    exact wv_congr2 fun i hi => Pub.Outside.word_apart ho C.sep h2 (by omega_arith) C.hS
  three := C.three

/-- `R2C` after steps that write only registers but `r26`. -/
theorem R2C.of_mem {q : Bool} {s t : State} {BX S : Addr} {Zs w Pv pL : Nat} {b : Bool}
    (C : R2C q s BX S Zs w Pv pL b) (hm : t.mem = s.mem) (hrw : t.rd ++ t.wr = s.rd ++ s.wr)
    (h26 : t.gpr .r26 = s.gpr .r26) : R2C q t BX S Zs w Pv pL b where
  src := by rw [hm]; exact C.src
  pl hq := by rw [hm]; exact C.pl hq
  pl1 := C.pl1
  pl2 := C.pl2
  hS := C.hS
  rd i hi := by rw [hrw]; exact C.rd i hi
  sep := C.sep
  r26 := h26.trans C.r26
  val hb := by rw [hm]; exact C.val hb
  three := C.three

/-- The source's address, from the header. -/
theorem r2Src_ok {q : Bool} {s : State} {BX : Addr} {Zs pL : Nat} (hX : Scr s BX Zs) (hZ : 256 ≤ Zs)
    (h23 : s.gpr .r23 = BX) (hpl : q = true → word s.mem BX oPLen = BitVec.ofNat 64 pL) (hp1 : 1 ≤ pL)
    (hp2 : pL < 2 ^ 60) :
    WP isa (.block (r2Src q)) s fun t =>
      (t.gpr .r30 = word s.mem BX oR2 + BitVec.ofNat 64 (if q then 8 * wsWords pL else 0) ∧ t.mem = s.mem) ∧
        Keep [.r0, .r3, .r4, .r30] s t := by
  cases q
  · refine WP.keep _ ?_ (by decide)
    simp only [r2Src, Bool.false_eq_true, ↓reduceIte, BitVec.add_zero]
    prun [h23, oR2, hX.ld (show 88 + 8 ≤ Zs by omega_arith)]
  · simp only [r2Src, ↓reduceIte]
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 pL ∧ t.mem = s.mem) (by
      have hpl' : s.mem.readW (off BX 40) 64 = BitVec.ofNat 64 pL := hpl rfl
      prun [h23, oPLen, hX.ld (show 40 + 8 ≤ Zs by omega_arith), hpl']) rfl) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (words_ok a3 hp1 hp2) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
    refine WP.mono (WP.keep [.r4, .r30] (Q := fun t => t.gpr .r30 =
        word s.mem BX oR2 + BitVec.ofNat 64 (8 * wsWords pL) ∧ t.mem = s.mem) (by
      prun [(k2.gpr .r23 (by decide)).trans ((k1.gpr .r23 (by decide)).trans h23), a4,
        oR2, (hX.congr ((k1.trans k2).wr)).ld (show 88 + 8 ≤ Zs by omega_arith), m2, m1]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      have : wsWords pL < 2 ^ 58 := by unfold wsWords; omega_arith
      rw [Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith) rfl) fun t ⟨⟨t30, tm⟩, k3⟩ => ⟨⟨by simpa using t30, tm⟩, ((k1.trans k2).trans k3).mono⟩

/-- `r2Ptr pc q`: with `pc`, the cached value's address into `r30`. -/
theorem r2Ptr_ok {pc q : Bool} {s₀ s : State} {BX : Addr} {Zs w Pv : Nat} (hX : Scr s BX Zs) (hZ : 256 ≤ Zs)
    (h23 : s.gpr .r23 = BX) (hm : s.mem = s₀.mem) (hR2 : pc = true → ∃ S pL b, R2C q s₀ BX S Zs w Pv pL b) :
    WP isa (.block (r2Ptr pc q)) s fun t =>
      ((pc = true → ∃ S pL b, R2C q s₀ BX S Zs w Pv pL b ∧ t.gpr .r30 = S) ∧ t.mem = s.mem) ∧
        Keep [.r0, .r3, .r4, .r30] s t := by
  cases pc
  · exact WP.block_nil_iff.mpr ⟨⟨nofun, rfl⟩, Keep.refl _ _⟩
  · obtain ⟨S, pL, b, C⟩ := hR2 rfl
    exact WP.mono (r2Src_ok hX hZ h23 (fun hq => by rw [hm]; exact C.pl hq) C.pl1 C.pl2) fun t ⟨⟨a30, m⟩, k⟩ =>
      ⟨⟨fun _ => ⟨S, pL, b, C, by rw [a30, C.src, hm]⟩, m⟩, k⟩

/-- `r2Step pc`: `R² mod p` into array 1, as `Pre.r2Prime_ok` gives it,
with `pc` from the cached values (`R2C`). -/
theorem r2Step_ok {pc q : Bool} {s : State} {BX B : Addr} {Z Zs w : Nat}
    (hs : Scr s B Z) (hsepB : ∀ S : Addr, (∀ x, ofs S x < 8 * w → Zs ≤ ofs BX x) →
      ∀ x, ofs S x < 8 * w → Z ≤ ofs B x)
    (h8 : s.gpr .r8 = off B (slot w 2)) (h9 : s.gpr .r9 = off B (slot w 3))
    (h10 : s.gpr .r10 = off B (slot w 0)) (h5 : s.gpr .r5 = off B (slot w 1))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hN : 2 ≤ val32 s.mem B (slot w 0) (2 * w)) (hodd : val32 s.mem B (slot w 0) (2 * w) % 2 = 1)
    (hC : pc = true → ∃ S pL b, R2C q s BX S Zs w (val32 s.mem B (slot w 0) (2 * w)) pL b ∧ s.gpr .r30 = S) :
    WP isa (r2Step pc) s fun t =>
      val32 t.mem B (slot w 1) (2 * w) = 2 ^ (128 * w) % val32 s.mem B (slot w 0) (2 * w) ∧
      Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep (.r30 :: Pre.r2PrimeRegs) s t := by
  cases pc
  · exact WP.mono (Pre.r2Prime_ok hs h8 h9 h10 h5 h11 hw hw' hZ h12 hinv hN hodd) fun t ⟨a, b, k⟩ =>
      ⟨a, b, k.mono fun r hr => List.mem_cons_of_mem _ hr⟩
  obtain ⟨S, pL, b, C, a30⟩ := hC rfl
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e1 := e 1; have e2 := e 2; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  refine WP.mono (r2Copy_ok (b := b) hs C.hS C.rd
    (hsepB S C.sep) (by rw [a30]; simp [off]) h10 h29 h11 C.r26 (by omega_arith) hw' (by omega_arith))
    fun t ⟨⟨tv, tout⟩, k2⟩ => ?_
  refine ⟨?_, fun x hx => tout x (by
    have ex : Mont.ofs B x = ofs B x := rfl
    rw [ex] at hx; exact hx.imp id fun h => by omega_arith), k2.mono (by decide)⟩
  rw [Pre.val32_eq_wv, tv]
  cases b
  · rw [C.three rfl, pow128_mod3]; rfl
  · exact C.val rfl

end VG.Proof.Bignum.PPC64LE.Crt

end

end

/-!
# The RSA private-key operation on PPC64LE: a prime's power, the input

`powerA_ok`: the prime from `X`'s array `xj` into the working space's array
0, `-p⁻¹ mod 2³²`, `R² mod p` into array 1, and the input modulo the prime
into array 4.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- The registers `power` writes. -/
def powerRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24,
    .r25, .r30, .r31]

/-- The bytes of a buffer apart from the working space, after a change
within it. -/
theorem bytesAt_out {B I : Addr} {Z o n k : Nat} {m m' : Mem} (h : Outside B o n m m') (hn : o + n ≤ Z)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off I i ≠ x) :
    Spec.Rsa.bytesAt m' I k = Spec.Rsa.bytesAt m I k := by
  rw [bytesAt_eq, bytesAt_eq]
  refine List.map_congr_left fun i hi => h _ ?_
  obtain hi := List.mem_range.mp hi
  by_contra hc
  exact hsep i hi (I + BitVec.ofNat 64 i) (by omega) rfl

theorem wv_low_mod2 (m : Mem) (p : Addr) (d : Nat) {n : Nat} (hn : 1 ≤ n) :
    wv m p d n % 2 = (word m p d).toNat % 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 1 + k := ⟨n - 1, by omega_arith⟩
  rw [wv_add]
  simp only [wv, Nat.zero_add, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.mul_one]
  rw [show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl, Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- `power`'s first part: `k` (the header's word) into `r25`, the prime (`wv`
of `X`'s array `xj`, `w_A` words) into array 0 of the working space
`off BX oA`, `-p⁻¹ mod 2³²` into `r12`, `R² mod p` into array 1
(`r2Prime`), and `c mod p` into array 4 (`reduceIn`), for `c` the first
`w_A n` words of `X`'s array 6. -/
theorem powerA_ok {pc q : Bool} {s : State} {BX : Addr} {Z oA wA wX xj k Pv Cv : Nat} {c : Prog isa}
    {Q : State → Prop}
    (hs : Scr s BX Z) (hA : oA + slot wA 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wA) (hw' : wA < 2 ^ 31)
    (hwx : wA ≤ wX) (hxj : xj < 8)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wA 0)) (h21 : s.gpr .r21 = off (off BX oA) (slot wA 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wA + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wA)) (h23 : s.gpr .r23 = BX)
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hK : word s.mem BX oNLen = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k < 2 ^ 40)
    (hn : wA * nChunks ((k + 7) / 8) wA ≤ wX)
    (hP : wv s.mem BX (slot wX xj) wA = Pv) (hP2 : 2 ≤ Pv) (hPodd : Pv % 2 = 1)
    (hC : wv s.mem BX (slot wX 6) (wA * nChunks ((k + 7) / 8) wA) = Cv)
    (hR2 : pc = true → ∃ S pL b, R2C q s BX S Z wA Pv pL b)
    (hc : ∀ t, val32 t.mem (off BX oA) (slot wA 0) (2 * wA) = Pv →
      val32 t.mem (off BX oA) (slot wA 1) (2 * wA) = 2 ^ (128 * wA) % Pv →
      val32 t.mem (off BX oA) (slot wA 4) (2 * wA) = Cv % Pv →
      (t.gpr .r12).toNat < 2 ^ 32 → (w32 t.mem (off BX oA) (slot wA 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0 →
      Outside BX oA (slot wA 24) s.mem t.mem → t.gpr .r10 = off (off BX oA) (slot wA 0) →
      Keep (.r10 :: powerRegs) s t → WP isa c t Q) :
    WP isa (.seq (.block (([.load .d .r25 .r23 oNLen, .addi .r14 .r10 0] : List Instr) ++ xb .r15 xj ++
      r2Ptr pc q)) (.seq copyN
      (.seq (.block (PublicChecked.minv ++ PublicChecked.base .r5 1 ++ PublicChecked.base .r8 2 ++
        PublicChecked.base .r9 3)) (.seq (r2Step pc) (.seq reduceIn c))))) s Q := by
  have hn' := hs.nowrap
  obtain e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  obtain eA0 := e wA 0; have eA1 := e wA 1; have eA4 := e wA 4; have eA8 := e wA 8; have eA24 := e wA 24
  obtain eX0 := e wX 0; have eX6 := e wX 6; have eX8 := e wX 8; have sXj := slot_le (w := wX) hxj
  have hK' : s.mem.readW (off BX 16) 64 = BitVec.ofNat 64 k := hK
  obtain hsA := hs.sub hA
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r25, .r14] (Q := fun t => t.gpr .r25 = BitVec.ofNat 64 k ∧
    t.gpr .r14 = off BX (oA + slot wA 0) ∧ t.mem = s.mem) (by
      prun [h23, h10, oNLen, hs.ld (show 16 + 8 ≤ Z by omega_arith), hK', BitVec.add_zero, off_off]) rfl)
    fun s₁ ⟨⟨a25, a14, m1⟩, k1⟩ => ?_
  refine WP.mono (xb_ok (rd := .r15) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h27)
    ((k1.gpr _ (by decide)).trans h28) xj) fun s₂' ⟨⟨a15', m2'⟩, k2'⟩ => ?_
  refine WP.mono (r2Ptr_ok (hs.congr (k1.trans k2').wr) (by omega_arith)
    ((k1.trans k2').gpr _ (by decide) |>.trans h23) (m2'.trans m1) hR2) fun s₂ ⟨⟨p30, mp⟩, kp⟩ => ?_
  obtain a15 : s₂.gpr .r15 = _ := (kp.gpr _ (by decide)).trans a15'
  obtain m2 : s₂.mem = s₁.mem := mp.trans m2'
  obtain k2 := k2'.trans kp
  obtain k12 := k1.trans k2
  -- The prime.
  refine WP.seq (WP.mono (copySub_ok (hs.congr k12.wr) a15 ((k2.gpr _ (by decide)).trans a14)
    ((k12.gpr _ (by decide)).trans h11) (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₃ ⟨⟨hw3, out3⟩, k3⟩ => ?_)
  obtain k13 := k12.trans k3
  rw [m2, m1] at hw3 out3
  obtain v0 : val32 s₃.mem (off BX oA) (slot wA 0) (2 * wA) = Pv := by
    rw [Pre.val32_eq_wv, wv_off, ← hP]; exact wv_congr2 fun i hi => hw3 i hi
  obtain hlow : (word s₃.mem (off BX oA) (slot wA 0)).toNat % 2 = 1 := by
    rw [← wv_low_mod2 _ _ _ (show 1 ≤ wA by omega_arith), ← Pre.val32_eq_wv, v0, hPodd]
  -- `-p⁻¹ mod 2³²` and the bases.
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pub.minv_ok (hsA.congr k13.wr) ((k13.gpr _ (by decide)).trans h10) (by omega_arith) hlow)
    fun s₄ ⟨⟨i12, iinv, m4⟩, k4⟩ => ?_
  obtain k14 := k13.trans k4
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) ((k14.gpr _ (by decide)).trans h10)
    ((k14.gpr _ (by decide)).trans h29) 1) fun s₅ ⟨⟨a5, m5⟩, k5⟩ => ?_
  obtain k15 := k14.trans k5
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) ((k15.gpr _ (by decide)).trans h10)
    ((k15.gpr _ (by decide)).trans h29) 2) fun s₆ ⟨⟨a8, m6⟩, k6⟩ => ?_
  obtain k16 := k15.trans k6
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k16.gpr _ (by decide)).trans h10)
    ((k16.gpr _ (by decide)).trans h29) 3) fun s₇ ⟨⟨a9, m7⟩, k7⟩ => ?_
  obtain k17 := k16.trans k7
  obtain hm7 : s₇.mem = s₃.mem := by rw [m7, m6, m5, m4]
  obtain g12 : s₇.gpr .r12 = s₄.gpr .r12 := by
    rw [k7.gpr .r12 (by decide), k6.gpr .r12 (by decide), k5.gpr .r12 (by decide)]
  -- `R² mod p`.
  obtain hsepB : ∀ S : Addr, (∀ x, ofs S x < 8 * wA → Z ≤ ofs BX x) →
      ∀ x, ofs S x < 8 * wA → slot wA 24 ≤ ofs (off BX oA) x := fun S hS x hx => by
    have := hS x hx
    rcases ofs_rebase BX x (o := oA) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩ <;> omega_arith
  refine WP.seq (WP.mono (r2Step_ok (hsA.congr k17.wr) hsepB
    ((k7.gpr _ (by decide)).trans a8) a9
    ((k17.gpr _ (by decide)).trans h10) ((k7.gpr _ (by decide)).trans ((k6.gpr _ (by decide)).trans a5))
    ((k17.gpr _ (by decide)).trans h11) ((k17.gpr _ (by decide)).trans h29)
    hw2 hw' (by simp only [e]; omega_arith) (by rw [g12]; exact i12)
    (by rw [g12, hm7]; exact iinv) (by rw [hm7, v0]; exact hP2) (by rw [hm7, v0]; exact hPodd)
    (fun hp => let ⟨S, pL, b, C, a30⟩ := p30 hp; ⟨S, pL, b, by
      rw [hm7, v0]
      exact C.mono (oA := oA) (n := slot wA 24) (by rw [hm7]; exact out3.mono (by omega_arith) (by omega_arith))
        (by omega_arith) hA (by rw [k17.rd, k17.wr]) (k17.gpr _ (by decide)),
      ((((k3.trans k4).trans k5).trans k6).trans k7 |>.gpr _ (by decide)).trans a30⟩))
    fun s₈ ⟨h1, out8, k8⟩ => ?_)
  obtain k18 := k17.trans k8
  rw [hm7, v0] at h1
  rw [hm7] at out8
  obtain v0' : val32 s₈.mem (off BX oA) (slot wA 0) (2 * wA) = Pv := by
    rw [out8.val32 (Or.inl (by omega_arith)) (by omega_arith), v0]
  obtain w8 : w32 s₈.mem (off BX oA) (slot wA 0) = w32 s₃.mem (off BX oA) (slot wA 0) := by
    have := out8.val32 (d := slot wA 0) (k := 1) (Or.inl (by omega_arith)) (by omega_arith)
    simpa [val32] using this
  obtain out38 : Outside BX oA (slot wA 24) s.mem s₈.mem :=
    (out3.mono (by omega_arith) (by omega_arith)).trans
      (out_sub (fun y hy => out8 y hy) (by omega_arith) (by omega_arith) (by omega_arith))
  obtain g12' : s₈.gpr .r12 = s₄.gpr .r12 := (k8.gpr .r12 (by decide)).trans g12
  obtain hc6 : wA * nChunks ((k + 7) / 8) wA ≤ wX + 2 := by omega_arith
  -- `c mod p`.
  refine WP.seq (WP.mono (reduceIn_ok (Cv := Cv) (hs.congr k18.wr) hA hXA hw2 hw' hn ((k18.gpr _ (by decide)).trans h10)
    ((k18.gpr _ (by decide)).trans h21) ((k18.gpr _ (by decide)).trans h29) ((k18.gpr _ (by decide)).trans h11)
    ((k18.gpr _ (by decide)).trans h27) ((k18.gpr _ (by decide)).trans h28)
    (by rw [k8.gpr .r25 (by decide), k7.gpr .r25 (by decide), k6.gpr .r25 (by decide), k5.gpr .r25 (by decide),
      k4.gpr .r25 (by decide), k3.gpr .r25 (by decide), k2.gpr .r25 (by decide), a25]) hk hk'
    (by rw [g12']; exact i12) (by rw [g12', w8]; exact iinv) v0' hP2 hPodd h1
    ((out38.wv (Or.inl (by omega_arith)) (by omega_arith)).trans hC))
    fun t ⟨⟨t4, t0, t1, t12, tinv, tout, t10⟩, kt⟩ => ?_)
  exact hc t t0 t1 t4 t12 tinv (out38.trans tout) t10 ((k18.trans kt).mono (by decide +kernel))

end VG.Proof.Bignum.PPC64LE.Crt
