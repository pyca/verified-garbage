module

public import VerifiedGarbage.Impl.MillerRabin.RISCV64.Prep
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Ctx
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.RsaKeyGen.Halve
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.RsaKeyGen.MillerRabin
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Miller–Rabin's exponent on RISC-V

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Prep.lean`), in the search's
registers (`Env`: `a7` array 0's base, `s5` the arrays' size, `t0` `w`, `s6`
the working space): `lowWord_ok`, the lowest nonzero word of `c − 1`;
`halfPass_ok`, `[t4] := s3 ? [t3] / 2 : [t3]`, in place or not;
`expSetup_ok`, `E = (c − 1) / 2^σ` in array 27 and the lowest set bit of
`c − 1`'s lowest nonzero word after it. `repeat16_val` and `sig_word` are
the masks of `σ > j`, which the round's last squarings test too.
-/

-- separate module: the round's last squarings (`repeat16_val`, `sig_word`) and the search's callers use it too

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64

open VG VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.MillerRabin.RISCV64
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot wv wv_lt word_of_wv)
open VG.Proof.RsaKeyGen (mrE mrA mrSig sigOf)
open VG.Proof.Mont (off Outside writeW_outside word_writeW_self wordsVal)
open VG.RISCV64.RegUpd
open VG.Impl.Bignum.RISCV64.PublicChecked (base)

/-! ## The search's registers -/

/-- The working space at `B` (`Z` bytes, its header at `s6`) with 28 arrays
of `w + 2` words, `a7` at array 0, `s5` their size, `t0` `w`. -/
structure Env (s : State) (B : Addr) (Z w : Nat) : Prop where
  hs : Scr s B Z
  a7 : s.gpr .a7 = off B (slot w 0)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))
  t0 : s.gpr .t0 = BitVec.ofNat 64 w
  s6 : s.gpr .s6 = B
  hw : 4 ≤ w
  hw' : w ≤ 128
  hZ : slot w 28 ≤ Z

/-- The registers `Env` reads. -/
def envRegs : List Reg := [.a7, .s5, .t0, .s6]

theorem Env.keep {s t : State} {B : Addr} {Z w : Nat} {rs : List Reg} (h : Env s B Z w) (k : Keep rs s t)
    (hr : ∀ r ∈ envRegs, r ∉ rs) : Env t B Z w :=
  ⟨h.hs.congr k.2.2, (k.gpr (hr _ (by decide))).trans h.a7, (k.gpr (hr _ (by decide))).trans h.s5,
    (k.gpr (hr _ (by decide))).trans h.t0, (k.gpr (hr _ (by decide))).trans h.s6, h.hw, h.hw', h.hZ⟩

theorem Env.arr {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) {j : Nat} (hj : j < 28) :
    slot w j + 8 * (w + 2) ≤ Z :=
  Nat.le_trans (slot_lt hj) h.hZ

/-- `base rd j` in `Env`. -/
theorem Env.base {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) {rd : Reg} (hrd : rd ≠ .s5) (j : Nat) :
    WP isa (.block (base rd j)) s fun t => (t.gpr rd = off B (slot w j) ∧ t.mem = s.mem) ∧ Keep [rd] s t :=
  Pub.base_ok hrd h.a7 h.s5 j

theorem Env.al {s : State} {B : Addr} {Z w : Nat} (_ : Env s B Z w) (j i : Nat) : (slot w j + 8 * i) % 8 = 0 := by
  have := slot_al w j; omega_arith

/-- The context of the round gives the search's registers, with `s6`. -/
theorem MCtx.env {s : State} {B : Addr} {Z w N : Nat} (h : MCtx s B Z w N) (h6 : s.gpr .s6 = B) : Env s B Z w :=
  ⟨h.scr, h.a7, h.s5, h.t0, h6, h.w4, h.w128, h.hZ⟩

/-! ## The lowest nonzero word -/

/-- Word `j` of `c − 1`, as the scan reads it: `c`'s, bit 0 of the first
flipped. -/
def cw (m : Mem) (B : Addr) (w j : Nat) : BitVec 64 :=
  VG.Proof.Bignum.word m B (slot w 0 + 8 * j) ^^^ BitVec.ofNat 64 (if j = 0 then 1 else 0)

theorem xor_one_odd {x : BitVec 64} (h : x.toNat % 2 = 1) : (x ^^^ BitVec.ofNat 64 1).toNat = x.toNat / 2 * 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [BitVec.toNat_xor, Nat.testBit_xor, show (BitVec.ofNat 64 1 : BitVec 64).toNat = 1 from rfl]
  rcases i with _ | i
  · rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero, h, Nat.mul_mod_left]; rfl
  · rw [Nat.testBit_lt_two_pow (show 1 < 2 ^ (i + 1) from Nat.one_lt_two_pow (by omega_arith)), Bool.xor_false,
      show x.toNat / 2 * 2 = x.toNat / 2 ^ 1 * 2 ^ 1 from rfl, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
    simp

theorem cw_toNat {m : Mem} {B : Addr} {w c : Nat} (hn : wv m B (slot w 0) w = c) (hodd : c % 2 = 1) {j : Nat}
    (hj : j < w) : (cw m B w j).toNat = (c - 1) / 2 ^ (64 * j) % 2 ^ 64 := by
  unfold cw
  split
  · rename_i hj0; subst hj0
    rw [Nat.mul_zero, Nat.add_zero]
    have h0 := word_of_wv m B (slot w 0) w (q := 0) hj
    rw [Nat.mul_zero, Nat.add_zero, hn, Nat.pow_zero, Nat.div_one] at h0
    rw [xor_one_odd (by rw [h0]; omega_arith), h0, Nat.pow_zero, Nat.div_one]
    omega_arith
  · rw [BitVec.xor_zero, word_of_wv m B (slot w 0) w hj, hn,
      VG.Proof.RsaKeyGen.odd_sub_one_div hodd (by omega_arith)]

theorem lw_val (v x : BitVec 64) : v ||| x &&& mask (decide (v = 0)) = if v = 0 then x else v := by
  by_cases h : v = 0
  · subst h
    rw [show decide ((0 : BitVec 64) = 0) = true from rfl, ite_eq_left rfl]
    show 0#64 ||| x &&& BitVec.allOnes 64 = x
    rw [BitVec.and_allOnes, BitVec.zero_or]
  · rw [decide_eq_false h, ite_eq_right h]
    show v ||| x &&& 0#64 = v
    rw [BitVec.and_zero, BitVec.or_zero]

/-- The registers `lowWord` writes. -/
def lowRegs : List Reg := [.t2, .t3, .t5, .s0, .s1, .s2]

/-- After `i` words of the scan. -/
structure LInv (s₀ : State) (B : Addr) (w i0 : Nat) (x : BitVec 64) (i : Nat) (t : State) : Prop where
  keep : Keep lowRegs s₀ t
  mem : t.mem = s₀.mem
  t3 : t.gpr .t3 = off B (slot w 0 + 8 * i)
  s1 : t.gpr .s1 = BitVec.ofNat 64 (if i = 0 then 1 else 0)
  s0 : t.gpr .s0 = if i ≤ i0 then 0 else x

theorem li1_eq : (BitVec.ofNat 64 1 : BitVec 64) = 1#64 := rfl

/-- `lowWord`: the lowest nonzero word of `c − 1` into `s0`. -/
theorem lowWord_ok {s : State} {B : Addr} {Z w c : Nat} (h : Env s B Z w) (hn : A s.mem B w 0 = c)
    (hodd : c % 2 = 1) (hc1 : 1 < c) :
    WP isa lowWord s fun t =>
      ((t.gpr .s0).toNat = (c - 1) / 2 ^ (64 * (mrA c / 64)) % 2 ^ 64 ∧ t.mem = s.mem) ∧ Keep lowRegs s t := by
  have hnw := h.hs.nowrap
  have hw := h.hw
  have hw' := h.hw'
  have s0 := Env.arr h (show 0 < 28 by decide)
  rw [A, Pre.wordsVal_eq_wv] at hn
  obtain ⟨hN, hm2⟩ := VG.Proof.RsaKeyGen.splitTwos_spec (c - 1) (by omega_arith)
  change c - 1 = (Spec.Rsa.splitTwos (c - 1)).2 * 2 ^ mrA c at hN
  obtain ⟨hz, -, -⟩ := VG.Proof.RsaKeyGen.lowWord_bits hN hm2
  have hcw : c < 2 ^ (64 * w) := by rw [← hn]; exact wv_lt _ _ _ _
  have ha : mrA c < 64 * w := by
    rcases Nat.lt_or_ge (mrA c) (64 * w) with h | h
    · exact h
    exfalso
    have h1 : 2 ^ (64 * w) ≤ 2 ^ mrA c := Nat.pow_le_pow_right (by decide) h
    have h2 : 2 ^ mrA c ≤ (Spec.Rsa.splitTwos (c - 1)).2 * 2 ^ mrA c := Nat.le_mul_of_pos_left _ (by omega_arith)
    omega_arith
  generalize hi0 : mrA c / 64 = i0 at hz ⊢
  have hi0w : i0 < w := by omega_arith
  have hx : (cw s.mem B w i0).toNat = (c - 1) / 2 ^ (64 * i0) % 2 ^ 64 := cw_toNat hn hodd hi0w
  have hne : cw s.mem B w i0 ≠ 0 := fun e => by
    obtain ⟨-, hx1, -⟩ := VG.Proof.RsaKeyGen.lowWord_bits hN hm2
    rw [hi0, ← hx, e] at hx1; simp at hx1
  unfold lowWord
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .t3) (by decide) 0) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  have hpre : WP isa (.block [.addi .t5 .t0 0, .li .s0 0, .li .s1 1]) s₁ fun t =>
      (t.gpr .t5 = BitVec.ofNat 64 w ∧ t.gpr .s0 = 0 ∧ t.gpr .s1 = BitVec.ofNat 64 1 ∧ t.mem = s₁.mem) ∧
        Keep [.t5, .s0, .s1] s₁ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li (show imm12 0 by decide), exec_li (show imm12 1 by decide), (k1.gpr (by decide)).trans h.t0,
      BitVec.add_zero]
    all_goals first | rfl | exact ⟨rfl, rfl⟩
  refine WP.mono hpre fun s₂ ⟨⟨a5, a0, a1, m2⟩, k2⟩ => ?_
  refine WP.mono (wp_countdown (N := w) (by omega_arith) (by omega_arith) (LInv s B w i0 (cw s.mem B w i0))
    (fun i hi t hI _ => ?_) ⟨(k1.trans k2).mono (by decide), by rw [m2, m1],
      by rw [k2.gpr (by decide), a3]; rfl, by rw [a1]; rfl, by rw [a0]; simp⟩ a5)
    fun t hI => ⟨⟨?_, hI.mem⟩, hI.keep⟩
  · have hs := h.hs.congr hI.keep.2.2
    have hwd : VG.Proof.Bignum.word t.mem B (slot w 0 + 8 * i) ^^^ BitVec.ofNat 64 (if i = 0 then 1 else 0) =
        cw s.mem B w i := by rw [hI.mem]; rfl
    have hr : t.gpr .s0 ||| cw s.mem B w i &&& mask (decide (t.gpr .s0 = 0)) =
        if i + 1 ≤ i0 then 0 else cw s.mem B w i0 := by
      rw [lw_val, hI.s0]
      rcases Nat.lt_trichotomy i i0 with hlt | rfl | hgt
      · have hz0 : cw s.mem B w i = 0 :=
          BitVec.eq_of_toNat_eq (by rw [cw_toNat hn hodd (by omega_arith), hz i hlt]; rfl)
        rw [ite_eq_left (show i ≤ i0 by omega_arith), ite_eq_left rfl, hz0, ite_eq_left (show i + 1 ≤ i0 by omega_arith)]
      · rw [ite_eq_left (Nat.le_refl _), ite_eq_left rfl, ite_eq_right (show ¬ i + 1 ≤ i by omega_arith)]
      · rw [ite_eq_right (show ¬ i ≤ i0 by omega_arith), ite_eq_right hne, ite_eq_right (show ¬ i + 1 ≤ i0 by omega_arith)]
    have hr' : t.gpr .s0 ||| (Mont.word t.mem B (slot w 0 + 8 * i) ^^^ BitVec.ofNat 64 (if i = 0 then 1 else 0)) &&&
        ((if 0#64 < t.gpr .s0 then 1 else 0) - 1#64) = if i + 1 ≤ i0 then 0 else cw s.mem B w i0 := by
      rw [zero_mask, ← hr, ← hwd]
    refine WP.mono (WP.keep lowRegs (Q := fun t' => t'.gpr .t3 = off B (slot w 0 + 8 * (i + 1)) ∧
        t'.gpr .s1 = BitVec.ofNat 64 0 ∧ t'.gpr .s0 = (if i + 1 ≤ i0 then 0 else cw s.mem B w i0) ∧
        t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧ t'.mem = t.mem) ?_ (by rfl) (by rfl))
      fun t' ⟨⟨b3, b1, b0, b5, bm⟩, k'⟩ => ⟨⟨(hI.keep.trans k').mono (by decide), bm.trans hI.mem, b3,
        by rw [b1]; simp, b0⟩, b5⟩
    brun [exec_li (show imm12 0 by decide), hI.t3, hI.s1,
      hs.ld (show slot w 0 + 8 * i + 8 ≤ Z by omega_arith), hs.al8 (show slot w 0 + 8 * i + 8 ≤ Z by omega_arith)
        (h.al 0 i), BitVec.add_zero, hr',
      show slot w 0 + 8 * i + 8 = slot w 0 + 8 * (i + 1) by omega_arith]
  · rw [hI.s0, ite_eq_right (show ¬ w ≤ i0 by omega_arith), hx]

/-! ## Halving -/

/-- A word of the halved number, or the word itself. -/
def hsel (mb : Bool) (a b : BitVec 64) : BitVec 64 := if mb then (a >>> 1) ||| (b <<< 63) else a

theorem hsel_eq (mb : Bool) (a b : BitVec 64) :
    ((a >>> 1 ||| b <<< 63) ^^^ a) &&& mask mb ^^^ a = hsel mb a b := by
  cases mb
  · show _ &&& 0#64 ^^^ a = a
    rw [BitVec.and_zero, BitVec.zero_xor]
  · show _ &&& BitVec.allOnes 64 ^^^ a = _
    rw [BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]; rfl

theorem top_sel (a : BitVec 64) (mb : Bool) :
    (a >>> 1 ^^^ a) &&& mask mb ^^^ a = if mb then a >>> 1 else a := by
  cases mb
  · show _ &&& 0#64 ^^^ a = a
    rw [BitVec.and_zero, BitVec.zero_xor]
  · show _ &&& BitVec.allOnes 64 ^^^ a = _
    rw [BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]; rfl

/-- The registers `halfPass` writes. -/
def halfRegs : List Reg := [.t3, .t4, .t5, .s0, .s1, .s2, .s4]

/-- After `i` words of a halving pass's loop from `s₀`. -/
structure HInv (s₀ : State) (B : Addr) (Z w eS eD : Nat) (mb : Bool) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep halfRegs s₀ t
  t3 : t.gpr .t3 = off B (eS + 8 * (i + 1))
  t4 : t.gpr .t4 = off B (eD + 8 * i)
  s0 : t.gpr .s0 = VG.Proof.Bignum.word s₀.mem B (eS + 8 * i)
  done : ∀ k, k < i → VG.Proof.Bignum.word t.mem B (eD + 8 * k) =
    hsel mb (VG.Proof.Bignum.word s₀.mem B (eS + 8 * k)) (VG.Proof.Bignum.word s₀.mem B (eS + 8 * (k + 1)))
  src : ∀ k, i + 1 ≤ k → k < w → VG.Proof.Bignum.word t.mem B (eS + 8 * k) = VG.Proof.Bignum.word s₀.mem B (eS + 8 * k)
  out : Outside B eD (8 * i) s₀.mem t.mem

/-- A word of a halving pass. -/
theorem halfStep_ok {s₀ : State} {B : Addr} {Z w eS eD : Nat} {mb : Bool} (h3 : s₀.gpr .s3 = mask mb)
    (hS : eS + 8 * w ≤ Z) (hD : eD + 8 * w ≤ Z) (aS : eS % 8 = 0) (aD : eD % 8 = 0)
    (hsep : eD = eS ∨ eD + 8 * w ≤ eS ∨ eS + 8 * w ≤ eD)
    {i : Nat} (hi : i + 1 < w) {t : State} (hI : HInv s₀ B Z w eS eD mb i t) :
    WP isa (.block (([.load .d .s1 .t3 0, .shift .sll .d .s2 .s1 63, .shift .srl .d .s4 .s0 1,
        .logic .or .s4 .s4 .s2, .logic .xor .s4 .s4 .s0, .logic .and .s4 .s4 .s3, .logic .xor .s4 .s4 .s0,
        .store .d .s4 .t4 0, .addi .t3 .t3 8, .addi .t4 .t4 8, .addi .s0 .s1 0] : List Instr) ++
        ([.addi .t5 .t5 (-1)] : List Instr))) t
      fun t' => HInv s₀ B Z w eS eD mb (i + 1) t' ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t3 : t.gpr .s3 = mask mb := (hI.keep.gpr (by decide)).trans h3
  have hSj : VG.Proof.Bignum.word t.mem B (eS + 8 * (i + 1)) = VG.Proof.Bignum.word s₀.mem B (eS + 8 * (i + 1)) :=
    hI.src (i + 1) (Nat.le_refl _) hi
  have hst : WP isa (.block ([.load .d .s1 .t3 0, .shift .sll .d .s2 .s1 63, .shift .srl .d .s4 .s0 1,
        .logic .or .s4 .s4 .s2, .logic .xor .s4 .s4 .s0, .logic .and .s4 .s4 .s3, .logic .xor .s4 .s4 .s0,
        .store .d .s4 .t4 0, .addi .t3 .t3 8, .addi .t4 .t4 8, .addi .s0 .s1 0] ++
        ([.addi .t5 .t5 (-1)] : List Instr))) t
      fun t' => (t'.mem = t.mem.writeW (off B (eD + 8 * i))
        (hsel mb (VG.Proof.Bignum.word s₀.mem B (eS + 8 * i)) (VG.Proof.Bignum.word s₀.mem B (eS + 8 * (i + 1)))) ∧
        t'.gpr .s0 = VG.Proof.Bignum.word s₀.mem B (eS + 8 * (i + 1)) ∧ t'.gpr .t3 = off B (eS + 8 * (i + 1 + 1)) ∧
        t'.gpr .t4 = off B (eD + 8 * (i + 1)) ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ∧
        Keep halfRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [hI.t3, hI.t4, hI.s0, t3, hI.scr.ld (show eS + 8 * (i + 1) + 8 ≤ Z by omega_arith),
      hI.scr.al8 (show eS + 8 * (i + 1) + 8 ≤ Z by omega_arith) (by omega_arith),
      hI.scr.st (show eD + 8 * i + 8 ≤ Z by omega_arith),
      hI.scr.al8 (show eD + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith), hSj, hsel_eq, BitVec.add_zero]
    rw [show eS + 8 * (i + 1) + 8 = eS + 8 * (i + 1 + 1) by omega_arith, show eD + 8 * i + 8 = eD + 8 * (i + 1) by omega_arith]
    exact ⟨rfl, rfl⟩
  refine WP.mono hst fun t' ⟨⟨hm, h5, h15, h16, h17⟩, k'⟩ => ⟨?_, h17⟩
  have hw8 : Outside B (eD + 8 * i) 8 t.mem t'.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by omega_arith)
  refine ⟨hI.scr.congr k'.2.2, (hI.keep.trans k').mono (by decide), h15, h16, h5, fun k hk => ?_,
    fun k hk hkw => ?_, ?_⟩
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [show VG.Proof.Bignum.word _ B (eD + 8 * k) = VG.Proof.Mont.word _ B (eD + 8 * k) from rfl,
        Outside.word (writeW_outside t.mem B _ (by omega_arith)) (by omega_arith) (by omega_arith)]
      exact hI.done k hk
    · exact word_writeW_self _ _ _ _
  · rw [hm, show VG.Proof.Bignum.word _ B (eS + 8 * k) = VG.Proof.Mont.word _ B (eS + 8 * k) from rfl,
      Outside.word (writeW_outside t.mem B _ (by omega_arith)) (by omega_arith) (by omega_arith)]
    exact hI.src k (by omega_arith) hkw
  · exact Outside.trans (Outside.mono hI.out (Nat.le_refl _) (by omega_arith)) (Outside.mono hw8 (by omega_arith) (by omega_arith))

/-- A halving pass: `[eD] := mb ? [eS] / 2 : [eS]` over `w` words, in place
or not. -/
theorem halfPass_ok {s : State} {B : Addr} {Z w eS eD : Nat} {mb : Bool} (hs : Scr s B Z)
    (h3 : s.gpr .t3 = off B eS) (h4 : s.gpr .t4 = off B eD) (hm : s.gpr .s3 = mask mb)
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 2 ≤ w) (hw' : w ≤ 128) (hS : eS + 8 * w ≤ Z)
    (hD : eD + 8 * w ≤ Z) (aS : eS % 8 = 0) (aD : eD % 8 = 0)
    (hsep : eD = eS ∨ eD + 8 * w ≤ eS ∨ eS + 8 * w ≤ eD) :
    WP isa halfPass s fun t => wordsVal t.mem B eD w = (if mb then wordsVal s.mem B eS w / 2 else wordsVal s.mem B eS w) ∧
      Outside B eD (8 * w) s.mem t.mem ∧ Keep halfRegs s t := by
  have hn := hs.nowrap
  simp only [Pre.wordsVal_eq_wv]
  unfold halfPass
  have hpre : WP isa (.block [.load .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t5 .t0 (-1)]) s
      fun t => (t.gpr .s0 = VG.Proof.Bignum.word s.mem B eS ∧ t.gpr .t3 = off B (eS + 8 * (0 + 1)) ∧
        t.gpr .t5 = BitVec.ofNat 64 (w - 1) ∧ t.mem = s.mem) ∧ Keep [.s0, .t3, .t5] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h3, ht0, hs.ld (show eS + 8 ≤ Z by omega_arith), hs.al8 (show eS + 8 ≤ Z by omega_arith) aS, BitVec.add_zero]
    try refine ⟨rfl, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  refine WP.seq (WP.mono hpre fun s₀ ⟨⟨h5₀, h15₀, h17₀, hm₀⟩, k₀⟩ => ?_)
  have hs₀ := hs.congr k₀.2.2
  have h9₀ : s₀.gpr .s3 = mask mb := (k₀.gpr (by decide)).trans hm
  have h16₀ : s₀.gpr .t4 = off B eD := (k₀.gpr (by decide)).trans h4
  refine WP.seq (WP.mono (wp_countdown (N := w - 1) (by omega_arith) (by omega_arith) (HInv s₀ B Z w eS eD mb)
    (fun i hi t hI _ => halfStep_ok h9₀ hS hD aS aD hsep (by omega_arith) hI)
    ⟨hs₀, Keep.refl _ _, h15₀, by rw [h16₀]; rfl, by rw [h5₀, hm₀, Nat.mul_zero, Nat.add_zero],
      fun k hk => absurd hk (by omega_arith), fun k _ _ => rfl, Outside.refl _ _ _ _⟩ h17₀) fun s₁ hI => ?_)
  have t9 : s₁.gpr .s3 = mask mb := (hI.keep.gpr (by decide)).trans h9₀
  have htopb : WP isa (.block [.shift .srl .d .s4 .s0 1, .logic .xor .s4 .s4 .s0, .logic .and .s4 .s4 .s3,
      .logic .xor .s4 .s4 .s0, .store .d .s4 .t4 0]) s₁ fun t =>
      t.mem = s₁.mem.writeW (off B (eD + 8 * (w - 1)))
        (if mb then VG.Proof.Bignum.word s₀.mem B (eS + 8 * (w - 1)) >>> 1
          else VG.Proof.Bignum.word s₀.mem B (eS + 8 * (w - 1))) ∧
        Keep halfRegs s₁ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [hI.t4, hI.scr.st (show eD + 8 * (w - 1) + 8 ≤ Z by omega_arith),
      hI.scr.al8 (show eD + 8 * (w - 1) + 8 ≤ Z by omega_arith) (by omega_arith), t9, hI.s0, top_sel,
      BitVec.add_zero]
  refine WP.mono htopb fun t ⟨hmt, k⟩ => ?_
  have hw8 : Outside B (eD + 8 * (w - 1)) 8 s₁.mem t.mem := by rw [hmt]; exact writeW_outside _ _ _ (by omega_arith)
  have hdone : ∀ i, i + 1 < w → VG.Proof.Bignum.word t.mem B (eD + 8 * i) =
      hsel mb (VG.Proof.Bignum.word s.mem B (eS + 8 * i)) (VG.Proof.Bignum.word s.mem B (eS + 8 * (i + 1))) :=
    fun i hi => by
      rw [show VG.Proof.Bignum.word _ B (eD + 8 * i) = VG.Proof.Mont.word _ B (eD + 8 * i) from rfl,
        Outside.word hw8 (by omega_arith) (by omega_arith)]
      rw [← hm₀]; exact hI.done i (by omega_arith)
  have htop : VG.Proof.Bignum.word t.mem B (eD + 8 * (w - 1)) = if mb then VG.Proof.Bignum.word s.mem B (eS + 8 * (w - 1)) >>> 1
      else VG.Proof.Bignum.word s.mem B (eS + 8 * (w - 1)) := by
    rw [hmt, ← hm₀]; exact word_writeW_self _ _ _ _
  refine ⟨?_, ?_, ((k₀.trans hI.keep).trans k).mono (by decide)⟩
  · cases mb
    · rw [ite_eq_right (by decide)] at htop ⊢
      refine VG.Proof.Bignum.wv_congr2 fun i hi => ?_
      rcases Nat.lt_or_ge (i + 1) w with h | h
      · exact hdone i h
      · rw [show i = w - 1 by omega_arith]; exact htop
    · rw [ite_eq_left rfl] at htop ⊢
      exact VG.Proof.RsaKeyGen.wv_half (by omega_arith) (fun i hi => hdone i hi) htop
  · rw [← hm₀]
    exact Outside.trans (Outside.mono hI.out (Nat.le_refl _) (by omega_arith)) (Outside.mono hw8 (by omega_arith) (by omega_arith))

/-! ## The exponent -/

theorem shl3_ofNat (w : Nat) : BitVec.ofNat 64 w <<< 3 = BitVec.ofNat 64 (8 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- `markerAddr rd`: the word after array 27's `w` into `rd`. -/
theorem markerAddr_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) {rd : Reg} (hrd : rd = .t3 ∨ rd = .t4) :
    WP isa (.block (markerAddr rd)) s fun t => (t.gpr rd = off B (slot w aE + 8 * w) ∧ t.mem = s.mem) ∧
      Keep [.t2, rd] s t := by
  unfold markerAddr
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := rd) (by rcases hrd with rfl | rfl <;> decide) aE) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  have hb : WP isa (.block [.shift .sll .d .t2 .t0 3, .add rd rd .t2]) s₁ fun t =>
      (t.gpr rd = off B (slot w aE + 8 * w) ∧ t.mem = s₁.mem) ∧ Keep [.t2, rd] s₁ t := by
    rcases hrd with rfl | rfl <;>
    · refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [(k1.gpr (by decide)).trans h.t0, shl3_ofNat w, a14]
  exact WP.mono hb fun t ⟨⟨a, m⟩, k⟩ => ⟨⟨a, m.trans m1⟩, (k1.trans k).mono (by
    rcases hrd with rfl | rfl <;> decide)⟩

theorem neg_and_low {x : BitVec 64} {k : Nat} (hk : k < 64) (h1 : x.toNat.testBit k = true)
    (h0 : ∀ j < k, x.toNat.testBit j = false) : x &&& (BitVec.ofNat 64 0 - x) = BitVec.twoPow 64 k := by
  rw [show (BitVec.ofNat 64 0 : BitVec 64) = 0#64 from rfl, BitVec.zero_sub]
  exact VG.Proof.RsaKeyGen.and_neg_eq_twoPow hk h1 h0

/-- `lowBit`: `l = x & −x` (`x` in `s0`) after array 27's `w` words. -/
theorem lowBit_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) {x : BitVec 64} {k : Nat} (hk : k < 64)
    (h0' : s.gpr .s0 = x) (h1 : x.toNat.testBit k = true) (h0 : ∀ j < k, x.toNat.testBit j = false) :
    WP isa (.block lowBit) s fun t =>
      t.mem = s.mem.writeW (off B (slot w aE + 8 * w)) (BitVec.twoPow 64 k) ∧ Keep [.t2, .t3, .s0] s t := by
  have hE := h.arr (show aE < 28 by decide)
  unfold lowBit
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have hb : WP isa (.block [.li .t2 0, .sub .t2 .t2 .s0, .logic .and .s0 .s0 .t2]) s fun t =>
      (t.gpr .s0 = BitVec.twoPow 64 k ∧ t.mem = s.mem) ∧ Keep [.t2, .s0] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li (show imm12 0 by decide), h0']
    exact neg_and_low hk h1 h0
  refine WP.mono hb fun s₁ ⟨⟨a6, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (markerAddr_ok (h.keep k1 (by decide)) (Or.inl rfl)) fun s₂ ⟨⟨a14, m2⟩, k2⟩ => ?_
  have hs₂ := h.hs.congr (k1.trans k2).2.2
  have hst : WP isa (.block [.store .d .s0 .t3 0]) s₂ fun t =>
      t.mem = s₂.mem.writeW (off B (slot w aE + 8 * w)) (BitVec.twoPow 64 k) ∧ Keep [] s₂ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [a14, hs₂.st (show slot w aE + 8 * w + 8 ≤ Z by omega_arith),
      hs₂.al8 (show slot w aE + 8 * w + 8 ≤ Z by omega_arith) (h.al aE w), (k2.gpr (by decide)).trans a6,
      BitVec.add_zero]
  exact WP.mono hst fun t ⟨m, k⟩ => ⟨by rw [m, m2, m1], ((k1.trans k2).trans k).mono (by decide)⟩

/-! ## The masks of `σ > j` -/

/-- `K` for `j = 1, 2, 3`: `0xDDDD…`, `0x9999…`, `0x1111…`. -/
def sigK64 (j : Nat) : BitVec 64 :=
  if j = 1 then 0xDDDDDDDDDDDDDDDD#64 else if j = 2 then 0x9999999999999999#64 else 0x1111111111111111#64

/-- `repeat16 t4 t5 (sigK j)`: `t4 := K`. -/
theorem repeat16_ok (s : State) {j : Nat} (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    WP isa (.block (repeat16 .t4 .t5 (sigK j))) s fun t => (t.gpr .t4 = sigK64 j ∧ t.mem = s.mem) ∧
      Keep [.t4, .t5] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  rcases hj with rfl | rfl | rfl <;>
  · simp only [repeat16, sigK, ↓reduceIte, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul, Int.cast_ofNat_Int,
      Int.reduceSub, Nat.reduceEqDiff]
    brun [exec_lui]
    decide

theorem sig_mask (j : Nat) (hj : j = 1 ∨ j = 2 ∨ j = 3) {k : Nat} (hk : k < 64) :
    (BitVec.twoPow 64 k &&& sigK64 j = 0) = ¬ (j < sigOf k) := by
  rcases hj with rfl | rfl | rfl
  · exact VG.Proof.RsaKeyGen.sig_mask1 k hk
  · exact VG.Proof.RsaKeyGen.sig_mask2 k hk
  · exact VG.Proof.RsaKeyGen.sig_mask3 k hk

theorem sig_word {c j : Nat} (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    decide (BitVec.twoPow 64 (mrA c % 64) &&& sigK64 j ≠ 0) = decide (j < mrSig c) := by
  have h := sig_mask j hj (k := mrA c % 64) (Nat.mod_lt _ (by decide))
  rw [VG.Proof.RsaKeyGen.sigOf_mod] at h
  apply decide_eq_decide.mpr
  rw [show mrSig c = sigOf (mrA c) from rfl, ne_eq, h, Decidable.not_not]

/-- `0 − (0 <u x)`: the mask of `x ≠ 0`. -/
theorem nz_mask (x : BitVec 64) : 0#64 - (if 0#64 < x then 1 else 0) = mask (decide (x ≠ 0)) := by
  by_cases hx : x = 0
  · subst hx; decide
  · have hlt : 0#64 < x := by
      rw [BitVec.lt_def]
      exact Nat.pos_of_ne_zero fun h' => hx (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
    simp only [hlt, ↓reduceIte, hx, ne_eq, not_false_eq_true, decide_true]
    decide

/-- The mask of `σ > j` into `s3`, from the word after array 27. -/
def condMid (j : Nat) : List Instr :=
  [.load .d .t3 .t3 0] ++ repeat16 .t4 .t5 (sigK j) ++
    ([.logic .and .t3 .t3 .t4, .li .t2 0, .sltu .s3 .t2 .t3, .sub .s3 .t2 .s3] : List Instr)

theorem condMid_ok {s : State} {B : Addr} {Z w c : Nat} (hs : Scr s B Z) (hZ : slot w aE + 8 * w + 8 ≤ Z)
    (hal : (slot w aE + 8 * w) % 8 = 0) (h3 : s.gpr .t3 = off B (slot w aE + 8 * w))
    (hL : s.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64)) {j : Nat}
    (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    WP isa (.block (condMid j)) s fun t => (t.gpr .s3 = mask (decide (j < mrSig c)) ∧ t.mem = s.mem) ∧
      Keep [.t2, .t3, .t4, .t5, .s3] s t := by
  unfold condMid
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have hld : WP isa (.block [.load .d .t3 .t3 0]) s fun t =>
      (t.gpr .t3 = BitVec.twoPow 64 (mrA c % 64) ∧ t.mem = s.mem) ∧ Keep [.t3] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h3, hs.ld hZ, hs.al8 hZ hal, BitVec.add_zero, hL]
  refine WP.mono hld fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (repeat16_ok s₁ hj) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  have hb : WP isa (.block [.logic .and .t3 .t3 .t4, .li .t2 0, .sltu .s3 .t2 .t3, .sub .s3 .t2 .s3]) s₂ fun t =>
      (t.gpr .s3 = mask (decide (j < mrSig c)) ∧ t.mem = s₂.mem) ∧ Keep [.t2, .t3, .s3] s₂ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li (show imm12 0 by decide), a4, (k2.gpr (by decide)).trans a3]
    rw [show (BitVec.ofNat 64 0 : BitVec 64) = 0#64 from rfl, nz_mask, sig_word hj]
  exact WP.mono hb fun t ⟨⟨a, m⟩, k⟩ => ⟨⟨a, by rw [m, m2, m1]⟩, ((k1.trans k2).trans k).mono (by decide)⟩

theorem halfCond_eq (j : Nat) : halfCond j =
    .seq (.block (markerAddr .t3 ++ (condMid j ++ (base .t3 aE ++ base .t4 aE)))) halfPass := by
  simp only [halfCond, condMid, List.append_assoc]

/-- The registers `expSetup` writes. -/
def prepRegs : List Reg := [.t2, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4]

/-- A conditional halving of array 27, in place, under the mask of `σ > j`. -/
theorem halfCond_ok {s : State} {B : Addr} {Z w c : Nat} (h : Env s B Z w)
    (hL : s.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64)) {j : Nat}
    (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    WP isa (halfCond j) s fun t =>
      A t.mem B w aE = (if j < mrSig c then A s.mem B w aE / 2 else A s.mem B w aE) ∧
      Outside B (slot w aE) (8 * w) s.mem t.mem ∧ Keep prepRegs s t := by
  have hE := h.arr (show aE < 28 by decide)
  have hw := h.hw
  have hw' := h.hw'
  rw [halfCond_eq]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (markerAddr_ok h (Or.inl rfl)) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (condMid_ok (c := c) (h.hs.congr k1.2.2) (by omega_arith) (h.al aE w) a14 (by rw [m1]; exact hL) hj)
    fun s₂ ⟨⟨a9, m2⟩, k2⟩ => ?_
  have e2 := (h.keep k1 (by decide)).keep k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e2.base (rd := .t3) (by decide) aE) fun s₃ ⟨⟨a15, m3⟩, k3⟩ => ?_
  refine WP.mono ((e2.keep k3 (by decide)).base (rd := .t4) (by decide) aE)
    fun s₄ ⟨⟨a16, m4⟩, k4⟩ => ?_
  have k14 := ((k1.trans k2).trans k3).trans k4
  refine WP.mono (halfPass_ok (h.hs.congr k14.2.2) ((k4.gpr (by decide)).trans a15) a16
    (((k3.trans k4).gpr (by decide)).trans a9) ((k14.gpr (by decide)).trans h.t0) (by omega_arith) hw'
    (by omega_arith) (by omega_arith) (slot_al w aE) (slot_al w aE) (Or.inl rfl)) fun t ⟨hv, ho, k⟩ => ?_
  have hm : s₄.mem = s.mem := by rw [m4, m3, m2, m1]
  rw [hm] at hv ho
  refine ⟨?_, ho, (k14.trans k).mono (by decide)⟩
  rw [A, hv]
  simp only [decide_eq_true_eq]

/-- `halfCond_ok` within `Env`, keeping the word after array 27. -/
theorem halfCond_step {s : State} {B : Addr} {Z w c e : Nat} (h : Env s B Z w)
    (hL : s.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64))
    (he : A s.mem B w aE = e) {j : Nat} (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    WP isa (halfCond j) s fun t => (Env t B Z w ∧
      t.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64) ∧
      A t.mem B w aE = (if j < mrSig c then e / 2 else e) ∧
      Outside B (slot w aE) (8 * (w + 2)) s.mem t.mem) ∧ Keep prepRegs s t := by
  have hE := h.arr (show aE < 28 by decide)
  have hn := h.hs.nowrap
  refine WP.mono (halfCond_ok h hL hj) fun t ⟨hv, ho, k⟩ => ⟨⟨h.keep k (by decide), ?_, by rw [hv, he], ?_⟩, k⟩
  · rw [← hL]; exact Outside.word ho (Or.inr (by omega_arith)) (by omega_arith)
  · exact Outside.mono ho (Nat.le_refl _) (by omega_arith)

/-- `expSetup`: `E = (c − 1) / 2^σ` in array 27, and after its `w` words the
lowest set bit of `c − 1`'s lowest nonzero word. -/
theorem expSetup_ok {s : State} {B : Addr} {Z w c : Nat} (h : Env s B Z w) (hn : A s.mem B w 0 = c)
    (hodd : c % 2 = 1) (hc1 : 1 < c) :
    WP isa expSetup s fun t => (A t.mem B w aE = mrE c ∧
      t.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64) ∧
      Outside B (slot w aE) (8 * (w + 2)) s.mem t.mem) ∧ Keep prepRegs s t := by
  have hE := h.arr (show aE < 28 by decide)
  have h0E : slot w 0 + 8 * (w + 2) ≤ slot w aE := slot_lt (by decide)
  have hnw := h.hs.nowrap
  have hw := h.hw
  have hw' := h.hw'
  obtain ⟨hN, hm2⟩ := VG.Proof.RsaKeyGen.splitTwos_spec (c - 1) (by omega_arith)
  change c - 1 = (Spec.Rsa.splitTwos (c - 1)).2 * 2 ^ mrA c at hN
  obtain ⟨-, hx1, hx0⟩ := VG.Proof.RsaKeyGen.lowWord_bits hN hm2
  unfold expSetup
  refine WP.seq (WP.mono (lowWord_ok h hn hodd hc1) fun s₁ ⟨⟨h6, m1⟩, k1⟩ => ?_)
  have e1 := h.keep k1 (by decide)
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (lowBit_ok e1 (k := mrA c % 64) (Nat.mod_lt _ (by decide)) rfl (by rw [h6]; exact hx1)
    (fun j hj => by rw [h6]; exact hx0 j hj)) fun s₂ ⟨m2, k2⟩ => ?_
  have e2 := e1.keep k2 (by decide)
  rw [WP.block_append_iff]
  have h9 : WP isa (.block [.li .s3 (-1)]) s₂ fun t =>
      (t.gpr .s3 = mask true ∧ t.mem = s₂.mem) ∧ Keep [.s3] s₂ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li (show imm12 (-1) by decide)]
    rfl
  refine WP.mono h9 fun s₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  have e3 := e2.keep k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e3.base (rd := .t3) (by decide) 0) fun s₄ ⟨⟨a15, m4⟩, k4⟩ => ?_
  have e4 := e3.keep k4 (by decide)
  refine WP.mono (e4.base (rd := .t4) (by decide) aE) fun s₅ ⟨⟨a16, m5⟩, k5⟩ => ?_
  have e5 := e4.keep k5 (by decide)
  have k15 := (((k1.trans k2).trans k3).trans k4).trans k5
  have hm5 : s₅.mem = s.mem.writeW (off B (slot w aE + 8 * w)) (BitVec.twoPow 64 (mrA c % 64)) := by
    rw [m5, m4, m3, m2, m1]
  have hwr : Outside B (slot w aE + 8 * w) 8 s.mem s₅.mem := by rw [hm5]; exact writeW_outside _ _ _ (by omega_arith)
  have hL5 : s₅.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64) := by
    rw [hm5]; exact word_writeW_self _ _ _ _
  have hc5 : A s₅.mem B w 0 = c := by
    rw [A, Outside.wordsVal hwr (Or.inl (by omega_arith)) (by omega_arith)]; exact hn
  refine WP.seq (WP.mono (halfPass_ok e5.hs (mb := true) ((k5.gpr (by decide)).trans a15) a16
    (((k4.trans k5).gpr (by decide)).trans a9) e5.t0 (by omega_arith) hw' (by omega_arith) (by omega_arith)
    (slot_al w 0) (slot_al w aE) (Or.inr (Or.inr (by omega_arith)))) fun s₆ ⟨hv6, ho6, k6⟩ => ?_)
  rw [show wordsVal s₅.mem B (slot w 0) w = A s₅.mem B w 0 from rfl, hc5, ite_eq_left rfl] at hv6
  have e6 := e5.keep k6 (by decide)
  have hL6 : s₆.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64) := by
    rw [← hL5]; exact Outside.word ho6 (Or.inr (by omega_arith)) (by omega_arith)
  refine WP.seq (WP.mono (halfCond_step e6 hL6 hv6 (j := 1) (by decide)) fun s₇ ⟨⟨e7, hL7, hv7, ho7⟩, k7⟩ => ?_)
  refine WP.seq (WP.mono (halfCond_step e7 hL7 hv7 (j := 2) (by decide)) fun s₈ ⟨⟨e8, hL8, hv8, ho8⟩, k8⟩ => ?_)
  refine WP.mono (halfCond_step e8 hL8 hv8 (j := 3) (by decide)) fun t ⟨⟨_, hLt, hvt, hot⟩, kt⟩ => ?_
  refine ⟨⟨?_, hLt, ?_⟩, ((((k15.trans k6).trans k7).trans k8).trans kt).mono (by decide)⟩
  · rw [hvt, ← VG.Proof.RsaKeyGen.mrE_halves hodd]
  · refine Outside.trans (Outside.mono hwr (by omega_arith) (by omega_arith)) (Outside.trans ?_ (Outside.trans ho7
      (Outside.trans ho8 hot)))
    exact Outside.mono ho6 (Nat.le_refl _) (by omega_arith)

end VG.Proof.MillerRabin.RISCV64
