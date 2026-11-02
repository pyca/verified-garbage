module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Double64
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Bignum.RISCV64.ModArith
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Bignum.RISCV64.MontRounds
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Multiword arithmetic on RISC-V: reductions of byte strings and masked sums

* `dbl64In_ok`: the accumulator := `2 x + b`, for a bit `b` in `s4`;
  `doubleBitMod64_ok`: `x := 2 x + b mod m`, `b` the top bit of `s7`;
* `reduce64_ok`: `x mod m` into array 1, for the bytes of `x` (most
  significant first) at `s9`, a doubling per bit, as PPC64LE's;
* `addMask64_ok`: `[t3] += [t4] & mask`, modulo `2^(64 w)`.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.ModArith

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.ModArith VG.Impl.Bignum.RISCV64.PublicChecked
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)

/-! ## Doublings with a bit in -/

/-- `dbl64In`, `x` (`w` words) at `dX` (`a2`), the accumulator at `dA` (`a5`)
and a bit `b` in `s4`: the accumulator's `w + 1` words are `2 x + b`. -/
theorem dbl64In_ok {s : State} {B : Addr} {Z dA dX w : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .a5 = off B dA) (h2 : s.gpr .a2 = off B dX) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (h4 : (s.gpr .s4).toNat ≤ 1) (hA8 : dA % 8 = 0) (hX8 : dX % 8 = 0)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : dA + 8 * (w + 1) ≤ Z)
    (hX : dX + 8 * w ≤ Z) (dXA : dX + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dX) :
    WP isa dbl64In s fun s' =>
      wordsVal s'.mem B dA (w + 1) = 2 * wordsVal s.mem B dX w + (s.gpr .s4).toNat ∧
      Outside B dA (8 * (w + 1)) s.mem s'.mem ∧ Keep dblWRegs s s' := by
  have hnw := hs.nowrap
  unfold dbl64In
  have hpre : WP isa (.block [.addi .t3 .a5 0, .addi .t4 .a2 0, .addi .t5 .t0 0]) s
      fun s₁ => (s₁.gpr .t3 = off B dA ∧ s₁.gpr .t4 = off B dX ∧ s₁.gpr .t5 = BitVec.ofNat 64 w ∧
        s₁.gpr .s4 = s.gpr .s4 ∧ s₁.mem = s.mem) ∧ Keep dblWRegs s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h5, h2, ht0, BitVec.add_zero]
  refine WP.seq (WP.mono hpre fun s₁ ⟨⟨i3, i4, i5, i20, im⟩, k₁⟩ => ?_)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (dA + 8 * i) ∧ t.gpr .t4 = off B (dX + 8 * i) ∧ (t.gpr .s4).toNat ≤ 1 ∧
      Outside B dA (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dA i + 2 ^ (64 * i) * (t.gpr .s4).toNat = 2 * wordsVal s.mem B dX i + (s.gpr .s4).toNat ∧
      Keep dblWRegs s₁ t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .d .s2 .t4 0, .shift .sll .d .s3 .s2 1,
      .add .s3 .s3 .s4, .shift .srl .d .s4 .s2 63, .store .d .s3 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8] ++
      ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w) (by omega) (by omega) Inv
    (fun i hi t ⟨j3, j4, j20, jout, jv, jk⟩ hc => ?_)
    ⟨by rw [i3]; rfl, by rw [i4]; rfl, by rw [i20]; exact h4, by rw [← im]; exact Outside.refl _ _ _ _,
      by simp [wordsVal, i20], Keep.refl _ _⟩ i5)
    fun t ⟨t3, _, _, tout, tv, tk⟩ => ?_)
  · have hs' := hs.congr (k₁.trans jk).2.2
    have hst : WP isa (.block [.load .d .s2 .t4 0, .shift .sll .d .s3 .s2 1, .add .s3 .s3 .s4,
        .shift .srl .d .s4 .s2 63, .store .d .s3 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8, .addi .t5 .t5 (-1)]) t
        fun t' => (t'.gpr .t3 = off B (dA + 8 * i + 8) ∧ t'.gpr .t4 = off B (dX + 8 * i + 8) ∧
          t'.gpr .s4 = word t.mem B (dX + 8 * i) >>> 63 ∧
          t'.mem = t.mem.writeW (off B (dA + 8 * i)) (word t.mem B (dX + 8 * i) <<< 1 + t.gpr .s4) ∧
          t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ∧ Keep dblWRegs t t' := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [j3, j4, hs'.ld (show dX + 8 * i + 8 ≤ Z by omega), hs'.st (show dA + 8 * i + 8 ≤ Z by omega),
        hs'.al8 (show dX + 8 * i + 8 ≤ Z by omega) (by omega),
        hs'.al8 (show dA + 8 * i + 8 ≤ Z by omega) (by omega), BitVec.add_zero]
    refine WP.mono hst fun t' ⟨⟨u3, u4, u20, um, u5⟩, uk⟩ => ⟨⟨u3.trans (by rw [Nat.mul_succ, Nat.add_assoc]),
      u4.trans (by rw [Nat.mul_succ, Nat.add_assoc]), ?_, ?_, ?_, Keep.trans' jk uk⟩, u5⟩
    · have := (dbl64_arith (word t.mem B (dX + 8 * i)) (t.gpr .s4) j20).2
      rw [u20]; exact this
    · rw [um]
      exact (jout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside t.mem B (d := dA + 8 * i) _ (by omega)).mono (by omega) (by omega))
    · have e := dbl64_arith (word t.mem B (dX + 8 * i)) (t.gpr .s4) j20
      have wx : word t.mem B (dX + 8 * i) = word s.mem B (dX + 8 * i) := jout.word (by omega) (by omega)
      rw [um, fin64_wordsVal_write_top _ _ _ _ _ (by omega), u20, Nat.mul_succ, Nat.pow_add,
        wordsVal_succ_top s.mem B dX i]
      rw [wx] at e
      rw [wx]
      have := e.1
      grind
  · have hst : WP isa (.block [.store .d .s4 .t3 0]) t fun t' =>
        t' = { t with mem := t.mem.writeW (off B (dA + 8 * w)) (t.gpr .s4) } := by
      brun [t3, (hs.congr (k₁.trans tk).2.2).st (show dA + 8 * w + 8 ≤ Z by omega),
        (hs.congr (k₁.trans tk).2.2).al8 (show dA + 8 * w + 8 ≤ Z by omega) (by omega), BitVec.add_zero]
    refine WP.mono hst fun t' e => ?_
    subst e
    refine ⟨?_, ?_, Keep.trans' k₁ ((tk.trans (Keep.mem _ _)).mono (by decide))⟩
    · show wordsVal (t.mem.writeW (off B (dA + 8 * w)) (t.gpr .s4)) B dA (w + 1) = _
      rw [fin64_wordsVal_write_top _ _ _ _ _ (by omega), tv]
    · exact (tout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside t.mem B (d := dA + 8 * w) _ (by omega)).mono (by omega) (by omega))

/-- The registers `doubleBitMod64` writes. -/
def dbmRegs : List Reg := [.a0, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4, .s7]

theorem top_bit_le (x : BitVec 64) : (x >>> 63).toNat ≤ 1 := by
  have := x.isLt
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega

/-- `doubleBitMod64`, in the arrays of the working space (`m` in array 0, `x`
in array 1, the accumulator and the temporary in arrays 2 and 3): `x := 2 x +
b mod m` for the top bit `b` of `s7`, which is shifted left, changing only
arrays 1–3. -/
theorem doubleBitMod64_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .a5 = off B (slot w 2)) (h6 : s.gpr .a6 = off B (slot w 3))
    (h7 : s.gpr .a7 = off B (slot w 0)) (h2 : s.gpr .a2 = off B (slot w 1))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hx : wordsVal s.mem B (slot w 1) w < wordsVal s.mem B (slot w 0) w) :
    WP isa doubleBitMod64 s fun t =>
      wordsVal t.mem B (slot w 1) w =
        (2 * wordsVal s.mem B (slot w 1) w + (s.gpr .s7 >>> 63).toNat) % wordsVal s.mem B (slot w 0) w ∧
      t.gpr .s7 = s.gpr .s7 <<< 1 ∧
      Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep dbmRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  have al := slot_al8 w
  unfold doubleBitMod64
  refine WP.seq (WP.mono (WP.keep [.s4, .s7] (Q := fun t => t.gpr .s4 = s.gpr .s7 >>> 63 ∧
      t.gpr .s7 = s.gpr .s7 <<< 1 ∧ t.mem = s.mem) (by brun) (by rfl) (by rfl))
    fun s₁ ⟨⟨b4, b7, bm⟩, k₁⟩ => ?_)
  have g1 : ∀ r ∈ [Reg.a2, .a5, .a6, .a7, .t0], s₁.gpr r = s.gpr r := fun r hr =>
    k₁.gpr (by revert r hr; decide)
  have hs₁ := hs.congr k₁.2.2
  refine WP.seq (WP.mono (dbl64In_ok (dA := slot w 2) (dX := slot w 1) hs₁
    (by rw [g1 .a5 (by decide), h5]) (by rw [g1 .a2 (by decide), h2]) (by rw [g1 .t0 (by decide), ht0])
    (by rw [b4]; exact top_bit_le _) (al 2) (al 1) hw hw' (by omega) (by omega) (by omega))
    fun s₂ ⟨hd, out₂, k₂⟩ => ?_)
  rw [bm, b4] at hd
  have hs₂ := hs₁.congr k₂.2.2
  have k12 := k₁.trans k₂
  have g2 : ∀ r ∈ [Reg.a2, .a5, .a6, .a7, .t0], s₂.gpr r = s.gpr r := fun r hr =>
    k12.gpr (by revert r hr; decide)
  have m₂ : wordsVal s₂.mem B (slot w 0) w = wordsVal s.mem B (slot w 0) w := by
    rw [← bm]; exact Outside.wordsVal out₂ (by omega) (by omega)
  refine WP.seq (WP.mono (subMod64_ok (w := w) (dA := slot w 2) (dT := slot w 3) (dM := slot w 0) hs₂
    (by rw [g2 .a5 (by decide), h5]) (by rw [g2 .a6 (by decide), h6])
    (by rw [g2 .a7 (by decide), h7]) (by rw [g2 .t0 (by decide), ht0]) hw hw' (al 2) (al 3) (al 0)
    (by omega) (by omega) (by omega) (by omega) (by omega))
    fun s₃ ⟨⟨c, hc, hD, h20'⟩, out₃, k₃⟩ => ?_)
  rw [m₂] at hD
  have hs₃ := hs₂.congr k₃.2.2
  have k13 := k12.trans k₃
  have accA : wordsVal s₃.mem B (slot w 2) w = wordsVal s₂.mem B (slot w 2) w :=
    Outside.wordsVal out₃ (by omega) (by omega)
  refine WP.mono (selectAcc64_ok (w := w) (dA := slot w 2) (dT := slot w 3) (dO := slot w 1)
    (b := decide ((word s₂.mem B (slot w 2 + 8 * w)).toNat < c)) hs₃
    (by rw [k13.gpr (by decide), h5]) (by rw [k13.gpr (by decide), h6])
    (by rw [k13.gpr (by decide), h2]) (by rw [k13.gpr (by decide), ht0])
    (by rw [h20']; simp only [decide_eq_true_eq]) hw hw' (al 2) (al 3) (al 1) (by omega) (by omega) (by omega)
    (by omega) (by omega))
    fun t ⟨hv, out₄, k₄⟩ => ⟨?_, ?_, ?_, (k13.trans k₄).mono (by decide)⟩
  · rw [accA] at hv
    have hM := wordsVal_lt s.mem B (slot w 0) w
    have hb := top_bit_le (s.gpr .s7)
    rw [wordsVal_succ_top] at hd
    rw [hv, ← hd, ← Nat.add_zero (word s₂.mem B (slot w 2 + 8 * w)).toNat, ← Nat.mul_zero (2 ^ 64),
      ← VG.Proof.Bignum.csub_result hM (wordsVal_lt _ _ _ _) hc (wordsVal_lt _ _ _ _)
        (by rw [Nat.mul_zero, Nat.add_zero, hd]; omega) hD]
    by_cases h : (word s₂.mem B (slot w 2 + 8 * w)).toNat < c <;> simp [h]
  · rw [(k₂.trans (k₃.trans k₄)).gpr (by decide), b7]
  · rw [bm] at out₂
    exact ((Outside.mono out₂ (by omega) (by omega)).trans (Outside.mono out₃ (by omega) (by omega))).trans
      (Outside.mono out₄ (by omega) (by omega))

/-- `w` words of zeros are the number 0. -/
theorem ma_wordsVal_zero {m : Mem} {B : Addr} {d : Nat} : ∀ {w : Nat}, (∀ i < w, word m B (d + 8 * i) = 0) →
    wordsVal m B d w = 0
  | 0, _ => rfl
  | w + 1, h => by
    rw [wordsVal_succ_top, ma_wordsVal_zero fun i hi => h i (by omega),
      show Mont.word m B (d + 8 * w) = 0 from h w (by omega)]; rfl

/-! ## Reducing a byte string -/

theorem ma_li8 {s : State} {d : Reg} : exec (.li d 8) s = some (s.write d (BitVec.ofNat 64 8)) := by
  rw [exec_li (by decide)]; rfl

/-- The registers the reduction writes. -/
def redRegs : List Reg := [.a0, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4, .s7, .s8, .s9, .s10]

/-- Between the bits of the scan from `s`: the arrays' bases in place, and the
accumulator (array 1) is `c mod N`, with only arrays 1–3 changed. -/
def RInv (s : State) (B : Addr) (w N c : Nat) (t : State) : Prop :=
  Keep redRegs s t ∧ Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧
    wordsVal t.mem B (slot w 1) w = c % N ∧ t.gpr .a2 = off B (slot w 1) ∧ t.gpr .a5 = off B (slot w 2) ∧
    t.gpr .a6 = off B (slot w 3)

theorem mod_double_bit (c N b : Nat) : (2 * (c % N) + b) % N = (2 * c + b) % N := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

/-- A shift left by one of the scanned bits: the bit shifted out and the rest. -/
theorem shl1_step (x : BitVec 64) :
    (x <<< 1).toNat = 2 * x.toNat - 2 ^ 64 * (x >>> 63).toNat := by
  have := x.isLt
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- `reduceByte`: the eight bits of the byte at `s9` scanned, `c := 256 c + b`. -/
theorem reduceByte_ok {s t : State} {B D : Addr} {Z w N c i : Nat} (hs : Scr s B Z) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hNd : wordsVal s.mem B (slot w 0) w = N) (hN : 0 < N)
    (ht : RInv s B w N c t) (h9 : t.gpr .s9 = off D i) (hrd : InRegions (t.rd ++ t.wr) (off D i) 1) :
    WP isa reduceByte t fun t' =>
      RInv s B w N (256 * c + (t.mem (off D i)).toNat) t' ∧ t'.gpr .s9 = off D (i + 1) ∧
        t'.gpr .s10 = t.gpr .s10 := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  obtain ⟨kt, ot, tv, t2, t5, t6⟩ := ht
  generalize hb : (t.mem (off D i)).toNat = b
  have hb256 : b < 256 := by rw [← hb]; exact (t.mem (off D i)).isLt
  unfold reduceByte
  refine WP.seq (WP.mono (WP.keep [.s7, .s9, .s8] (Q := fun t₁ =>
    t₁.gpr .s7 = BitVec.ofNat 64 b <<< 56 ∧ t₁.gpr .s9 = off D (i + 1) ∧ t₁.gpr .s8 = BitVec.ofNat 64 8 ∧
      t₁.mem = t.mem) ?_ (by rfl) (by rfl)) fun t₁ ⟨⟨a7', a9, a8, m1⟩, k1⟩ => ?_)
  · brun [h9, hrd, read_byte64, hb, ma_li8, add_ofNat_zero]
  let Inv : Nat → State → Prop := fun j u =>
    (∃ c', c' * 2 ^ 64 + (u.gpr .s7).toNat = (256 * c + b) * 2 ^ 56 * 2 ^ j ∧ RInv s B w N c' u) ∧
      u.gpr .s9 = off D (i + 1) ∧ u.gpr .s10 = t.gpr .s10
  refine WP.mono (wp_countdown (cnt := .s8) (N := 8) (by decide) (by decide) Inv
    (fun j _ u ⟨⟨c', hc, ku, ou, uv, u2, u5, u6⟩, u9, u10⟩ _ => ?_)
    ⟨⟨c, ?_, Keep.trans' kt (k1.mono (by decide)), by rw [m1]; exact ot, by rw [m1]; exact tv,
      by rw [k1.gpr (by decide)]; exact t2, by rw [k1.gpr (by decide)]; exact t5,
      by rw [k1.gpr (by decide)]; exact t6⟩, a9, k1.gpr (by decide)⟩ a8)
    fun u ⟨⟨c', hc, hu⟩, u9, u10⟩ => ⟨?_, u9, u10⟩
  · have g : ∀ r ∈ [Reg.a7, .t0], u.gpr r = s.gpr r := fun r hr => ku.gpr (by revert r hr; decide)
    have hN₁ : wordsVal u.mem B (slot w 0) w = N := (Outside.wordsVal ou (by omega_arith) (by omega_arith)).trans hNd
    refine WP.seq (WP.mono (doubleBitMod64_ok (hs.congr ku.2.2) u5 u6 ((g .a7 (by simp)).trans h7) u2
      ((g .t0 (by simp)).trans ht0) hw hw' hZ (by rw [uv, hN₁]; exact Nat.mod_lt _ hN))
      fun u₁ ⟨hv, a7'', out₁, k'⟩ => ?_)
    refine WP.mono (dec_ok u₁ .s8) fun u₂ e => ?_
    subst e
    refine ⟨⟨⟨2 * c' + (u.gpr .s7 >>> 63).toNat, ?_,
      Keep.trans' ku (Keep.trans' (k'.mono (by decide)) ((Keep.write _ _ _).mono (by decide))),
      ou.trans out₁, by rw [mem_write, hv, hN₁, uv, mod_double_bit], ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]
      rw [a7'', shl1_step, show (2 : Nat) ^ (j + 1) = 2 ^ j * 2 from Nat.pow_succ 2 j, ← Nat.mul_assoc]
      have hlt := (u.gpr .s7).isLt
      have h63 : (u.gpr .s7 >>> 63).toNat = (u.gpr .s7).toNat / 2 ^ 63 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      rw [h63]
      generalize (u.gpr .s7).toNat = r at hc hlt ⊢
      generalize (256 * c + b) * 2 ^ 56 * 2 ^ j = Y at hc ⊢
      omega_using [hc, hlt]
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k'.gpr (by decide)]; exact u2
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k'.gpr (by decide)]; exact u5
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k'.gpr (by decide)]; exact u6
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k'.gpr (by decide)]; exact u9
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k'.gpr (by decide)]; exact u10
    · simp only [gpr_write, ↓reduceIte]; rw [k'.gpr (by decide)]
  · rw [a7', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    omega_arith
  · have hc' : c' = 256 * c + b := by
      have := (u.gpr .s7).isLt
      rw [show (256 * c + b) * 2 ^ 56 * 2 ^ 8 = (256 * c + b) * 2 ^ 64 by rw [Nat.mul_assoc]] at hc
      omega_arith
    rw [← hc']; exact hu

/-- `reduceScan`: the `L ≥ 1` bytes at `D` (`s9`, `s10`) scanned, most
significant first, apart from the working space. -/
theorem reduceScan_ok {s t : State} {B D : Addr} {Z w N L : Nat} (hs : Scr s B Z) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hNd : wordsVal s.mem B (slot w 0) w = N) (hN : 0 < N)
    (hL : 1 ≤ L) (hL' : L < 2 ^ 63) (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x)
    (ht : RInv s B w N 0 t) (h9 : t.gpr .s9 = off D 0) (h10 : t.gpr .s10 = BitVec.ofNat 64 L) :
    WP isa reduceScan t (RInv s B w N (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L))) := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e1 := e 1; have e4 := e 4
  let Inv : Nat → State → Prop := fun i u =>
    RInv s B w N (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D i)) u ∧ u.gpr .s9 = off D i
  refine WP.mono (wp_countdown (cnt := .s10) (N := L) (by omega_arith) (by omega_arith) Inv
    (fun i hi u ⟨hu, u9⟩ _ => ?_) ⟨ht, h9⟩ h10) fun u h => h.1
  have hb : u.mem (off D i) = s.mem (off D i) := by
    refine hu.2.1 _ (Or.inr ?_)
    by_contra hc
    exact hsep i hi (off D i) (by simp only [ofs] at hc ⊢; omega_arith) rfl
  refine WP.seq (WP.mono (reduceByte_ok hs hw hw' hZ h7 ht0 hNd hN hu u9
    (by rw [hu.1.2.1, hu.1.2.2]; exact hrd i hi)) fun u₁ ⟨hu₁, a9, a10⟩ => ?_)
  refine WP.mono (dec_ok u₁ .s10) fun u₂ e => ?_
  subst e
  obtain ⟨k₁, o₁, v₁, u2, u5, u6⟩ := hu₁
  refine ⟨⟨⟨Keep.trans' k₁ ((Keep.write _ _ _).mono (by decide)), o₁, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [mem_write, v₁, hb, Pub.bytesAt_succ, VG.Proof.Rsa.os2ip_snoc]
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact u2
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact u5
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact u6
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact a9
  · simp only [gpr_write, ↓reduceIte]; rw [a10]

/-- `reduce64`: `x mod m` into array 1, for `m` (not zero) in array 0 and the
`L ≥ 1` bytes of `x` at `D` (`s9`, `s10`), most significant first, apart
from the working space; only arrays 1–3 change. -/
theorem reduce64_ok {s : State} {B D : Addr} {Z w L : Nat} (hs : Scr s B Z) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hN : 0 < wordsVal s.mem B (slot w 0) w)
    (h9 : s.gpr .s9 = off D 0) (h10 : s.gpr .s10 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x) :
    WP isa reduce64 s fun t =>
      (wordsVal t.mem B (slot w 1) w =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) % wordsVal s.mem B (slot w 0) w ∧
        Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem) ∧
      Keep (redRegs ++ ([.a2, .a5, .a6] : List Reg)) s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  have al := slot_al8 w
  unfold reduce64
  refine WP.seq (WP.mono (Pub.base_ok (rd := .t3) (by decide) h7 h5 1) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr k1.2.2) a3 ((k1.gpr (by decide)).trans ht0) hw hw'
    (al 1) (by omega_arith)) fun s₂ ⟨⟨_, hz, out₂⟩, k₂⟩ => ?_)
  have k12 := k1.trans k₂
  rw [m1] at out₂
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) ((k12.gpr (by decide)).trans h7)
    ((k12.gpr (by decide)).trans h5) 1) fun s₃ ⟨⟨a2, m3⟩, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide)
    ((k3.gpr (by decide)).trans ((k12.gpr (by decide)).trans h7))
    ((k3.gpr (by decide)).trans ((k12.gpr (by decide)).trans h5)) 2) fun s₄ ⟨⟨a5, m4⟩, k4⟩ => ?_
  have k14 := (k12.trans k3).trans k4
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k14.gpr (by decide)).trans h7)
    ((k14.gpr (by decide)).trans h5) 3) fun s₅ ⟨⟨a6, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  have m25 : s₅.mem = s₂.mem := m5.trans (m4.trans m3)
  have o25 : Outside B (slot w 1) (24 * (w + 2)) s.mem s₅.mem := by
    rw [m25]; exact Outside.mono out₂ (Nat.le_refl _) (by omega_arith)
  have hNd : wordsVal s₅.mem B (slot w 0) w = wordsVal s.mem B (slot w 0) w :=
    Outside.wordsVal o25 (by omega_arith) (by omega_arith)
  have hrd5 : ∀ i < L, InRegions (s₅.rd ++ s₅.wr) (off D i) 1 := by
    rw [k15.2.1, k15.2.2]; exact hrd
  have hz5 : wordsVal s₅.mem B (slot w 1) w = 0 := by
    rw [m25]
    exact ma_wordsVal_zero hz
  refine WP.mono (reduceScan_ok (s := s₅) (hs.congr k15.2.2) hw hw' hZ ((k15.gpr (by decide)).trans h7)
    ((k15.gpr (by decide)).trans ht0) hNd hN hL hL' hrd5 hsep
    ⟨Keep.refl _ _, Outside.refl _ _ _ _, by rw [hz5, Nat.zero_mod], (k5.gpr (by decide)).trans ((k4.gpr (by decide)).trans a2),
      (k5.gpr (by decide)).trans a5, a6⟩ ((k15.gpr (by decide)).trans h9) ((k15.gpr (by decide)).trans h10))
    fun t ⟨kt, ot, tv, _, _, _⟩ => ⟨⟨?_, o25.trans ot⟩, (k15.trans kt).mono (by decide)⟩
  have hbytes : Spec.Rsa.bytesAt s₅.mem D L = Spec.Rsa.bytesAt s.mem D L := by
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    show s₅.mem (off D i) = s.mem (off D i)
    refine o25 _ (Or.inr ?_)
    by_contra hc
    exact hsep i hi (off D i) (by simp only [ofs] at hc ⊢; omega_arith) rfl
  rw [tv, hbytes]

/-! ## Masked sums -/

/-- A word of `addMask64`: `x + (y & mask) + c` is the low word of the two
additions and `2⁶⁴` times their carries, which are never both set. -/
theorem add_arith (x y c : BitVec 64) (hc : c.toNat ≤ 1) :
    (x + y + c).toNat + 2 ^ 64 * ((if x + y + c < c then (1 : BitVec 64) else 0) |||
        (if x + y < y then 1 else 0)).toNat = x.toNat + y.toNat + c.toNat ∧
      ((if x + y + c < c then (1 : BitVec 64) else 0) ||| (if x + y < y then 1 else 0)).toNat ≤ 1 := by
  have hx := x.isLt
  have hy := y.isLt
  have hc' := c.isLt
  have A : (x + y).toNat = (x.toNat + y.toNat) % 2 ^ 64 := BitVec.toNat_add x y
  have Bq : (x + y + c).toNat = ((x + y).toNat + c.toNat) % 2 ^ 64 := BitVec.toNat_add _ _
  have o00 : ((0 : BitVec 64) ||| 0).toNat = 0 := by decide
  have o01 : ((0 : BitVec 64) ||| 1).toNat = 1 := by decide
  have o10 : ((1 : BitVec 64) ||| 0).toNat = 1 := by decide
  have o11 : ((1 : BitVec 64) ||| 1).toNat = 1 := by decide
  by_cases h1 : x + y < y <;> by_cases h2 : x + y + c < c <;>
    simp only [h1, h2, ite_true, ite_false, o00, o01, o10, o11] <;>
    rw [BitVec.lt_def] at h1 h2 <;> omega

theorem and_mask (y : BitVec 64) (b : Bool) :
    y &&& (if b then BitVec.allOnes 64 else 0) = if b then y else 0 := by
  cases b
  · show y &&& 0 = 0; exact BitVec.and_zero
  · show y &&& BitVec.allOnes 64 = y; exact BitVec.and_allOnes

/-- `addMask64`: `[t3] := [t3] + ([t4] & mask) mod 2^(64 w)`, the mask in
`s4` all ones (`b`) or zero, over `w` (`t0`) words. -/
theorem addMask64_ok {s : State} {B : Addr} {Z dT dM w : Nat} {b : Bool} (hs : Scr s B Z)
    (h3 : s.gpr .t3 = off B dT) (h4 : s.gpr .t4 = off B dM) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hm : s.gpr .s4 = if b then BitVec.allOnes 64 else 0) (hT8 : dT % 8 = 0) (hM8 : dM % 8 = 0)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hT : dT + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (dTM : dT + 8 * w ≤ dM ∨ dM + 8 * w ≤ dT) :
    WP isa addMask64 s fun s' =>
      wordsVal s'.mem B dT w =
        (wordsVal s.mem B dT w + (if b then wordsVal s.mem B dM w else 0)) % 2 ^ (64 * w) ∧
      Outside B dT (8 * w) s.mem s'.mem ∧ Keep [.t3, .t4, .t5, .s0, .s1, .s2, .s3] s s' := by
  have hnw := hs.nowrap
  unfold addMask64
  have hpre : WP isa (.block [.addi .t5 .t0 0, .li .s1 0]) s
      fun s₁ => (s₁.gpr .t5 = BitVec.ofNat 64 w ∧ s₁.gpr .s1 = 0 ∧ s₁.mem = s.mem) ∧
        Keep [.t5, .s1] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [ht0, fin64_exec_li_zero, BitVec.add_zero]
  refine WP.seq (WP.mono hpre fun s₁ ⟨⟨i5, i1, im⟩, k₁⟩ => ?_)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (dT + 8 * i) ∧ t.gpr .t4 = off B (dM + 8 * i) ∧ (t.gpr .s1).toNat ≤ 1 ∧
      Outside B dT (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dT i + 2 ^ (64 * i) * (t.gpr .s1).toNat =
        wordsVal s.mem B dT i + (if b then wordsVal s.mem B dM i else 0) ∧
      Keep [.t3, .t4, .t5, .s0, .s1, .s2, .s3] s t
  have body := fun (i : Nat) (hi : i < w) (t : State) (hI : Inv i t) =>
    show WP isa (.block ([.load .d .s2 .t3 0, .load .d .s3 .t4 0, .logic .and .s3 .s3 .s4, .add .s2 .s2 .s3,
      .sltu .s0 .s2 .s3, .add .s2 .s2 .s1, .sltu .s1 .s2 .s1, .logic .or .s1 .s1 .s0, .store .d .s2 .t3 0,
      .addi .t3 .t3 8, .addi .t4 .t4 8] ++ ([.addi .t5 .t5 (-1)] : List Instr))) t
        (fun t' => Inv (i + 1) t' ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) from by
    obtain ⟨j3, j4, j1, jout, jv, jk⟩ := hI
    have hs' := hs.congr jk.2.2
    have j44 : t.gpr .s4 = if b then BitVec.allOnes 64 else 0 := (jk.gpr (by decide)).trans hm
    have wT : word t.mem B (dT + 8 * i) = word s.mem B (dT + 8 * i) := jout.word (by omega) (by omega)
    have wM : word t.mem B (dM + 8 * i) = word s.mem B (dM + 8 * i) := jout.word (by omega) (by omega)
    refine WP.mono (WP.keep [.t3, .t4, .t5, .s0, .s1, .s2, .s3] (Q := fun t' =>
        t'.gpr .t3 = off B (dT + 8 * i + 8) ∧ t'.gpr .t4 = off B (dM + 8 * i + 8) ∧
        t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
        let y := word t.mem B (dM + 8 * i) &&& t.gpr .s4
        let x := word t.mem B (dT + 8 * i)
        t'.gpr .s1 = ((if x + y + t.gpr .s1 < t.gpr .s1 then (1 : BitVec 64) else 0) |||
          (if x + y < y then 1 else 0)) ∧
        t'.mem = t.mem.writeW (off B (dT + 8 * i)) (x + y + t.gpr .s1)) ?_ (by rfl) (by rfl))
      fun t' ⟨⟨u3, u4, u5, u1, um⟩, uk⟩ => ⟨⟨u3.trans (by rw [Nat.mul_succ, Nat.add_assoc]),
        u4.trans (by rw [Nat.mul_succ, Nat.add_assoc]), ?_, ?_, ?_, Keep.trans' jk uk⟩, u5⟩
    · brun [j3, j4, hs'.ld (show dT + 8 * i + 8 ≤ Z by omega), hs'.ld (show dM + 8 * i + 8 ≤ Z by omega),
        hs'.st (show dT + 8 * i + 8 ≤ Z by omega),
        hs'.al8 (show dT + 8 * i + 8 ≤ Z by omega) (by omega),
        hs'.al8 (show dM + 8 * i + 8 ≤ Z by omega) (by omega), BitVec.add_zero]
    · rw [u1]; exact (add_arith _ _ _ j1).2
    · rw [um]
      exact (jout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside t.mem B (d := dT + 8 * i) _ (by omega)).mono (by omega) (by omega))
    · have e := (add_arith (word t.mem B (dT + 8 * i)) (word t.mem B (dM + 8 * i) &&& t.gpr .s4) (t.gpr .s1) j1).1
      rw [j44, and_mask, wT, wM] at e
      rw [um, u1, j44, and_mask, wT, wM, fin64_wordsVal_write_top _ _ _ _ _ (by omega), Nat.mul_succ, Nat.pow_add,
        wordsVal_succ_top s.mem B dT i, wordsVal_succ_top s.mem B dM i]
      cases b <;> simp only [ite_true, ite_false, Bool.false_eq_true] at e jv ⊢ <;>
        grind
  refine WP.mono (wp_countdown (cnt := .t5) (N := w) (by omega) (by omega) Inv
    (fun i hi t hI _ => body i hi t hI)
    ⟨by rw [k₁.gpr (by decide), h3]; rfl, by rw [k₁.gpr (by decide), h4]; rfl, by rw [i1]; decide,
      by rw [← im]; exact Outside.refl _ _ _ _, by simp [wordsVal, i1], k₁.mono (by decide)⟩ i5)
    fun t ⟨_, _, t1, tout, tv, tk⟩ => ?_
  refine ⟨?_, tout, tk⟩
  have hlt := wordsVal_lt t.mem B dT w
  rw [← tv]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

end VG.Proof.Bignum.RISCV64.ModArith
