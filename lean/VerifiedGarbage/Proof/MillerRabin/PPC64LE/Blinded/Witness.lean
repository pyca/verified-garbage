module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.Ctx
import VerifiedGarbage.Proof.RsaKeyGen.WitnessBits
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Copy
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Prep
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# The blinded Miller–Rabin loop on PPC64LE: a draw's witness

For the draw `x` in array 4:

* `atLeast2_ok`: `r24 = 0` exactly when `x < 2`;
* `ltC_ok`: `r20` is all ones exactly when `(x | 1) < c` (`subMod` of a
  copy of `x | 1` in array 3, `wv_or_one`, and `c` into array 6);
* `force_ok`: `x` forced into the range, `(x | 2) mod 2^(64 t + b − 1)`
  (`wv_fallback`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Blinded

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Proof.Mont (val32 w32 val32_lt)
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE.Search VG.Impl.MillerRabin.PPC64LE.Blinded
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.Bignum (slot Frm wv word off writeW_outside word_writeW_self)

/-- `x >> 1` is zero exactly when `x < 2`. -/
theorem shr1_eq_zero (x : BitVec 64) : x >>> 1 = 0#64 ↔ x.toNat < 2 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.pow_one]
  omega

theorem or_eq_zero (x y : BitVec 64) : x ||| y = 0#64 ↔ x = 0#64 ∧ y = 0#64 := by
  constructor
  · intro h
    have hx : x = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_or] at this
      simp only [BitVec.toNat_ofNat, Nat.zero_mod] at this ⊢
      exact (Nat.or_eq_zero_iff.mp this).1
    subst hx
    rw [BitVec.zero_or] at h
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The registers `atLeast2` writes. -/
def a2Regs : List Reg := [.r3, .r5, .r6, .r24]

/-- `r24 = 0` exactly when the draw in array 4 is below 2. -/
theorem atLeast2_ok {s : State} {B : Addr} {Z w : Nat} (e : Env s B Z w) :
    WP isa atLeast2 s fun t =>
      ((t.gpr .r24 = 0#64 ↔ wv s.mem B (slot w 4) w < 2) ∧ t.mem = s.mem) ∧ Keep a2Regs s t := by
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  have es : slot w 4 = 256 + 4 * (8 * (w + 2)) := rfl
  unfold atLeast2
  refine WP.seq (WP.mono (WP.keep [.r5, .r6, .r24] (Q := fun u => u.gpr .r24 = word s.mem B (slot w 4) >>> 1 ∧
      u.gpr .r5 = off B (slot w 4 + 8) ∧ u.gpr .r6 = BitVec.ofNat 64 (w - 1) ∧ u.mem = s.mem) ?_ (by decide))
    fun u ⟨⟨u24, u5, u6, um⟩, ku⟩ => ?_)
  · rw [WP.block_append_iff]
    refine WP.mono (e.base (rd := .r5) (by decide) (by decide) 4) fun v ⟨⟨v5, vm⟩, kv⟩ => ?_
    have v11 : v.gpr .r11 = BitVec.ofNat 64 (2 * w) := (kv.gpr .r11 (by decide)).trans e.h11
    have hv : Scr v B Z := hs.congr kv.wr
    prun [v5, v11, vm, hv.ld (d := slot w 4) (n := 8) (by omega), BitVec.add_zero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    omega
  let Inv : Nat → State → Prop := fun j v =>
    (v.gpr .r5 = off B (slot w 4 + 8 * (j + 1)) ∧
      (v.gpr .r24 = 0#64 ↔ (word s.mem B (slot w 4)).toNat < 2 ∧
        ∀ i, 1 ≤ i → i ≤ j → word s.mem B (slot w 4 + 8 * i) = 0#64) ∧ v.mem = s.mem) ∧ Keep a2Regs s v
  refine WP.mono (wp_countdown (cnt := .r6) (N := w - 1) (by omega) (by omega) Inv
    (fun j hj v ⟨⟨v5, v24, vm⟩, kv⟩ _ => ?_)
    ⟨⟨by rw [u5, Nat.zero_add, Nat.mul_one], by rw [u24, shr1_eq_zero]; exact ⟨fun h => ⟨h, fun i h1 h2 => by omega⟩,
      fun h => h.1⟩, um⟩, ku.mono (by decide)⟩ u6) fun t ⟨⟨_, t24, tm⟩, kt⟩ => ⟨⟨?_, tm⟩, kt⟩
  · rw [WP.block_append_iff]
    have hv : Scr v B Z := hs.congr kv.wr
    refine WP.mono (WP.keep [.r3, .r5, .r24] (Q := fun x => x.gpr .r24 = v.gpr .r24 ||| word s.mem B (slot w 4 + 8 * (j + 1)) ∧
        x.gpr .r5 = off B (slot w 4 + 8 * (j + 2)) ∧ x.mem = s.mem) (by
          prun [v5, vm, hv.ld (d := slot w 4 + 8 * (j + 1)) (n := 8) (by omega), BitVec.add_zero]
          rw [show slot w 4 + 8 * (j + 1) + 8 = slot w 4 + 8 * (j + 2) by omega]) (by decide))
      fun x ⟨⟨x24, x5, xm⟩, kx⟩ => ?_
    refine WP.mono (subi_ok x .r6 (by decide)) fun y e => ?_
    subst e
    refine ⟨⟨⟨by simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact x5, ?_, by rw [mem_write, xm]⟩,
      (kv.trans (kx.trans (Keep.write _ _ _))).mono (by decide)⟩, by simp only [gpr_write, ↓reduceIte]; rw [kx.gpr .r6 (by decide)]⟩
    simp only [gpr_write, reduceCtorEq, ↓reduceIte]
    rw [x24, or_eq_zero, v24]
    constructor
    · rintro ⟨⟨h0, hi⟩, hj1⟩
      exact ⟨h0, fun i h1 h2 => by
        rcases Nat.lt_or_ge i (j + 1) with h | h
        · exact hi i h1 (by omega)
        · rw [show i = j + 1 by omega]; exact hj1⟩
    · rintro ⟨h0, hi⟩
      exact ⟨⟨h0, fun i h1 h2 => hi i h1 (by omega)⟩, hi (j + 1) (by omega) (by omega)⟩
  · rw [t24, VG.Proof.RsaKeyGen.wv_lt_two_iff s.mem B (slot w 4) (show 1 ≤ w by omega)]
    exact ⟨fun ⟨h0, hi⟩ => ⟨h0, fun i h1 h2 => hi i h1 (by omega)⟩, fun ⟨h0, hi⟩ => ⟨h0, fun i h1 h2 => hi i h1 (by omega)⟩⟩

/-- The registers `ltCMid` writes. -/
def ltCMidRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r8, .r9]

/-- The middle of `ltC`: `x | 1` in array 3, its word `w` zeroed, and `subMod`'s bases. -/
theorem ltCMid_ok {v : State} {B : Addr} {Z w : Nat} (ev : Env v B Z w) :
    WP isa (.block (base .r5 3 ++ ([.load .d .r3 .r5 0, .li .r4 1, .logic .or .r3 .r3 .r4, .store .d .r3 .r5 0,
        .lsl .r6 .r11 2, .add .r5 .r5 .r6, .li .r0 0, .store .d .r0 .r5 0] : List Instr) ++ base .r8 3 ++ base .r9 6))
      v fun x => (x.gpr .r8 = off B (slot w 3) ∧ x.gpr .r9 = off B (slot w 6) ∧
        x.mem = (v.mem.writeW (off B (slot w 3)) (word v.mem B (slot w 3) ||| 1#64)).writeW
          (off B (slot w 3 + 8 * w)) 0#64) ∧ Keep ltCMidRegs v x := by
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := ev.hZ
  have hw4 := ev.hw
  have hw128 := ev.hw'
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  refine WP.keep _ ?_ (by decide)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ev.base (rd := .r5) (by decide) (by decide) 3) fun y ⟨⟨y5, ym⟩, ky⟩ => ?_
  have ey : Env y B Z w := ev.keep ky (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (z : State) => (z.mem = (v.mem.writeW (off B (slot w 3)) (word v.mem B (slot w 3) ||| 1#64)).writeW
      (off B (slot w 3 + 8 * w)) 0#64) ∧ Keep [.r0, .r3, .r4, .r5, .r6] y z) (WP.keep _ ?_ (by decide))
    fun z ⟨zm, kz⟩ => ?_
  · prun [y5, ym, ey.h11, ey.hs.ld (d := slot w 3) (n := 8) (by rw [es]; omega),
      ey.hs.st (d := slot w 3) (n := 8) (by rw [es]; omega),
      ey.hs.st (d := slot w 3 + 8 * w) (n := 8) (by rw [es]; omega), BitVec.add_zero,
      VG.Proof.MillerRabin.PPC64LE.shl2_ofNat]
  · have ez : Env z B Z w := ey.keep kz (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (ez.base (rd := .r8) (by decide) (by decide) 3) fun a ⟨⟨a8, am⟩, ka⟩ => ?_
    refine WP.mono ((ez.keep ka (by decide)).base (rd := .r9) (by decide) (by decide) 6) fun b ⟨⟨b9, bm⟩, kb⟩ => ?_
    exact ⟨(kb.gpr .r8 (by decide)).trans a8, b9, bm.trans (am.trans zm)⟩

/-- The registers `ltC` writes. -/
def ltCRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r8, .r9, .r14, .r15, .r16, .r17, .r20]

/-- `r20` is all ones exactly when `(x | 1) < c`, for the draw `x` in array 4. -/
theorem ltC_ok {s : State} {B : Addr} {Z w c : Nat} (e : Env s B Z w) (hc : arr s.mem B w 0 = c) :
    WP isa ltC s fun t =>
      (t.gpr .r20 = 0#64 - BitVec.ofNat 64 (if (wv s.mem B (slot w 4) w ||| 1) < c then 1 else 0) ∧
        Frm B [(slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))] s.mem t.mem) ∧ Keep ltCRegs s t := by
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  unfold ltC
  -- The copy's bases.
  refine WP.seq (WP.mono (WP.keep [.r14, .r15] (Q := fun u => u.gpr .r14 = off B (slot w 3) ∧
      u.gpr .r15 = off B (slot w 4) ∧ u.mem = s.mem) ?_ (by decide)) fun u ⟨⟨u14, u15, um⟩, ku⟩ => ?_)
  · rw [WP.block_append_iff]
    refine WP.mono (e.base (rd := .r14) (by decide) (by decide) 3) fun v ⟨⟨v14, vm⟩, kv⟩ => ?_
    refine WP.mono ((e.keep kv (by decide)).base (rd := .r15) (by decide) (by decide) 4) fun x ⟨⟨x15, xm⟩, kx⟩ => ?_
    exact ⟨(kx.gpr .r14 (by decide)).trans v14, x15, xm.trans vm⟩
  have eu : Env u B Z w := e.keep ku (by decide)
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.PPC64LE.Search.copyWithin_ok (dS := slot w 4) (dD := slot w 3) eu.hs u15 u14 eu.h11 (by omega) (by omega)
    (by rw [es]; omega) (by rw [es]; omega) (by rw [es, es]; omega)) fun v ⟨⟨v14, vcp, vo⟩, kv⟩ => ?_)
  have ev : Env v B Z w := eu.keep kv (by decide)
  -- `x | 1` in array 3, its word `w` zeroed, and `subMod`'s bases.
  refine WP.seq (WP.mono (ltCMid_ok ev) fun x ⟨⟨x8, x9, xm⟩, kx⟩ => ?_)
  have ex : Env x B Z w := ev.keep kx (by decide)
  have h3 : slot w 3 + 8 * w + 8 ≤ 2 ^ 64 := by rw [es]; omega
  have h3' : slot w 3 + 8 ≤ 2 ^ 64 := by rw [es]; omega
  -- Array 3: `x | 1` in its first `w` words, 0 in its word `w`.
  have o1 := writeW_outside v.mem B (word v.mem B (slot w 3) ||| 1#64) h3'
  have o2 := writeW_outside (v.mem.writeW (off B (slot w 3)) (word v.mem B (slot w 3) ||| 1#64)) B 0#64 (d := slot w 3 + 8 * w) h3
  have w0 : word x.mem B (slot w 3) = word s.mem B (slot w 4) ||| 1#64 := by
    rw [xm, o2.word (by omega) h3', word_writeW_self]
    exact congrArg (· ||| 1#64) ((vcp 0 (by omega)).trans (by rw [um]; rfl))
  have wj : ∀ j < w, j ≠ 0 → word x.mem B (slot w 3 + 8 * j) = word s.mem B (slot w 4 + 8 * j) := fun j hj hj0 => by
    rw [xm, o2.word (by omega) (by omega), o1.word (by omega) (by omega)]
    exact (vcp j hj).trans (by rw [um])
  have hA : wv x.mem B (slot w 3) w = wv s.mem B (slot w 4) w ||| 1 :=
    VG.Proof.RsaKeyGen.wv_or_one (by omega) w0 wj
  have hAn : w32 x.mem B (slot w 3 + 4 * (2 * w)) = 0 := by
    have h0w : word x.mem B (slot w 3 + 8 * w) = 0#64 := by rw [xm, word_writeW_self]
    have := VG.Proof.Mont.word_eq_w32 x.mem B (slot w 3 + 8 * w)
    have e : VG.Proof.Mont.word x.mem B (slot w 3 + 8 * w) = word x.mem B (slot w 3 + 8 * w) := rfl
    rw [e, h0w] at this
    rw [show slot w 3 + 4 * (2 * w) = slot w 3 + 8 * w by omega]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at this
    omega
  have hM : val32 x.mem B (slot w 0) (2 * w) = c := by
    rw [← hc]
    show val32 x.mem B (slot w 0) (2 * w) = val32 s.mem B (slot w 0) (2 * w)
    rw [VG.Proof.Bignum.PPC64LE.Pre.val32_eq_wv, VG.Proof.Bignum.PPC64LE.Pre.val32_eq_wv, xm,
      o2.wv (by rw [es, es]; omega) (by rw [es]; omega), o1.wv (by rw [es, es]; omega) (by rw [es]; omega),
      vo.wv (by rw [es, es]; omega) (by rw [es]; omega), um]
  refine WP.mono (subMod_ok (dA := slot w 3) (dT := slot w 6) (dM := slot w 0) (n := 2 * w) ex.hs x8 x9 ex.h10 ex.h11
    (by omega) (by omega) (by rw [es]; omega) (by rw [es]; omega) (by rw [es]; omega) (by rw [es, es]; omega)
    (by rw [es, es]; omega)) fun y ⟨⟨cb, hcb, hsum, y20⟩, yo, ky⟩ => ?_
  refine ⟨⟨?_, ?_⟩, ((ku.trans kv).trans (kx.trans ky)).mono (by decide)⟩
  · rw [y20, hAn]
    rw [VG.Proof.Bignum.PPC64LE.Pre.val32_eq_wv x.mem B (slot w 3) w, hA, hM] at hsum
    have hT := val32_lt y.mem B (slot w 6) (2 * w)
    have hX := VG.Proof.Bignum.wv_lt s.mem B (slot w 4) w
    have hX1 : wv s.mem B (slot w 4) w ||| 1 < 2 ^ (64 * w) := Nat.or_lt_two_pow hX (by
      have := Nat.one_lt_two_pow (show 64 * w ≠ 0 by omega); omega)
    rw [show 32 * (2 * w) = 64 * w by omega] at hsum hT
    have key : (0 < cb) = (wv s.mem B (slot w 4) w ||| 1 < c) := by
      apply propext
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcb with h0 | h1
      · subst h0; omega
      · subst h1; omega
    simp only [key]
  · have f1 : Frm B [(slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))] s.mem x.mem := by
      refine Frm.trans (Frm.of_outside (o := slot w 3) (n := 8 * (w + 2)) (by rw [← um]; exact vo.mono (by omega) (by omega))
        (by simp)) ?_
      rw [xm]
      exact Frm.trans (Frm.of_outside (o := slot w 3) (n := 8 * (w + 2)) (o1.mono (by omega) (by omega)) (by simp))
        (Frm.of_outside (o := slot w 3) (n := 8 * (w + 2)) (o2.mono (by omega) (by omega)) (by simp))
    exact f1.trans (Frm.of_outside (o := slot w 6) (n := 8 * (w + 2)) (yo.mono (by omega) (by omega)) (by simp))

/-- `(2^b − 1) >> 1 = 2^(b−1) − 1`. -/
theorem mask_shr1 {b : Nat} (hb1 : 1 ≤ b) (hb : b ≤ 64) :
    BitVec.ofNat 64 (2 ^ b - 1) >>> 1 = BitVec.ofNat 64 (2 ^ (b - 1) - 1) := by
  have h1 : 2 ^ b = 2 * 2 ^ (b - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have h2 : 2 ^ b ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hb
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- The registers `force` writes. -/
def forceRegs : List Reg := [.r3, .r4, .r5, .r6]

/-- The draw `x < 2^(64 t + b)` in array 4 forced into the range:
`(x | 2) mod 2^(64 t + b − 1)`. -/
theorem force_ok {s : State} {B : Addr} {Z w t b : Nat} (e : Env s B Z w)
    (htop : word s.mem B (8 * hTop) = BitVec.ofNat 64 (2 ^ b - 1))
    (hoff : word s.mem B (8 * hTopOff) = BitVec.ofNat 64 (8 * t)) (ht0 : 0 < t) (htw : t < w) (hb1 : 1 ≤ b)
    (hb : b ≤ 64) (hV : wv s.mem B (slot w 4) w < 2 ^ (64 * t + b)) :
    WP isa (.block force) s fun s' =>
      (wv s'.mem B (slot w 4) w = (wv s.mem B (slot w 4) w ||| 2) % 2 ^ (64 * t + b - 1) ∧
        Frm B [(slot w 4, 8 * (w + 2))] s.mem s'.mem) ∧ Keep forceRegs s s' := by
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  have hw4 := e.hw
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  refine WP.keep _ ?_ (by decide)
  unfold force
  rw [WP.block_append_iff]
  refine WP.mono (e.base (rd := .r5) (by decide) (by decide) 4) fun y ⟨⟨y5, ym⟩, ky⟩ => ?_
  have hy : Scr y B Z := hs.congr ky.wr
  have y31 : y.gpr .r31 = B := (ky.gpr .r31 (by decide)).trans e.h31
  have h4 : slot w 4 + 8 ≤ 2 ^ 64 := by rw [es]; omega
  have h4t : slot w 4 + 8 * t + 8 ≤ 2 ^ 64 := by rw [es]; omega
  have o1 := writeW_outside s.mem B (word s.mem B (slot w 4) ||| 2#64) h4
  have r128 : (s.mem.writeW (off B (slot w 4)) (word s.mem B (slot w 4) ||| 2#64)).readW (B + 128#64) 64 =
      BitVec.ofNat 64 (8 * t) := (o1.word (by rw [es]; omega) (by omega)).trans hoff
  have r192 : (s.mem.writeW (off B (slot w 4)) (word s.mem B (slot w 4) ||| 2#64)).readW (B + 192#64) 64 =
      BitVec.ofNat 64 (2 ^ b - 1) := (o1.word (by rw [es]; omega) (by omega)).trans htop
  have rt : (s.mem.writeW (off B (slot w 4)) (word s.mem B (slot w 4) ||| 2#64)).readW (off B (slot w 4 + 8 * t)) 64 =
      word s.mem B (slot w 4 + 8 * t) := o1.word (by omega) h4t
  simp only [ldh, hTopOff, hTop]
  prun [y5, ym, y31, hy.ld (d := slot w 4) (n := 8) (by rw [es]; omega), hy.st (d := slot w 4) (n := 8) (by rw [es]; omega),
    hy.ld (d := 128) (n := 8) (by omega), hy.ld (d := 192) (n := 8) (by omega),
    hy.ld (d := slot w 4 + 8 * t) (n := 8) (by rw [es]; omega), hy.st (d := slot w 4 + 8 * t) (n := 8) (by rw [es]; omega),
    r128, r192, rt, mask_shr1 hb1 hb, BitVec.add_zero]
  have o2 := writeW_outside (s.mem.writeW (off B (slot w 4)) (word s.mem B (slot w 4) ||| 2#64)) B
    (word s.mem B (slot w 4 + 8 * t) &&& BitVec.ofNat 64 (2 ^ (b - 1) - 1)) h4t
  refine ⟨VG.Proof.RsaKeyGen.wv_fallback ht0 htw hb1 hb ?_ (word_writeW_self _ _ _ _) (fun j hj hj0 hjt => ?_) hV, ?_⟩
  · rw [o2.word (by omega) h4, word_writeW_self]
  · rw [o2.word (by omega) (by rw [es]; omega), o1.word (by omega) (by rw [es]; omega)]
  · exact Frm.trans (Frm.of_outside (o := slot w 4) (n := 8 * (w + 2)) (o1.mono (by omega) (by omega)) (by simp))
      (Frm.of_outside (o := slot w 4) (n := 8 * (w + 2)) (o2.mono (by omega) (by omega)) (by simp))

/-- One more uniform witness. -/
theorem countUni_ok {s : State} {B : Addr} {Z w u : Nat} (e : Env s B Z w)
    (hu : word s.mem B (8 * hUni) = BitVec.ofNat 64 u) :
    WP isa (.block countUni) s fun s' =>
      (word s'.mem B (8 * hUni) = BitVec.ofNat 64 (u + 1) ∧ Frm B [(8 * hUni, 8)] s.mem s'.mem) ∧ Keep [.r3] s s' := by
  have hs := e.hs
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  refine WP.keep _ ?_ (by decide)
  have r32 : s.mem.readW (B + 32#64) 64 = BitVec.ofNat 64 u := hu
  simp only [countUni, ldh, sth, hUni]
  prun [e.h31, hs.ld (d := 32) (n := 8) (by omega), hs.st (d := 32) (n := 8) (by omega), r32]
  refine ⟨by rw [show (B + 32#64 : Addr) = off B 32 from rfl, word_writeW_self, BitVec.ofNat_add], ?_⟩
  exact Frm.of_outside (o := 32) (n := 8) (writeW_outside _ _ _ (by omega)) (by simp)

/-- The registers `witness` writes. -/
def witRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r8, .r9, .r14, .r15, .r16, .r17, .r20, .r24]

/-- The ranges `witness` writes. -/
def witRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * hUni, 8), (slot w 3, 8 * (w + 2)), (slot w 4, 8 * (w + 2)), (slot w 6, 8 * (w + 2))]

/-- The draw `X`, cut to the bits of `c − 1` in array 4, made the witness
`Spec.RsaKeyGen.witness (c − 1) X`, and `hUni` counted if it is uniform. -/
theorem witness_ok {s : State} {B : Addr} {Z w c t b X u : Nat} (e : Env s B Z w) (hc : arr s.mem B w 0 = c)
    (hodd : c % 2 = 1) (hshape : Spec.RsaKeyGen.bitLength (c - 1) = 64 * t + b)
    (htop : word s.mem B (8 * hTop) = BitVec.ofNat 64 (2 ^ b - 1))
    (hoff : word s.mem B (8 * hTopOff) = BitVec.ofNat 64 (8 * t)) (ht0 : 0 < t) (htw : t < w) (hb1 : 1 ≤ b)
    (hb : b ≤ 64) (hx : wv s.mem B (slot w 4) w = X % 2 ^ (64 * t + b))
    (hu : word s.mem B (8 * hUni) = BitVec.ofNat 64 u) :
    WP isa witness s fun s' =>
      (wv s'.mem B (slot w 4) w = (Spec.RsaKeyGen.witness (c - 1) X).1 ∧
        word s'.mem B (8 * hUni) =
          BitVec.ofNat 64 (u + if (Spec.RsaKeyGen.witness (c - 1) X).2 then 1 else 0) ∧
        Frm B (witRanges w) s.mem s'.mem) ∧ Keep witRegs s s' := by
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  have hw4 := e.hw
  have hnw := e.hs.nowrap
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hspec : Spec.RsaKeyGen.witness (c - 1) X =
      if 2 ≤ X % 2 ^ (64 * t + b) ∧ X % 2 ^ (64 * t + b) < c - 1 then (X % 2 ^ (64 * t + b), true)
      else ((X % 2 ^ (64 * t + b) ||| 2) % 2 ^ (64 * t + b - 1), false) := by
    simp only [Spec.RsaKeyGen.witness, hshape]
  have hxl : wv s.mem B (slot w 4) w < 2 ^ (64 * t + b) := by rw [hx]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold witness
  refine WP.seq (WP.mono (atLeast2_ok e) fun t1 ⟨⟨t24, tm⟩, k1⟩ => ?_)
  have e1 : Env t1 B Z w := e.keep k1 (by decide)
  refine WP.seq (WP.mono (ltC_ok (c := c) e1 (by rw [tm]; exact hc)) fun t2 ⟨⟨t20, f2⟩, k2⟩ => ?_)
  have e2 : Env t2 B Z w := e1.keep k2 (by decide)
  have kw : ∀ d, d + 8 ≤ slot w 3 → word t2.mem B d = word s.mem B d := fun d hd => by
    rw [← tm]; exact f2.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [es] at hd ⊢ <;> omega) (by rw [es] at hd; omega)
  have x2 : wv t2.mem B (slot w 4) w = wv s.mem B (slot w 4) w := by
    rw [← tm]; exact f2.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [es] <;> omega) (by rw [es]; omega)
  have top2 := (kw _ (by simp only [hTop, es]; omega)).trans htop
  have off2 := (kw _ (by simp only [hTopOff, es]; omega)).trans hoff
  have u2 := (kw _ (by simp only [hUni, es]; omega)).trans hu
  have fr : ∀ m', Frm B [(slot w 4, 8 * (w + 2))] t2.mem m' ∨ Frm B [(8 * hUni, 8)] t2.mem m' →
      Frm B (witRanges w) s.mem m' := fun m' h => by
    have f2' : Frm B (witRanges w) s.mem t2.mem := by
      rw [← tm]; exact f2.mono (by simp [witRanges])
    rcases h with h | h
    · exact f2'.trans (h.mono (by simp [witRanges]))
    · exact f2'.trans (h.mono (by simp [witRanges]))
  have t24' : t2.gpr .r24 = 0#64 ↔ X % 2 ^ (64 * t + b) < 2 := by
    rw [k2.gpr .r24 (by decide), t24, hx]
  have hxv : wv t2.mem B (slot w 4) w = X % 2 ^ (64 * t + b) := x2.trans hx
  have hforce : ¬ (2 ≤ X % 2 ^ (64 * t + b) ∧ X % 2 ^ (64 * t + b) < c - 1) →
      WP isa (.block force) t2 fun s' =>
        (wv s'.mem B (slot w 4) w = (Spec.RsaKeyGen.witness (c - 1) X).1 ∧
          word s'.mem B (8 * hUni) =
            BitVec.ofNat 64 (u + if (Spec.RsaKeyGen.witness (c - 1) X).2 then 1 else 0) ∧
          Frm B (witRanges w) s.mem s'.mem) ∧ Keep witRegs s s' := fun hn => by
    rw [hspec]
    simp only [hn, ↓reduceIte]
    refine WP.mono (force_ok e2 top2 off2 ht0 htw hb1 hb (by rw [hxv]; exact Nat.mod_lt _ (Nat.two_pow_pos _)))
      fun s3 ⟨⟨v3, f3⟩, k3⟩ => ⟨⟨by rw [v3, hxv], ?_, fr _ (.inl f3)⟩, ((k1.trans k2).trans k3).mono (by decide)⟩
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    rw [← u2]
    exact f3.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; simp only [hUni, es]; omega) (by simp only [hUni]; omega)
  refine WP.ite (t2.gpr .r24 == 0#64) (VG.PPC64LE.eval_zero t2 .r24) (fun h0 => hforce ?_) (fun h0 => ?_)
  · have : X % 2 ^ (64 * t + b) < 2 := t24'.mp (by simpa using h0)
    omega
  have h2 : 2 ≤ X % 2 ^ (64 * t + b) := by
    have : ¬ t2.gpr .r24 = 0#64 := by simpa using h0
    rw [t24'] at this
    omega
  refine WP.ite (t2.gpr .r20 == 0#64) (VG.PPC64LE.eval_zero t2 .r20) (fun h1 => hforce ?_) (fun h1 => ?_)
  · rw [t20, tm, hx] at h1
    intro ⟨_, hlt⟩
    have : X % 2 ^ (64 * t + b) ||| 1 < c := (VG.Proof.RsaKeyGen.or_one_lt_iff hodd).mpr hlt
    simp [this] at h1
  · rw [t20, tm, hx] at h1
    have hlt : X % 2 ^ (64 * t + b) ||| 1 < c := by
      by_contra hn
      simp [hn] at h1
    have hlt' := (VG.Proof.RsaKeyGen.or_one_lt_iff hodd).mp hlt
    rw [hspec]
    simp only [h2, hlt', and_self, ↓reduceIte]
    refine WP.mono (countUni_ok e2 u2) fun s3 ⟨⟨v3, f3⟩, k3⟩ =>
      ⟨⟨?_, by simpa using v3, fr _ (.inr f3)⟩, ((k1.trans k2).trans k3).mono (by decide)⟩
    rw [← hxv]
    exact f3.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; simp only [hUni, es]; omega) (by rw [es]; omega)

end VG.Proof.MillerRabin.PPC64LE.Blinded
